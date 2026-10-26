import V185TrunkScan22Chunk211

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1890991 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 5]
def baseStart_1890991 : Nat := 118140960795 + 1890991 * 2 ^ 59
def prefixEnd_1890991 : Nat := 4983230072969 + 3 ^ 40 * 1890991 * 2
def baseEnd_1890991 : Nat := 215774954739181382825777

theorem tailTrace_1890991 : CollatzResearch.WordTrace tailWord_1890991 prefixEnd_1890991 215774954739181382825777 := by
  unfold tailWord_1890991
  simp only [CollatzResearch.WordTrace]
  refine ⟨68970107892270037396104827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45980071928180024930736551 68970107892270037396104827)
  ·
    refine ⟨103455161838405056094157241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68970107892270037396104827 103455161838405056094157241)
    ·
      refine ⟨77591371378803792070617931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103455161838405056094157241 77591371378803792070617931)
      ·
        refine ⟨116387057068205688105926897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77591371378803792070617931 116387057068205688105926897)
        ·
          refine ⟨87290292801154266079445173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116387057068205688105926897 87290292801154266079445173)
          ·
            refine ⟨8183464950108212444947985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87290292801154266079445173 8183464950108212444947985)
            ·
              refine ⟨6137598712581159333710989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8183464950108212444947985 6137598712581159333710989)
              ·
                refine ⟨2301599517217934750141621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6137598712581159333710989 2301599517217934750141621)
                ·
                  refine ⟨215774954739181382825777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2301599517217934750141621 215774954739181382825777)
                  ·
                    rfl

theorem cell22_1890991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 5].length) (baseStart_1890991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890991 prefixEnd_1890991 := by exact prefixLift 1890991
  have htrace : WordTrace (prefixWord ++ tailWord_1890991) baseStart_1890991 baseEnd_1890991 := by
    simpa [prefixWord, tailWord_1890991, baseEnd_1890991] using wordTrace_append hprefix tailTrace_1890991
  have hstable : (prefixWord ++ tailWord_1890991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890991).length < 2 ^ (prefixWord ++ tailWord_1890991).sum := by decide
  have hdescent : baseEnd_1890991 < baseStart_1890991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891006 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1891006 : Nat := 118140960795 + 1891006 * 2 ^ 59
def prefixEnd_1891006 : Nat := 4983230072969 + 3 ^ 40 * 1891006 * 2
def baseEnd_1891006 : Nat := 647329999024089109352285

theorem tailTrace_1891006 : CollatzResearch.WordTrace tailWord_1891006 prefixEnd_1891006 647329999024089109352285 := by
  unfold tailWord_1891006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8621331873401961869737609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45980436658143796638600581 8621331873401961869737609)
  ·
    refine ⟨6465998905051471402303207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8621331873401961869737609 6465998905051471402303207)
    ·
      refine ⟨9698998357577207103454811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6465998905051471402303207 9698998357577207103454811)
      ·
        refine ⟨14548497536365810655182217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698998357577207103454811 14548497536365810655182217)
        ·
          refine ⟨10911373152274357991386663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14548497536365810655182217 10911373152274357991386663)
          ·
            refine ⟨16367059728411536987079995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10911373152274357991386663 16367059728411536987079995)
            ·
              refine ⟨24550589592617305480619993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16367059728411536987079995 24550589592617305480619993)
              ·
                refine ⟨18412942194462979110464995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24550589592617305480619993 18412942194462979110464995)
                ·
                  refine ⟨27619413291694468665697493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18412942194462979110464995 27619413291694468665697493)
                  ·
                    refine ⟨647329999024089109352285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27619413291694468665697493 647329999024089109352285)
                    ·
                      rfl

theorem cell22_1891006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1891006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891006 prefixEnd_1891006 := by exact prefixLift 1891006
  have htrace : WordTrace (prefixWord ++ tailWord_1891006) baseStart_1891006 baseEnd_1891006 := by
    simpa [prefixWord, tailWord_1891006, baseEnd_1891006] using wordTrace_append hprefix tailTrace_1891006
  have hstable : (prefixWord ++ tailWord_1891006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891006).length < 2 ^ (prefixWord ++ tailWord_1891006).sum := by decide
  have hdescent : baseEnd_1891006 < baseStart_1891006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891012 : List Nat := [2, 3, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1891012 : Nat := 118140960795 + 1891012 * 2 ^ 59
def prefixEnd_1891012 : Nat := 4983230072969 + 3 ^ 40 * 1891012 * 2
def baseEnd_1891012 : Nat := 647332052946707093702267

theorem tailTrace_1891012 : CollatzResearch.WordTrace tailWord_1891012 prefixEnd_1891012 647332052946707093702267 := by
  unfold tailWord_1891012
  simp only [CollatzResearch.WordTrace]
  refine ⟨34485436912596978991309645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45980582550129305321746193 34485436912596978991309645)
  ·
    refine ⟨12932038842223867121741117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34485436912596978991309645 12932038842223867121741117)
    ·
      refine ⟨4849514565833950170652919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12932038842223867121741117 4849514565833950170652919)
      ·
        refine ⟨7274271848750925255979379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4849514565833950170652919 7274271848750925255979379)
        ·
          refine ⟨10911407773126387883969069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7274271848750925255979379 10911407773126387883969069)
          ·
            refine ⟨4091777914922395456488401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10911407773126387883969069 4091777914922395456488401)
            ·
              refine ⟨3068833436191796592366301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4091777914922395456488401 3068833436191796592366301)
              ·
                refine ⟨1150812538571923722137363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3068833436191796592366301 1150812538571923722137363)
                ·
                  refine ⟨1726218807857885583206045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150812538571923722137363 1726218807857885583206045)
                  ·
                    refine ⟨647332052946707093702267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726218807857885583206045 647332052946707093702267)
                    ·
                      rfl

theorem cell22_1891012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1891012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891012 prefixEnd_1891012 := by exact prefixLift 1891012
  have htrace : WordTrace (prefixWord ++ tailWord_1891012) baseStart_1891012 baseEnd_1891012 := by
    simpa [prefixWord, tailWord_1891012, baseEnd_1891012] using wordTrace_append hprefix tailTrace_1891012
  have hstable : (prefixWord ++ tailWord_1891012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891012).length < 2 ^ (prefixWord ++ tailWord_1891012).sum := by decide
  have hdescent : baseEnd_1891012 < baseStart_1891012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891066 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_1891066 : Nat := 118140960795 + 1891066 * 2 ^ 59
def prefixEnd_1891066 : Nat := 4983230072969 + 3 ^ 40 * 1891066 * 2
def baseEnd_1891066 : Nat := 647350538250268952852101

theorem tailTrace_1891066 : CollatzResearch.WordTrace tailWord_1891066 prefixEnd_1891066 647350538250268952852101 := by
  unfold tailWord_1891066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17243210841749581301271263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45981895577998883470056701 17243210841749581301271263)
  ·
    refine ⟨25864816262624371951906895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17243210841749581301271263 25864816262624371951906895)
    ·
      refine ⟨38797224393936557927860343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25864816262624371951906895 38797224393936557927860343)
      ·
        refine ⟨58195836590904836891790515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38797224393936557927860343 58195836590904836891790515)
        ·
          refine ⟨87293754886357255337685773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58195836590904836891790515 87293754886357255337685773)
          ·
            refine ⟨32735158082383970751632165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87293754886357255337685773 32735158082383970751632165)
            ·
              refine ⟨6137842140446994515931031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32735158082383970751632165 6137842140446994515931031)
              ·
                refine ⟨9206763210670491773896547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137842140446994515931031 9206763210670491773896547)
                ·
                  refine ⟨13810144816005737660844821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9206763210670491773896547 13810144816005737660844821)
                  ·
                    refine ⟨647350538250268952852101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13810144816005737660844821 647350538250268952852101)
                    ·
                      rfl

theorem cell22_1891066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_1891066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891066 prefixEnd_1891066 := by exact prefixLift 1891066
  have htrace : WordTrace (prefixWord ++ tailWord_1891066) baseStart_1891066 baseEnd_1891066 := by
    simpa [prefixWord, tailWord_1891066, baseEnd_1891066] using wordTrace_append hprefix tailTrace_1891066
  have hstable : (prefixWord ++ tailWord_1891066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891066).length < 2 ^ (prefixWord ++ tailWord_1891066).sum := by decide
  have hdescent : baseEnd_1891066 < baseStart_1891066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891068 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_1891068 : Nat := 118140960795 + 1891068 * 2 ^ 59
def prefixEnd_1891068 : Nat := 4983230072969 + 3 ^ 40 * 1891068 * 2
def baseEnd_1891068 : Nat := 647351222891141614302095

theorem tailTrace_1891068 : CollatzResearch.WordTrace tailWord_1891068 prefixEnd_1891068 647351222891141614302095 := by
  unfold tailWord_1891068
  simp only [CollatzResearch.WordTrace]
  refine ⟨34486458156495539773328929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45981944208660719697771905 34486458156495539773328929)
  ·
    refine ⟨25864843617371654829996697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34486458156495539773328929 25864843617371654829996697)
    ·
      refine ⟨19398632713028741122497523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25864843617371654829996697 19398632713028741122497523)
      ·
        refine ⟨29097949069543111683746285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19398632713028741122497523 29097949069543111683746285)
        ·
          refine ⟨10911730901078666881404857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29097949069543111683746285 10911730901078666881404857)
          ·
            refine ⟨8183798175809000161053643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10911730901078666881404857 8183798175809000161053643)
            ·
              refine ⟨12275697263713500241580465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183798175809000161053643 12275697263713500241580465)
              ·
                refine ⟨9206772947785125181185349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12275697263713500241580465 9206772947785125181185349)
                ·
                  refine ⟨1726269927709710971472253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9206772947785125181185349 1726269927709710971472253)
                  ·
                    refine ⟨647351222891141614302095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726269927709710971472253 647351222891141614302095)
                    ·
                      rfl

theorem cell22_1891068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_1891068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891068 prefixEnd_1891068 := by exact prefixLift 1891068
  have htrace : WordTrace (prefixWord ++ tailWord_1891068) baseStart_1891068 baseEnd_1891068 := by
    simpa [prefixWord, tailWord_1891068, baseEnd_1891068] using wordTrace_append hprefix tailTrace_1891068
  have hstable : (prefixWord ++ tailWord_1891068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891068).length < 2 ^ (prefixWord ++ tailWord_1891068).sum := by decide
  have hdescent : baseEnd_1891068 < baseStart_1891068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891173 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_1891173 : Nat := 118140960795 + 1891173 * 2 ^ 59
def prefixEnd_1891173 : Nat := 4983230072969 + 3 ^ 40 * 1891173 * 2
def baseEnd_1891173 : Nat := 647387166536956340426773

theorem tailTrace_1891173 : CollatzResearch.WordTrace tailWord_1891173 prefixEnd_1891173 647387166536956340426773 := by
  unfold tailWord_1891173
  simp only [CollatzResearch.WordTrace]
  refine ⟨68976745977610682479230173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45984497318407121652820115 68976745977610682479230173)
  ·
    refine ⟨25866279741604005929711315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68976745977610682479230173 25866279741604005929711315)
    ·
      refine ⟨38799419612406008894566973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25866279741604005929711315 38799419612406008894566973)
      ·
        refine ⟨14549782354652253335462615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38799419612406008894566973 14549782354652253335462615)
        ·
          refine ⟨21824673531978380003193923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14549782354652253335462615 21824673531978380003193923)
          ·
            refine ⟨32737010297967570004790885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21824673531978380003193923 32737010297967570004790885)
            ·
              refine ⟨6138189430868919375898291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32737010297967570004790885 6138189430868919375898291)
              ·
                refine ⟨9207284146303379063847437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138189430868919375898291 9207284146303379063847437)
                ·
                  refine ⟨3452731554863767148942789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9207284146303379063847437 3452731554863767148942789)
                  ·
                    refine ⟨647387166536956340426773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3452731554863767148942789 647387166536956340426773)
                    ·
                      rfl

theorem cell22_1891173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_1891173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891173 prefixEnd_1891173 := by exact prefixLift 1891173
  have htrace : WordTrace (prefixWord ++ tailWord_1891173) baseStart_1891173 baseEnd_1891173 := by
    simpa [prefixWord, tailWord_1891173, baseEnd_1891173] using wordTrace_append hprefix tailTrace_1891173
  have hstable : (prefixWord ++ tailWord_1891173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891173).length < 2 ^ (prefixWord ++ tailWord_1891173).sum := by decide
  have hdescent : baseEnd_1891173 < baseStart_1891173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891205 : List Nat := [1, 3, 1, 1, 3, 3, 2, 4, 4]
def baseStart_1891205 : Nat := 118140960795 + 1891205 * 2 ^ 59
def prefixEnd_1891205 : Nat := 4983230072969 + 3 ^ 40 * 1891205 * 2
def baseEnd_1891205 : Nat := 215799373596972974542225

theorem tailTrace_1891205 : CollatzResearch.WordTrace tailWord_1891205 prefixEnd_1891205 215799373596972974542225 := by
  unfold tailWord_1891205
  simp only [CollatzResearch.WordTrace]
  refine ⟨68977913113494751944395069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45985275408996501296263379 68977913113494751944395069)
  ·
    refine ⟨25866717417560531979148151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68977913113494751944395069 25866717417560531979148151)
    ·
      refine ⟨38800076126340797968722227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25866717417560531979148151 38800076126340797968722227)
      ·
        refine ⟨58200114189511196953083341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38800076126340797968722227 58200114189511196953083341)
        ·
          refine ⟨21825042821066698857406253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58200114189511196953083341 21825042821066698857406253)
          ·
            refine ⟨8184391057900012071527345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21825042821066698857406253 8184391057900012071527345)
            ·
              refine ⟨6138293293425009053645509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8184391057900012071527345 6138293293425009053645509)
              ·
                refine ⟨1150929992517189197558533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6138293293425009053645509 1150929992517189197558533)
                ·
                  refine ⟨215799373596972974542225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1150929992517189197558533 215799373596972974542225)
                  ·
                    rfl

theorem cell22_1891205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_1891205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891205 prefixEnd_1891205 := by exact prefixLift 1891205
  have htrace : WordTrace (prefixWord ++ tailWord_1891205) baseStart_1891205 baseEnd_1891205 := by
    simpa [prefixWord, tailWord_1891205, baseEnd_1891205] using wordTrace_append hprefix tailTrace_1891205
  have hstable : (prefixWord ++ tailWord_1891205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891205).length < 2 ^ (prefixWord ++ tailWord_1891205).sum := by decide
  have hdescent : baseEnd_1891205 < baseStart_1891205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891239 : List Nat := [1, 1, 6, 1, 3, 2, 1, 3, 4]
def baseStart_1891239 : Nat := 118140960795 + 1891239 * 2 ^ 59
def prefixEnd_1891239 : Nat := 4983230072969 + 3 ^ 40 * 1891239 * 2
def baseEnd_1891239 : Nat := 215803253228584722758857

theorem tailTrace_1891239 : CollatzResearch.WordTrace tailWord_1891239 prefixEnd_1891239 215803253228584722758857 := by
  unfold tailWord_1891239
  simp only [CollatzResearch.WordTrace]
  refine ⟨68979153195371575751132771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45986102130247717167421847 68979153195371575751132771)
  ·
    refine ⟨103468729793057363626699157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68979153195371575751132771 103468729793057363626699157)
    ·
      refine ⟨4850096709049563920001523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103468729793057363626699157 4850096709049563920001523)
      ·
        refine ⟨7275145063574345880002285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850096709049563920001523 7275145063574345880002285)
        ·
          refine ⟨2728179398840379705000857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7275145063574345880002285 2728179398840379705000857)
          ·
            refine ⟨2046134549130284778750643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728179398840379705000857 2046134549130284778750643)
            ·
              refine ⟨3069201823695427168125965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046134549130284778750643 3069201823695427168125965)
              ·
                refine ⟨1150950683885785188047237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3069201823695427168125965 1150950683885785188047237)
                ·
                  refine ⟨215803253228584722758857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1150950683885785188047237 215803253228584722758857)
                  ·
                    rfl

theorem cell22_1891239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 4].length) (baseStart_1891239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891239 prefixEnd_1891239 := by exact prefixLift 1891239
  have htrace : WordTrace (prefixWord ++ tailWord_1891239) baseStart_1891239 baseEnd_1891239 := by
    simpa [prefixWord, tailWord_1891239, baseEnd_1891239] using wordTrace_append hprefix tailTrace_1891239
  have hstable : (prefixWord ++ tailWord_1891239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891239).length < 2 ^ (prefixWord ++ tailWord_1891239).sum := by decide
  have hdescent : baseEnd_1891239 < baseStart_1891239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891252 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1891252 : Nat := 118140960795 + 1891252 * 2 ^ 59
def prefixEnd_1891252 : Nat := 4983230072969 + 3 ^ 40 * 1891252 * 2
def baseEnd_1891252 : Nat := 647414209851426467701531

theorem tailTrace_1891252 : CollatzResearch.WordTrace tailWord_1891252 prefixEnd_1891252 647414209851426467701531 := by
  unfold tailWord_1891252
  simp only [CollatzResearch.WordTrace]
  refine ⟨34489813672162239485678005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45986418229549652647570673 34489813672162239485678005)
  ·
    refine ⟨3233420031765209951782313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34489813672162239485678005 3233420031765209951782313)
    ·
      refine ⟨2425065023823907463836735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3233420031765209951782313 2425065023823907463836735)
      ·
        refine ⟨3637597535735861195755103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425065023823907463836735 3637597535735861195755103)
        ·
          refine ⟨5456396303603791793632655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637597535735861195755103 5456396303603791793632655)
          ·
            refine ⟨8184594455405687690448983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456396303603791793632655 8184594455405687690448983)
            ·
              refine ⟨12276891683108531535673475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8184594455405687690448983 12276891683108531535673475)
              ·
                refine ⟨18415337524662797303510213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12276891683108531535673475 18415337524662797303510213)
                ·
                  refine ⟨3452875785874274494408165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18415337524662797303510213 3452875785874274494408165)
                  ·
                    refine ⟨647414209851426467701531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3452875785874274494408165 647414209851426467701531)
                    ·
                      rfl

theorem cell22_1891252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1891252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891252 prefixEnd_1891252 := by exact prefixLift 1891252
  have htrace : WordTrace (prefixWord ++ tailWord_1891252) baseStart_1891252 baseEnd_1891252 := by
    simpa [prefixWord, tailWord_1891252, baseEnd_1891252] using wordTrace_append hprefix tailTrace_1891252
  have hstable : (prefixWord ++ tailWord_1891252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891252).length < 2 ^ (prefixWord ++ tailWord_1891252).sum := by decide
  have hdescent : baseEnd_1891252 < baseStart_1891252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891323 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 6]
def baseStart_1891323 : Nat := 118140960795 + 1891323 * 2 ^ 59
def prefixEnd_1891323 : Nat := 4983230072969 + 3 ^ 40 * 1891323 * 2
def baseEnd_1891323 : Nat := 215812838200801983058771

theorem tailTrace_1891323 : CollatzResearch.WordTrace tailWord_1891323 prefixEnd_1891323 215812838200801983058771 := by
  unfold tailWord_1891323
  simp only [CollatzResearch.WordTrace]
  refine ⟨68982216927067258097190623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45988144618044838731460415 68982216927067258097190623)
  ·
    refine ⟨103473325390600887145785935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68982216927067258097190623 103473325390600887145785935)
    ·
      refine ⟨155209988085901330718678903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103473325390600887145785935 155209988085901330718678903)
      ·
        refine ⟨232814982128851996078018355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155209988085901330718678903 232814982128851996078018355)
        ·
          refine ⟨349222473193277994117027533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232814982128851996078018355 349222473193277994117027533)
          ·
            refine ⟨130958427447479247793885325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349222473193277994117027533 130958427447479247793885325)
            ·
              refine ⟨49109410292804717922706997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130958427447479247793885325 49109410292804717922706997)
              ·
                refine ⟨4604007214950442305253781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49109410292804717922706997 4604007214950442305253781)
                ·
                  refine ⟨215812838200801983058771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4604007214950442305253781 215812838200801983058771)
                  ·
                    rfl

theorem cell22_1891323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 6].length) (baseStart_1891323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891323 prefixEnd_1891323 := by exact prefixLift 1891323
  have htrace : WordTrace (prefixWord ++ tailWord_1891323) baseStart_1891323 baseEnd_1891323 := by
    simpa [prefixWord, tailWord_1891323, baseEnd_1891323] using wordTrace_append hprefix tailTrace_1891323
  have hstable : (prefixWord ++ tailWord_1891323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891323).length < 2 ^ (prefixWord ++ tailWord_1891323).sum := by decide
  have hdescent : baseEnd_1891323 < baseStart_1891323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891340 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 6]
def baseStart_1891340 : Nat := 118140960795 + 1891340 * 2 ^ 59
def prefixEnd_1891340 : Nat := 4983230072969 + 3 ^ 40 * 1891340 * 2
def baseEnd_1891340 : Nat := 215814778016607857167087

theorem tailTrace_1891340 : CollatzResearch.WordTrace tailWord_1891340 prefixEnd_1891340 215814778016607857167087 := by
  unfold tailWord_1891340
  simp only [CollatzResearch.WordTrace]
  refine ⟨34491418484002835000279737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45988557978670446667039649 34491418484002835000279737)
  ·
    refine ⟨25868563863002126250209803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34491418484002835000279737 25868563863002126250209803)
    ·
      refine ⟨38802845794503189375314705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25868563863002126250209803 38802845794503189375314705)
      ·
        refine ⟨29102134345877392031486029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38802845794503189375314705 29102134345877392031486029)
        ·
          refine ⟨10913300379704022011807261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29102134345877392031486029 10913300379704022011807261)
          ·
            refine ⟨4092487642389008254427723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10913300379704022011807261 4092487642389008254427723)
            ·
              refine ⟨6138731463583512381641585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092487642389008254427723 6138731463583512381641585)
              ·
                refine ⟨4604048597687634286231189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6138731463583512381641585 4604048597687634286231189)
                ·
                  refine ⟨215814778016607857167087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4604048597687634286231189 215814778016607857167087)
                  ·
                    rfl

theorem cell22_1891340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_1891340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891340 prefixEnd_1891340 := by exact prefixLift 1891340
  have htrace : WordTrace (prefixWord ++ tailWord_1891340) baseStart_1891340 baseEnd_1891340 := by
    simpa [prefixWord, tailWord_1891340, baseEnd_1891340] using wordTrace_append hprefix tailTrace_1891340
  have hstable : (prefixWord ++ tailWord_1891340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891340).length < 2 ^ (prefixWord ++ tailWord_1891340).sum := by decide
  have hdescent : baseEnd_1891340 < baseStart_1891340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891359 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 1, 4]
def baseStart_1891359 : Nat := 118140960795 + 1891359 * 2 ^ 59
def prefixEnd_1891359 : Nat := 4983230072969 + 3 ^ 40 * 1891359 * 2
def baseEnd_1891359 : Nat := 647450838138113855276203

theorem tailTrace_1891359 : CollatzResearch.WordTrace tailWord_1891359 prefixEnd_1891359 647450838138113855276203 := by
  unfold tailWord_1891359
  simp only [CollatzResearch.WordTrace]
  refine ⟨68983529954936836245501131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45989019969957890830334087 68983529954936836245501131)
  ·
    refine ⟨103475294932405254368251697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68983529954936836245501131 103475294932405254368251697)
    ·
      refine ⟨77606471199303940776188773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103475294932405254368251697 77606471199303940776188773)
      ·
        refine ⟨14551213349869488895535395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77606471199303940776188773 14551213349869488895535395)
        ·
          refine ⟨21826820024804233343303093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14551213349869488895535395 21826820024804233343303093)
          ·
            refine ⟨2046264377325396875934665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21826820024804233343303093 2046264377325396875934665)
            ·
              refine ⟨1534698282994047656950999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046264377325396875934665 1534698282994047656950999)
              ·
                refine ⟨2302047424491071485426499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534698282994047656950999 2302047424491071485426499)
                ·
                  refine ⟨3453071136736607228139749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302047424491071485426499 3453071136736607228139749)
                  ·
                    refine ⟨647450838138113855276203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3453071136736607228139749 647450838138113855276203)
                    ·
                      rfl

theorem cell22_1891359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 4].length) (baseStart_1891359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891359 prefixEnd_1891359 := by exact prefixLift 1891359
  have htrace : WordTrace (prefixWord ++ tailWord_1891359) baseStart_1891359 baseEnd_1891359 := by
    simpa [prefixWord, tailWord_1891359, baseEnd_1891359] using wordTrace_append hprefix tailTrace_1891359
  have hstable : (prefixWord ++ tailWord_1891359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891359).length < 2 ^ (prefixWord ++ tailWord_1891359).sum := by decide
  have hdescent : baseEnd_1891359 < baseStart_1891359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891434 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1891434 : Nat := 118140960795 + 1891434 * 2 ^ 59
def prefixEnd_1891434 : Nat := 4983230072969 + 3 ^ 40 * 1891434 * 2
def baseEnd_1891434 : Nat := 647476512170838659650973

theorem tailTrace_1891434 : CollatzResearch.WordTrace tailWord_1891434 prefixEnd_1891434 647476512170838659650973 := by
  unfold tailWord_1891434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17246566357416281013620339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45990843619776749369654237 17246566357416281013620339)
  ·
    refine ⟨25869849536124421520430509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17246566357416281013620339 25869849536124421520430509)
    ·
      refine ⟨9701193576046658070161441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25869849536124421520430509 9701193576046658070161441)
      ·
        refine ⟨7275895182034993552621081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9701193576046658070161441 7275895182034993552621081)
        ·
          refine ⟨5456921386526245164465811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7275895182034993552621081 5456921386526245164465811)
          ·
            refine ⟨8185382079789367746698717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456921386526245164465811 8185382079789367746698717)
            ·
              refine ⟨3069518279921012905012019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8185382079789367746698717 3069518279921012905012019)
              ·
                refine ⟨4604277419881519357518029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069518279921012905012019 4604277419881519357518029)
                ·
                  refine ⟨1726604032455569759069261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4604277419881519357518029 1726604032455569759069261)
                  ·
                    refine ⟨647476512170838659650973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726604032455569759069261 647476512170838659650973)
                    ·
                      rfl

theorem cell22_1891434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1891434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891434 prefixEnd_1891434 := by exact prefixLift 1891434
  have htrace : WordTrace (prefixWord ++ tailWord_1891434) baseStart_1891434 baseEnd_1891434 := by
    simpa [prefixWord, tailWord_1891434, baseEnd_1891434] using wordTrace_append hprefix tailTrace_1891434
  have hstable : (prefixWord ++ tailWord_1891434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891434).length < 2 ^ (prefixWord ++ tailWord_1891434).sum := by decide
  have hdescent : baseEnd_1891434 < baseStart_1891434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891541 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_1891541 : Nat := 118140960795 + 1891541 * 2 ^ 59
def prefixEnd_1891541 : Nat := 4983230072969 + 3 ^ 40 * 1891541 * 2
def baseEnd_1891541 : Nat := 647513140457526047225645

theorem tailTrace_1891541 : CollatzResearch.WordTrace tailWord_1891541 prefixEnd_1891541 647513140457526047225645 := by
  unfold tailWord_1891541
  simp only [CollatzResearch.WordTrace]
  refine ⟨68990168040277481328626477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45993445360184987552417651 68990168040277481328626477)
  ·
    refine ⟨25871313015104055498234929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68990168040277481328626477 25871313015104055498234929)
    ·
      refine ⟨19403484761328041623676197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25871313015104055498234929 19403484761328041623676197)
      ·
        refine ⟨3638153392749007804439287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19403484761328041623676197 3638153392749007804439287)
        ·
          refine ⟨5457230089123511706658931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638153392749007804439287 5457230089123511706658931)
          ·
            refine ⟨8185845133685267559988397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5457230089123511706658931 8185845133685267559988397)
            ·
              refine ⟨3069691925131975334995649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8185845133685267559988397 3069691925131975334995649)
              ·
                refine ⟨2302268943848981501246737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3069691925131975334995649 2302268943848981501246737)
                ·
                  refine ⟨1726701707886736125935053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2302268943848981501246737 1726701707886736125935053)
                  ·
                    refine ⟨647513140457526047225645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726701707886736125935053 647513140457526047225645)
                    ·
                      rfl

theorem cell22_1891541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_1891541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891541 prefixEnd_1891541 := by exact prefixLift 1891541
  have htrace : WordTrace (prefixWord ++ tailWord_1891541) baseStart_1891541 baseEnd_1891541 := by
    simpa [prefixWord, tailWord_1891541, baseEnd_1891541] using wordTrace_append hprefix tailTrace_1891541
  have hstable : (prefixWord ++ tailWord_1891541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891541).length < 2 ^ (prefixWord ++ tailWord_1891541).sum := by decide
  have hdescent : baseEnd_1891541 < baseStart_1891541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891710 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1891710 : Nat := 118140960795 + 1891710 * 2 ^ 59
def prefixEnd_1891710 : Nat := 4983230072969 + 3 ^ 40 * 1891710 * 2
def baseEnd_1891710 : Nat := 647570992611265939750127

theorem tailTrace_1891710 : CollatzResearch.WordTrace tailWord_1891710 prefixEnd_1891710 647570992611265939750127 := by
  unfold tailWord_1891710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8624541497083152898941073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45997554651110148794352389 8624541497083152898941073)
  ·
    refine ⟨6468406122812364674205805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8624541497083152898941073 6468406122812364674205805)
    ·
      refine ⟨2425652296054636752827177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6468406122812364674205805 2425652296054636752827177)
      ·
        refine ⟨1819239222040977564620383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425652296054636752827177 1819239222040977564620383)
        ·
          refine ⟨2728858833061466346930575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819239222040977564620383 2728858833061466346930575)
          ·
            refine ⟨4093288249592199520395863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728858833061466346930575 4093288249592199520395863)
            ·
              refine ⟨6139932374388299280593795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093288249592199520395863 6139932374388299280593795)
              ·
                refine ⟨9209898561582448920890693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139932374388299280593795 9209898561582448920890693)
                ·
                  refine ⟨1726855980296709172667005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9209898561582448920890693 1726855980296709172667005)
                  ·
                    refine ⟨647570992611265939750127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726855980296709172667005 647570992611265939750127)
                    ·
                      rfl

theorem cell22_1891710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1891710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891710 prefixEnd_1891710 := by exact prefixLift 1891710
  have htrace : WordTrace (prefixWord ++ tailWord_1891710) baseStart_1891710 baseEnd_1891710 := by
    simpa [prefixWord, tailWord_1891710, baseEnd_1891710] using wordTrace_append hprefix tailTrace_1891710
  have hstable : (prefixWord ++ tailWord_1891710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891710).length < 2 ^ (prefixWord ++ tailWord_1891710).sum := by decide
  have hdescent : baseEnd_1891710 < baseStart_1891710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891740 : List Nat := [2, 2, 3, 4, 2, 1, 2, 6]
def baseStart_1891740 : Nat := 118140960795 + 1891740 * 2 ^ 59
def prefixEnd_1891740 : Nat := 4983230072969 + 3 ^ 40 * 1891740 * 2
def baseEnd_1891740 : Nat := 71953473580483984611115

theorem tailTrace_1891740 : CollatzResearch.WordTrace tailWord_1891740 prefixEnd_1891740 71953473580483984611115 := by
  unfold tailWord_1891740
  simp only [CollatzResearch.WordTrace]
  refine ⟨34498713083278269157560337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45998284111037692210080449 34498713083278269157560337)
  ·
    refine ⟨25874034812458701868170253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34498713083278269157560337 25874034812458701868170253)
    ·
      refine ⟨9702763054672013200563845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25874034812458701868170253 9702763054672013200563845)
      ·
        refine ⟨1819268072751002475105721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9702763054672013200563845 1819268072751002475105721)
        ·
          refine ⟨1364451054563251856329291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1819268072751002475105721 1364451054563251856329291)
          ·
            refine ⟨2046676581844877784493937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364451054563251856329291 2046676581844877784493937)
            ·
              refine ⟨1535007436383658338370453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046676581844877784493937 1535007436383658338370453)
              ·
                refine ⟨71953473580483984611115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1535007436383658338370453 71953473580483984611115)
                ·
                  rfl

theorem cell22_1891740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 6].length) (baseStart_1891740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891740 prefixEnd_1891740 := by exact prefixLift 1891740
  have htrace : WordTrace (prefixWord ++ tailWord_1891740) baseStart_1891740 baseEnd_1891740 := by
    simpa [prefixWord, tailWord_1891740, baseEnd_1891740] using wordTrace_append hprefix tailTrace_1891740
  have hstable : (prefixWord ++ tailWord_1891740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891740).length < 2 ^ (prefixWord ++ tailWord_1891740).sum := by decide
  have hdescent : baseEnd_1891740 < baseStart_1891740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891772 : List Nat := [2, 2, 2, 4, 2, 1, 3, 2, 1, 3]
def baseStart_1891772 : Nat := 118140960795 + 1891772 * 2 ^ 59
def prefixEnd_1891772 : Nat := 4983230072969 + 3 ^ 40 * 1891772 * 2
def baseEnd_1891772 : Nat := 647592216478318444699937

theorem tailTrace_1891772 : CollatzResearch.WordTrace tailWord_1891772 prefixEnd_1891772 647592216478318444699937 := by
  unfold tailWord_1891772
  simp only [CollatzResearch.WordTrace]
  refine ⟨34499296651220303890142785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45999062201627071853523713 34499296651220303890142785)
  ·
    refine ⟨25874472488415227917607089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34499296651220303890142785 25874472488415227917607089)
    ·
      refine ⟨19405854366311420938205317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25874472488415227917607089 19405854366311420938205317)
      ·
        refine ⟨3638597693683391425913497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19405854366311420938205317 3638597693683391425913497)
        ·
          refine ⟨2728948270262543569435123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3638597693683391425913497 2728948270262543569435123)
          ·
            refine ⟨4093422405393815354152685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728948270262543569435123 4093422405393815354152685)
            ·
              refine ⟨1535033402022680757807257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4093422405393815354152685 1535033402022680757807257)
              ·
                refine ⟨1151275051517010568355443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535033402022680757807257 1151275051517010568355443)
                ·
                  refine ⟨1726912577275515852533165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151275051517010568355443 1726912577275515852533165)
                  ·
                    refine ⟨647592216478318444699937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726912577275515852533165 647592216478318444699937)
                    ·
                      rfl

theorem cell22_1891772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_1891772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891772 prefixEnd_1891772 := by exact prefixLift 1891772
  have htrace : WordTrace (prefixWord ++ tailWord_1891772) baseStart_1891772 baseEnd_1891772 := by
    simpa [prefixWord, tailWord_1891772, baseEnd_1891772] using wordTrace_append hprefix tailTrace_1891772
  have hstable : (prefixWord ++ tailWord_1891772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891772).length < 2 ^ (prefixWord ++ tailWord_1891772).sum := by decide
  have hdescent : baseEnd_1891772 < baseStart_1891772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891778 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1891778 : Nat := 118140960795 + 1891778 * 2 ^ 59
def prefixEnd_1891778 : Nat := 4983230072969 + 3 ^ 40 * 1891778 * 2
def baseEnd_1891778 : Nat := 647594270400936429049919

theorem tailTrace_1891778 : CollatzResearch.WordTrace tailWord_1891778 prefixEnd_1891778 647594270400936429049919 := by
  unfold tailWord_1891778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17249703035104717701250997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45999208093612580536669325 17249703035104717701250997)
  ·
    refine ⟨1617159659541067284492281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17249703035104717701250997 1617159659541067284492281)
    ·
      refine ⟨1212869744655800463369211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1617159659541067284492281 1212869744655800463369211)
      ·
        refine ⟨1819304616983700695053817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212869744655800463369211 1819304616983700695053817)
        ·
          refine ⟨1364478462737775521290363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1819304616983700695053817 1364478462737775521290363)
          ·
            refine ⟨2046717694106663281935545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364478462737775521290363 2046717694106663281935545)
            ·
              refine ⟨1535038270579997461451659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046717694106663281935545 1535038270579997461451659)
              ·
                refine ⟨2302557405869996192177489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535038270579997461451659 2302557405869996192177489)
                ·
                  refine ⟨1726918054402497144133117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2302557405869996192177489 1726918054402497144133117)
                  ·
                    refine ⟨647594270400936429049919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726918054402497144133117 647594270400936429049919)
                    ·
                      rfl

theorem cell22_1891778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1891778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891778 prefixEnd_1891778 := by exact prefixLift 1891778
  have htrace : WordTrace (prefixWord ++ tailWord_1891778) baseStart_1891778 baseEnd_1891778 := by
    simpa [prefixWord, tailWord_1891778, baseEnd_1891778] using wordTrace_append hprefix tailTrace_1891778
  have hstable : (prefixWord ++ tailWord_1891778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891778).length < 2 ^ (prefixWord ++ tailWord_1891778).sum := by decide
  have hdescent : baseEnd_1891778 < baseStart_1891778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891779 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 6]
def baseStart_1891779 : Nat := 118140960795 + 1891779 * 2 ^ 59
def prefixEnd_1891779 : Nat := 4983230072969 + 3 ^ 40 * 1891779 * 2
def baseEnd_1891779 : Nat := 215864870907124253258305

theorem tailTrace_1891779 : CollatzResearch.WordTrace tailWord_1891779 prefixEnd_1891779 215864870907124253258305 := by
  unfold tailWord_1891779
  simp only [CollatzResearch.WordTrace]
  refine ⟨68998848613415247975790391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45999232408943498650526927 68998848613415247975790391)
  ·
    refine ⟨103498272920122871963685587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68998848613415247975790391 103498272920122871963685587)
    ·
      refine ⟨155247409380184307945528381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103498272920122871963685587 155247409380184307945528381)
      ·
        refine ⟨58217778517569115479573143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155247409380184307945528381 58217778517569115479573143)
        ·
          refine ⟨87326667776353673219359715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58217778517569115479573143 87326667776353673219359715)
          ·
            refine ⟨130990001664530509829039573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87326667776353673219359715 130990001664530509829039573)
            ·
              refine ⟨3070078164012433824118115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 130990001664530509829039573 3070078164012433824118115)
              ·
                refine ⟨4605117246018650736177173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070078164012433824118115 4605117246018650736177173)
                ·
                  refine ⟨215864870907124253258305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4605117246018650736177173 215864870907124253258305)
                  ·
                    rfl

theorem cell22_1891779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 6].length) (baseStart_1891779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891779 prefixEnd_1891779 := by exact prefixLift 1891779
  have htrace : WordTrace (prefixWord ++ tailWord_1891779) baseStart_1891779 baseEnd_1891779 := by
    simpa [prefixWord, tailWord_1891779, baseEnd_1891779] using wordTrace_append hprefix tailTrace_1891779
  have hstable : (prefixWord ++ tailWord_1891779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891779).length < 2 ^ (prefixWord ++ tailWord_1891779).sum := by decide
  have hdescent : baseEnd_1891779 < baseStart_1891779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891798 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1891798 : Nat := 118140960795 + 1891798 * 2 ^ 59
def prefixEnd_1891798 : Nat := 4983230072969 + 3 ^ 40 * 1891798 * 2
def baseEnd_1891798 : Nat := 647601116809663043549857

theorem tailTrace_1891798 : CollatzResearch.WordTrace tailWord_1891798 prefixEnd_1891798 647601116809663043549857 := by
  unfold tailWord_1891798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4312471350021650888795753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45999694400230942813821365 4312471350021650888795753)
  ·
    refine ⟨3234353512516238166596815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4312471350021650888795753 3234353512516238166596815)
    ·
      refine ⟨4851530268774357249895223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3234353512516238166596815 4851530268774357249895223)
      ·
        refine ⟨7277295403161535874842835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851530268774357249895223 7277295403161535874842835)
        ·
          refine ⟨10915943104742303812264253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277295403161535874842835 10915943104742303812264253)
          ·
            refine ⟨4093478664278363929599095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10915943104742303812264253 4093478664278363929599095)
            ·
              refine ⟨6140217996417545894398643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093478664278363929599095 6140217996417545894398643)
              ·
                refine ⟨9210326994626318841597965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140217996417545894398643 9210326994626318841597965)
                ·
                  refine ⟨3453872622984869565599237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9210326994626318841597965 3453872622984869565599237)
                  ·
                    refine ⟨647601116809663043549857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3453872622984869565599237 647601116809663043549857)
                    ·
                      rfl

theorem cell22_1891798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1891798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891798 prefixEnd_1891798 := by exact prefixLift 1891798
  have htrace : WordTrace (prefixWord ++ tailWord_1891798) baseStart_1891798 baseEnd_1891798 := by
    simpa [prefixWord, tailWord_1891798, baseEnd_1891798] using wordTrace_append hprefix tailTrace_1891798
  have hstable : (prefixWord ++ tailWord_1891798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891798).length < 2 ^ (prefixWord ++ tailWord_1891798).sum := by decide
  have hdescent : baseEnd_1891798 < baseStart_1891798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891811 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 1, 5]
def baseStart_1891811 : Nat := 118140960795 + 1891811 * 2 ^ 59
def prefixEnd_1891811 : Nat := 4983230072969 + 3 ^ 40 * 1891811 * 2
def baseEnd_1891811 : Nat := 647605566975335342974817

theorem tailTrace_1891811 : CollatzResearch.WordTrace tailWord_1891811 prefixEnd_1891811 647605566975335342974817 := by
  unfold tailWord_1891811
  simp only [CollatzResearch.WordTrace]
  refine ⟨69000015749299317440955287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46000010499532878293970191 69000015749299317440955287)
  ·
    refine ⟨103500023623948976161432931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69000015749299317440955287 103500023623948976161432931)
    ·
      refine ⟨155250035435923464242149397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103500023623948976161432931 155250035435923464242149397)
      ·
        refine ⟨7277345411058912386350753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155250035435923464242149397 7277345411058912386350753)
        ·
          refine ⟨5458009058294184289763065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7277345411058912386350753 5458009058294184289763065)
          ·
            refine ⟨4093506793720638217322299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5458009058294184289763065 4093506793720638217322299)
            ·
              refine ⟨6140260190580957325983449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093506793720638217322299 6140260190580957325983449)
              ·
                refine ⟨4605195142935717994487587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6140260190580957325983449 4605195142935717994487587)
                ·
                  refine ⟨6907792714403576991731381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605195142935717994487587 6907792714403576991731381)
                  ·
                    refine ⟨647605566975335342974817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6907792714403576991731381 647605566975335342974817)
                    ·
                      rfl

theorem cell22_1891811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 5].length) (baseStart_1891811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891811 prefixEnd_1891811 := by exact prefixLift 1891811
  have htrace : WordTrace (prefixWord ++ tailWord_1891811) baseStart_1891811 baseEnd_1891811 := by
    simpa [prefixWord, tailWord_1891811, baseEnd_1891811] using wordTrace_append hprefix tailTrace_1891811
  have hstable : (prefixWord ++ tailWord_1891811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891811).length < 2 ^ (prefixWord ++ tailWord_1891811).sum := by decide
  have hdescent : baseEnd_1891811 < baseStart_1891811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891830 : List Nat := [5, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_1891830 : Nat := 118140960795 + 1891830 * 2 ^ 59
def prefixEnd_1891830 : Nat := 4983230072969 + 3 ^ 40 * 1891830 * 2
def baseEnd_1891830 : Nat := 215870690354541875583253

theorem tailTrace_1891830 : CollatzResearch.WordTrace tailWord_1891830 prefixEnd_1891830 215870690354541875583253 := by
  unfold tailWord_1891830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4312544296014405230368559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46000472490820322457264629 4312544296014405230368559)
  ·
    refine ⟨6468816444021607845552839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4312544296014405230368559 6468816444021607845552839)
    ·
      refine ⟨9703224666032411768329259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6468816444021607845552839 9703224666032411768329259)
      ·
        refine ⟨14554836999048617652493889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9703224666032411768329259 14554836999048617652493889)
        ·
          refine ⟨10916127749286463239370417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14554836999048617652493889 10916127749286463239370417)
          ·
            refine ⟨8187095811964847429527813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10916127749286463239370417 8187095811964847429527813)
            ·
              refine ⟨1535080464743408893036465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8187095811964847429527813 1535080464743408893036465)
              ·
                refine ⟨1151310348557556669777349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535080464743408893036465 1151310348557556669777349)
                ·
                  refine ⟨215870690354541875583253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151310348557556669777349 215870690354541875583253)
                  ·
                    rfl

theorem cell22_1891830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_1891830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891830 prefixEnd_1891830 := by exact prefixLift 1891830
  have htrace : WordTrace (prefixWord ++ tailWord_1891830) baseStart_1891830 baseEnd_1891830 := by
    simpa [prefixWord, tailWord_1891830, baseEnd_1891830] using wordTrace_append hprefix tailTrace_1891830
  have hstable : (prefixWord ++ tailWord_1891830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891830).length < 2 ^ (prefixWord ++ tailWord_1891830).sum := by decide
  have hdescent : baseEnd_1891830 < baseStart_1891830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891903 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 5]
def baseStart_1891903 : Nat := 118140960795 + 1891903 * 2 ^ 59
def prefixEnd_1891903 : Nat := 4983230072969 + 3 ^ 40 * 1891903 * 2
def baseEnd_1891903 : Nat := 215879020151825923224845

theorem tailTrace_1891903 : CollatzResearch.WordTrace tailWord_1891903 prefixEnd_1891903 215879020151825923224845 := by
  unfold tailWord_1891903
  simp only [CollatzResearch.WordTrace]
  refine ⟨69003371264966017153304363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46002247509977344768869575 69003371264966017153304363)
  ·
    refine ⟨103505056897449025729956545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69003371264966017153304363 103505056897449025729956545)
    ·
      refine ⟨77628792673086769297467409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103505056897449025729956545 77628792673086769297467409)
      ·
        refine ⟨58221594504815076973100557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77628792673086769297467409 58221594504815076973100557)
        ·
          refine ⟨21833097939305653864912709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58221594504815076973100557 21833097939305653864912709)
          ·
            refine ⟨4093705863619810099671133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21833097939305653864912709 4093705863619810099671133)
            ·
              refine ⟨1535139698857428787376675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4093705863619810099671133 1535139698857428787376675)
              ·
                refine ⟨2302709548286143181065013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535139698857428787376675 2302709548286143181065013)
                ·
                  refine ⟨215879020151825923224845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2302709548286143181065013 215879020151825923224845)
                  ·
                    rfl

theorem cell22_1891903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 5].length) (baseStart_1891903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891903 prefixEnd_1891903 := by exact prefixLift 1891903
  have htrace : WordTrace (prefixWord ++ tailWord_1891903) baseStart_1891903 baseEnd_1891903 := by
    simpa [prefixWord, tailWord_1891903, baseEnd_1891903] using wordTrace_append hprefix tailTrace_1891903
  have hstable : (prefixWord ++ tailWord_1891903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891903).length < 2 ^ (prefixWord ++ tailWord_1891903).sum := by decide
  have hdescent : baseEnd_1891903 < baseStart_1891903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891961 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_1891961 : Nat := 118140960795 + 1891961 * 2 ^ 59
def prefixEnd_1891961 : Nat := 4983230072969 + 3 ^ 40 * 1891961 * 2
def baseEnd_1891961 : Nat := 647656915040784951724357

theorem tailTrace_1891961 : CollatzResearch.WordTrace tailWord_1891961 prefixEnd_1891961 647656915040784951724357 := by
  unfold tailWord_1891961
  simp only [CollatzResearch.WordTrace]
  refine ⟨69005486698755893058915737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46003657799170595372610491 69005486698755893058915737)
  ·
    refine ⟨51754115024066919794186803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69005486698755893058915737 51754115024066919794186803)
    ·
      refine ⟨77631172536100379691280205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51754115024066919794186803 77631172536100379691280205)
      ·
        refine ⟨29111689701037642384230077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77631172536100379691280205 29111689701037642384230077)
        ·
          refine ⟨10916883637889115894086279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29111689701037642384230077 10916883637889115894086279)
          ·
            refine ⟨16375325456833673841129419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916883637889115894086279 16375325456833673841129419)
            ·
              refine ⟨24562988185250510761694129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16375325456833673841129419 24562988185250510761694129)
              ·
                refine ⟨18422241138937883071270597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24562988185250510761694129 18422241138937883071270597)
                ·
                  refine ⟨3454170213550853075863237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18422241138937883071270597 3454170213550853075863237)
                  ·
                    refine ⟨647656915040784951724357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3454170213550853075863237 647656915040784951724357)
                    ·
                      rfl

theorem cell22_1891961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_1891961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891961 prefixEnd_1891961 := by exact prefixLift 1891961
  have htrace : WordTrace (prefixWord ++ tailWord_1891961) baseStart_1891961 baseEnd_1891961 := by
    simpa [prefixWord, tailWord_1891961, baseEnd_1891961] using wordTrace_append hprefix tailTrace_1891961
  have hstable : (prefixWord ++ tailWord_1891961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891961).length < 2 ^ (prefixWord ++ tailWord_1891961).sum := by decide
  have hdescent : baseEnd_1891961 < baseStart_1891961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891963 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 2, 3]
def baseStart_1891963 : Nat := 118140960795 + 1891963 * 2 ^ 59
def prefixEnd_1891963 : Nat := 4983230072969 + 3 ^ 40 * 1891963 * 2
def baseEnd_1891963 : Nat := 647657599681657613174351

theorem tailTrace_1891963 : CollatzResearch.WordTrace tailWord_1891963 prefixEnd_1891963 647657599681657613174351 := by
  unfold tailWord_1891963
  simp only [CollatzResearch.WordTrace]
  refine ⟨69005559644748647400488543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46003706429832431600325695 69005559644748647400488543)
  ·
    refine ⟨103508339467122971100732815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69005559644748647400488543 103508339467122971100732815)
    ·
      refine ⟨155262509200684456651099223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103508339467122971100732815 155262509200684456651099223)
      ·
        refine ⟨232893763801026684976648835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155262509200684456651099223 232893763801026684976648835)
        ·
          refine ⟨349340645701540027464973253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232893763801026684976648835 349340645701540027464973253)
          ·
            refine ⟨65501371069038755149682485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349340645701540027464973253 65501371069038755149682485)
            ·
              refine ⟨6140753537722383295282733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65501371069038755149682485 6140753537722383295282733)
              ·
                refine ⟨2302782576645893735731025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6140753537722383295282733 2302782576645893735731025)
                ·
                  refine ⟨1727086932484420301798269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2302782576645893735731025 1727086932484420301798269)
                  ·
                    refine ⟨647657599681657613174351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1727086932484420301798269 647657599681657613174351)
                    ·
                      rfl

theorem cell22_1891963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 3].length) (baseStart_1891963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891963 prefixEnd_1891963 := by exact prefixLift 1891963
  have htrace : WordTrace (prefixWord ++ tailWord_1891963) baseStart_1891963 baseEnd_1891963 := by
    simpa [prefixWord, tailWord_1891963, baseEnd_1891963] using wordTrace_append hprefix tailTrace_1891963
  have hstable : (prefixWord ++ tailWord_1891963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891963).length < 2 ^ (prefixWord ++ tailWord_1891963).sum := by decide
  have hdescent : baseEnd_1891963 < baseStart_1891963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891978 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_1891978 : Nat := 118140960795 + 1891978 * 2 ^ 59
def prefixEnd_1891978 : Nat := 4983230072969 + 3 ^ 40 * 1891978 * 2
def baseEnd_1891978 : Nat := 647662734488202574049305

theorem tailTrace_1891978 : CollatzResearch.WordTrace tailWord_1891978 prefixEnd_1891978 647662734488202574049305 := by
  unfold tailWord_1891978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17251526684923576240571147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46004071159796203308189725 17251526684923576240571147)
  ·
    refine ⟨25877290027385364360856721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17251526684923576240571147 25877290027385364360856721)
    ·
      refine ⟨19407967520539023270642541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25877290027385364360856721 19407967520539023270642541)
      ·
        refine ⟨7277987820202133726490953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19407967520539023270642541 7277987820202133726490953)
        ·
          refine ⟨5458490865151600294868215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7277987820202133726490953 5458490865151600294868215)
          ·
            refine ⟨8187736297727400442302323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5458490865151600294868215 8187736297727400442302323)
            ·
              refine ⟨12281604446591100663453485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187736297727400442302323 12281604446591100663453485)
              ·
                refine ⟨4605601667471662748795057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12281604446591100663453485 4605601667471662748795057)
                ·
                  refine ⟨3454201250603747061596293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4605601667471662748795057 3454201250603747061596293)
                  ·
                    refine ⟨647662734488202574049305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3454201250603747061596293 647662734488202574049305)
                    ·
                      rfl

theorem cell22_1891978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_1891978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891978 prefixEnd_1891978 := by exact prefixLift 1891978
  have htrace : WordTrace (prefixWord ++ tailWord_1891978) baseStart_1891978 baseEnd_1891978 := by
    simpa [prefixWord, tailWord_1891978, baseEnd_1891978] using wordTrace_append hprefix tailTrace_1891978
  have hstable : (prefixWord ++ tailWord_1891978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891978).length < 2 ^ (prefixWord ++ tailWord_1891978).sum := by decide
  have hdescent : baseEnd_1891978 < baseStart_1891978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891999 : List Nat := [1, 1, 2, 7, 1, 2, 2, 2, 4]
def baseStart_1891999 : Nat := 118140960795 + 1891999 * 2 ^ 59
def prefixEnd_1891999 : Nat := 4983230072969 + 3 ^ 40 * 1891999 * 2
def baseEnd_1891999 : Nat := 215889974405788506424747

theorem tailTrace_1891999 : CollatzResearch.WordTrace tailWord_1891999 prefixEnd_1891999 215889974405788506424747 := by
  unfold tailWord_1891999
  simp only [CollatzResearch.WordTrace]
  refine ⟨69006872672618225548799051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46004581781745483699199367 69006872672618225548799051)
  ·
    refine ⟨103510309008927338323198577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69006872672618225548799051 103510309008927338323198577)
    ·
      refine ⟨77632731756695503742398933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103510309008927338323198577 77632731756695503742398933)
      ·
        refine ⟨1819517150547550868962475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 77632731756695503742398933 1819517150547550868962475)
        ·
          refine ⟨2729275725821326303443713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819517150547550868962475 2729275725821326303443713)
          ·
            refine ⟨2046956794365994727582785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2729275725821326303443713 2046956794365994727582785)
            ·
              refine ⟨1535217595774496045687089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046956794365994727582785 1535217595774496045687089)
              ·
                refine ⟨1151413196830872034265317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535217595774496045687089 1151413196830872034265317)
                ·
                  refine ⟨215889974405788506424747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151413196830872034265317 215889974405788506424747)
                  ·
                    rfl

theorem cell22_1891999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 4].length) (baseStart_1891999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1891999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1891999 prefixEnd_1891999 := by exact prefixLift 1891999
  have htrace : WordTrace (prefixWord ++ tailWord_1891999) baseStart_1891999 baseEnd_1891999 := by
    simpa [prefixWord, tailWord_1891999, baseEnd_1891999] using wordTrace_append hprefix tailTrace_1891999
  have hstable : (prefixWord ++ tailWord_1891999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891999).length < 2 ^ (prefixWord ++ tailWord_1891999).sum := by decide
  have hdescent : baseEnd_1891999 < baseStart_1891999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892117 : List Nat := [1, 3, 2, 1, 2, 4, 3, 2, 4]
def baseStart_1892117 : Nat := 118140960795 + 1892117 * 2 ^ 59
def prefixEnd_1892117 : Nat := 4983230072969 + 3 ^ 40 * 1892117 * 2
def baseEnd_1892117 : Nat := 215903439009617514941293

theorem tailTrace_1892117 : CollatzResearch.WordTrace tailWord_1892117 prefixEnd_1892117 215903439009617514941293 := by
  unfold tailWord_1892117
  simp only [CollatzResearch.WordTrace]
  refine ⟨69011176486190731701594605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46007450990793821134396403 69011176486190731701594605)
  ·
    refine ⟨25879191182321524388097977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69011176486190731701594605 25879191182321524388097977)
    ·
      refine ⟨19409393386741143291073483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25879191182321524388097977 19409393386741143291073483)
      ·
        refine ⟨29114090080111714936610225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19409393386741143291073483 29114090080111714936610225)
        ·
          refine ⟨21835567560083786202457669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29114090080111714936610225 21835567560083786202457669)
          ·
            refine ⟨4094168917515709912960813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21835567560083786202457669 4094168917515709912960813)
            ·
              refine ⟨1535313344068391217360305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4094168917515709912960813 1535313344068391217360305)
              ·
                refine ⟨1151485008051293413020229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535313344068391217360305 1151485008051293413020229)
                ·
                  refine ⟨215903439009617514941293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151485008051293413020229 215903439009617514941293)
                  ·
                    rfl

theorem cell22_1892117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_1892117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892117 prefixEnd_1892117 := by exact prefixLift 1892117
  have htrace : WordTrace (prefixWord ++ tailWord_1892117) baseStart_1892117 baseEnd_1892117 := by
    simpa [prefixWord, tailWord_1892117, baseEnd_1892117] using wordTrace_append hprefix tailTrace_1892117
  have hstable : (prefixWord ++ tailWord_1892117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892117).length < 2 ^ (prefixWord ++ tailWord_1892117).sum := by decide
  have hdescent : baseEnd_1892117 < baseStart_1892117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892128 : List Nat := [2, 1, 1, 5, 1, 1, 4, 7]
def baseStart_1892128 : Nat := 118140960795 + 1892128 * 2 ^ 59
def prefixEnd_1892128 : Nat := 4983230072969 + 3 ^ 40 * 1892128 * 2
def baseEnd_1892128 : Nat := 71968231394850242533205

theorem tailTrace_1892128 : CollatzResearch.WordTrace tailWord_1892128 prefixEnd_1892128 71968231394850242533205 := by
  unfold tailWord_1892128
  simp only [CollatzResearch.WordTrace]
  refine ⟨34505788844575440290122519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46007718459433920386830025 34505788844575440290122519)
  ·
    refine ⟨51758683266863160435183779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34505788844575440290122519 51758683266863160435183779)
    ·
      refine ⟨77638024900294740652775669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51758683266863160435183779 77638024900294740652775669)
      ·
        refine ⟨7278564834402631936197719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77638024900294740652775669 7278564834402631936197719)
        ·
          refine ⟨10917847251603947904296579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278564834402631936197719 10917847251603947904296579)
          ·
            refine ⟨16376770877405921856444869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917847251603947904296579 16376770877405921856444869)
            ·
              refine ⟨3070644539513610348083413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16376770877405921856444869 3070644539513610348083413)
              ·
                refine ⟨71968231394850242533205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3070644539513610348083413 71968231394850242533205)
                ·
                  rfl

theorem cell22_1892128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 7].length) (baseStart_1892128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892128 prefixEnd_1892128 := by exact prefixLift 1892128
  have htrace : WordTrace (prefixWord ++ tailWord_1892128) baseStart_1892128 baseEnd_1892128 := by
    simpa [prefixWord, tailWord_1892128, baseEnd_1892128] using wordTrace_append hprefix tailTrace_1892128
  have hstable : (prefixWord ++ tailWord_1892128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892128).length < 2 ^ (prefixWord ++ tailWord_1892128).sum := by decide
  have hdescent : baseEnd_1892128 < baseStart_1892128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892132 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1892132 : Nat := 118140960795 + 1892132 * 2 ^ 59
def prefixEnd_1892132 : Nat := 4983230072969 + 3 ^ 40 * 1892132 * 2
def baseEnd_1892132 : Nat := 647715451835397505698833

theorem tailTrace_1892132 : CollatzResearch.WordTrace tailWord_1892132 prefixEnd_1892132 647715451835397505698833 := by
  unfold tailWord_1892132
  simp only [CollatzResearch.WordTrace]
  refine ⟨34505861790568194631695325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46007815720757592842260433 34505861790568194631695325)
  ·
    refine ⟨12939698171463072986885747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34505861790568194631695325 12939698171463072986885747)
    ·
      refine ⟨19409547257194609480328621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12939698171463072986885747 19409547257194609480328621)
      ·
        refine ⟨7278580221447978555123233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19409547257194609480328621 7278580221447978555123233)
        ·
          refine ⟨5458935166085983916342425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7278580221447978555123233 5458935166085983916342425)
          ·
            refine ⟨4094201374564487937256819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5458935166085983916342425 4094201374564487937256819)
            ·
              refine ⟨6141302061846731905885229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4094201374564487937256819 6141302061846731905885229)
              ·
                refine ⟨2302988273192524464706961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6141302061846731905885229 2302988273192524464706961)
                ·
                  refine ⟨1727241204894393348530221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2302988273192524464706961 1727241204894393348530221)
                  ·
                    refine ⟨647715451835397505698833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1727241204894393348530221 647715451835397505698833)
                    ·
                      rfl

theorem cell22_1892132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1892132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892132 prefixEnd_1892132 := by exact prefixLift 1892132
  have htrace : WordTrace (prefixWord ++ tailWord_1892132) baseStart_1892132 baseEnd_1892132 := by
    simpa [prefixWord, tailWord_1892132, baseEnd_1892132] using wordTrace_append hprefix tailTrace_1892132
  have hstable : (prefixWord ++ tailWord_1892132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892132).length < 2 ^ (prefixWord ++ tailWord_1892132).sum := by decide
  have hdescent : baseEnd_1892132 < baseStart_1892132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892166 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1892166 : Nat := 118140960795 + 1892166 * 2 ^ 59
def prefixEnd_1892166 : Nat := 4983230072969 + 3 ^ 40 * 1892166 * 2
def baseEnd_1892166 : Nat := 647727090730232750348729

theorem tailTrace_1892166 : CollatzResearch.WordTrace tailWord_1892166 prefixEnd_1892166 647727090730232750348729 := by
  unfold tailWord_1892166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156655114469162908441511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46008642442008808713418901 2156655114469162908441511)
  ·
    refine ⟨3234982671703744362662267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2156655114469162908441511 3234982671703744362662267)
    ·
      refine ⟨4852474007555616543993401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3234982671703744362662267 4852474007555616543993401)
      ·
        refine ⟨3639355505666712407995051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4852474007555616543993401 3639355505666712407995051)
        ·
          refine ⟨5459033258500068611992577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639355505666712407995051 5459033258500068611992577)
          ·
            refine ⟨4094274943875051458994433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5459033258500068611992577 4094274943875051458994433)
            ·
              refine ⟨3070706207906288594245825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4094274943875051458994433 3070706207906288594245825)
              ·
                refine ⟨2303029655929716445684369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070706207906288594245825 2303029655929716445684369)
                ·
                  refine ⟨1727272241947287334263277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2303029655929716445684369 1727272241947287334263277)
                  ·
                    refine ⟨647727090730232750348729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1727272241947287334263277 647727090730232750348729)
                    ·
                      rfl

theorem cell22_1892166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1892166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892166 prefixEnd_1892166 := by exact prefixLift 1892166
  have htrace : WordTrace (prefixWord ++ tailWord_1892166) baseStart_1892166 baseEnd_1892166 := by
    simpa [prefixWord, tailWord_1892166, baseEnd_1892166] using wordTrace_append hprefix tailTrace_1892166
  have hstable : (prefixWord ++ tailWord_1892166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892166).length < 2 ^ (prefixWord ++ tailWord_1892166).sum := by decide
  have hdescent : baseEnd_1892166 < baseStart_1892166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892222 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1892222 : Nat := 118140960795 + 1892222 * 2 ^ 59
def prefixEnd_1892222 : Nat := 4983230072969 + 3 ^ 40 * 1892222 * 2
def baseEnd_1892222 : Nat := 647746260674667270948557

theorem tailTrace_1892222 : CollatzResearch.WordTrace tailWord_1892222 prefixEnd_1892222 647746260674667270948557 := by
  unfold tailWord_1892222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8626875768851291829270865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46010004100540223089444613 8626875768851291829270865)
  ·
    refine ⟨6470156826638468871953149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8626875768851291829270865 6470156826638468871953149)
    ·
      refine ⟨2426308809989425826982431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6470156826638468871953149 2426308809989425826982431)
      ·
        refine ⟨3639463214984138740473647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426308809989425826982431 3639463214984138740473647)
        ·
          refine ⟨5459194822476208110710471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639463214984138740473647 5459194822476208110710471)
          ·
            refine ⟨8188792233714312166065707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5459194822476208110710471 8188792233714312166065707)
            ·
              refine ⟨12283188350571468249098561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8188792233714312166065707 12283188350571468249098561)
              ·
                refine ⟨9212391262928601186823921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12283188350571468249098561 9212391262928601186823921)
                ·
                  refine ⟨6909293447196450890117941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9212391262928601186823921 6909293447196450890117941)
                  ·
                    refine ⟨647746260674667270948557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6909293447196450890117941 647746260674667270948557)
                    ·
                      rfl

theorem cell22_1892222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1892222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892222 prefixEnd_1892222 := by exact prefixLift 1892222
  have htrace : WordTrace (prefixWord ++ tailWord_1892222) baseStart_1892222 baseEnd_1892222 := by
    simpa [prefixWord, tailWord_1892222, baseEnd_1892222] using wordTrace_append hprefix tailTrace_1892222
  have hstable : (prefixWord ++ tailWord_1892222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892222).length < 2 ^ (prefixWord ++ tailWord_1892222).sum := by decide
  have hdescent : baseEnd_1892222 < baseStart_1892222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892389 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 1, 4]
def baseStart_1892389 : Nat := 118140960795 + 1892389 * 2 ^ 59
def prefixEnd_1892389 : Nat := 4983230072969 + 3 ^ 40 * 1892389 * 2
def baseEnd_1892389 : Nat := 647803428187534502023045

theorem tailTrace_1892389 : CollatzResearch.WordTrace tailWord_1892389 prefixEnd_1892389 647803428187534502023045 := by
  unfold tailWord_1892389
  simp only [CollatzResearch.WordTrace]
  refine ⟨69021097141205322155496221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46014064760803548103664147 69021097141205322155496221)
  ·
    refine ⟨25882911427951995808311083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69021097141205322155496221 25882911427951995808311083)
    ·
      refine ⟨38824367141927993712466625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25882911427951995808311083 38824367141927993712466625)
      ·
        refine ⟨29118275356445995284349969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38824367141927993712466625 29118275356445995284349969)
        ·
          refine ⟨21838706517334496463262477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29118275356445995284349969 21838706517334496463262477)
          ·
            refine ⟨8189514944000436173723429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21838706517334496463262477 8189514944000436173723429)
            ·
              refine ⟨1535534052000081782573143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8189514944000436173723429 1535534052000081782573143)
              ·
                refine ⟨2303301078000122673859715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535534052000081782573143 2303301078000122673859715)
                ·
                  refine ⟨3454951617000184010789573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303301078000122673859715 3454951617000184010789573)
                  ·
                    refine ⟨647803428187534502023045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3454951617000184010789573 647803428187534502023045)
                    ·
                      rfl

theorem cell22_1892389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_1892389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892389 prefixEnd_1892389 := by exact prefixLift 1892389
  have htrace : WordTrace (prefixWord ++ tailWord_1892389) baseStart_1892389 baseEnd_1892389 := by
    simpa [prefixWord, tailWord_1892389, baseEnd_1892389] using wordTrace_append hprefix tailTrace_1892389
  have hstable : (prefixWord ++ tailWord_1892389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892389).length < 2 ^ (prefixWord ++ tailWord_1892389).sum := by decide
  have hdescent : baseEnd_1892389 < baseStart_1892389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892417 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1892417 : Nat := 118140960795 + 1892417 * 2 ^ 59
def prefixEnd_1892417 : Nat := 4983230072969 + 3 ^ 40 * 1892417 * 2
def baseEnd_1892417 : Nat := 647813013159751762322959

theorem tailTrace_1892417 : CollatzResearch.WordTrace tailWord_1892417 prefixEnd_1892417 647813013159751762322959 := by
  unfold tailWord_1892417
  simp only [CollatzResearch.WordTrace]
  refine ⟨69022118385103882937515505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46014745590069255291677003 69022118385103882937515505)
  ·
    refine ⟨51766588788827912203136629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69022118385103882937515505 51766588788827912203136629)
    ·
      refine ⟨4853117698952616769044059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51766588788827912203136629 4853117698952616769044059)
      ·
        refine ⟨7279676548428925153566089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4853117698952616769044059 7279676548428925153566089)
        ·
          refine ⟨5459757411321693865174567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7279676548428925153566089 5459757411321693865174567)
          ·
            refine ⟨8189636116982540797761851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5459757411321693865174567 8189636116982540797761851)
            ·
              refine ⟨12284454175473811196642777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8189636116982540797761851 12284454175473811196642777)
              ·
                refine ⟨9213340631605358397482083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12284454175473811196642777 9213340631605358397482083)
                ·
                  refine ⟨13820010947408037596223125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9213340631605358397482083 13820010947408037596223125)
                  ·
                    refine ⟨647813013159751762322959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13820010947408037596223125 647813013159751762322959)
                    ·
                      rfl

theorem cell22_1892417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1892417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892417 prefixEnd_1892417 := by exact prefixLift 1892417
  have htrace : WordTrace (prefixWord ++ tailWord_1892417) baseStart_1892417 baseEnd_1892417 := by
    simpa [prefixWord, tailWord_1892417, baseEnd_1892417] using wordTrace_append hprefix tailTrace_1892417
  have hstable : (prefixWord ++ tailWord_1892417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892417).length < 2 ^ (prefixWord ++ tailWord_1892417).sum := by decide
  have hdescent : baseEnd_1892417 < baseStart_1892417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892438 : List Nat := [5, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1892438 : Nat := 118140960795 + 1892438 * 2 ^ 59
def prefixEnd_1892438 : Nat := 4983230072969 + 3 ^ 40 * 1892438 * 2
def baseEnd_1892438 : Nat := 215940067296304902515965

theorem tailTrace_1892438 : CollatzResearch.WordTrace tailWord_1892438 prefixEnd_1892438 215940067296304902515965 := by
  unfold tailWord_1892438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313930269876737720251873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46015256212018535682686645 4313930269876737720251873)
  ·
    refine ⟨3235447702407553290188905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4313930269876737720251873 3235447702407553290188905)
    ·
      refine ⟨2426585776805664967641679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3235447702407553290188905 2426585776805664967641679)
      ·
        refine ⟨3639878665208497451462519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426585776805664967641679 3639878665208497451462519)
        ·
          refine ⟨5459817997812746177193779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639878665208497451462519 5459817997812746177193779)
          ·
            refine ⟨8189726996719119265790669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5459817997812746177193779 8189726996719119265790669)
            ·
              refine ⟨3071147623769669724671501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8189726996719119265790669 3071147623769669724671501)
              ·
                refine ⟨1151680358913626146751813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3071147623769669724671501 1151680358913626146751813)
                ·
                  refine ⟨215940067296304902515965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151680358913626146751813 215940067296304902515965)
                  ·
                    rfl

theorem cell22_1892438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1892438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892438 prefixEnd_1892438 := by exact prefixLift 1892438
  have htrace : WordTrace (prefixWord ++ tailWord_1892438) baseStart_1892438 baseEnd_1892438 := by
    simpa [prefixWord, tailWord_1892438, baseEnd_1892438] using wordTrace_append hprefix tailTrace_1892438
  have hstable : (prefixWord ++ tailWord_1892438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892438).length < 2 ^ (prefixWord ++ tailWord_1892438).sum := by decide
  have hdescent : baseEnd_1892438 < baseStart_1892438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892462 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1892462 : Nat := 118140960795 + 1892462 * 2 ^ 59
def prefixEnd_1892462 : Nat := 4983230072969 + 3 ^ 40 * 1892462 * 2
def baseEnd_1892462 : Nat := 647828417579386644947821

theorem tailTrace_1892462 : CollatzResearch.WordTrace tailWord_1892462 prefixEnd_1892462 647828417579386644947821 := by
  unfold tailWord_1892462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8627969958742606952862955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46015839779960570415269093 8627969958742606952862955)
  ·
    refine ⟨12941954938113910429294433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8627969958742606952862955 12941954938113910429294433)
    ·
      refine ⟨9706466203585432821970825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12941954938113910429294433 9706466203585432821970825)
      ·
        refine ⟨7279849652689074616478119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9706466203585432821970825 7279849652689074616478119)
        ·
          refine ⟨10919774479033611924717179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7279849652689074616478119 10919774479033611924717179)
          ·
            refine ⟨16379661718550417887075769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10919774479033611924717179 16379661718550417887075769)
            ·
              refine ⟨12284746288912813415306827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16379661718550417887075769 12284746288912813415306827)
              ·
                refine ⟨18427119433369220122960241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12284746288912813415306827 18427119433369220122960241)
                ·
                  refine ⟨13820339575026915092220181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18427119433369220122960241 13820339575026915092220181)
                  ·
                    refine ⟨647828417579386644947821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13820339575026915092220181 647828417579386644947821)
                    ·
                      rfl

theorem cell22_1892462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1892462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892462 prefixEnd_1892462 := by exact prefixLift 1892462
  have htrace : WordTrace (prefixWord ++ tailWord_1892462) baseStart_1892462 baseEnd_1892462 := by
    simpa [prefixWord, tailWord_1892462, baseEnd_1892462] using wordTrace_append hprefix tailTrace_1892462
  have hstable : (prefixWord ++ tailWord_1892462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892462).length < 2 ^ (prefixWord ++ tailWord_1892462).sum := by decide
  have hdescent : baseEnd_1892462 < baseStart_1892462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892464 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 3, 3]
def baseStart_1892464 : Nat := 118140960795 + 1892464 * 2 ^ 59
def prefixEnd_1892464 : Nat := 4983230072969 + 3 ^ 40 * 1892464 * 2
def baseEnd_1892464 : Nat := 647829102220259306397815

theorem tailTrace_1892464 : CollatzResearch.WordTrace tailWord_1892464 prefixEnd_1892464 647829102220259306397815 := by
  unfold tailWord_1892464
  simp only [CollatzResearch.WordTrace]
  refine ⟨34511916307966804982238223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46015888410622406642984297 34511916307966804982238223)
  ·
    refine ⟨51767874461950207473357335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34511916307966804982238223 51767874461950207473357335)
    ·
      refine ⟨77651811692925311210036003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51767874461950207473357335 77651811692925311210036003)
      ·
        refine ⟨116477717539387966815054005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77651811692925311210036003 116477717539387966815054005)
        ·
          refine ⟨10919786019317621888911313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116477717539387966815054005 10919786019317621888911313)
          ·
            refine ⟨8189839514488216416683485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10919786019317621888911313 8189839514488216416683485)
            ·
              refine ⟨3071189817933081156256307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8189839514488216416683485 3071189817933081156256307)
              ·
                refine ⟨4606784726899621734384461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071189817933081156256307 4606784726899621734384461)
                ·
                  refine ⟨1727544272587358150394173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4606784726899621734384461 1727544272587358150394173)
                  ·
                    refine ⟨647829102220259306397815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1727544272587358150394173 647829102220259306397815)
                    ·
                      rfl

theorem cell22_1892464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_1892464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892464 prefixEnd_1892464 := by exact prefixLift 1892464
  have htrace : WordTrace (prefixWord ++ tailWord_1892464) baseStart_1892464 baseEnd_1892464 := by
    simpa [prefixWord, tailWord_1892464, baseEnd_1892464] using wordTrace_append hprefix tailTrace_1892464
  have hstable : (prefixWord ++ tailWord_1892464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892464).length < 2 ^ (prefixWord ++ tailWord_1892464).sum := by decide
  have hdescent : baseEnd_1892464 < baseStart_1892464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892554 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_1892554 : Nat := 118140960795 + 1892554 * 2 ^ 59
def prefixEnd_1892554 : Nat := 4983230072969 + 3 ^ 40 * 1892554 * 2
def baseEnd_1892554 : Nat := 647859911059529071647539

theorem tailTrace_1892554 : CollatzResearch.WordTrace tailWord_1892554 prefixEnd_1892554 647859911059529071647539 := by
  unfold tailWord_1892554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17256778796401888833813179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46018076790405036890168477 17256778796401888833813179)
  ·
    refine ⟨25885168194602833250719769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17256778796401888833813179 25885168194602833250719769)
    ·
      refine ⟨19413876145952124938039827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25885168194602833250719769 19413876145952124938039827)
      ·
        refine ⟨29120814218928187407059741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19413876145952124938039827 29120814218928187407059741)
        ·
          refine ⟨10920305332098070277647403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29120814218928187407059741 10920305332098070277647403)
          ·
            refine ⟨16380457998147105416471105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10920305332098070277647403 16380457998147105416471105)
            ·
              refine ⟨12285343498610329062353329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16380457998147105416471105 12285343498610329062353329)
              ·
                refine ⟨9214007623957746796764997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12285343498610329062353329 9214007623957746796764997)
                ·
                  refine ⟨1727626429492077524393437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9214007623957746796764997 1727626429492077524393437)
                  ·
                    refine ⟨647859911059529071647539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1727626429492077524393437 647859911059529071647539)
                    ·
                      rfl

theorem cell22_1892554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_1892554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892554 prefixEnd_1892554 := by exact prefixLift 1892554
  have htrace : WordTrace (prefixWord ++ tailWord_1892554) baseStart_1892554 baseEnd_1892554 := by
    simpa [prefixWord, tailWord_1892554, baseEnd_1892554] using wordTrace_append hprefix tailTrace_1892554
  have hstable : (prefixWord ++ tailWord_1892554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892554).length < 2 ^ (prefixWord ++ tailWord_1892554).sum := by decide
  have hdescent : baseEnd_1892554 < baseStart_1892554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892558 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_1892558 : Nat := 118140960795 + 1892558 * 2 ^ 59
def prefixEnd_1892558 : Nat := 4983230072969 + 3 ^ 40 * 1892558 * 2
def baseEnd_1892558 : Nat := 647861280341274394547527

theorem tailTrace_1892558 : CollatzResearch.WordTrace tailWord_1892558 prefixEnd_1892558 647861280341274394547527 := by
  unfold tailWord_1892558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8628407634699133002299791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46018174051728709345598885 8628407634699133002299791)
  ·
    refine ⟨12942611452048699503449687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8628407634699133002299791 12942611452048699503449687)
    ·
      refine ⟨19413917178073049255174531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12942611452048699503449687 19413917178073049255174531)
      ·
        refine ⟨29120875767109573882761797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19413917178073049255174531 29120875767109573882761797)
        ·
          refine ⟨5460164206333045103017837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29120875767109573882761797 5460164206333045103017837)
          ·
            refine ⟨2047561577374891913631689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5460164206333045103017837 2047561577374891913631689)
            ·
              refine ⟨1535671183031168935223767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047561577374891913631689 1535671183031168935223767)
              ·
                refine ⟨2303506774546753402835651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535671183031168935223767 2303506774546753402835651)
                ·
                  refine ⟨3455260161820130104253477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303506774546753402835651 3455260161820130104253477)
                  ·
                    refine ⟨647861280341274394547527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3455260161820130104253477 647861280341274394547527)
                    ·
                      rfl

theorem cell22_1892558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_1892558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892558 prefixEnd_1892558 := by exact prefixLift 1892558
  have htrace : WordTrace (prefixWord ++ tailWord_1892558) baseStart_1892558 baseEnd_1892558 := by
    simpa [prefixWord, tailWord_1892558, baseEnd_1892558] using wordTrace_append hprefix tailTrace_1892558
  have hstable : (prefixWord ++ tailWord_1892558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892558).length < 2 ^ (prefixWord ++ tailWord_1892558).sum := by decide
  have hdescent : baseEnd_1892558 < baseStart_1892558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892627 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 4, 5]
def baseStart_1892627 : Nat := 118140960795 + 1892627 * 2 ^ 59
def prefixEnd_1892627 : Nat := 4983230072969 + 3 ^ 40 * 1892627 * 2
def baseEnd_1892627 : Nat := 647884900451381214572315

theorem tailTrace_1892627 : CollatzResearch.WordTrace tailWord_1892627 prefixEnd_1892627 647884900451381214572315 := by
  unfold tailWord_1892627
  simp only [CollatzResearch.WordTrace]
  refine ⟨69029777714343088802660135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46019851809562059201773423 69029777714343088802660135)
  ·
    refine ⟨103544666571514633203990203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69029777714343088802660135 103544666571514633203990203)
    ·
      refine ⟨155316999857271949805985305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103544666571514633203990203 155316999857271949805985305)
      ·
        refine ⟨116487749892953962354488979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155316999857271949805985305 116487749892953962354488979)
        ·
          refine ⟨174731624839430943531733469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116487749892953962354488979 174731624839430943531733469)
          ·
            refine ⟨65524359314786603824400051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174731624839430943531733469 65524359314786603824400051)
            ·
              refine ⟨98286538972179905736600077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65524359314786603824400051 98286538972179905736600077)
              ·
                refine ⟨36857452114567464651225029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98286538972179905736600077 36857452114567464651225029)
                ·
                  refine ⟨6910772271481399622104693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36857452114567464651225029 6910772271481399622104693)
                  ·
                    refine ⟨647884900451381214572315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6910772271481399622104693 647884900451381214572315)
                    ·
                      rfl

theorem cell22_1892627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_1892627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892627 prefixEnd_1892627 := by exact prefixLift 1892627
  have htrace : WordTrace (prefixWord ++ tailWord_1892627) baseStart_1892627 baseEnd_1892627 := by
    simpa [prefixWord, tailWord_1892627, baseEnd_1892627] using wordTrace_append hprefix tailTrace_1892627
  have hstable : (prefixWord ++ tailWord_1892627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892627).length < 2 ^ (prefixWord ++ tailWord_1892627).sum := by decide
  have hdescent : baseEnd_1892627 < baseStart_1892627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892659 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 3, 4]
def baseStart_1892659 : Nat := 118140960795 + 1892659 * 2 ^ 59
def prefixEnd_1892659 : Nat := 4983230072969 + 3 ^ 40 * 1892659 * 2
def baseEnd_1892659 : Nat := 647895854705343797772217

theorem tailTrace_1892659 : CollatzResearch.WordTrace tailWord_1892659 prefixEnd_1892659 647895854705343797772217 := by
  unfold tailWord_1892659
  simp only [CollatzResearch.WordTrace]
  refine ⟨69030944850227158267825031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46020629900151438845216687 69030944850227158267825031)
  ·
    refine ⟨103546417275340737401737547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69030944850227158267825031 103546417275340737401737547)
    ·
      refine ⟨155319625913011106102606321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103546417275340737401737547 155319625913011106102606321)
      ·
        refine ⟨116489719434758329576954741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155319625913011106102606321 116489719434758329576954741)
        ·
          refine ⟨10920911197008593397839507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116489719434758329576954741 10920911197008593397839507)
          ·
            refine ⟨16381366795512890096759261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10920911197008593397839507 16381366795512890096759261)
            ·
              refine ⟨6143012548317333786284723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16381366795512890096759261 6143012548317333786284723)
              ·
                refine ⟨9214518822476000679427085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143012548317333786284723 9214518822476000679427085)
                ·
                  refine ⟨3455444558428500254785157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9214518822476000679427085 3455444558428500254785157)
                  ·
                    refine ⟨647895854705343797772217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3455444558428500254785157 647895854705343797772217)
                    ·
                      rfl

theorem cell22_1892659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 4].length) (baseStart_1892659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892659 prefixEnd_1892659 := by exact prefixLift 1892659
  have htrace : WordTrace (prefixWord ++ tailWord_1892659) baseStart_1892659 baseEnd_1892659 := by
    simpa [prefixWord, tailWord_1892659, baseEnd_1892659] using wordTrace_append hprefix tailTrace_1892659
  have hstable : (prefixWord ++ tailWord_1892659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892659).length < 2 ^ (prefixWord ++ tailWord_1892659).sum := by decide
  have hdescent : baseEnd_1892659 < baseStart_1892659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892706 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1892706 : Nat := 118140960795 + 1892706 * 2 ^ 59
def prefixEnd_1892706 : Nat := 4983230072969 + 3 ^ 40 * 1892706 * 2
def baseEnd_1892706 : Nat := 647911943765851341847073

theorem tailTrace_1892706 : CollatzResearch.WordTrace tailWord_1892706 prefixEnd_1892706 647911943765851341847073 := by
  unfold tailWord_1892706
  simp only [CollatzResearch.WordTrace]
  refine ⟨17258164770264221323696493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46021772720704590196523981 17258164770264221323696493)
  ·
    refine ⟨6471811788849082996386185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17258164770264221323696493 6471811788849082996386185)
    ·
      refine ⟨4853858841636812247289639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6471811788849082996386185 4853858841636812247289639)
      ·
        refine ⟨7280788262455218370934459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4853858841636812247289639 7280788262455218370934459)
        ·
          refine ⟨10921182393682827556401689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7280788262455218370934459 10921182393682827556401689)
          ·
            refine ⟨8190886795262120667301267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10921182393682827556401689 8190886795262120667301267)
            ·
              refine ⟨12286330192893181000951901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190886795262120667301267 12286330192893181000951901)
              ·
                refine ⟨4607373822334942875356963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12286330192893181000951901 4607373822334942875356963)
                ·
                  refine ⟨6911060733502414313035445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607373822334942875356963 6911060733502414313035445)
                  ·
                    refine ⟨647911943765851341847073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6911060733502414313035445 647911943765851341847073)
                    ·
                      rfl

theorem cell22_1892706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1892706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892706 prefixEnd_1892706 := by exact prefixLift 1892706
  have htrace : WordTrace (prefixWord ++ tailWord_1892706) baseStart_1892706 baseEnd_1892706 := by
    simpa [prefixWord, tailWord_1892706, baseEnd_1892706] using wordTrace_append hprefix tailTrace_1892706
  have hstable : (prefixWord ++ tailWord_1892706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892706).length < 2 ^ (prefixWord ++ tailWord_1892706).sum := by decide
  have hdescent : baseEnd_1892706 < baseStart_1892706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892785 : List Nat := [1, 2, 2, 4, 1, 2, 3, 3, 1, 3]
def baseStart_1892785 : Nat := 118140960795 + 1892785 * 2 ^ 59
def prefixEnd_1892785 : Nat := 4983230072969 + 3 ^ 40 * 1892785 * 2
def baseEnd_1892785 : Nat := 647938987080321469121831

theorem tailTrace_1892785 : CollatzResearch.WordTrace tailWord_1892785 prefixEnd_1892785 647938987080321469121831 := by
  unfold tailWord_1892785
  simp only [CollatzResearch.WordTrace]
  refine ⟨69035540447770681786911809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46023693631847121191274539 69035540447770681786911809)
  ·
    refine ⟨51776655335828011340183857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69035540447770681786911809 51776655335828011340183857)
    ·
      refine ⟨38832491501871008505137893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51776655335828011340183857 38832491501871008505137893)
      ·
        refine ⟨7281092156600814094713355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38832491501871008505137893 7281092156600814094713355)
        ·
          refine ⟨10921638234901221142070033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281092156600814094713355 10921638234901221142070033)
          ·
            refine ⟨8191228676175915856552525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10921638234901221142070033 8191228676175915856552525)
            ·
              refine ⟨3071710753565968446207197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8191228676175915856552525 3071710753565968446207197)
              ·
                refine ⟨1151891532587238167327699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3071710753565968446207197 1151891532587238167327699)
                ·
                  refine ⟨1727837298880857250991549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151891532587238167327699 1727837298880857250991549)
                  ·
                    refine ⟨647938987080321469121831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1727837298880857250991549 647938987080321469121831)
                    ·
                      rfl

theorem cell22_1892785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_1892785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892785 prefixEnd_1892785 := by exact prefixLift 1892785
  have htrace : WordTrace (prefixWord ++ tailWord_1892785) baseStart_1892785 baseEnd_1892785 := by
    simpa [prefixWord, tailWord_1892785, baseEnd_1892785] using wordTrace_append hprefix tailTrace_1892785
  have hstable : (prefixWord ++ tailWord_1892785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892785).length < 2 ^ (prefixWord ++ tailWord_1892785).sum := by decide
  have hdescent : baseEnd_1892785 < baseStart_1892785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892841 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 4, 3]
def baseStart_1892841 : Nat := 118140960795 + 1892841 * 2 ^ 59
def prefixEnd_1892841 : Nat := 4983230072969 + 3 ^ 40 * 1892841 * 2
def baseEnd_1892841 : Nat := 647958157024755989721659

theorem tailTrace_1892841 : CollatzResearch.WordTrace tailWord_1892841 prefixEnd_1892841 647958157024755989721659 := by
  unfold tailWord_1892841
  simp only [CollatzResearch.WordTrace]
  refine ⟨69037582935567803350950377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46025055290378535567300251 69037582935567803350950377)
  ·
    refine ⟨51778187201675852513212783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69037582935567803350950377 51778187201675852513212783)
    ·
      refine ⟨77667280802513778769819175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51778187201675852513212783 77667280802513778769819175)
      ·
        refine ⟨116500921203770668154728763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77667280802513778769819175 116500921203770668154728763)
        ·
          refine ⟨174751381805656002232093145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116500921203770668154728763 174751381805656002232093145)
          ·
            refine ⟨131063536354242001674069859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174751381805656002232093145 131063536354242001674069859)
            ·
              refine ⟨196595304531363002511104789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131063536354242001674069859 196595304531363002511104789)
              ·
                refine ⟨9215404899907640742708037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196595304531363002511104789 9215404899907640742708037)
                ·
                  refine ⟨1727888418732682639257757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9215404899907640742708037 1727888418732682639257757)
                  ·
                    refine ⟨647958157024755989721659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1727888418732682639257757 647958157024755989721659)
                    ·
                      rfl

theorem cell22_1892841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_1892841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892841 prefixEnd_1892841 := by exact prefixLift 1892841
  have htrace : WordTrace (prefixWord ++ tailWord_1892841) baseStart_1892841 baseEnd_1892841 := by
    simpa [prefixWord, tailWord_1892841, baseEnd_1892841] using wordTrace_append hprefix tailTrace_1892841
  have hstable : (prefixWord ++ tailWord_1892841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892841).length < 2 ^ (prefixWord ++ tailWord_1892841).sum := by decide
  have hdescent : baseEnd_1892841 < baseStart_1892841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892856 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_1892856 : Nat := 118140960795 + 1892856 * 2 ^ 59
def prefixEnd_1892856 : Nat := 4983230072969 + 3 ^ 40 * 1892856 * 2
def baseEnd_1892856 : Nat := 647963291831300950596613

theorem tailTrace_1892856 : CollatzResearch.WordTrace tailWord_1892856 prefixEnd_1892856 647963291831300950596613 := by
  unfold tailWord_1892856
  simp only [CollatzResearch.WordTrace]
  refine ⟨34519065015256730456373211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46025420020342307275164281 34519065015256730456373211)
  ·
    refine ⟨51778597522885095684559817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34519065015256730456373211 51778597522885095684559817)
    ·
      refine ⟨38833948142163821763419863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51778597522885095684559817 38833948142163821763419863)
      ·
        refine ⟨58250922213245732645129795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38833948142163821763419863 58250922213245732645129795)
        ·
          refine ⟨87376383319868598967694693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58250922213245732645129795 87376383319868598967694693)
          ·
            refine ⟨16383071872475362306442755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87376383319868598967694693 16383071872475362306442755)
            ·
              refine ⟨24574607808713043459664133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16383071872475362306442755 24574607808713043459664133)
              ·
                refine ⟨4607738964133695648687025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24574607808713043459664133 4607738964133695648687025)
                ·
                  refine ⟨3455804223100271736515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4607738964133695648687025 3455804223100271736515269)
                  ·
                    refine ⟨647963291831300950596613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3455804223100271736515269 647963291831300950596613)
                    ·
                      rfl

theorem cell22_1892856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_1892856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892856 prefixEnd_1892856 := by exact prefixLift 1892856
  have htrace : WordTrace (prefixWord ++ tailWord_1892856) baseStart_1892856 baseEnd_1892856 := by
    simpa [prefixWord, tailWord_1892856, baseEnd_1892856] using wordTrace_append hprefix tailTrace_1892856
  have hstable : (prefixWord ++ tailWord_1892856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892856).length < 2 ^ (prefixWord ++ tailWord_1892856).sum := by decide
  have hdescent : baseEnd_1892856 < baseStart_1892856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892888 : List Nat := [2, 1, 2, 3, 3, 2, 3, 6]
def baseStart_1892888 : Nat := 118140960795 + 1892888 * 2 ^ 59
def prefixEnd_1892888 : Nat := 4983230072969 + 3 ^ 40 * 1892888 * 2
def baseEnd_1892888 : Nat := 71997138453918170421835

theorem tailTrace_1892888 : CollatzResearch.WordTrace tailWord_1892888 prefixEnd_1892888 71997138453918170421835 := by
  unfold tailWord_1892888
  simp only [CollatzResearch.WordTrace]
  refine ⟨34519648583198765188955659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46026198110931686918607545 34519648583198765188955659)
  ·
    refine ⟨51779472874798147783433489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34519648583198765188955659 51779472874798147783433489)
    ·
      refine ⟨38834604656098610837575117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51779472874798147783433489 38834604656098610837575117)
      ·
        refine ⟨14562976746036979064090669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38834604656098610837575117 14562976746036979064090669)
        ·
          refine ⟨5461116279763867149034001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14562976746036979064090669 5461116279763867149034001)
          ·
            refine ⟨4095837209822900361775501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5461116279763867149034001 4095837209822900361775501)
            ·
              refine ⟨1535938953683587635665813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4095837209822900361775501 1535938953683587635665813)
              ·
                refine ⟨71997138453918170421835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1535938953683587635665813 71997138453918170421835)
                ·
                  rfl

theorem cell22_1892888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 6].length) (baseStart_1892888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892888 prefixEnd_1892888 := by exact prefixLift 1892888
  have htrace : WordTrace (prefixWord ++ tailWord_1892888) baseStart_1892888 baseEnd_1892888 := by
    simpa [prefixWord, tailWord_1892888, baseEnd_1892888] using wordTrace_append hprefix tailTrace_1892888
  have hstable : (prefixWord ++ tailWord_1892888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892888).length < 2 ^ (prefixWord ++ tailWord_1892888).sum := by decide
  have hdescent : baseEnd_1892888 < baseStart_1892888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892909 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1892909 : Nat := 118140960795 + 1892909 * 2 ^ 59
def prefixEnd_1892909 : Nat := 4983230072969 + 3 ^ 40 * 1892909 * 2
def baseEnd_1892909 : Nat := 647981434814426479021451

theorem tailTrace_1892909 : CollatzResearch.WordTrace tailWord_1892909 prefixEnd_1892909 647981434814426479021451 := by
  unfold tailWord_1892909
  simp only [CollatzResearch.WordTrace]
  refine ⟨69040063099321450964425781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46026708732880967309617187 69040063099321450964425781)
  ·
    refine ⟨6472505915561386027914917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69040063099321450964425781 6472505915561386027914917)
    ·
      refine ⟨1213594859167759880234047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6472505915561386027914917 1213594859167759880234047)
      ·
        refine ⟨1820392288751639820351071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213594859167759880234047 1820392288751639820351071)
        ·
          refine ⟨2730588433127459730526607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820392288751639820351071 2730588433127459730526607)
          ·
            refine ⟨4095882649691189595789911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730588433127459730526607 4095882649691189595789911)
            ·
              refine ⟨6143823974536784393684867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095882649691189595789911 6143823974536784393684867)
              ·
                refine ⟨9215735961805176590527301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143823974536784393684867 9215735961805176590527301)
                ·
                  refine ⟨1727950492838470610723869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9215735961805176590527301 1727950492838470610723869)
                  ·
                    refine ⟨647981434814426479021451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1727950492838470610723869 647981434814426479021451)
                    ·
                      rfl

theorem cell22_1892909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1892909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892909 prefixEnd_1892909 := by exact prefixLift 1892909
  have htrace : WordTrace (prefixWord ++ tailWord_1892909) baseStart_1892909 baseEnd_1892909 := by
    simpa [prefixWord, tailWord_1892909, baseEnd_1892909] using wordTrace_append hprefix tailTrace_1892909
  have hstable : (prefixWord ++ tailWord_1892909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892909).length < 2 ^ (prefixWord ++ tailWord_1892909).sum := by decide
  have hdescent : baseEnd_1892909 < baseStart_1892909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892920 : List Nat := [2, 1, 2, 1, 4, 1, 1, 6, 1, 3]
def baseStart_1892920 : Nat := 118140960795 + 1892920 * 2 ^ 59
def prefixEnd_1892920 : Nat := 4983230072969 + 3 ^ 40 * 1892920 * 2
def baseEnd_1892920 : Nat := 647985200339226116996417

theorem tailTrace_1892920 : CollatzResearch.WordTrace tailWord_1892920 prefixEnd_1892920 647985200339226116996417 := by
  unfold tailWord_1892920
  simp only [CollatzResearch.WordTrace]
  refine ⟨34520232151140799921538107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46026976201521066562050809 34520232151140799921538107)
  ·
    refine ⟨51780348226711199882307161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34520232151140799921538107 51780348226711199882307161)
    ·
      refine ⟨38835261170033399911730371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51780348226711199882307161 38835261170033399911730371)
      ·
        refine ⟨58252891755050099867595557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38835261170033399911730371 58252891755050099867595557)
        ·
          refine ⟨10922417204071893725174167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58252891755050099867595557 10922417204071893725174167)
          ·
            refine ⟨16383625806107840587761251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10922417204071893725174167 16383625806107840587761251)
            ·
              refine ⟨24575438709161760881641877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16383625806107840587761251 24575438709161760881641877)
              ·
                refine ⟨1151973689491957541326963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24575438709161760881641877 1151973689491957541326963)
                ·
                  refine ⟨1727960534237936311990445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151973689491957541326963 1727960534237936311990445)
                  ·
                    refine ⟨647985200339226116996417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1727960534237936311990445 647985200339226116996417)
                    ·
                      rfl

theorem cell22_1892920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_1892920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892920 prefixEnd_1892920 := by exact prefixLift 1892920
  have htrace : WordTrace (prefixWord ++ tailWord_1892920) baseStart_1892920 baseEnd_1892920 := by
    simpa [prefixWord, tailWord_1892920, baseEnd_1892920] using wordTrace_append hprefix tailTrace_1892920
  have hstable : (prefixWord ++ tailWord_1892920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892920).length < 2 ^ (prefixWord ++ tailWord_1892920).sum := by decide
  have hdescent : baseEnd_1892920 < baseStart_1892920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892963 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 1, 4]
def baseStart_1892963 : Nat := 118140960795 + 1892963 * 2 ^ 59
def prefixEnd_1892963 : Nat := 4983230072969 + 3 ^ 40 * 1892963 * 2
def baseEnd_1892963 : Nat := 647999920117988338171285

theorem tailTrace_1892963 : CollatzResearch.WordTrace tailWord_1892963 prefixEnd_1892963 647999920117988338171285 := by
  unfold tailWord_1892963
  simp only [CollatzResearch.WordTrace]
  refine ⟨69042032641125818186891543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46028021760750545457927695 69042032641125818186891543)
  ·
    refine ⟨103563048961688727280337315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69042032641125818186891543 103563048961688727280337315)
    ·
      refine ⟨155344573442533090920505973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103563048961688727280337315 155344573442533090920505973)
      ·
        refine ⟨14563553760237477273797435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155344573442533090920505973 14563553760237477273797435)
        ·
          refine ⟨21845330640356215910696153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14563553760237477273797435 21845330640356215910696153)
          ·
            refine ⟨16383997980267161933022115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21845330640356215910696153 16383997980267161933022115)
            ·
              refine ⟨24575996970400742899533173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16383997980267161933022115 24575996970400742899533173)
              ·
                refine ⟨2303999715975069646831235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24575996970400742899533173 2303999715975069646831235)
                ·
                  refine ⟨3455999573962604470246853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303999715975069646831235 3455999573962604470246853)
                  ·
                    refine ⟨647999920117988338171285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3455999573962604470246853 647999920117988338171285)
                    ·
                      rfl

theorem cell22_1892963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 4].length) (baseStart_1892963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892963 prefixEnd_1892963 := by exact prefixLift 1892963
  have htrace : WordTrace (prefixWord ++ tailWord_1892963) baseStart_1892963 baseEnd_1892963 := by
    simpa [prefixWord, tailWord_1892963, baseEnd_1892963] using wordTrace_append hprefix tailTrace_1892963
  have hstable : (prefixWord ++ tailWord_1892963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892963).length < 2 ^ (prefixWord ++ tailWord_1892963).sum := by decide
  have hdescent : baseEnd_1892963 < baseStart_1892963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892991 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 1, 6]
def baseStart_1892991 : Nat := 118140960795 + 1892991 * 2 ^ 59
def prefixEnd_1892991 : Nat := 4983230072969 + 3 ^ 40 * 1892991 * 2
def baseEnd_1892991 : Nat := 648009505090205598471199

theorem tailTrace_1892991 : CollatzResearch.WordTrace tailWord_1892991 prefixEnd_1892991 648009505090205598471199 := by
  unfold tailWord_1892991
  simp only [CollatzResearch.WordTrace]
  refine ⟨69043053885024378968910827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46028702590016252645940551 69043053885024378968910827)
  ·
    refine ⟨103564580827536568453366241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69043053885024378968910827 103564580827536568453366241)
    ·
      refine ⟨77673435620652426340024681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103564580827536568453366241 77673435620652426340024681)
      ·
        refine ⟨58255076715489319755018511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77673435620652426340024681 58255076715489319755018511)
        ·
          refine ⟨87382615073233979632527767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58255076715489319755018511 87382615073233979632527767)
          ·
            refine ⟨131073922609850969448791651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87382615073233979632527767 131073922609850969448791651)
            ·
              refine ⟨196610883914776454173187477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131073922609850969448791651 196610883914776454173187477)
              ·
                refine ⟨9216135183505146289368163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196610883914776454173187477 9216135183505146289368163)
                ·
                  refine ⟨13824202775257719434052245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9216135183505146289368163 13824202775257719434052245)
                  ·
                    refine ⟨648009505090205598471199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13824202775257719434052245 648009505090205598471199)
                    ·
                      rfl

theorem cell22_1892991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_1892991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892991 prefixEnd_1892991 := by exact prefixLift 1892991
  have htrace : WordTrace (prefixWord ++ tailWord_1892991) baseStart_1892991 baseEnd_1892991 := by
    simpa [prefixWord, tailWord_1892991, baseEnd_1892991] using wordTrace_append hprefix tailTrace_1892991
  have hstable : (prefixWord ++ tailWord_1892991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892991).length < 2 ^ (prefixWord ++ tailWord_1892991).sum := by decide
  have hdescent : baseEnd_1892991 < baseStart_1892991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892993 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1892993 : Nat := 118140960795 + 1892993 * 2 ^ 59
def prefixEnd_1892993 : Nat := 4983230072969 + 3 ^ 40 * 1892993 * 2
def baseEnd_1892993 : Nat := 648010189731078259921193

theorem tailTrace_1892993 : CollatzResearch.WordTrace tailWord_1892993 prefixEnd_1892993 648010189731078259921193 := by
  unfold tailWord_1892993
  simp only [CollatzResearch.WordTrace]
  refine ⟨69043126831017133310483633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46028751220678088873655755 69043126831017133310483633)
  ·
    refine ⟨51782345123262849982862725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69043126831017133310483633 51782345123262849982862725)
    ·
      refine ⟨9709189710611784371786761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51782345123262849982862725 9709189710611784371786761)
      ·
        refine ⟨7281892282958838278840071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9709189710611784371786761 7281892282958838278840071)
        ·
          refine ⟨10922838424438257418260107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281892282958838278840071 10922838424438257418260107)
          ·
            refine ⟨16384257636657386127390161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10922838424438257418260107 16384257636657386127390161)
            ·
              refine ⟨12288193227493039595542621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16384257636657386127390161 12288193227493039595542621)
              ·
                refine ⟨4608072460309889848328483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12288193227493039595542621 4608072460309889848328483)
                ·
                  refine ⟨6912108690464834772492725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608072460309889848328483 6912108690464834772492725)
                  ·
                    refine ⟨648010189731078259921193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6912108690464834772492725 648010189731078259921193)
                    ·
                      rfl

theorem cell22_1892993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1892993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1892993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1892993 prefixEnd_1892993 := by exact prefixLift 1892993
  have htrace : WordTrace (prefixWord ++ tailWord_1892993) baseStart_1892993 baseEnd_1892993 := by
    simpa [prefixWord, tailWord_1892993, baseEnd_1892993] using wordTrace_append hprefix tailTrace_1892993
  have hstable : (prefixWord ++ tailWord_1892993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892993).length < 2 ^ (prefixWord ++ tailWord_1892993).sum := by decide
  have hdescent : baseEnd_1892993 < baseStart_1892993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893010 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1893010 : Nat := 118140960795 + 1893010 * 2 ^ 59
def prefixEnd_1893010 : Nat := 4983230072969 + 3 ^ 40 * 1893010 * 2
def baseEnd_1893010 : Nat := 648016009178495882246141

theorem tailTrace_1893010 : CollatzResearch.WordTrace tailWord_1893010 prefixEnd_1893010 648016009178495882246141 := by
  unfold tailWord_1893010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17260936717988886303463121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46029164581303696809234989 17260936717988886303463121)
  ·
    refine ⟨12945702538491664727597341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17260936717988886303463121 12945702538491664727597341)
    ·
      refine ⟨4854638451934374272849003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12945702538491664727597341 4854638451934374272849003)
      ·
        refine ⟨7281957677901561409273505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854638451934374272849003 7281957677901561409273505)
        ·
          refine ⟨5461468258426171056955129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7281957677901561409273505 5461468258426171056955129)
          ·
            refine ⟨4096101193819628292716347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5461468258426171056955129 4096101193819628292716347)
            ·
              refine ⟨6144151790729442439074521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096101193819628292716347 6144151790729442439074521)
              ·
                refine ⟨4608113843047081829305891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6144151790729442439074521 4608113843047081829305891)
                ·
                  refine ⟨6912170764570622743958837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608113843047081829305891 6912170764570622743958837)
                  ·
                    refine ⟨648016009178495882246141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6912170764570622743958837 648016009178495882246141)
                    ·
                      rfl

theorem cell22_1893010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1893010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893010 prefixEnd_1893010 := by exact prefixLift 1893010
  have htrace : WordTrace (prefixWord ++ tailWord_1893010) baseStart_1893010 baseEnd_1893010 := by
    simpa [prefixWord, tailWord_1893010, baseEnd_1893010] using wordTrace_append hprefix tailTrace_1893010
  have hstable : (prefixWord ++ tailWord_1893010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893010).length < 2 ^ (prefixWord ++ tailWord_1893010).sum := by decide
  have hdescent : baseEnd_1893010 < baseStart_1893010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893051 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 11]
def baseStart_1893051 : Nat := 118140960795 + 1893051 * 2 ^ 59
def prefixEnd_1893051 : Nat := 4983230072969 + 3 ^ 40 * 1893051 * 2
def baseEnd_1893051 : Nat := 216010014772128480657005

theorem tailTrace_1893051 : CollatzResearch.WordTrace tailWord_1893051 prefixEnd_1893051 216010014772128480657005 := by
  unfold tailWord_1893051
  simp only [CollatzResearch.WordTrace]
  refine ⟨69045242264807009216095007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46030161509871339477396671 69045242264807009216095007)
  ·
    refine ⟨103567863397210513824142511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69045242264807009216095007 103567863397210513824142511)
    ·
      refine ⟨155351795095815770736213767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103567863397210513824142511 155351795095815770736213767)
      ·
        refine ⟨233027692643723656104320651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155351795095815770736213767 233027692643723656104320651)
        ·
          refine ⟨349541538965585484156480977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233027692643723656104320651 349541538965585484156480977)
          ·
            refine ⟨262156154224189113117360733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349541538965585484156480977 262156154224189113117360733)
            ·
              refine ⟨98308557834070917419010275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262156154224189113117360733 98308557834070917419010275)
              ·
                refine ⟨147462836751106376128515413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98308557834070917419010275 147462836751106376128515413)
                ·
                  refine ⟨216010014772128480657005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 147462836751106376128515413 216010014772128480657005)
                  ·
                    rfl

theorem cell22_1893051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 11].length) (baseStart_1893051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893051 prefixEnd_1893051 := by exact prefixLift 1893051
  have htrace : WordTrace (prefixWord ++ tailWord_1893051) baseStart_1893051 baseEnd_1893051 := by
    simpa [prefixWord, tailWord_1893051, baseEnd_1893051] using wordTrace_append hprefix tailTrace_1893051
  have hstable : (prefixWord ++ tailWord_1893051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893051).length < 2 ^ (prefixWord ++ tailWord_1893051).sum := by decide
  have hdescent : baseEnd_1893051 < baseStart_1893051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893055 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 3, 3]
def baseStart_1893055 : Nat := 118140960795 + 1893055 * 2 ^ 59
def prefixEnd_1893055 : Nat := 4983230072969 + 3 ^ 40 * 1893055 * 2
def baseEnd_1893055 : Nat := 648031413598130764871003

theorem tailTrace_1893055 : CollatzResearch.WordTrace tailWord_1893055 prefixEnd_1893055 648031413598130764871003 := by
  unfold tailWord_1893055
  simp only [CollatzResearch.WordTrace]
  refine ⟨69045388156792517899240619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46030258771195011932827079 69045388156792517899240619)
  ·
    refine ⟨103568082235188776848860929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69045388156792517899240619 103568082235188776848860929)
    ·
      refine ⟨77676061676391582636645697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103568082235188776848860929 77676061676391582636645697)
      ·
        refine ⟨58257046257293686977484273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77676061676391582636645697 58257046257293686977484273)
        ·
          refine ⟨43692784692970265233113205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58257046257293686977484273 43692784692970265233113205)
          ·
            refine ⟨4096198564965962365604363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43692784692970265233113205 4096198564965962365604363)
            ·
              refine ⟨6144297847448943548406545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096198564965962365604363 6144297847448943548406545)
              ·
                refine ⟨4608223385586707661304909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6144297847448943548406545 4608223385586707661304909)
                ·
                  refine ⟨1728083769595015372989341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4608223385586707661304909 1728083769595015372989341)
                  ·
                    refine ⟨648031413598130764871003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1728083769595015372989341 648031413598130764871003)
                    ·
                      rfl

theorem cell22_1893055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_1893055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893055 prefixEnd_1893055 := by exact prefixLift 1893055
  have htrace : WordTrace (prefixWord ++ tailWord_1893055) baseStart_1893055 baseEnd_1893055 := by
    simpa [prefixWord, tailWord_1893055, baseEnd_1893055] using wordTrace_append hprefix tailTrace_1893055
  have hstable : (prefixWord ++ tailWord_1893055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893055).length < 2 ^ (prefixWord ++ tailWord_1893055).sum := by decide
  have hdescent : baseEnd_1893055 < baseStart_1893055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893102 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_1893102 : Nat := 118140960795 + 1893102 * 2 ^ 59
def prefixEnd_1893102 : Nat := 4983230072969 + 3 ^ 40 * 1893102 * 2
def baseEnd_1893102 : Nat := 216015834219546102981953

theorem tailTrace_1893102 : CollatzResearch.WordTrace tailWord_1893102 prefixEnd_1893102 216015834219546102981953 := by
  unfold tailWord_1893102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630887798452780615775195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46031401591748163284134373 8630887798452780615775195)
  ·
    refine ⟨12946331697679170923662793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8630887798452780615775195 12946331697679170923662793)
    ·
      refine ⟨9709748773259378192747095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12946331697679170923662793 9709748773259378192747095)
      ·
        refine ⟨14564623159889067289120643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9709748773259378192747095 14564623159889067289120643)
        ·
          refine ⟨21846934739833600933680965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14564623159889067289120643 21846934739833600933680965)
          ·
            refine ⟨4096300263718800175065181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21846934739833600933680965 4096300263718800175065181)
            ·
              refine ⟨1536112598894550065649443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4096300263718800175065181 1536112598894550065649443)
              ·
                refine ⟨2304168898341825098474165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536112598894550065649443 2304168898341825098474165)
                ·
                  refine ⟨216015834219546102981953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304168898341825098474165 216015834219546102981953)
                  ·
                    rfl

theorem cell22_1893102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_1893102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893102 prefixEnd_1893102 := by exact prefixLift 1893102
  have htrace : WordTrace (prefixWord ++ tailWord_1893102) baseStart_1893102 baseEnd_1893102 := by
    simpa [prefixWord, tailWord_1893102, baseEnd_1893102] using wordTrace_append hprefix tailTrace_1893102
  have hstable : (prefixWord ++ tailWord_1893102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893102).length < 2 ^ (prefixWord ++ tailWord_1893102).sum := by decide
  have hdescent : baseEnd_1893102 < baseStart_1893102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893160 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1893160 : Nat := 118140960795 + 1893160 * 2 ^ 59
def prefixEnd_1893160 : Nat := 4983230072969 + 3 ^ 40 * 1893160 * 2
def baseEnd_1893160 : Nat := 648067357243945490995681

theorem tailTrace_1893160 : CollatzResearch.WordTrace tailWord_1893160 prefixEnd_1893160 648067357243945490995681 := by
  unfold tailWord_1893160
  simp only [CollatzResearch.WordTrace]
  refine ⟨34524608910706060415906467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46032811880941413887875289 34524608910706060415906467)
  ·
    refine ⟨51786913366059090623859701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34524608910706060415906467 51786913366059090623859701)
    ·
      refine ⟨4855023128068039745986847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51786913366059090623859701 4855023128068039745986847)
      ·
        refine ⟨7282534692102059618980271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4855023128068039745986847 7282534692102059618980271)
        ·
          refine ⟨10923802038153089428470407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7282534692102059618980271 10923802038153089428470407)
          ·
            refine ⟨16385703057229634142705611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923802038153089428470407 16385703057229634142705611)
            ·
              refine ⟨24578554585844451214058417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16385703057229634142705611 24578554585844451214058417)
              ·
                refine ⟨18433915939383338410543813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24578554585844451214058417 18433915939383338410543813)
                ·
                  refine ⟨3456359238634375951976965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18433915939383338410543813 3456359238634375951976965)
                  ·
                    refine ⟨648067357243945490995681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3456359238634375951976965 648067357243945490995681)
                    ·
                      rfl

theorem cell22_1893160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1893160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893160 prefixEnd_1893160 := by exact prefixLift 1893160
  have htrace : WordTrace (prefixWord ++ tailWord_1893160) baseStart_1893160 baseEnd_1893160 := by
    simpa [prefixWord, tailWord_1893160, baseEnd_1893160] using wordTrace_append hprefix tailTrace_1893160
  have hstable : (prefixWord ++ tailWord_1893160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893160).length < 2 ^ (prefixWord ++ tailWord_1893160).sum := by decide
  have hdescent : baseEnd_1893160 < baseStart_1893160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893203 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 7]
def baseStart_1893203 : Nat := 118140960795 + 1893203 * 2 ^ 59
def prefixEnd_1893203 : Nat := 4983230072969 + 3 ^ 40 * 1893203 * 2
def baseEnd_1893203 : Nat := 216027359007569237390183

theorem tailTrace_1893203 : CollatzResearch.WordTrace tailWord_1893203 prefixEnd_1893203 216027359007569237390183 := by
  unfold tailWord_1893203
  simp only [CollatzResearch.WordTrace]
  refine ⟨69050786160256339175628263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46033857440170892783752175 69050786160256339175628263)
  ·
    refine ⟨103576179240384508763442395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69050786160256339175628263 103576179240384508763442395)
    ·
      refine ⟨155364268860576763145163593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103576179240384508763442395 155364268860576763145163593)
      ·
        refine ⟨116523201645432572358872695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155364268860576763145163593 116523201645432572358872695)
        ·
          refine ⟨174784802468148858538309043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116523201645432572358872695 174784802468148858538309043)
          ·
            refine ⟨262177203702223287807463565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174784802468148858538309043 262177203702223287807463565)
            ·
              refine ⟨98316451388333732927798837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262177203702223287807463565 98316451388333732927798837)
              ·
                refine ⟨9217167317656287461981141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98316451388333732927798837 9217167317656287461981141)
                ·
                  refine ⟨216027359007569237390183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9217167317656287461981141 216027359007569237390183)
                  ·
                    rfl

theorem cell22_1893203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 7].length) (baseStart_1893203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893203 prefixEnd_1893203 := by exact prefixLift 1893203
  have htrace : WordTrace (prefixWord ++ tailWord_1893203) baseStart_1893203 baseEnd_1893203 := by
    simpa [prefixWord, tailWord_1893203, baseEnd_1893203] using wordTrace_append hprefix tailTrace_1893203
  have hstable : (prefixWord ++ tailWord_1893203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893203).length < 2 ^ (prefixWord ++ tailWord_1893203).sum := by decide
  have hdescent : baseEnd_1893203 < baseStart_1893203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893282 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1893282 : Nat := 118140960795 + 1893282 * 2 ^ 59
def prefixEnd_1893282 : Nat := 4983230072969 + 3 ^ 40 * 1893282 * 2
def baseEnd_1893282 : Nat := 216036373445725946481769

theorem tailTrace_1893282 : CollatzResearch.WordTrace tailWord_1893282 prefixEnd_1893282 216036373445725946481769 := by
  unfold tailWord_1893282
  simp only [CollatzResearch.WordTrace]
  refine ⟨17263416881742533916938525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46035778351313423778502733 17263416881742533916938525)
  ·
    refine ⟨6473781330653450218851947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17263416881742533916938525 6473781330653450218851947)
    ·
      refine ⟨9710671995980175328277921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473781330653450218851947 9710671995980175328277921)
      ·
        refine ⟨7283003996985131496208441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9710671995980175328277921 7283003996985131496208441)
        ·
          refine ⟨5462252997738848622156331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7283003996985131496208441 5462252997738848622156331)
          ·
            refine ⟨8193379496608272933234497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462252997738848622156331 8193379496608272933234497)
            ·
              refine ⟨6145034622456204699925873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8193379496608272933234497 6145034622456204699925873)
              ·
                refine ⟨4608775966842153524944405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6145034622456204699925873 4608775966842153524944405)
                ·
                  refine ⟨216036373445725946481769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4608775966842153524944405 216036373445725946481769)
                  ·
                    rfl

theorem cell22_1893282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1893282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893282 prefixEnd_1893282 := by exact prefixLift 1893282
  have htrace : WordTrace (prefixWord ++ tailWord_1893282) baseStart_1893282 baseEnd_1893282 := by
    simpa [prefixWord, tailWord_1893282, baseEnd_1893282] using wordTrace_append hprefix tailTrace_1893282
  have hstable : (prefixWord ++ tailWord_1893282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893282).length < 2 ^ (prefixWord ++ tailWord_1893282).sum := by decide
  have hdescent : baseEnd_1893282 < baseStart_1893282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893312 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_1893312 : Nat := 118140960795 + 1893312 * 2 ^ 59
def prefixEnd_1893312 : Nat := 4983230072969 + 3 ^ 40 * 1893312 * 2
def baseEnd_1893312 : Nat := 648119389950267761195215

theorem tailTrace_1893312 : CollatzResearch.WordTrace tailWord_1893312 prefixEnd_1893312 648119389950267761195215 := by
  unfold tailWord_1893312
  simp only [CollatzResearch.WordTrace]
  refine ⟨34527380858430725395673095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46036507811240967194230793 34527380858430725395673095)
  ·
    refine ⟨51791071287646088093509643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34527380858430725395673095 51791071287646088093509643)
    ·
      refine ⟨77686606931469132140264465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51791071287646088093509643 77686606931469132140264465)
      ·
        refine ⟨58264955198601849105198349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77686606931469132140264465 58264955198601849105198349)
        ·
          refine ⟨21849358199475693414449381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58264955198601849105198349 21849358199475693414449381)
          ·
            refine ⟨4096754662401692515209259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21849358199475693414449381 4096754662401692515209259)
            ·
              refine ⟨6145131993602538772813889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096754662401692515209259 6145131993602538772813889)
              ·
                refine ⟨4608848995201904079610417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6145131993602538772813889 4608848995201904079610417)
                ·
                  refine ⟨3456636746401428059707813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4608848995201904079610417 3456636746401428059707813)
                  ·
                    refine ⟨648119389950267761195215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3456636746401428059707813 648119389950267761195215)
                    ·
                      rfl

theorem cell22_1893312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_1893312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893312 prefixEnd_1893312 := by exact prefixLift 1893312
  have htrace : WordTrace (prefixWord ++ tailWord_1893312) baseStart_1893312 baseEnd_1893312 := by
    simpa [prefixWord, tailWord_1893312, baseEnd_1893312] using wordTrace_append hprefix tailTrace_1893312
  have hstable : (prefixWord ++ tailWord_1893312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893312).length < 2 ^ (prefixWord ++ tailWord_1893312).sum := by decide
  have hdescent : baseEnd_1893312 < baseStart_1893312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893316 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 6]
def baseStart_1893316 : Nat := 118140960795 + 1893316 * 2 ^ 59
def prefixEnd_1893316 : Nat := 4983230072969 + 3 ^ 40 * 1893316 * 2
def baseEnd_1893316 : Nat := 216040253077337694698401

theorem tailTrace_1893316 : CollatzResearch.WordTrace tailWord_1893316 prefixEnd_1893316 216040253077337694698401 := by
  unfold tailWord_1893316
  simp only [CollatzResearch.WordTrace]
  refine ⟨34527453804423479737245901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46036605072564639649661201 34527453804423479737245901)
  ·
    refine ⟨12947795176658804901467213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34527453804423479737245901 12947795176658804901467213)
    ·
      refine ⟨4855423191247051838050205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12947795176658804901467213 4855423191247051838050205)
      ·
        refine ⟨1820783696717644439268827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4855423191247051838050205 1820783696717644439268827)
        ·
          refine ⟨2731175545076466658903241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820783696717644439268827 2731175545076466658903241)
          ·
            refine ⟨2048381658807349994177431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731175545076466658903241 2048381658807349994177431)
            ·
              refine ⟨3072572488211024991266147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048381658807349994177431 3072572488211024991266147)
              ·
                refine ⟨4608858732316537486899221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072572488211024991266147 4608858732316537486899221)
                ·
                  refine ⟨216040253077337694698401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4608858732316537486899221 216040253077337694698401)
                  ·
                    rfl

theorem cell22_1893316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_1893316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893316 prefixEnd_1893316 := by exact prefixLift 1893316
  have htrace : WordTrace (prefixWord ++ tailWord_1893316) baseStart_1893316 baseEnd_1893316 := by
    simpa [prefixWord, tailWord_1893316, baseEnd_1893316] using wordTrace_append hprefix tailTrace_1893316
  have hstable : (prefixWord ++ tailWord_1893316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893316).length < 2 ^ (prefixWord ++ tailWord_1893316).sum := by decide
  have hdescent : baseEnd_1893316 < baseStart_1893316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893346 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1893346 : Nat := 118140960795 + 1893346 * 2 ^ 59
def prefixEnd_1893346 : Nat := 4983230072969 + 3 ^ 40 * 1893346 * 2
def baseEnd_1893346 : Nat := 648131028845103005845111

theorem tailTrace_1893346 : CollatzResearch.WordTrace tailWord_1893346 prefixEnd_1893346 648131028845103005845111 := by
  unfold tailWord_1893346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264000449684568649520973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46037334532492183065389261 17264000449684568649520973)
  ·
    refine ⟨6474000168631713243570365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17264000449684568649520973 6474000168631713243570365)
    ·
      refine ⟨2427750063236892466338887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6474000168631713243570365 2427750063236892466338887)
      ·
        refine ⟨3641625094855338699508331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427750063236892466338887 3641625094855338699508331)
        ·
          refine ⟨5462437642283008049262497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3641625094855338699508331 5462437642283008049262497)
          ·
            refine ⟨4096828231712256036946873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5462437642283008049262497 4096828231712256036946873)
            ·
              refine ⟨3072621173784192027710155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4096828231712256036946873 3072621173784192027710155)
              ·
                refine ⟨4608931760676288041565233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072621173784192027710155 4608931760676288041565233)
                ·
                  refine ⟨3456698820507216031173925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4608931760676288041565233 3456698820507216031173925)
                  ·
                    refine ⟨648131028845103005845111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3456698820507216031173925 648131028845103005845111)
                    ·
                      rfl

theorem cell22_1893346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1893346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893346 prefixEnd_1893346 := by exact prefixLift 1893346
  have htrace : WordTrace (prefixWord ++ tailWord_1893346) baseStart_1893346 baseEnd_1893346 := by
    simpa [prefixWord, tailWord_1893346, baseEnd_1893346] using wordTrace_append hprefix tailTrace_1893346
  have hstable : (prefixWord ++ tailWord_1893346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893346).length < 2 ^ (prefixWord ++ tailWord_1893346).sum := by decide
  have hdescent : baseEnd_1893346 < baseStart_1893346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893370 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_1893370 : Nat := 118140960795 + 1893370 * 2 ^ 59
def prefixEnd_1893370 : Nat := 4983230072969 + 3 ^ 40 * 1893370 * 2
def baseEnd_1893370 : Nat := 648139244535574943245037

theorem tailTrace_1893370 : CollatzResearch.WordTrace tailWord_1893370 prefixEnd_1893370 648139244535574943245037 := by
  unfold tailWord_1893370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264219287662831674239391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46037918100434217797971709 17264219287662831674239391)
  ·
    refine ⟨25896328931494247511359087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17264219287662831674239391 25896328931494247511359087)
    ·
      refine ⟨38844493397241371267038631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25896328931494247511359087 38844493397241371267038631)
      ·
        refine ⟨58266740095862056900557947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38844493397241371267038631 58266740095862056900557947)
        ·
          refine ⟨87400110143793085350836921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58266740095862056900557947 87400110143793085350836921)
          ·
            refine ⟨65550082607844814013127691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87400110143793085350836921 65550082607844814013127691)
            ·
              refine ⟨98325123911767221019691537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65550082607844814013127691 98325123911767221019691537)
              ·
                refine ⟨73743842933825415764768653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98325123911767221019691537 73743842933825415764768653)
                ·
                  refine ⟨27653941100184530911788245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73743842933825415764768653 27653941100184530911788245)
                  ·
                    refine ⟨648139244535574943245037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27653941100184530911788245 648139244535574943245037)
                    ·
                      rfl

theorem cell22_1893370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_1893370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893370 prefixEnd_1893370 := by exact prefixLift 1893370
  have htrace : WordTrace (prefixWord ++ tailWord_1893370) baseStart_1893370 baseEnd_1893370 := by
    simpa [prefixWord, tailWord_1893370, baseEnd_1893370] using wordTrace_append hprefix tailTrace_1893370
  have hstable : (prefixWord ++ tailWord_1893370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893370).length < 2 ^ (prefixWord ++ tailWord_1893370).sum := by decide
  have hdescent : baseEnd_1893370 < baseStart_1893370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893372 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 5]
def baseStart_1893372 : Nat := 118140960795 + 1893372 * 2 ^ 59
def prefixEnd_1893372 : Nat := 4983230072969 + 3 ^ 40 * 1893372 * 2
def baseEnd_1893372 : Nat := 216046643058815868231677

theorem tailTrace_1893372 : CollatzResearch.WordTrace tailWord_1893372 prefixEnd_1893372 216046643058815868231677 := by
  unfold tailWord_1893372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34528475048322040519265185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46037966731096054025686913 34528475048322040519265185)
  ·
    refine ⟨25896356286241530389448889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34528475048322040519265185 25896356286241530389448889)
    ·
      refine ⟨19422267214681147792086667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25896356286241530389448889 19422267214681147792086667)
      ·
        refine ⟨29133400822021721688130001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19422267214681147792086667 29133400822021721688130001)
        ·
          refine ⟨21850050616516291266097501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29133400822021721688130001 21850050616516291266097501)
          ·
            refine ⟨8193768981193609224786563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21850050616516291266097501 8193768981193609224786563)
            ·
              refine ⟨12290653471790413837179845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8193768981193609224786563 12290653471790413837179845)
              ·
                refine ⟨2304497525960702594471221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12290653471790413837179845 2304497525960702594471221)
                ·
                  refine ⟨216046643058815868231677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304497525960702594471221 216046643058815868231677)
                  ·
                    rfl

theorem cell22_1893372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_1893372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893372 prefixEnd_1893372 := by exact prefixLift 1893372
  have htrace : WordTrace (prefixWord ++ tailWord_1893372) baseStart_1893372 baseEnd_1893372 := by
    simpa [prefixWord, tailWord_1893372, baseEnd_1893372] using wordTrace_append hprefix tailTrace_1893372
  have hstable : (prefixWord ++ tailWord_1893372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893372).length < 2 ^ (prefixWord ++ tailWord_1893372).sum := by decide
  have hdescent : baseEnd_1893372 < baseStart_1893372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893378 : List Nat := [3, 4, 1, 3, 2, 1, 1, 7]
def baseStart_1893378 : Nat := 118140960795 + 1893378 * 2 ^ 59
def prefixEnd_1893378 : Nat := 4983230072969 + 3 ^ 40 * 1893378 * 2
def baseEnd_1893378 : Nat := 72015775899896176560557

theorem tailTrace_1893378 : CollatzResearch.WordTrace tailWord_1893378 prefixEnd_1893378 72015775899896176560557 := by
  unfold tailWord_1893378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264292233655586015812197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46038112623081562708832525 17264292233655586015812197)
  ·
    refine ⟨3237054793810422377964787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17264292233655586015812197 3237054793810422377964787)
    ·
      refine ⟨4855582190715633566947181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3237054793810422377964787 4855582190715633566947181)
      ·
        refine ⟨1820843321518362587605193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4855582190715633566947181 1820843321518362587605193)
        ·
          refine ⟨1365632491138771940703895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1820843321518362587605193 1365632491138771940703895)
          ·
            refine ⟨2048448736708157911055843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365632491138771940703895 2048448736708157911055843)
            ·
              refine ⟨3072673105062236866583765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048448736708157911055843 3072673105062236866583765)
              ·
                refine ⟨72015775899896176560557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3072673105062236866583765 72015775899896176560557)
                ·
                  rfl

theorem cell22_1893378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_1893378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893378 prefixEnd_1893378 := by exact prefixLift 1893378
  have htrace : WordTrace (prefixWord ++ tailWord_1893378) baseStart_1893378 baseEnd_1893378 := by
    simpa [prefixWord, tailWord_1893378, baseEnd_1893378] using wordTrace_append hprefix tailTrace_1893378
  have hstable : (prefixWord ++ tailWord_1893378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893378).length < 2 ^ (prefixWord ++ tailWord_1893378).sum := by decide
  have hdescent : baseEnd_1893378 < baseStart_1893378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893387 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 2, 5]
def baseStart_1893387 : Nat := 118140960795 + 1893387 * 2 ^ 59
def prefixEnd_1893387 : Nat := 4983230072969 + 3 ^ 40 * 1893387 * 2
def baseEnd_1893387 : Nat := 648145063982992565569985

theorem tailTrace_1893387 : CollatzResearch.WordTrace tailWord_1893387 prefixEnd_1893387 648145063982992565569985 := by
  unfold tailWord_1893387
  simp only [CollatzResearch.WordTrace]
  refine ⟨69057497191589738600326415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46038331461059825733550943 69057497191589738600326415)
  ·
    refine ⟨103586245787384607900489623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69057497191589738600326415 103586245787384607900489623)
    ·
      refine ⟨155379368681076911850734435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103586245787384607900489623 155379368681076911850734435)
      ·
        refine ⟨233069053021615367776101653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155379368681076911850734435 233069053021615367776101653)
        ·
          refine ⟨10925111860388220364504765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233069053021615367776101653 10925111860388220364504765)
          ·
            refine ⟨4096916947645582636689287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10925111860388220364504765 4096916947645582636689287)
            ·
              refine ⟨6145375421468373955033931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096916947645582636689287 6145375421468373955033931)
              ·
                refine ⟨9218063132202560932550897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145375421468373955033931 9218063132202560932550897)
                ·
                  refine ⟨6913547349151920699413173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9218063132202560932550897 6913547349151920699413173)
                  ·
                    refine ⟨648145063982992565569985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6913547349151920699413173 648145063982992565569985)
                    ·
                      rfl

theorem cell22_1893387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 5].length) (baseStart_1893387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893387 prefixEnd_1893387 := by exact prefixLift 1893387
  have htrace : WordTrace (prefixWord ++ tailWord_1893387) baseStart_1893387 baseEnd_1893387 := by
    simpa [prefixWord, tailWord_1893387, baseEnd_1893387] using wordTrace_append hprefix tailTrace_1893387
  have hstable : (prefixWord ++ tailWord_1893387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893387).length < 2 ^ (prefixWord ++ tailWord_1893387).sum := by decide
  have hdescent : baseEnd_1893387 < baseStart_1893387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893402 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_1893402 : Nat := 118140960795 + 1893402 * 2 ^ 59
def prefixEnd_1893402 : Nat := 4983230072969 + 3 ^ 40 * 1893402 * 2
def baseEnd_1893402 : Nat := 648150198789537526444939

theorem tailTrace_1893402 : CollatzResearch.WordTrace tailWord_1893402 prefixEnd_1893402 648150198789537526444939 := by
  unfold tailWord_1893402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264511071633849040530615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46038696191023597441414973 17264511071633849040530615)
  ·
    refine ⟨25896766607450773560795923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17264511071633849040530615 25896766607450773560795923)
    ·
      refine ⟨38845149911176160341193885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25896766607450773560795923 38845149911176160341193885)
      ·
        refine ⟨14566931216691060127947707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38845149911176160341193885 14566931216691060127947707)
        ·
          refine ⟨21850396825036590191921561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14566931216691060127947707 21850396825036590191921561)
          ·
            refine ⟨16387797618777442643941171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21850396825036590191921561 16387797618777442643941171)
            ·
              refine ⟨24581696428166163965911757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16387797618777442643941171 24581696428166163965911757)
              ·
                refine ⟨9218136160562311487216909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24581696428166163965911757 9218136160562311487216909)
                ·
                  refine ⟨3456801060210866807706341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9218136160562311487216909 3456801060210866807706341)
                  ·
                    refine ⟨648150198789537526444939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3456801060210866807706341 648150198789537526444939)
                    ·
                      rfl

theorem cell22_1893402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_1893402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893402 prefixEnd_1893402 := by exact prefixLift 1893402
  have htrace : WordTrace (prefixWord ++ tailWord_1893402) baseStart_1893402 baseEnd_1893402 := by
    simpa [prefixWord, tailWord_1893402, baseEnd_1893402] using wordTrace_append hprefix tailTrace_1893402
  have hstable : (prefixWord ++ tailWord_1893402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893402).length < 2 ^ (prefixWord ++ tailWord_1893402).sum := by decide
  have hdescent : baseEnd_1893402 < baseStart_1893402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893434 : List Nat := [3, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_1893434 : Nat := 118140960795 + 1893434 * 2 ^ 59
def prefixEnd_1893434 : Nat := 4983230072969 + 3 ^ 40 * 1893434 * 2
def baseEnd_1893434 : Nat := 216053717681166703214947

theorem tailTrace_1893434 : CollatzResearch.WordTrace tailWord_1893434 prefixEnd_1893434 216053717681166703214947 := by
  unfold tailWord_1893434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264802855604866406821839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46039474281612977084858237 17264802855604866406821839)
  ·
    refine ⟨25897204283407299610232759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17264802855604866406821839 25897204283407299610232759)
    ·
      refine ⟨38845806425110949415349139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25897204283407299610232759 38845806425110949415349139)
      ·
        refine ⟨58268709637666424123023709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38845806425110949415349139 58268709637666424123023709)
        ·
          refine ⟨21850766114124909046133891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58268709637666424123023709 21850766114124909046133891)
          ·
            refine ⟨32776149171187363569200837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21850766114124909046133891 32776149171187363569200837)
            ·
              refine ⟨6145527969597630669225157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32776149171187363569200837 6145527969597630669225157)
              ·
                refine ⟨1152286494299555750479717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6145527969597630669225157 1152286494299555750479717)
                ·
                  refine ⟨216053717681166703214947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1152286494299555750479717 216053717681166703214947)
                  ·
                    rfl

theorem cell22_1893434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_1893434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893434 prefixEnd_1893434 := by exact prefixLift 1893434
  have htrace : WordTrace (prefixWord ++ tailWord_1893434) baseStart_1893434 baseEnd_1893434 := by
    simpa [prefixWord, tailWord_1893434, baseEnd_1893434] using wordTrace_append hprefix tailTrace_1893434
  have hstable : (prefixWord ++ tailWord_1893434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893434).length < 2 ^ (prefixWord ++ tailWord_1893434).sum := by decide
  have hdescent : baseEnd_1893434 < baseStart_1893434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893447 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1893447 : Nat := 118140960795 + 1893447 * 2 ^ 59
def prefixEnd_1893447 : Nat := 4983230072969 + 3 ^ 40 * 1893447 * 2
def baseEnd_1893447 : Nat := 648165603209172409069801

theorem tailTrace_1893447 : CollatzResearch.WordTrace tailWord_1893447 prefixEnd_1893447 648165603209172409069801 := by
  unfold tailWord_1893447
  simp only [CollatzResearch.WordTrace]
  refine ⟨69059685571372368847510595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46039790380914912565007063 69059685571372368847510595)
  ·
    refine ⟨103589528357058553271265893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69059685571372368847510595 103589528357058553271265893)
    ·
      refine ⟨19423036566948478738362355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103589528357058553271265893 19423036566948478738362355)
      ·
        refine ⟨29134554850422718107543533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19423036566948478738362355 29134554850422718107543533)
        ·
          refine ⟨10925458068908519290328825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29134554850422718107543533 10925458068908519290328825)
          ·
            refine ⟨8194093551681389467746619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10925458068908519290328825 8194093551681389467746619)
            ·
              refine ⟨12291140327522084201619929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8194093551681389467746619 12291140327522084201619929)
              ·
                refine ⟨9218355245641563151214947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12291140327522084201619929 9218355245641563151214947)
                ·
                  refine ⟨13827532868462344726822421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9218355245641563151214947 13827532868462344726822421)
                  ·
                    refine ⟨648165603209172409069801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13827532868462344726822421 648165603209172409069801)
                    ·
                      rfl

theorem cell22_1893447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1893447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893447 prefixEnd_1893447 := by exact prefixLift 1893447
  have htrace : WordTrace (prefixWord ++ tailWord_1893447) baseStart_1893447 baseEnd_1893447 := by
    simpa [prefixWord, tailWord_1893447, baseEnd_1893447] using wordTrace_append hprefix tailTrace_1893447
  have hstable : (prefixWord ++ tailWord_1893447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893447).length < 2 ^ (prefixWord ++ tailWord_1893447).sum := by decide
  have hdescent : baseEnd_1893447 < baseStart_1893447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893554 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1893554 : Nat := 118140960795 + 1893554 * 2 ^ 59
def prefixEnd_1893554 : Nat := 4983230072969 + 3 ^ 40 * 1893554 * 2
def baseEnd_1893554 : Nat := 648202231495859796644473

theorem tailTrace_1893554 : CollatzResearch.WordTrace tailWord_1893554 prefixEnd_1893554 648202231495859796644473 := by
  unfold tailWord_1893554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265897045496181530413929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46042392121323150747770477 17265897045496181530413929)
  ·
    refine ⟨12949422784122136147810447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17265897045496181530413929 12949422784122136147810447)
    ·
      refine ⟨19424134176183204221715671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12949422784122136147810447 19424134176183204221715671)
      ·
        refine ⟨29136201264274806332573507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19424134176183204221715671 29136201264274806332573507)
        ·
          refine ⟨43704301896412209498860261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29136201264274806332573507 43704301896412209498860261)
          ·
            refine ⟨8194556605577289281036299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43704301896412209498860261 8194556605577289281036299)
            ·
              refine ⟨12291834908365933921554449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8194556605577289281036299 12291834908365933921554449)
              ·
                refine ⟨9218876181274450441165837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12291834908365933921554449 9218876181274450441165837)
                ·
                  refine ⟨3457078567977918915437189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9218876181274450441165837 3457078567977918915437189)
                  ·
                    refine ⟨648202231495859796644473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3457078567977918915437189 648202231495859796644473)
                    ·
                      rfl

theorem cell22_1893554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1893554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893554 prefixEnd_1893554 := by exact prefixLift 1893554
  have htrace : WordTrace (prefixWord ++ tailWord_1893554) baseStart_1893554 baseEnd_1893554 := by
    simpa [prefixWord, tailWord_1893554, baseEnd_1893554] using wordTrace_append hprefix tailTrace_1893554
  have hstable : (prefixWord ++ tailWord_1893554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893554).length < 2 ^ (prefixWord ++ tailWord_1893554).sum := by decide
  have hdescent : baseEnd_1893554 < baseStart_1893554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893599 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 2, 4]
def baseStart_1893599 : Nat := 118140960795 + 1893599 * 2 ^ 59
def prefixEnd_1893599 : Nat := 4983230072969 + 3 ^ 40 * 1893599 * 2
def baseEnd_1893599 : Nat := 648217635915494679269335

theorem tailTrace_1893599 : CollatzResearch.WordTrace tailWord_1893599 prefixEnd_1893599 648217635915494679269335 := by
  unfold tailWord_1893599
  simp only [CollatzResearch.WordTrace]
  refine ⟨69065229466821698807043851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46043486311214465871362567 69065229466821698807043851)
  ·
    refine ⟨103597844200232548210565777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69065229466821698807043851 103597844200232548210565777)
    ·
      refine ⟨77698383150174411157924333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103597844200232548210565777 77698383150174411157924333)
      ·
        refine ⟨29136893681315404184221625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77698383150174411157924333 29136893681315404184221625)
        ·
          refine ⟨21852670260986553138166219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29136893681315404184221625 21852670260986553138166219)
          ·
            refine ⟨32779005391479829707249329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21852670260986553138166219 32779005391479829707249329)
            ·
              refine ⟨24584254043609872280436997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32779005391479829707249329 24584254043609872280436997)
              ·
                refine ⟨4609547633176851052581937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24584254043609872280436997 4609547633176851052581937)
                ·
                  refine ⟨3457160724882638289436453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4609547633176851052581937 3457160724882638289436453)
                  ·
                    refine ⟨648217635915494679269335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3457160724882638289436453 648217635915494679269335)
                    ·
                      rfl

theorem cell22_1893599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_1893599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893599 prefixEnd_1893599 := by exact prefixLift 1893599
  have htrace : WordTrace (prefixWord ++ tailWord_1893599) baseStart_1893599 baseEnd_1893599 := by
    simpa [prefixWord, tailWord_1893599, baseEnd_1893599] using wordTrace_append hprefix tailTrace_1893599
  have hstable : (prefixWord ++ tailWord_1893599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893599).length < 2 ^ (prefixWord ++ tailWord_1893599).sum := by decide
  have hdescent : baseEnd_1893599 < baseStart_1893599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893601 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 4, 3]
def baseStart_1893601 : Nat := 118140960795 + 1893601 * 2 ^ 59
def prefixEnd_1893601 : Nat := 4983230072969 + 3 ^ 40 * 1893601 * 2
def baseEnd_1893601 : Nat := 648218320556367340719329

theorem tailTrace_1893601 : CollatzResearch.WordTrace tailWord_1893601 prefixEnd_1893601 648218320556367340719329 := by
  unfold tailWord_1893601
  simp only [CollatzResearch.WordTrace]
  refine ⟨69065302412814453148616657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46043534941876302099077771 69065302412814453148616657)
  ·
    refine ⟨51798976809610839861462493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69065302412814453148616657 51798976809610839861462493)
    ·
      refine ⟨19424616303604064948048435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51798976809610839861462493 19424616303604064948048435)
      ·
        refine ⟨29136924455406097422072653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19424616303604064948048435 29136924455406097422072653)
        ·
          refine ⟨10926346670777286533277245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29136924455406097422072653 10926346670777286533277245)
          ·
            refine ⟨4097380001541482449978967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10926346670777286533277245 4097380001541482449978967)
            ·
              refine ⟨6146070002312223674968451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097380001541482449978967 6146070002312223674968451)
              ·
                refine ⟨9219105003468335512452677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146070002312223674968451 9219105003468335512452677)
                ·
                  refine ⟨1728582188150312908584877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9219105003468335512452677 1728582188150312908584877)
                  ·
                    refine ⟨648218320556367340719329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1728582188150312908584877 648218320556367340719329)
                    ·
                      rfl

theorem cell22_1893601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_1893601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893601 prefixEnd_1893601 := by exact prefixLift 1893601
  have htrace : WordTrace (prefixWord ++ tailWord_1893601) baseStart_1893601 baseEnd_1893601 := by
    simpa [prefixWord, tailWord_1893601, baseEnd_1893601] using wordTrace_append hprefix tailTrace_1893601
  have hstable : (prefixWord ++ tailWord_1893601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893601).length < 2 ^ (prefixWord ++ tailWord_1893601).sum := by decide
  have hdescent : baseEnd_1893601 < baseStart_1893601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893618 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_1893618 : Nat := 118140960795 + 1893618 * 2 ^ 59
def prefixEnd_1893618 : Nat := 4983230072969 + 3 ^ 40 * 1893618 * 2
def baseEnd_1893618 : Nat := 648224140003784963044277

theorem tailTrace_1893618 : CollatzResearch.WordTrace tailWord_1893618 prefixEnd_1893618 648224140003784963044277 := by
  unfold tailWord_1893618
  simp only [CollatzResearch.WordTrace]
  refine ⟨17266480613438216262996377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46043948302501910034657005 17266480613438216262996377)
  ·
    refine ⟨12949860460078662197247283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17266480613438216262996377 12949860460078662197247283)
    ·
      refine ⟨19424790690117993295870925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12949860460078662197247283 19424790690117993295870925)
      ·
        refine ⟨7284296508794247485951597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19424790690117993295870925 7284296508794247485951597)
        ·
          refine ⟨2731611190797842807231849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7284296508794247485951597 2731611190797842807231849)
          ·
            refine ⟨2048708393098382105423887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731611190797842807231849 2048708393098382105423887)
            ·
              refine ⟨3073062589647573158135831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048708393098382105423887 3073062589647573158135831)
              ·
                refine ⟨4609593884471359737203747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073062589647573158135831 4609593884471359737203747)
                ·
                  refine ⟨6914390826707039605805621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609593884471359737203747 6914390826707039605805621)
                  ·
                    refine ⟨648224140003784963044277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6914390826707039605805621 648224140003784963044277)
                    ·
                      rfl

theorem cell22_1893618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_1893618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893618 prefixEnd_1893618 := by exact prefixLift 1893618
  have htrace : WordTrace (prefixWord ++ tailWord_1893618) baseStart_1893618 baseEnd_1893618 := by
    simpa [prefixWord, tailWord_1893618, baseEnd_1893618] using wordTrace_append hprefix tailTrace_1893618
  have hstable : (prefixWord ++ tailWord_1893618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893618).length < 2 ^ (prefixWord ++ tailWord_1893618).sum := by decide
  have hdescent : baseEnd_1893618 < baseStart_1893618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893631 : List Nat := [1, 1, 2, 2, 1, 7, 2, 6]
def baseStart_1893631 : Nat := 118140960795 + 1893631 * 2 ^ 59
def prefixEnd_1893631 : Nat := 4983230072969 + 3 ^ 40 * 1893631 * 2
def baseEnd_1893631 : Nat := 72025398907717473607693

theorem tailTrace_1893631 : CollatzResearch.WordTrace tailWord_1893631 prefixEnd_1893631 72025398907717473607693 := by
  unfold tailWord_1893631
  simp only [CollatzResearch.WordTrace]
  refine ⟨69066396602705768272208747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46044264401803845514805831 69066396602705768272208747)
  ·
    refine ⟨103599594904058652408313121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69066396602705768272208747 103599594904058652408313121)
    ·
      refine ⟨77699696178043989306234841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103599594904058652408313121 77699696178043989306234841)
      ·
        refine ⟨58274772133532991979676131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77699696178043989306234841 58274772133532991979676131)
        ·
          refine ⟨87412158200299487969514197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58274772133532991979676131 87412158200299487969514197)
          ·
            refine ⟨2048722457819519249285489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 87412158200299487969514197 2048722457819519249285489)
            ·
              refine ⟨1536541843364639436964117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048722457819519249285489 1536541843364639436964117)
              ·
                refine ⟨72025398907717473607693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1536541843364639436964117 72025398907717473607693)
                ·
                  rfl

theorem cell22_1893631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 6].length) (baseStart_1893631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893631 prefixEnd_1893631 := by exact prefixLift 1893631
  have htrace : WordTrace (prefixWord ++ tailWord_1893631) baseStart_1893631 baseEnd_1893631 := by
    simpa [prefixWord, tailWord_1893631, baseEnd_1893631] using wordTrace_append hprefix tailTrace_1893631
  have hstable : (prefixWord ++ tailWord_1893631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893631).length < 2 ^ (prefixWord ++ tailWord_1893631).sum := by decide
  have hdescent : baseEnd_1893631 < baseStart_1893631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893650 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1893650 : Nat := 118140960795 + 1893650 * 2 ^ 59
def prefixEnd_1893650 : Nat := 4983230072969 + 3 ^ 40 * 1893650 * 2
def baseEnd_1893650 : Nat := 648235094257747546244179

theorem tailTrace_1893650 : CollatzResearch.WordTrace tailWord_1893650 prefixEnd_1893650 648235094257747546244179 := by
  unfold tailWord_1893650
  simp only [CollatzResearch.WordTrace]
  refine ⟨17266772397409233629287601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46044726393091289678100269 17266772397409233629287601)
  ·
    refine ⟨12950079298056925221965701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17266772397409233629287601 12950079298056925221965701)
    ·
      refine ⟨2428139868385673479118569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12950079298056925221965701 2428139868385673479118569)
      ·
        refine ⟨1821104901289255109338927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2428139868385673479118569 1821104901289255109338927)
        ·
          refine ⟨2731657351933882664008391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821104901289255109338927 2731657351933882664008391)
          ·
            refine ⟨4097486027900823996012587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731657351933882664008391 4097486027900823996012587)
            ·
              refine ⟨6146229041851235994018881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097486027900823996012587 6146229041851235994018881)
              ·
                refine ⟨4609671781388426995514161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6146229041851235994018881 4609671781388426995514161)
                ·
                  refine ⟨3457253836041320246635621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4609671781388426995514161 3457253836041320246635621)
                  ·
                    refine ⟨648235094257747546244179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3457253836041320246635621 648235094257747546244179)
                    ·
                      rfl

theorem cell22_1893650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1893650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893650 prefixEnd_1893650 := by exact prefixLift 1893650
  have htrace : WordTrace (prefixWord ++ tailWord_1893650) baseStart_1893650 baseEnd_1893650 := by
    simpa [prefixWord, tailWord_1893650, baseEnd_1893650] using wordTrace_append hprefix tailTrace_1893650
  have hstable : (prefixWord ++ tailWord_1893650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893650).length < 2 ^ (prefixWord ++ tailWord_1893650).sum := by decide
  have hdescent : baseEnd_1893650 < baseStart_1893650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893659 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 5]
def baseStart_1893659 : Nat := 118140960795 + 1893659 * 2 ^ 59
def prefixEnd_1893659 : Nat := 4983230072969 + 3 ^ 40 * 1893659 * 2
def baseEnd_1893659 : Nat := 216079391713891507589717

theorem tailTrace_1893659 : CollatzResearch.WordTrace tailWord_1893659 prefixEnd_1893659 216079391713891507589717 := by
  unfold tailWord_1893659
  simp only [CollatzResearch.WordTrace]
  refine ⟨69067417846604329054228031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46044945231069552702818687 69067417846604329054228031)
  ·
    refine ⟨103601126769906493581342047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69067417846604329054228031 103601126769906493581342047)
    ·
      refine ⟨155401690154859740372013071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103601126769906493581342047 155401690154859740372013071)
      ·
        refine ⟨233102535232289610558019607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155401690154859740372013071 233102535232289610558019607)
        ·
          refine ⟨349653802848434415837029411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233102535232289610558019607 349653802848434415837029411)
          ·
            refine ⟨524480704272651623755544117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349653802848434415837029411 524480704272651623755544117)
            ·
              refine ⟨49170066025561089727082261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 524480704272651623755544117 49170066025561089727082261)
              ·
                refine ⟨2304846844948176080956981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49170066025561089727082261 2304846844948176080956981)
                ·
                  refine ⟨216079391713891507589717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304846844948176080956981 216079391713891507589717)
                  ·
                    rfl

theorem cell22_1893659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 5].length) (baseStart_1893659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893659 prefixEnd_1893659 := by exact prefixLift 1893659
  have htrace : WordTrace (prefixWord ++ tailWord_1893659) baseStart_1893659 baseEnd_1893659 := by
    simpa [prefixWord, tailWord_1893659, baseEnd_1893659] using wordTrace_append hprefix tailTrace_1893659
  have hstable : (prefixWord ++ tailWord_1893659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893659).length < 2 ^ (prefixWord ++ tailWord_1893659).sum := by decide
  have hdescent : baseEnd_1893659 < baseStart_1893659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893706 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_1893706 : Nat := 118140960795 + 1893706 * 2 ^ 59
def prefixEnd_1893706 : Nat := 4983230072969 + 3 ^ 40 * 1893706 * 2
def baseEnd_1893706 : Nat := 648254264202182066844007

theorem tailTrace_1893706 : CollatzResearch.WordTrace tailWord_1893706 prefixEnd_1893706 648254264202182066844007 := by
  unfold tailWord_1893706
  simp only [CollatzResearch.WordTrace]
  refine ⟨17267283019358514020297243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46046088051622704054125981 17267283019358514020297243)
  ·
    refine ⟨25900924529037771030445865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17267283019358514020297243 25900924529037771030445865)
    ·
      refine ⟨19425693396778328272834399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25900924529037771030445865 19425693396778328272834399)
      ·
        refine ⟨29138540095167492409251599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19425693396778328272834399 29138540095167492409251599)
        ·
          refine ⟨43707810142751238613877399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29138540095167492409251599 43707810142751238613877399)
          ·
            refine ⟨65561715214126857920816099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43707810142751238613877399 65561715214126857920816099)
            ·
              refine ⟨98342572821190286881224149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65561715214126857920816099 98342572821190286881224149)
              ·
                refine ⟨2304904050496647348778691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98342572821190286881224149 2304904050496647348778691)
                ·
                  refine ⟨3457356075744971023168037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304904050496647348778691 3457356075744971023168037)
                  ·
                    refine ⟨648254264202182066844007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3457356075744971023168037 648254264202182066844007)
                    ·
                      rfl

theorem cell22_1893706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_1893706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893706 prefixEnd_1893706 := by exact prefixLift 1893706
  have htrace : WordTrace (prefixWord ++ tailWord_1893706) baseStart_1893706 baseEnd_1893706 := by
    simpa [prefixWord, tailWord_1893706, baseEnd_1893706] using wordTrace_append hprefix tailTrace_1893706
  have hstable : (prefixWord ++ tailWord_1893706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893706).length < 2 ^ (prefixWord ++ tailWord_1893706).sum := by decide
  have hdescent : baseEnd_1893706 < baseStart_1893706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893738 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_1893738 : Nat := 118140960795 + 1893738 * 2 ^ 59
def prefixEnd_1893738 : Nat := 4983230072969 + 3 ^ 40 * 1893738 * 2
def baseEnd_1893738 : Nat := 216088406152048216681303

theorem tailTrace_1893738 : CollatzResearch.WordTrace tailWord_1893738 prefixEnd_1893738 216088406152048216681303 := by
  unfold tailWord_1893738
  simp only [CollatzResearch.WordTrace]
  refine ⟨17267574803329531386588467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46046866142212083697569245 17267574803329531386588467)
  ·
    refine ⟨25901362204994297079882701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17267574803329531386588467 25901362204994297079882701)
    ·
      refine ⟨9713010826872861404956013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25901362204994297079882701 9713010826872861404956013)
      ·
        refine ⟨3642379060077323026858505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9713010826872861404956013 3642379060077323026858505)
        ·
          refine ⟨2731784295057992270143879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3642379060077323026858505 2731784295057992270143879)
          ·
            refine ⟨4097676442586988405215819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731784295057992270143879 4097676442586988405215819)
            ·
              refine ⟨6146514663880482607823729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097676442586988405215819 6146514663880482607823729)
              ·
                refine ⟨4609885997910361955867797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6146514663880482607823729 4609885997910361955867797)
                ·
                  refine ⟨216088406152048216681303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4609885997910361955867797 216088406152048216681303)
                  ·
                    rfl

theorem cell22_1893738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_1893738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893738 prefixEnd_1893738 := by exact prefixLift 1893738
  have htrace : WordTrace (prefixWord ++ tailWord_1893738) baseStart_1893738 baseEnd_1893738 := by
    simpa [prefixWord, tailWord_1893738, baseEnd_1893738] using wordTrace_append hprefix tailTrace_1893738
  have hstable : (prefixWord ++ tailWord_1893738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893738).length < 2 ^ (prefixWord ++ tailWord_1893738).sum := by decide
  have hdescent : baseEnd_1893738 < baseStart_1893738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893828 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 7]
def baseStart_1893828 : Nat := 118140960795 + 1893828 * 2 ^ 59
def prefixEnd_1893828 : Nat := 4983230072969 + 3 ^ 40 * 1893828 * 2
def baseEnd_1893828 : Nat := 216098675765138138431211

theorem tailTrace_1893828 : CollatzResearch.WordTrace tailWord_1893828 prefixEnd_1893828 216098675765138138431211 := by
  unfold tailWord_1893828
  simp only [CollatzResearch.WordTrace]
  refine ⟨34536790891496035458565069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46049054521994713944753425 34536790891496035458565069)
  ·
    refine ⟨12951296584311013296961901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34536790891496035458565069 12951296584311013296961901)
    ·
      refine ⟨4856736219116629986360713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12951296584311013296961901 4856736219116629986360713)
      ·
        refine ⟨3642552164337472489770535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4856736219116629986360713 3642552164337472489770535)
        ·
          refine ⟨5463828246506208734655803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642552164337472489770535 5463828246506208734655803)
          ·
            refine ⟨8195742369759313101983705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463828246506208734655803 8195742369759313101983705)
            ·
              refine ⟨6146806777319484826487779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8195742369759313101983705 6146806777319484826487779)
              ·
                refine ⟨9220210165979227239731669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146806777319484826487779 9220210165979227239731669)
                ·
                  refine ⟨216098675765138138431211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9220210165979227239731669 216098675765138138431211)
                  ·
                    rfl

theorem cell22_1893828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_1893828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893828 prefixEnd_1893828 := by exact prefixLift 1893828
  have htrace : WordTrace (prefixWord ++ tailWord_1893828) baseStart_1893828 baseEnd_1893828 := by
    simpa [prefixWord, tailWord_1893828, baseEnd_1893828] using wordTrace_append hprefix tailTrace_1893828
  have hstable : (prefixWord ++ tailWord_1893828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893828).length < 2 ^ (prefixWord ++ tailWord_1893828).sum := by decide
  have hdescent : baseEnd_1893828 < baseStart_1893828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893832 : List Nat := [2, 1, 3, 1, 3, 1, 5, 2, 1, 3]
def baseStart_1893832 : Nat := 118140960795 + 1893832 * 2 ^ 59
def prefixEnd_1893832 : Nat := 4983230072969 + 3 ^ 40 * 1893832 * 2
def baseEnd_1893832 : Nat := 648297396577159738193621

theorem tailTrace_1893832 : CollatzResearch.WordTrace tailWord_1893832 prefixEnd_1893832 648297396577159738193621 := by
  unfold tailWord_1893832
  simp only [CollatzResearch.WordTrace]
  refine ⟨34536863837488789800137875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46049151783318386400183833 34536863837488789800137875)
  ·
    refine ⟨51805295756233184700206813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34536863837488789800137875 51805295756233184700206813)
    ·
      refine ⟨19426985908587444262577555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51805295756233184700206813 19426985908587444262577555)
      ·
        refine ⟨29140478862881166393866333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19426985908587444262577555 29140478862881166393866333)
        ·
          refine ⟨10927679573580437397699875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29140478862881166393866333 10927679573580437397699875)
          ·
            refine ⟨16391519360370656096549813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10927679573580437397699875 16391519360370656096549813)
            ·
              refine ⟨1536704940034749009051545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16391519360370656096549813 1536704940034749009051545)
              ·
                refine ⟨1152528705026061756788659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1536704940034749009051545 1152528705026061756788659)
                ·
                  refine ⟨1728793057539092635182989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152528705026061756788659 1728793057539092635182989)
                  ·
                    refine ⟨648297396577159738193621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1728793057539092635182989 648297396577159738193621)
                    ·
                      rfl

theorem cell22_1893832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_1893832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893832 prefixEnd_1893832 := by exact prefixLift 1893832
  have htrace : WordTrace (prefixWord ++ tailWord_1893832) baseStart_1893832 baseEnd_1893832 := by
    simpa [prefixWord, tailWord_1893832, baseEnd_1893832] using wordTrace_append hprefix tailTrace_1893832
  have hstable : (prefixWord ++ tailWord_1893832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893832).length < 2 ^ (prefixWord ++ tailWord_1893832).sum := by decide
  have hdescent : baseEnd_1893832 < baseStart_1893832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893871 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 3, 5]
def baseStart_1893871 : Nat := 118140960795 + 1893871 * 2 ^ 59
def prefixEnd_1893871 : Nat := 4983230072969 + 3 ^ 40 * 1893871 * 2
def baseEnd_1893871 : Nat := 648310747074176636468501

theorem tailTrace_1893871 : CollatzResearch.WordTrace tailWord_1893871 prefixEnd_1893871 648310747074176636468501 := by
  unfold tailWord_1893871
  simp only [CollatzResearch.WordTrace]
  refine ⟨69075150121836289260945467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46050100081224192840630311 69075150121836289260945467)
  ·
    refine ⟨103612725182754433891418201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69075150121836289260945467 103612725182754433891418201)
    ·
      refine ⟨77709543887065825418563651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103612725182754433891418201 77709543887065825418563651)
      ·
        refine ⟨116564315830598738127845477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77709543887065825418563651 116564315830598738127845477)
        ·
          refine ⟨21855809218237263398971027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116564315830598738127845477 21855809218237263398971027)
          ·
            refine ⟨32783713827355895098456541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21855809218237263398971027 32783713827355895098456541)
            ·
              refine ⟨12293892685258460661921203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32783713827355895098456541 12293892685258460661921203)
              ·
                refine ⟨18440839027887690992881805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12293892685258460661921203 18440839027887690992881805)
                ·
                  refine ⟨6915314635457884122330677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18440839027887690992881805 6915314635457884122330677)
                  ·
                    refine ⟨648310747074176636468501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6915314635457884122330677 648310747074176636468501)
                    ·
                      rfl

theorem cell22_1893871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_1893871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893871 prefixEnd_1893871 := by exact prefixLift 1893871
  have htrace : WordTrace (prefixWord ++ tailWord_1893871) baseStart_1893871 baseEnd_1893871 := by
    simpa [prefixWord, tailWord_1893871, baseEnd_1893871] using wordTrace_append hprefix tailTrace_1893871
  have hstable : (prefixWord ++ tailWord_1893871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893871).length < 2 ^ (prefixWord ++ tailWord_1893871).sum := by decide
  have hdescent : baseEnd_1893871 < baseStart_1893871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893894 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1893894 : Nat := 118140960795 + 1893894 * 2 ^ 59
def prefixEnd_1893894 : Nat := 4983230072969 + 3 ^ 40 * 1893894 * 2
def baseEnd_1893894 : Nat := 648318620444212243143431

theorem tailTrace_1893894 : CollatzResearch.WordTrace tailWord_1893894 prefixEnd_1893894 648318620444212243143431 := by
  unfold tailWord_1893894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158624656273530130907273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46050659333835309459355157 2158624656273530130907273)
  ·
    refine ⟨1618968492205147598180455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2158624656273530130907273 1618968492205147598180455)
    ·
      refine ⟨2428452738307721397270683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618968492205147598180455 2428452738307721397270683)
      ·
        refine ⟨3642679107461582095906025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428452738307721397270683 3642679107461582095906025)
        ·
          refine ⟨2732009330596186571929519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3642679107461582095906025 2732009330596186571929519)
          ·
            refine ⟨4098013995894279857894279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732009330596186571929519 4098013995894279857894279)
            ·
              refine ⟨6147020993841419786841419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098013995894279857894279 6147020993841419786841419)
              ·
                refine ⟨9220531490762129680262129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6147020993841419786841419 9220531490762129680262129)
                ·
                  refine ⟨6915398618071597260196597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9220531490762129680262129 6915398618071597260196597)
                  ·
                    refine ⟨648318620444212243143431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6915398618071597260196597 648318620444212243143431)
                    ·
                      rfl

theorem cell22_1893894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1893894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893894 prefixEnd_1893894 := by exact prefixLift 1893894
  have htrace : WordTrace (prefixWord ++ tailWord_1893894) baseStart_1893894 baseEnd_1893894 := by
    simpa [prefixWord, tailWord_1893894, baseEnd_1893894] using wordTrace_append hprefix tailTrace_1893894
  have hstable : (prefixWord ++ tailWord_1893894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893894).length < 2 ^ (prefixWord ++ tailWord_1893894).sum := by decide
  have hdescent : baseEnd_1893894 < baseStart_1893894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893920 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_1893920 : Nat := 118140960795 + 1893920 * 2 ^ 59
def prefixEnd_1893920 : Nat := 4983230072969 + 3 ^ 40 * 1893920 * 2
def baseEnd_1893920 : Nat := 648327520775556841993351

theorem tailTrace_1893920 : CollatzResearch.WordTrace tailWord_1893920 prefixEnd_1893920 648327520775556841993351 := by
  unfold tailWord_1893920
  simp only [CollatzResearch.WordTrace]
  refine ⟨34538468649329385314739607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46051291532439180419652809 34538468649329385314739607)
  ·
    refine ⟨51807702973994077972109411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34538468649329385314739607 51807702973994077972109411)
    ·
      refine ⟨77711554460991116958164117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51807702973994077972109411 77711554460991116958164117)
      ·
        refine ⟨3642729115358958607413943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77711554460991116958164117 3642729115358958607413943)
        ·
          refine ⟨5464093673038437911120915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642729115358958607413943 5464093673038437911120915)
          ·
            refine ⟨8196140509557656866681373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464093673038437911120915 8196140509557656866681373)
            ·
              refine ⟨3073552691084121325005515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8196140509557656866681373 3073552691084121325005515)
              ·
                refine ⟨4610329036626181987508273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073552691084121325005515 4610329036626181987508273)
                ·
                  refine ⟨3457746777469636490631205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4610329036626181987508273 3457746777469636490631205)
                  ·
                    refine ⟨648327520775556841993351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3457746777469636490631205 648327520775556841993351)
                    ·
                      rfl

theorem cell22_1893920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_1893920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1893920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1893920 prefixEnd_1893920 := by exact prefixLift 1893920
  have htrace : WordTrace (prefixWord ++ tailWord_1893920) baseStart_1893920 baseEnd_1893920 := by
    simpa [prefixWord, tailWord_1893920, baseEnd_1893920] using wordTrace_append hprefix tailTrace_1893920
  have hstable : (prefixWord ++ tailWord_1893920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893920).length < 2 ^ (prefixWord ++ tailWord_1893920).sum := by decide
  have hdescent : baseEnd_1893920 < baseStart_1893920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894040 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_1894040 : Nat := 118140960795 + 1894040 * 2 ^ 59
def prefixEnd_1894040 : Nat := 4983230072969 + 3 ^ 40 * 1894040 * 2
def baseEnd_1894040 : Nat := 648368599227916528992983

theorem tailTrace_1894040 : CollatzResearch.WordTrace tailWord_1894040 prefixEnd_1894040 648368599227916528992983 := by
  unfold tailWord_1894040
  simp only [CollatzResearch.WordTrace]
  refine ⟨34540657029112015561923787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46054209372149354082565049 34540657029112015561923787)
  ·
    refine ⟨51810985543668023342885681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34540657029112015561923787 51810985543668023342885681)
    ·
      refine ⟨38858239157751017507164261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51810985543668023342885681 38858239157751017507164261)
      ·
        refine ⟨7285919842078315782593299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38858239157751017507164261 7285919842078315782593299)
        ·
          refine ⟨10928879763117473673889949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285919842078315782593299 10928879763117473673889949)
          ·
            refine ⟨4098329911169052627708731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10928879763117473673889949 4098329911169052627708731)
            ·
              refine ⟨6147494866753578941563097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098329911169052627708731 6147494866753578941563097)
              ·
                refine ⟨4610621150065184206172323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6147494866753578941563097 4610621150065184206172323)
                ·
                  refine ⟨6915931725097776309258485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610621150065184206172323 6915931725097776309258485)
                  ·
                    refine ⟨648368599227916528992983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6915931725097776309258485 648368599227916528992983)
                    ·
                      rfl

theorem cell22_1894040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_1894040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894040 prefixEnd_1894040 := by exact prefixLift 1894040
  have htrace : WordTrace (prefixWord ++ tailWord_1894040) baseStart_1894040 baseEnd_1894040 := by
    simpa [prefixWord, tailWord_1894040, baseEnd_1894040] using wordTrace_append hprefix tailTrace_1894040
  have hstable : (prefixWord ++ tailWord_1894040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894040).length < 2 ^ (prefixWord ++ tailWord_1894040).sum := by decide
  have hdescent : baseEnd_1894040 < baseStart_1894040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894044 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 1, 4]
def baseStart_1894044 : Nat := 118140960795 + 1894044 * 2 ^ 59
def prefixEnd_1894044 : Nat := 4983230072969 + 3 ^ 40 * 1894044 * 2
def baseEnd_1894044 : Nat := 648369968509661851892971

theorem tailTrace_1894044 : CollatzResearch.WordTrace tailWord_1894044 prefixEnd_1894044 648369968509661851892971 := by
  unfold tailWord_1894044
  simp only [CollatzResearch.WordTrace]
  refine ⟨34540729975104769903496593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46054306633473026537995457 34540729975104769903496593)
  ·
    refine ⟨25905547481328577427622445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34540729975104769903496593 25905547481328577427622445)
    ·
      refine ⟨9714580305498216535358417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25905547481328577427622445 9714580305498216535358417)
      ·
        refine ⟨7285935229123662401518813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9714580305498216535358417 7285935229123662401518813)
        ·
          refine ⟨2732225710921373400569555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7285935229123662401518813 2732225710921373400569555)
          ·
            refine ⟨4098338566382060100854333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732225710921373400569555 4098338566382060100854333)
            ·
              refine ⟨1536876962393272537820375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4098338566382060100854333 1536876962393272537820375)
              ·
                refine ⟨2305315443589908806730563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536876962393272537820375 2305315443589908806730563)
                ·
                  refine ⟨3457973165384863210095845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305315443589908806730563 3457973165384863210095845)
                  ·
                    refine ⟨648369968509661851892971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3457973165384863210095845 648369968509661851892971)
                    ·
                      rfl

theorem cell22_1894044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_1894044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894044 prefixEnd_1894044 := by exact prefixLift 1894044
  have htrace : WordTrace (prefixWord ++ tailWord_1894044) baseStart_1894044 baseEnd_1894044 := by
    simpa [prefixWord, tailWord_1894044, baseEnd_1894044] using wordTrace_append hprefix tailTrace_1894044
  have hstable : (prefixWord ++ tailWord_1894044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894044).length < 2 ^ (prefixWord ++ tailWord_1894044).sum := by decide
  have hdescent : baseEnd_1894044 < baseStart_1894044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894085 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_1894085 : Nat := 118140960795 + 1894085 * 2 ^ 59
def prefixEnd_1894085 : Nat := 4983230072969 + 3 ^ 40 * 1894085 * 2
def baseEnd_1894085 : Nat := 648384003647551411617845

theorem tailTrace_1894085 : CollatzResearch.WordTrace tailWord_1894085 prefixEnd_1894085 648384003647551411617845 := by
  unfold tailWord_1894085
  simp only [CollatzResearch.WordTrace]
  refine ⟨69082955343061003809235709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46055303562040669206157139 69082955343061003809235709)
  ·
    refine ⟨25906108253647876428463391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69082955343061003809235709 25906108253647876428463391)
    ·
      refine ⟨38859162380471814642695087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25906108253647876428463391 38859162380471814642695087)
      ·
        refine ⟨58288743570707721964042631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38859162380471814642695087 58288743570707721964042631)
        ·
          refine ⟨87433115356061582946063947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58288743570707721964042631 87433115356061582946063947)
          ·
            refine ⟨131149673034092374419095921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87433115356061582946063947 131149673034092374419095921)
            ·
              refine ⟨98362254775569280814321941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131149673034092374419095921 98362254775569280814321941)
              ·
                refine ⟨4610730692604810038171341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98362254775569280814321941 4610730692604810038171341)
                ·
                  refine ⟨1729024009726803764314253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4610730692604810038171341 1729024009726803764314253)
                  ·
                    refine ⟨648384003647551411617845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1729024009726803764314253 648384003647551411617845)
                    ·
                      rfl

theorem cell22_1894085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_1894085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894085 prefixEnd_1894085 := by exact prefixLift 1894085
  have htrace : WordTrace (prefixWord ++ tailWord_1894085) baseStart_1894085 baseEnd_1894085 := by
    simpa [prefixWord, tailWord_1894085, baseEnd_1894085] using wordTrace_append hprefix tailTrace_1894085
  have hstable : (prefixWord ++ tailWord_1894085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894085).length < 2 ^ (prefixWord ++ tailWord_1894085).sum := by decide
  have hdescent : baseEnd_1894085 < baseStart_1894085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894108 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1894108 : Nat := 118140960795 + 1894108 * 2 ^ 59
def prefixEnd_1894108 : Nat := 4983230072969 + 3 ^ 40 * 1894108 * 2
def baseEnd_1894108 : Nat := 648391877017587018292775

theorem tailTrace_1894108 : CollatzResearch.WordTrace tailWord_1894108 prefixEnd_1894108 648391877017587018292775 := by
  unfold tailWord_1894108
  simp only [CollatzResearch.WordTrace]
  refine ⟨34541897110988839368661489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46055862814651785824881985 34541897110988839368661489)
  ·
    refine ⟨25906422833241629526496117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34541897110988839368661489 25906422833241629526496117)
    ·
      refine ⟨2428727140616402768109011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25906422833241629526496117 2428727140616402768109011)
      ·
        refine ⟨3643090710924604152163517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428727140616402768109011 3643090710924604152163517)
        ·
          refine ⟨1366159016596726557061319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3643090710924604152163517 1366159016596726557061319)
          ·
            refine ⟨2049238524895089835591979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366159016596726557061319 2049238524895089835591979)
            ·
              refine ⟨3073857787342634753387969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049238524895089835591979 3073857787342634753387969)
              ·
                refine ⟨2305393340506976065040977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3073857787342634753387969 2305393340506976065040977)
                ·
                  refine ⟨1729045005380232048780733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2305393340506976065040977 1729045005380232048780733)
                  ·
                    refine ⟨648391877017587018292775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1729045005380232048780733 648391877017587018292775)
                    ·
                      rfl

theorem cell22_1894108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1894108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894108 prefixEnd_1894108 := by exact prefixLift 1894108
  have htrace : WordTrace (prefixWord ++ tailWord_1894108) baseStart_1894108 baseEnd_1894108 := by
    simpa [prefixWord, tailWord_1894108, baseEnd_1894108] using wordTrace_append hprefix tailTrace_1894108
  have hstable : (prefixWord ++ tailWord_1894108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894108).length < 2 ^ (prefixWord ++ tailWord_1894108).sum := by decide
  have hdescent : baseEnd_1894108 < baseStart_1894108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894128 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_1894128 : Nat := 118140960795 + 1894128 * 2 ^ 59
def prefixEnd_1894128 : Nat := 4983230072969 + 3 ^ 40 * 1894128 * 2
def baseEnd_1894128 : Nat := 648398723426313632792713

theorem tailTrace_1894128 : CollatzResearch.WordTrace tailWord_1894128 prefixEnd_1894128 648398723426313632792713 := by
  unfold tailWord_1894128
  simp only [CollatzResearch.WordTrace]
  refine ⟨34542261840952611076525519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46056349121270148102034025 34542261840952611076525519)
  ·
    refine ⟨51813392761428916614788279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34542261840952611076525519 51813392761428916614788279)
    ·
      refine ⟨77720089142143374922182419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51813392761428916614788279 77720089142143374922182419)
      ·
        refine ⟨116580133713215062383273629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77720089142143374922182419 116580133713215062383273629)
        ·
          refine ⟨43717550142455648393727611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116580133713215062383273629 43717550142455648393727611)
          ·
            refine ⟨65576325213683472590591417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43717550142455648393727611 65576325213683472590591417)
            ·
              refine ⟨49182243910262604442943563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65576325213683472590591417 49182243910262604442943563)
              ·
                refine ⟨73773365865393906664415345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49182243910262604442943563 73773365865393906664415345)
                ·
                  refine ⟨55330024399045429998311509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73773365865393906664415345 55330024399045429998311509)
                  ·
                    refine ⟨648398723426313632792713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55330024399045429998311509 648398723426313632792713)
                    ·
                      rfl

theorem cell22_1894128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_1894128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894128 prefixEnd_1894128 := by exact prefixLift 1894128
  have htrace : WordTrace (prefixWord ++ tailWord_1894128) baseStart_1894128 baseEnd_1894128 := by
    simpa [prefixWord, tailWord_1894128, baseEnd_1894128] using wordTrace_append hprefix tailTrace_1894128
  have hstable : (prefixWord ++ tailWord_1894128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894128).length < 2 ^ (prefixWord ++ tailWord_1894128).sum := by decide
  have hdescent : baseEnd_1894128 < baseStart_1894128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894130 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1894130 : Nat := 118140960795 + 1894130 * 2 ^ 59
def prefixEnd_1894130 : Nat := 4983230072969 + 3 ^ 40 * 1894130 * 2
def baseEnd_1894130 : Nat := 648399408067186294242707

theorem tailTrace_1894130 : CollatzResearch.WordTrace tailWord_1894130 prefixEnd_1894130 648399408067186294242707 := by
  unfold tailWord_1894130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17271149156974494123655961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46056397751931984329749229 17271149156974494123655961)
  ·
    refine ⟨12953361867730870592741971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17271149156974494123655961 12953361867730870592741971)
    ·
      refine ⟨19430042801596305889112957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12953361867730870592741971 19430042801596305889112957)
      ·
        refine ⟨7286266050598614708417359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19430042801596305889112957 7286266050598614708417359)
        ·
          refine ⟨10929399075897922062626039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7286266050598614708417359 10929399075897922062626039)
          ·
            refine ⟨16394098613846883093939059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929399075897922062626039 16394098613846883093939059)
            ·
              refine ⟨24591147920770324640908589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16394098613846883093939059 24591147920770324640908589)
              ·
                refine ⟨9221680470288871740340721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24591147920770324640908589 9221680470288871740340721)
                ·
                  refine ⟨6916260352716653805255541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9221680470288871740340721 6916260352716653805255541)
                  ·
                    refine ⟨648399408067186294242707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6916260352716653805255541 648399408067186294242707)
                    ·
                      rfl

theorem cell22_1894130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1894130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894130 prefixEnd_1894130 := by exact prefixLift 1894130
  have htrace : WordTrace (prefixWord ++ tailWord_1894130) baseStart_1894130 baseEnd_1894130 := by
    simpa [prefixWord, tailWord_1894130, baseEnd_1894130] using wordTrace_append hprefix tailTrace_1894130
  have hstable : (prefixWord ++ tailWord_1894130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894130).length < 2 ^ (prefixWord ++ tailWord_1894130).sum := by decide
  have hdescent : baseEnd_1894130 < baseStart_1894130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894145 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1894145 : Nat := 118140960795 + 1894145 * 2 ^ 59
def prefixEnd_1894145 : Nat := 4983230072969 + 3 ^ 40 * 1894145 * 2
def baseEnd_1894145 : Nat := 648404542873731255117661

theorem tailTrace_1894145 : CollatzResearch.WordTrace tailWord_1894145 prefixEnd_1894145 648404542873731255117661 := by
  unfold tailWord_1894145
  simp only [CollatzResearch.WordTrace]
  refine ⟨69085143722843634056419889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46056762481895756037613259 69085143722843634056419889)
  ·
    refine ⟨51813857792132725542314917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69085143722843634056419889 51813857792132725542314917)
    ·
      refine ⟨9715098336024886039184047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51813857792132725542314917 9715098336024886039184047)
      ·
        refine ⟨14572647504037329058776071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9715098336024886039184047 14572647504037329058776071)
        ·
          refine ⟨21858971256055993588164107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14572647504037329058776071 21858971256055993588164107)
          ·
            refine ⟨32788456884083990382246161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21858971256055993588164107 32788456884083990382246161)
            ·
              refine ⟨24591342663062992786684621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32788456884083990382246161 24591342663062992786684621)
              ·
                refine ⟨9221753498648622295006733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24591342663062992786684621 9221753498648622295006733)
                ·
                  refine ⟨3458157561993233360627525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9221753498648622295006733 3458157561993233360627525)
                  ·
                    refine ⟨648404542873731255117661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3458157561993233360627525 648404542873731255117661)
                    ·
                      rfl

theorem cell22_1894145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1894145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894145 prefixEnd_1894145 := by exact prefixLift 1894145
  have htrace : WordTrace (prefixWord ++ tailWord_1894145) baseStart_1894145 baseEnd_1894145 := by
    simpa [prefixWord, tailWord_1894145, baseEnd_1894145] using wordTrace_append hprefix tailTrace_1894145
  have hstable : (prefixWord ++ tailWord_1894145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894145).length < 2 ^ (prefixWord ++ tailWord_1894145).sum := by decide
  have hdescent : baseEnd_1894145 < baseStart_1894145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894177 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 6]
def baseStart_1894177 : Nat := 118140960795 + 1894177 * 2 ^ 59
def prefixEnd_1894177 : Nat := 4983230072969 + 3 ^ 40 * 1894177 * 2
def baseEnd_1894177 : Nat := 216138499042564612772521

theorem tailTrace_1894177 : CollatzResearch.WordTrace tailWord_1894177 prefixEnd_1894177 216138499042564612772521 := by
  unfold tailWord_1894177
  simp only [CollatzResearch.WordTrace]
  refine ⟨69086310858727703521584785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46057540572485135681056523 69086310858727703521584785)
  ·
    refine ⟨51814733144045777641188589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69086310858727703521584785 51814733144045777641188589)
    ·
      refine ⟨19430524929017166615445721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51814733144045777641188589 19430524929017166615445721)
      ·
        refine ⟨14572893696762874961584291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19430524929017166615445721 14572893696762874961584291)
        ·
          refine ⟨21859340545144312442376437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14572893696762874961584291 21859340545144312442376437)
          ·
            refine ⟨2049313176107279291472791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21859340545144312442376437 2049313176107279291472791)
            ·
              refine ⟨3073969764160918937209187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049313176107279291472791 3073969764160918937209187)
              ·
                refine ⟨4610954646241378405813781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073969764160918937209187 4610954646241378405813781)
                ·
                  refine ⟨216138499042564612772521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4610954646241378405813781 216138499042564612772521)
                  ·
                    rfl

theorem cell22_1894177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_1894177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894177 prefixEnd_1894177 := by exact prefixLift 1894177
  have htrace : WordTrace (prefixWord ++ tailWord_1894177) baseStart_1894177 baseEnd_1894177 := by
    simpa [prefixWord, tailWord_1894177, baseEnd_1894177] using wordTrace_append hprefix tailTrace_1894177
  have hstable : (prefixWord ++ tailWord_1894177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894177).length < 2 ^ (prefixWord ++ tailWord_1894177).sum := by decide
  have hdescent : baseEnd_1894177 < baseStart_1894177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894196 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1894196 : Nat := 118140960795 + 1894196 * 2 ^ 59
def prefixEnd_1894196 : Nat := 4983230072969 + 3 ^ 40 * 1894196 * 2
def baseEnd_1894196 : Nat := 648422001215984122092505

theorem tailTrace_1894196 : CollatzResearch.WordTrace tailWord_1894196 prefixEnd_1894196 648422001215984122092505 := by
  unfold tailWord_1894196
  simp only [CollatzResearch.WordTrace]
  refine ⟨34543501922829434883263221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46058002563772579844350961 34543501922829434883263221)
  ·
    refine ⟨3238453305265259520305927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34543501922829434883263221 3238453305265259520305927)
    ·
      refine ⟨4857679957897889280458891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238453305265259520305927 4857679957897889280458891)
      ·
        refine ⟨7286519936846833920688337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4857679957897889280458891 7286519936846833920688337)
        ·
          refine ⟨5464889952635125440516253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7286519936846833920688337 5464889952635125440516253)
          ·
            refine ⟨2049333732238172040193595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5464889952635125440516253 2049333732238172040193595)
            ·
              refine ⟨3074000598357258060290393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049333732238172040193595 3074000598357258060290393)
              ·
                refine ⟨2305500448767943545217795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074000598357258060290393 2305500448767943545217795)
                ·
                  refine ⟨3458250673151915317826693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305500448767943545217795 3458250673151915317826693)
                  ·
                    refine ⟨648422001215984122092505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3458250673151915317826693 648422001215984122092505)
                    ·
                      rfl

theorem cell22_1894196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1894196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894196 prefixEnd_1894196 := by exact prefixLift 1894196
  have htrace : WordTrace (prefixWord ++ tailWord_1894196) baseStart_1894196 baseEnd_1894196 := by
    simpa [prefixWord, tailWord_1894196, baseEnd_1894196] using wordTrace_append hprefix tailTrace_1894196
  have hstable : (prefixWord ++ tailWord_1894196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894196).length < 2 ^ (prefixWord ++ tailWord_1894196).sum := by decide
  have hdescent : baseEnd_1894196 < baseStart_1894196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894254 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_1894254 : Nat := 118140960795 + 1894254 * 2 ^ 59
def prefixEnd_1894254 : Nat := 4983230072969 + 3 ^ 40 * 1894254 * 2
def baseEnd_1894254 : Nat := 648441855801291304142327

theorem tailTrace_1894254 : CollatzResearch.WordTrace tailWord_1894254 prefixEnd_1894254 648441855801291304142327 := by
  unfold tailWord_1894254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8636139909931093209017227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46059412852965830448091877 8636139909931093209017227)
  ·
    refine ⟨12954209864896639813525841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8636139909931093209017227 12954209864896639813525841)
    ·
      refine ⟨9715657398672479860144381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12954209864896639813525841 9715657398672479860144381)
      ·
        refine ⟨3643371524502179947554143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9715657398672479860144381 3643371524502179947554143)
        ·
          refine ⟨5465057286753269921331215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643371524502179947554143 5465057286753269921331215)
          ·
            refine ⟨8197585930129904881996823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465057286753269921331215 8197585930129904881996823)
            ·
              refine ⟨12296378895194857322995235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197585930129904881996823 12296378895194857322995235)
              ·
                refine ⟨18444568342792285984492853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12296378895194857322995235 18444568342792285984492853)
                ·
                  refine ⟨1729178282136776811046205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18444568342792285984492853 1729178282136776811046205)
                  ·
                    refine ⟨648441855801291304142327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1729178282136776811046205 648441855801291304142327)
                    ·
                      rfl

theorem cell22_1894254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_1894254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894254 prefixEnd_1894254 := by exact prefixLift 1894254
  have htrace : WordTrace (prefixWord ++ tailWord_1894254) baseStart_1894254 baseEnd_1894254 := by
    simpa [prefixWord, tailWord_1894254, baseEnd_1894254] using wordTrace_append hprefix tailTrace_1894254
  have hstable : (prefixWord ++ tailWord_1894254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894254).length < 2 ^ (prefixWord ++ tailWord_1894254).sum := by decide
  have hdescent : baseEnd_1894254 < baseStart_1894254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894265 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_1894265 : Nat := 118140960795 + 1894265 * 2 ^ 59
def prefixEnd_1894265 : Nat := 4983230072969 + 3 ^ 40 * 1894265 * 2
def baseEnd_1894265 : Nat := 648445621326090942117293

theorem tailTrace_1894265 : CollatzResearch.WordTrace tailWord_1894265 prefixEnd_1894265 648445621326090942117293 := by
  unfold tailWord_1894265
  simp only [CollatzResearch.WordTrace]
  refine ⟨69089520482408894550788249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46059680321605929700525499 69089520482408894550788249)
  ·
    refine ⟨51817140361806670913091187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69089520482408894550788249 51817140361806670913091187)
    ·
      refine ⟨77725710542710006369636781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51817140361806670913091187 77725710542710006369636781)
      ·
        refine ⟨29147141453516252388613793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77725710542710006369636781 29147141453516252388613793)
        ·
          refine ⟨21860356090137189291460345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29147141453516252388613793 21860356090137189291460345)
          ·
            refine ⟨16395267067602891968595259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21860356090137189291460345 16395267067602891968595259)
            ·
              refine ⟨24592900601404337952892889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16395267067602891968595259 24592900601404337952892889)
              ·
                refine ⟨18444675451053253464669667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24592900601404337952892889 18444675451053253464669667)
                ·
                  refine ⟨27667013176579880197004501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18444675451053253464669667 27667013176579880197004501)
                  ·
                    refine ⟨648445621326090942117293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27667013176579880197004501 648445621326090942117293)
                    ·
                      rfl

theorem cell22_1894265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_1894265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894265 prefixEnd_1894265 := by exact prefixLift 1894265
  have htrace : WordTrace (prefixWord ++ tailWord_1894265) baseStart_1894265 baseEnd_1894265 := by
    simpa [prefixWord, tailWord_1894265, baseEnd_1894265] using wordTrace_append hprefix tailTrace_1894265
  have hstable : (prefixWord ++ tailWord_1894265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894265).length < 2 ^ (prefixWord ++ tailWord_1894265).sum := by decide
  have hdescent : baseEnd_1894265 < baseStart_1894265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894344 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 4, 3]
def baseStart_1894344 : Nat := 118140960795 + 1894344 * 2 ^ 59
def prefixEnd_1894344 : Nat := 4983230072969 + 3 ^ 40 * 1894344 * 2
def baseEnd_1894344 : Nat := 648472664640561069392051

theorem tailTrace_1894344 : CollatzResearch.WordTrace tailWord_1894344 prefixEnd_1894344 648472664640561069392051 := by
  unfold tailWord_1894344
  simp only [CollatzResearch.WordTrace]
  refine ⟨34546200924561345521457043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46061601232748460695276057 34546200924561345521457043)
  ·
    refine ⟨51819301386842018282185565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34546200924561345521457043 51819301386842018282185565)
    ·
      refine ⟨19432238020065756855819587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51819301386842018282185565 19432238020065756855819587)
      ·
        refine ⟨29148357030098635283729381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19432238020065756855819587 29148357030098635283729381)
        ·
          refine ⟨5465316943143494115699259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29148357030098635283729381 5465316943143494115699259)
          ·
            refine ⟨8197975414715241173548889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465316943143494115699259 8197975414715241173548889)
            ·
              refine ⟨6148481561036430880161667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8197975414715241173548889 6148481561036430880161667)
              ·
                refine ⟨9222722341554646320242501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148481561036430880161667 9222722341554646320242501)
                ·
                  refine ⟨1729260439041496185045469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9222722341554646320242501 1729260439041496185045469)
                  ·
                    refine ⟨648472664640561069392051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1729260439041496185045469 648472664640561069392051)
                    ·
                      rfl

theorem cell22_1894344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_1894344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894344 prefixEnd_1894344 := by exact prefixLift 1894344
  have htrace : WordTrace (prefixWord ++ tailWord_1894344) baseStart_1894344 baseEnd_1894344 := by
    simpa [prefixWord, tailWord_1894344, baseEnd_1894344] using wordTrace_append hprefix tailTrace_1894344
  have hstable : (prefixWord ++ tailWord_1894344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894344).length < 2 ^ (prefixWord ++ tailWord_1894344).sum := by decide
  have hdescent : baseEnd_1894344 < baseStart_1894344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894357 : List Nat := [1, 3, 2, 3, 2, 1, 1, 9]
def baseStart_1894357 : Nat := 118140960795 + 1894357 * 2 ^ 59
def prefixEnd_1894357 : Nat := 4983230072969 + 3 ^ 40 * 1894357 * 2
def baseEnd_1894357 : Nat := 72053012756248152090779

theorem tailTrace_1894357 : CollatzResearch.WordTrace tailWord_1894357 prefixEnd_1894357 72053012756248152090779 := by
  unfold tailWord_1894357
  simp only [CollatzResearch.WordTrace]
  refine ⟨69092875998075594263137325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46061917332050396175424883 69092875998075594263137325)
  ·
    refine ⟨25909828499278347848676497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69092875998075594263137325 25909828499278347848676497)
    ·
      refine ⟨19432371374458760886507373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25909828499278347848676497 19432371374458760886507373)
      ·
        refine ⟨7287139265422035332440265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19432371374458760886507373 7287139265422035332440265)
        ·
          refine ⟨5465354449066526499330199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7287139265422035332440265 5465354449066526499330199)
          ·
            refine ⟨8198031673599789748995299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465354449066526499330199 8198031673599789748995299)
            ·
              refine ⟨12297047510399684623492949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198031673599789748995299 12297047510399684623492949)
              ·
                refine ⟨72053012756248152090779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12297047510399684623492949 72053012756248152090779)
                ·
                  rfl

theorem cell22_1894357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 9].length) (baseStart_1894357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894357 prefixEnd_1894357 := by exact prefixLift 1894357
  have htrace : WordTrace (prefixWord ++ tailWord_1894357) baseStart_1894357 baseEnd_1894357 := by
    simpa [prefixWord, tailWord_1894357, baseEnd_1894357] using wordTrace_append hprefix tailTrace_1894357
  have hstable : (prefixWord ++ tailWord_1894357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894357).length < 2 ^ (prefixWord ++ tailWord_1894357).sum := by decide
  have hdescent : baseEnd_1894357 < baseStart_1894357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894361 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 2, 3]
def baseStart_1894361 : Nat := 118140960795 + 1894361 * 2 ^ 59
def prefixEnd_1894361 : Nat := 4983230072969 + 3 ^ 40 * 1894361 * 2
def baseEnd_1894361 : Nat := 648478484087978691716999

theorem tailTrace_1894361 : CollatzResearch.WordTrace tailWord_1894361 prefixEnd_1894361 648478484087978691716999 := by
  unfold tailWord_1894361
  simp only [CollatzResearch.WordTrace]
  refine ⟨69093021890061102946282937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46062014593374068630855291 69093021890061102946282937)
  ·
    refine ⟨51819766417545827209712203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69093021890061102946282937 51819766417545827209712203)
    ·
      refine ⟨77729649626318740814568305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51819766417545827209712203 77729649626318740814568305)
      ·
        refine ⟨58297237219739055610926229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77729649626318740814568305 58297237219739055610926229)
        ·
          refine ⟨2732682994675268231762167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58297237219739055610926229 2732682994675268231762167)
          ·
            refine ⟨4099024492012902347643251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732682994675268231762167 4099024492012902347643251)
            ·
              refine ⟨6148536738019353521464877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099024492012902347643251 6148536738019353521464877)
              ·
                refine ⟨2305701276757257570549329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6148536738019353521464877 2305701276757257570549329)
                ·
                  refine ⟨1729275957567943177911997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2305701276757257570549329 1729275957567943177911997)
                  ·
                    refine ⟨648478484087978691716999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1729275957567943177911997 648478484087978691716999)
                    ·
                      rfl

theorem cell22_1894361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_1894361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894361 prefixEnd_1894361 := by exact prefixLift 1894361
  have htrace : WordTrace (prefixWord ++ tailWord_1894361) baseStart_1894361 baseEnd_1894361 := by
    simpa [prefixWord, tailWord_1894361, baseEnd_1894361] using wordTrace_append hprefix tailTrace_1894361
  have hstable : (prefixWord ++ tailWord_1894361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894361).length < 2 ^ (prefixWord ++ tailWord_1894361).sum := by decide
  have hdescent : baseEnd_1894361 < baseStart_1894361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894464 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 6]
def baseStart_1894464 : Nat := 118140960795 + 1894464 * 2 ^ 59
def prefixEnd_1894464 : Nat := 4983230072969 + 3 ^ 40 * 1894464 * 2
def baseEnd_1894464 : Nat := 216171247697640252130561

theorem tailTrace_1894464 : CollatzResearch.WordTrace tailWord_1894464 prefixEnd_1894464 216171247697640252130561 := by
  unfold tailWord_1894464
  simp only [CollatzResearch.WordTrace]
  refine ⟨34548389304343975768641223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46064519072458634358188297 34548389304343975768641223)
  ·
    refine ⟨51822583956515963652961835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34548389304343975768641223 51822583956515963652961835)
    ·
      refine ⟨77733875934773945479442753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51822583956515963652961835 77733875934773945479442753)
      ·
        refine ⟨58300406951080459109582065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77733875934773945479442753 58300406951080459109582065)
        ·
          refine ⟨43725305213310344332186549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58300406951080459109582065 43725305213310344332186549)
          ·
            refine ⟨4099247363747844781142489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43725305213310344332186549 4099247363747844781142489)
            ·
              refine ⟨3074435522810883585856867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099247363747844781142489 3074435522810883585856867)
              ·
                refine ⟨4611653284216325378785301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074435522810883585856867 4611653284216325378785301)
                ·
                  refine ⟨216171247697640252130561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4611653284216325378785301 216171247697640252130561)
                  ·
                    rfl

theorem cell22_1894464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_1894464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894464 prefixEnd_1894464 := by exact prefixLift 1894464
  have htrace : WordTrace (prefixWord ++ tailWord_1894464) baseStart_1894464 baseEnd_1894464 := by
    simpa [prefixWord, tailWord_1894464, baseEnd_1894464] using wordTrace_append hprefix tailTrace_1894464
  have hstable : (prefixWord ++ tailWord_1894464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894464).length < 2 ^ (prefixWord ++ tailWord_1894464).sum := by decide
  have hdescent : baseEnd_1894464 < baseStart_1894464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894584 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_1894584 : Nat := 118140960795 + 1894584 * 2 ^ 59
def prefixEnd_1894584 : Nat := 4983230072969 + 3 ^ 40 * 1894584 * 2
def baseEnd_1894584 : Nat := 648554821545280443391315

theorem tailTrace_1894584 : CollatzResearch.WordTrace tailWord_1894584 prefixEnd_1894584 648554821545280443391315 := by
  unfold tailWord_1894584
  simp only [CollatzResearch.WordTrace]
  refine ⟨34550577684126606015825403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46067436912168808021100537 34550577684126606015825403)
  ·
    refine ⟨51825866526189909023738105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34550577684126606015825403 51825866526189909023738105)
    ·
      refine ⟨38869399894642431767803579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51825866526189909023738105 38869399894642431767803579)
      ·
        refine ⟨58304099841963647651705369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38869399894642431767803579 58304099841963647651705369)
        ·
          refine ⟨43728074881472735738779027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58304099841963647651705369 43728074881472735738779027)
          ·
            refine ⟨65592112322209103608168541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43728074881472735738779027 65592112322209103608168541)
            ·
              refine ⟨24597042120828413853063203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65592112322209103608168541 24597042120828413853063203)
              ·
                refine ⟨36895563181242620779594805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24597042120828413853063203 36895563181242620779594805)
                ·
                  refine ⟨3458959048241495698087013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36895563181242620779594805 3458959048241495698087013)
                  ·
                    refine ⟨648554821545280443391315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3458959048241495698087013 648554821545280443391315)
                    ·
                      rfl

theorem cell22_1894584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_1894584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894584 prefixEnd_1894584 := by exact prefixLift 1894584
  have htrace : WordTrace (prefixWord ++ tailWord_1894584) baseStart_1894584 baseEnd_1894584 := by
    simpa [prefixWord, tailWord_1894584, baseEnd_1894584] using wordTrace_append hprefix tailTrace_1894584
  have hstable : (prefixWord ++ tailWord_1894584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894584).length < 2 ^ (prefixWord ++ tailWord_1894584).sum := by decide
  have hdescent : baseEnd_1894584 < baseStart_1894584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894618 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 1, 4]
def baseStart_1894618 : Nat := 118140960795 + 1894618 * 2 ^ 59
def prefixEnd_1894618 : Nat := 4983230072969 + 3 ^ 40 * 1894618 * 2
def baseEnd_1894618 : Nat := 648566460440115688041211

theorem tailTrace_1894618 : CollatzResearch.WordTrace tailWord_1894618 prefixEnd_1894618 648566460440115688041211 := by
  unfold tailWord_1894618
  simp only [CollatzResearch.WordTrace]
  refine ⟨17275598862532508959597127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46068263633420023892259005 17275598862532508959597127)
  ·
    refine ⟨25913398293798763439395691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17275598862532508959597127 25913398293798763439395691)
    ·
      refine ⟨38870097440698145159093537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25913398293798763439395691 38870097440698145159093537)
      ·
        refine ⟨29152573080523608869320153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38870097440698145159093537 29152573080523608869320153)
        ·
          refine ⟨21864429810392706651990115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29152573080523608869320153 21864429810392706651990115)
          ·
            refine ⟨32796644715589059977985173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21864429810392706651990115 32796644715589059977985173)
            ·
              refine ⟨1537342721043237186468055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32796644715589059977985173 1537342721043237186468055)
              ·
                refine ⟨2306014081564855779702083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537342721043237186468055 2306014081564855779702083)
                ·
                  refine ⟨3459021122347283669553125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306014081564855779702083 3459021122347283669553125)
                  ·
                    refine ⟨648566460440115688041211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3459021122347283669553125 648566460440115688041211)
                    ·
                      rfl

theorem cell22_1894618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_1894618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894618 prefixEnd_1894618 := by exact prefixLift 1894618
  have htrace : WordTrace (prefixWord ++ tailWord_1894618) baseStart_1894618 baseEnd_1894618 := by
    simpa [prefixWord, tailWord_1894618, baseEnd_1894618] using wordTrace_append hprefix tailTrace_1894618
  have hstable : (prefixWord ++ tailWord_1894618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894618).length < 2 ^ (prefixWord ++ tailWord_1894618).sum := by decide
  have hdescent : baseEnd_1894618 < baseStart_1894618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894646 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1894646 : Nat := 118140960795 + 1894646 * 2 ^ 59
def prefixEnd_1894646 : Nat := 4983230072969 + 3 ^ 40 * 1894646 * 2
def baseEnd_1894646 : Nat := 648576045412332948341125

theorem tailTrace_1894646 : CollatzResearch.WordTrace tailWord_1894646 prefixEnd_1894646 648576045412332948341125 := by
  unfold tailWord_1894646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318963543376787288775487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46068944462685731080271861 4318963543376787288775487)
  ·
    refine ⟨6478445315065180933163231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4318963543376787288775487 6478445315065180933163231)
    ·
      refine ⟨9717667972597771399744847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6478445315065180933163231 9717667972597771399744847)
      ·
        refine ⟨14576501958896657099617271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9717667972597771399744847 14576501958896657099617271)
        ·
          refine ⟨21864752938344985649425907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14576501958896657099617271 21864752938344985649425907)
          ·
            refine ⟨32797129407517478474138861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21864752938344985649425907 32797129407517478474138861)
            ·
              refine ⟨12298923527819054427802073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32797129407517478474138861 12298923527819054427802073)
              ·
                refine ⟨9224192645864290820851555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12298923527819054427802073 9224192645864290820851555)
                ·
                  refine ⟨13836288968796436231277333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9224192645864290820851555 13836288968796436231277333)
                  ·
                    refine ⟨648576045412332948341125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13836288968796436231277333 648576045412332948341125)
                    ·
                      rfl

theorem cell22_1894646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1894646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894646 prefixEnd_1894646 := by exact prefixLift 1894646
  have htrace : WordTrace (prefixWord ++ tailWord_1894646) baseStart_1894646 baseEnd_1894646 := by
    simpa [prefixWord, tailWord_1894646, baseEnd_1894646] using wordTrace_append hprefix tailTrace_1894646
  have hstable : (prefixWord ++ tailWord_1894646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894646).length < 2 ^ (prefixWord ++ tailWord_1894646).sum := by decide
  have hdescent : baseEnd_1894646 < baseStart_1894646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894659 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 2, 7]
def baseStart_1894659 : Nat := 118140960795 + 1894659 * 2 ^ 59
def prefixEnd_1894659 : Nat := 4983230072969 + 3 ^ 40 * 1894659 * 2
def baseEnd_1894659 : Nat := 648580495578005247766085

theorem tailTrace_1894659 : CollatzResearch.WordTrace tailWord_1894659 prefixEnd_1894659 648580495578005247766085 := by
  unfold tailWord_1894659
  simp only [CollatzResearch.WordTrace]
  refine ⟨69103890842981499840631031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46069260561987666560420687 69103890842981499840631031)
  ·
    refine ⟨103655836264472249760946547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69103890842981499840631031 103655836264472249760946547)
    ·
      refine ⟨155483754396708374641419821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103655836264472249760946547 155483754396708374641419821)
      ·
        refine ⟨58306407898765640490532433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155483754396708374641419821 58306407898765640490532433)
        ·
          refine ⟨43729805924074230367899325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58306407898765640490532433 43729805924074230367899325)
          ·
            refine ⟨16398677221527836387962247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43729805924074230367899325 16398677221527836387962247)
            ·
              refine ⟨24598015832291754581943371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16398677221527836387962247 24598015832291754581943371)
              ·
                refine ⟨36897023748437631872915057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24598015832291754581943371 36897023748437631872915057)
                ·
                  refine ⟨27672767811328223904686293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36897023748437631872915057 27672767811328223904686293)
                  ·
                    refine ⟨648580495578005247766085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27672767811328223904686293 648580495578005247766085)
                    ·
                      rfl

theorem cell22_1894659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_1894659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894659 prefixEnd_1894659 := by exact prefixLift 1894659
  have htrace : WordTrace (prefixWord ++ tailWord_1894659) baseStart_1894659 baseEnd_1894659 := by
    simpa [prefixWord, tailWord_1894659, baseEnd_1894659] using wordTrace_append hprefix tailTrace_1894659
  have hstable : (prefixWord ++ tailWord_1894659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894659).length < 2 ^ (prefixWord ++ tailWord_1894659).sum := by decide
  have hdescent : baseEnd_1894659 < baseStart_1894659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894785 : List Nat := [1, 2, 4, 3, 1, 1, 1, 5, 4]
def baseStart_1894785 : Nat := 118140960795 + 1894785 * 2 ^ 59
def prefixEnd_1894785 : Nat := 4983230072969 + 3 ^ 40 * 1894785 * 2
def baseEnd_1894785 : Nat := 216207875984327639705233

theorem tailTrace_1894785 : CollatzResearch.WordTrace tailWord_1894785 prefixEnd_1894785 216207875984327639705233 := by
  unfold tailWord_1894785
  simp only [CollatzResearch.WordTrace]
  refine ⟨69108486440525023359717809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46072324293683348906478539 69108486440525023359717809)
  ·
    refine ⟨51831364830393767519788357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69108486440525023359717809 51831364830393767519788357)
    ·
      refine ⟨9718380905698831409960317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51831364830393767519788357 9718380905698831409960317)
      ·
        refine ⟨3644392839637061778735119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9718380905698831409960317 3644392839637061778735119)
        ·
          refine ⟨5466589259455592668102679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644392839637061778735119 5466589259455592668102679)
          ·
            refine ⟨8199883889183389002154019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466589259455592668102679 8199883889183389002154019)
            ·
              refine ⟨12299825833775083503231029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8199883889183389002154019 12299825833775083503231029)
              ·
                refine ⟨1153108671916414078427909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12299825833775083503231029 1153108671916414078427909)
                ·
                  refine ⟨216207875984327639705233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153108671916414078427909 216207875984327639705233)
                  ·
                    rfl

theorem cell22_1894785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 4].length) (baseStart_1894785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894785 prefixEnd_1894785 := by exact prefixLift 1894785
  have htrace : WordTrace (prefixWord ++ tailWord_1894785) baseStart_1894785 baseEnd_1894785 := by
    simpa [prefixWord, tailWord_1894785, baseEnd_1894785] using wordTrace_append hprefix tailTrace_1894785
  have hstable : (prefixWord ++ tailWord_1894785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894785).length < 2 ^ (prefixWord ++ tailWord_1894785).sum := by decide
  have hdescent : baseEnd_1894785 < baseStart_1894785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894787 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 1, 4]
def baseStart_1894787 : Nat := 118140960795 + 1894787 * 2 ^ 59
def prefixEnd_1894787 : Nat := 4983230072969 + 3 ^ 40 * 1894787 * 2
def baseEnd_1894787 : Nat := 648624312593855580565693

theorem tailTrace_1894787 : CollatzResearch.WordTrace tailWord_1894787 prefixEnd_1894787 648624312593855580565693 := by
  unfold tailWord_1894787
  simp only [CollatzResearch.WordTrace]
  refine ⟨69108559386517777701290615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46072372924345185134193743 69108559386517777701290615)
  ·
    refine ⟨103662839079776666551935923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69108559386517777701290615 103662839079776666551935923)
    ·
      refine ⟨155494258619664999827903885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103662839079776666551935923 155494258619664999827903885)
      ·
        refine ⟨58310346982374374935463957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155494258619664999827903885 58310346982374374935463957)
        ·
          refine ⟨2733297514798798825099873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58310346982374374935463957 2733297514798798825099873)
          ·
            refine ⟨2049973136099099118824905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2733297514798798825099873 2049973136099099118824905)
            ·
              refine ⟨1537479852074324339118679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2049973136099099118824905 1537479852074324339118679)
              ·
                refine ⟨2306219778111486508678019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537479852074324339118679 2306219778111486508678019)
                ·
                  refine ⟨3459329667167229763017029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306219778111486508678019 3459329667167229763017029)
                  ·
                    refine ⟨648624312593855580565693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3459329667167229763017029 648624312593855580565693)
                    ·
                      rfl

theorem cell22_1894787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 4].length) (baseStart_1894787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894787 prefixEnd_1894787 := by exact prefixLift 1894787
  have htrace : WordTrace (prefixWord ++ tailWord_1894787) baseStart_1894787 baseEnd_1894787 := by
    simpa [prefixWord, tailWord_1894787, baseEnd_1894787] using wordTrace_append hprefix tailTrace_1894787
  have hstable : (prefixWord ++ tailWord_1894787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894787).length < 2 ^ (prefixWord ++ tailWord_1894787).sum := by decide
  have hdescent : baseEnd_1894787 < baseStart_1894787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894796 : List Nat := [2, 2, 1, 2, 1, 5, 9]
def baseStart_1894796 : Nat := 118140960795 + 1894796 * 2 ^ 59
def prefixEnd_1894796 : Nat := 4983230072969 + 3 ^ 40 * 1894796 * 2
def baseEnd_1894796 : Nat := 24023236795473428040395

theorem tailTrace_1894796 : CollatzResearch.WordTrace tailWord_1894796 prefixEnd_1894796 24023236795473428040395 := by
  unfold tailWord_1894796
  simp only [CollatzResearch.WordTrace]
  refine ⟨34554443821742586119184121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46072591762323448158912161 34554443821742586119184121)
  ·
    refine ⟨25915832866306939589388091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34554443821742586119184121 25915832866306939589388091)
    ·
      refine ⟨38873749299460409384082137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25915832866306939589388091 38873749299460409384082137)
      ·
        refine ⟨29155311974595307038061603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38873749299460409384082137 29155311974595307038061603)
        ·
          refine ⟨43732967961892960557092405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29155311974595307038061603 43732967961892960557092405)
          ·
            refine ⟨4099965746427465052227413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43732967961892960557092405 4099965746427465052227413)
            ·
              refine ⟨24023236795473428040395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4099965746427465052227413 24023236795473428040395)
              ·
                rfl

theorem cell22_1894796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 9].length) (baseStart_1894796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894796 prefixEnd_1894796 := by exact prefixLift 1894796
  have htrace : WordTrace (prefixWord ++ tailWord_1894796) baseStart_1894796 baseEnd_1894796 := by
    simpa [prefixWord, tailWord_1894796, baseEnd_1894796] using wordTrace_append hprefix tailTrace_1894796
  have hstable : (prefixWord ++ tailWord_1894796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894796).length < 2 ^ (prefixWord ++ tailWord_1894796).sum := by decide
  have hdescent : baseEnd_1894796 < baseStart_1894796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894817 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 1, 5]
def baseStart_1894817 : Nat := 118140960795 + 1894817 * 2 ^ 59
def prefixEnd_1894817 : Nat := 4983230072969 + 3 ^ 40 * 1894817 * 2
def baseEnd_1894817 : Nat := 648634582206945502315601

theorem tailTrace_1894817 : CollatzResearch.WordTrace tailWord_1894817 prefixEnd_1894817 648634582206945502315601 := by
  unfold tailWord_1894817
  simp only [CollatzResearch.WordTrace]
  refine ⟨69109653576409092824882705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46073102384272728549921803 69109653576409092824882705)
  ·
    refine ⟨51832240182306819618662029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69109653576409092824882705 51832240182306819618662029)
    ·
      refine ⟨19437090068365057356998261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51832240182306819618662029 19437090068365057356998261)
      ·
        refine ⟨1822227193909224127218587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19437090068365057356998261 1822227193909224127218587)
        ·
          refine ⟨2733340790863836190827881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822227193909224127218587 2733340790863836190827881)
          ·
            refine ⟨2050005593147877143120911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2733340790863836190827881 2050005593147877143120911)
            ·
              refine ⟨3075008389721815714681367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050005593147877143120911 3075008389721815714681367)
              ·
                refine ⟨4612512584582723572022051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075008389721815714681367 4612512584582723572022051)
                ·
                  refine ⟨6918768876874085358033077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612512584582723572022051 6918768876874085358033077)
                  ·
                    refine ⟨648634582206945502315601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6918768876874085358033077 648634582206945502315601)
                    ·
                      rfl

theorem cell22_1894817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_1894817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894817 prefixEnd_1894817 := by exact prefixLift 1894817
  have htrace : WordTrace (prefixWord ++ tailWord_1894817) baseStart_1894817 baseEnd_1894817 := by
    simpa [prefixWord, tailWord_1894817, baseEnd_1894817] using wordTrace_append hprefix tailTrace_1894817
  have hstable : (prefixWord ++ tailWord_1894817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894817).length < 2 ^ (prefixWord ++ tailWord_1894817).sum := by decide
  have hdescent : baseEnd_1894817 < baseStart_1894817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894836 : List Nat := [2, 5, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1894836 : Nat := 118140960795 + 1894836 * 2 ^ 59
def prefixEnd_1894836 : Nat := 4983230072969 + 3 ^ 40 * 1894836 * 2
def baseEnd_1894836 : Nat := 216213695431745262030181

theorem tailTrace_1894836 : CollatzResearch.WordTrace tailWord_1894836 prefixEnd_1894836 216213695431745262030181 := by
  unfold tailWord_1894836
  simp only [CollatzResearch.WordTrace]
  refine ⟨34555173281670129534912181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46073564375560172713216241 34555173281670129534912181)
  ·
    refine ⟨3239547495156574643898017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34555173281670129534912181 3239547495156574643898017)
    ·
      refine ⟨2429660621367430982923513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3239547495156574643898017 2429660621367430982923513)
      ·
        refine ⟨1822245466025573237192635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2429660621367430982923513 1822245466025573237192635)
        ·
          refine ⟨2733368199038359855788953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822245466025573237192635 2733368199038359855788953)
          ·
            refine ⟨2050026149278769891841715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2733368199038359855788953 2050026149278769891841715)
            ·
              refine ⟨3075039223918154837762573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050026149278769891841715 3075039223918154837762573)
              ·
                refine ⟨1153139708969308064160965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3075039223918154837762573 1153139708969308064160965)
                ·
                  refine ⟨216213695431745262030181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153139708969308064160965 216213695431745262030181)
                  ·
                    rfl

theorem cell22_1894836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1894836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894836 prefixEnd_1894836 := by exact prefixLift 1894836
  have htrace : WordTrace (prefixWord ++ tailWord_1894836) baseStart_1894836 baseEnd_1894836 := by
    simpa [prefixWord, tailWord_1894836, baseEnd_1894836] using wordTrace_append hprefix tailTrace_1894836
  have hstable : (prefixWord ++ tailWord_1894836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894836).length < 2 ^ (prefixWord ++ tailWord_1894836).sum := by decide
  have hdescent : baseEnd_1894836 < baseStart_1894836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894849 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1894849 : Nat := 118140960795 + 1894849 * 2 ^ 59
def prefixEnd_1894849 : Nat := 4983230072969 + 3 ^ 40 * 1894849 * 2
def baseEnd_1894849 : Nat := 648645536460908085515503

theorem tailTrace_1894849 : CollatzResearch.WordTrace tailWord_1894849 prefixEnd_1894849 648645536460908085515503 := by
  unfold tailWord_1894849
  simp only [CollatzResearch.WordTrace]
  refine ⟨69110820712293162290047601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46073880474862108193365067 69110820712293162290047601)
  ·
    refine ⟨51833115534219871717535701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69110820712293162290047601 51833115534219871717535701)
    ·
      refine ⟨1214838645333278243379743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 51833115534219871717535701 1214838645333278243379743)
      ·
        refine ⟨1822257967999917365069615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214838645333278243379743 1822257967999917365069615)
        ·
          refine ⟨2733386951999876047604423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822257967999917365069615 2733386951999876047604423)
          ·
            refine ⟨4100080427999814071406635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733386951999876047604423 4100080427999814071406635)
            ·
              refine ⟨6150120641999721107109953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100080427999814071406635 6150120641999721107109953)
              ·
                refine ⟨4612590481499790830332465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6150120641999721107109953 4612590481499790830332465)
                ·
                  refine ⟨3459442861124843122749349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4612590481499790830332465 3459442861124843122749349)
                  ·
                    refine ⟨648645536460908085515503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3459442861124843122749349 648645536460908085515503)
                    ·
                      rfl

theorem cell22_1894849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1894849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894849 prefixEnd_1894849 := by exact prefixLift 1894849
  have htrace : WordTrace (prefixWord ++ tailWord_1894849) baseStart_1894849 baseEnd_1894849 := by
    simpa [prefixWord, tailWord_1894849, baseEnd_1894849] using wordTrace_append hprefix tailTrace_1894849
  have hstable : (prefixWord ++ tailWord_1894849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894849).length < 2 ^ (prefixWord ++ tailWord_1894849).sum := by decide
  have hdescent : baseEnd_1894849 < baseStart_1894849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894858 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_1894858 : Nat := 118140960795 + 1894858 * 2 ^ 59
def prefixEnd_1894858 : Nat := 4983230072969 + 3 ^ 40 * 1894858 * 2
def baseEnd_1894858 : Nat := 216216205781611687346825

theorem tailTrace_1894858 : CollatzResearch.WordTrace tailWord_1894858 prefixEnd_1894858 216216205781611687346825 := by
  unfold tailWord_1894858
  simp only [CollatzResearch.WordTrace]
  refine ⟨17277787242315139206781307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46074099312840371218083485 17277787242315139206781307)
  ·
    refine ⟨25916680863472708810171961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17277787242315139206781307 25916680863472708810171961)
    ·
      refine ⟨19437510647604531607628971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25916680863472708810171961 19437510647604531607628971)
      ·
        refine ⟨29156265971406797411443457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19437510647604531607628971 29156265971406797411443457)
        ·
          refine ⟨21867199478555098058582593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29156265971406797411443457 21867199478555098058582593)
          ·
            refine ⟨16400399608916323543936945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21867199478555098058582593 16400399608916323543936945)
            ·
              refine ⟨12300299706687242657952709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16400399608916323543936945 12300299706687242657952709)
              ·
                refine ⟨2306306195003857998366133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12300299706687242657952709 2306306195003857998366133)
                ·
                  refine ⟨216216205781611687346825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2306306195003857998366133 216216205781611687346825)
                  ·
                    rfl

theorem cell22_1894858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_1894858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894858 prefixEnd_1894858 := by exact prefixLift 1894858
  have htrace : WordTrace (prefixWord ++ tailWord_1894858) baseStart_1894858 baseEnd_1894858 := by
    simpa [prefixWord, tailWord_1894858, baseEnd_1894858] using wordTrace_append hprefix tailTrace_1894858
  have hstable : (prefixWord ++ tailWord_1894858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894858).length < 2 ^ (prefixWord ++ tailWord_1894858).sum := by decide
  have hdescent : baseEnd_1894858 < baseStart_1894858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894871 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1894871 : Nat := 118140960795 + 1894871 * 2 ^ 59
def prefixEnd_1894871 : Nat := 4983230072969 + 3 ^ 40 * 1894871 * 2
def baseEnd_1894871 : Nat := 648653067510507361465435

theorem tailTrace_1894871 : CollatzResearch.WordTrace tailWord_1894871 prefixEnd_1894871 648653067510507361465435 := by
  unfold tailWord_1894871
  simp only [CollatzResearch.WordTrace]
  refine ⟨69111623118213460047348467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46074415412142306698232311 69111623118213460047348467)
  ·
    refine ⟨103667434677320190071022701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69111623118213460047348467 103667434677320190071022701)
    ·
      refine ⟨38875288003995071276633513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103667434677320190071022701 38875288003995071276633513)
      ·
        refine ⟨29156466002996303457475135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38875288003995071276633513 29156466002996303457475135)
        ·
          refine ⟨43734699004494455186212703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29156466002996303457475135 43734699004494455186212703)
          ·
            refine ⟨65602048506741682779319055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43734699004494455186212703 65602048506741682779319055)
            ·
              refine ⟨98403072760112524168978583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65602048506741682779319055 98403072760112524168978583)
              ·
                refine ⟨147604609140168786253467875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98403072760112524168978583 147604609140168786253467875)
                ·
                  refine ⟨221406913710253179380201813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147604609140168786253467875 221406913710253179380201813)
                  ·
                    refine ⟨648653067510507361465435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 221406913710253179380201813 648653067510507361465435)
                    ·
                      rfl

theorem cell22_1894871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1894871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894871 prefixEnd_1894871 := by exact prefixLift 1894871
  have htrace : WordTrace (prefixWord ++ tailWord_1894871) baseStart_1894871 baseEnd_1894871 := by
    simpa [prefixWord, tailWord_1894871, baseEnd_1894871] using wordTrace_append hprefix tailTrace_1894871
  have hstable : (prefixWord ++ tailWord_1894871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894871).length < 2 ^ (prefixWord ++ tailWord_1894871).sum := by decide
  have hdescent : baseEnd_1894871 < baseStart_1894871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894933 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1894933 : Nat := 118140960795 + 1894933 * 2 ^ 59
def prefixEnd_1894933 : Nat := 4983230072969 + 3 ^ 40 * 1894933 * 2
def baseEnd_1894933 : Nat := 648674291377559866415245

theorem tailTrace_1894933 : CollatzResearch.WordTrace tailWord_1894933 prefixEnd_1894933 648674291377559866415245 := by
  unfold tailWord_1894933
  simp only [CollatzResearch.WordTrace]
  refine ⟨69113884443988844636105453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46075922962659229757403635 69113884443988844636105453)
  ·
    refine ⟨25917706666495816738539545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69113884443988844636105453 25917706666495816738539545)
    ·
      refine ⟨19438279999871862553904659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25917706666495816738539545 19438279999871862553904659)
      ·
        refine ⟨29157419999807793830856989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19438279999871862553904659 29157419999807793830856989)
        ·
          refine ⟨10934032499927922686571371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29157419999807793830856989 10934032499927922686571371)
          ·
            refine ⟨16401048749891884029857057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10934032499927922686571371 16401048749891884029857057)
            ·
              refine ⟨12300786562418913022392793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16401048749891884029857057 12300786562418913022392793)
              ·
                refine ⟨9225589921814184766794595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12300786562418913022392793 9225589921814184766794595)
                ·
                  refine ⟨13838384882721277150191893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9225589921814184766794595 13838384882721277150191893)
                  ·
                    refine ⟨648674291377559866415245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13838384882721277150191893 648674291377559866415245)
                    ·
                      rfl

theorem cell22_1894933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1894933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1894933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1894933 prefixEnd_1894933 := by exact prefixLift 1894933
  have htrace : WordTrace (prefixWord ++ tailWord_1894933) baseStart_1894933 baseEnd_1894933 := by
    simpa [prefixWord, tailWord_1894933, baseEnd_1894933] using wordTrace_append hprefix tailTrace_1894933
  have hstable : (prefixWord ++ tailWord_1894933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894933).length < 2 ^ (prefixWord ++ tailWord_1894933).sum := by decide
  have hdescent : baseEnd_1894933 < baseStart_1894933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895008 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_1895008 : Nat := 118140960795 + 1895008 * 2 ^ 59
def prefixEnd_1895008 : Nat := 4983230072969 + 3 ^ 40 * 1895008 * 2
def baseEnd_1895008 : Nat := 648699965410284670790015

theorem tailTrace_1895008 : CollatzResearch.WordTrace tailWord_1895008 prefixEnd_1895008 648699965410284670790015 := by
  unfold tailWord_1895008
  simp only [CollatzResearch.WordTrace]
  refine ⟨34558309959358566222542839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46077746612478088296723785 34558309959358566222542839)
  ·
    refine ⟨51837464939037849333814259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34558309959358566222542839 51837464939037849333814259)
    ·
      refine ⟨77756197408556774000721389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51837464939037849333814259 77756197408556774000721389)
      ·
        refine ⟨29158574028208790250270521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77756197408556774000721389 29158574028208790250270521)
        ·
          refine ⟨21868930521156592687702891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29158574028208790250270521 21868930521156592687702891)
          ·
            refine ⟨32803395781734889031554337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21868930521156592687702891 32803395781734889031554337)
            ·
              refine ⟨24602546836301166773665753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32803395781734889031554337 24602546836301166773665753)
              ·
                refine ⟨18451910127225875080249315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24602546836301166773665753 18451910127225875080249315)
                ·
                  refine ⟨27677865190838812620373973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18451910127225875080249315 27677865190838812620373973)
                  ·
                    refine ⟨648699965410284670790015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27677865190838812620373973 648699965410284670790015)
                    ·
                      rfl

theorem cell22_1895008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_1895008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895008 prefixEnd_1895008 := by exact prefixLift 1895008
  have htrace : WordTrace (prefixWord ++ tailWord_1895008) baseStart_1895008 baseEnd_1895008 := by
    simpa [prefixWord, tailWord_1895008, baseEnd_1895008] using wordTrace_append hprefix tailTrace_1895008
  have hstable : (prefixWord ++ tailWord_1895008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895008).length < 2 ^ (prefixWord ++ tailWord_1895008).sum := by decide
  have hdescent : baseEnd_1895008 < baseStart_1895008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895044 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 5]
def baseStart_1895044 : Nat := 118140960795 + 1895044 * 2 ^ 59
def prefixEnd_1895044 : Nat := 4983230072969 + 3 ^ 40 * 1895044 * 2
def baseEnd_1895044 : Nat := 216237429648664192296635

theorem tailTrace_1895044 : CollatzResearch.WordTrace tailWord_1895044 prefixEnd_1895044 216237429648664192296635 := by
  unfold tailWord_1895044
  simp only [CollatzResearch.WordTrace]
  refine ⟨34558966473293355296698093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46078621964391140395597457 34558966473293355296698093)
  ·
    refine ⟨12959612427485008236261785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34558966473293355296698093 12959612427485008236261785)
    ·
      refine ⟨9719709320613756177196339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12959612427485008236261785 9719709320613756177196339)
      ·
        refine ⟨14579563980920634265794509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9719709320613756177196339 14579563980920634265794509)
        ·
          refine ⟨5467336492845237849672941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14579563980920634265794509 5467336492845237849672941)
          ·
            refine ⟨2050251184816964193627353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5467336492845237849672941 2050251184816964193627353)
            ·
              refine ⟨1537688388612723145220515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2050251184816964193627353 1537688388612723145220515)
              ·
                refine ⟨2306532582919084717830773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537688388612723145220515 2306532582919084717830773)
                ·
                  refine ⟨216237429648664192296635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2306532582919084717830773 216237429648664192296635)
                  ·
                    rfl

theorem cell22_1895044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_1895044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895044 prefixEnd_1895044 := by exact prefixLift 1895044
  have htrace : WordTrace (prefixWord ++ tailWord_1895044) baseStart_1895044 baseEnd_1895044 := by
    simpa [prefixWord, tailWord_1895044, baseEnd_1895044] using wordTrace_append hprefix tailTrace_1895044
  have hstable : (prefixWord ++ tailWord_1895044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895044).length < 2 ^ (prefixWord ++ tailWord_1895044).sum := by decide
  have hdescent : baseEnd_1895044 < baseStart_1895044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895082 : List Nat := [3, 1, 5, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1895082 : Nat := 118140960795 + 1895082 * 2 ^ 59
def prefixEnd_1895082 : Nat := 4983230072969 + 3 ^ 40 * 1895082 * 2
def baseEnd_1895082 : Nat := 648725297122573144439789

theorem tailTrace_1895082 : CollatzResearch.WordTrace tailWord_1895082 prefixEnd_1895082 648725297122573144439789 := by
  unfold tailWord_1895082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17279829730112260770819875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46079545946966028722186333 17279829730112260770819875)
  ·
    refine ⟨25919744595168391156229813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17279829730112260770819875 25919744595168391156229813)
    ·
      refine ⟨2429976055797036670896545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25919744595168391156229813 2429976055797036670896545)
      ·
        refine ⟨1822482041847777503172409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2429976055797036670896545 1822482041847777503172409)
        ·
          refine ⟨1366861531385833127379307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1822482041847777503172409 1366861531385833127379307)
          ·
            refine ⟨2050292297078749691068961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366861531385833127379307 2050292297078749691068961)
            ·
              refine ⟨1537719222809062268301721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2050292297078749691068961 1537719222809062268301721)
              ·
                refine ⟨1153289417106796701226291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537719222809062268301721 1153289417106796701226291)
                ·
                  refine ⟨1729934125660195051839437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153289417106796701226291 1729934125660195051839437)
                  ·
                    refine ⟨648725297122573144439789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1729934125660195051839437 648725297122573144439789)
                    ·
                      rfl

theorem cell22_1895082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1895082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895082 prefixEnd_1895082 := by exact prefixLift 1895082
  have htrace : WordTrace (prefixWord ++ tailWord_1895082) baseStart_1895082 baseEnd_1895082 := by
    simpa [prefixWord, tailWord_1895082, baseEnd_1895082] using wordTrace_append hprefix tailTrace_1895082
  have hstable : (prefixWord ++ tailWord_1895082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895082).length < 2 ^ (prefixWord ++ tailWord_1895082).sum := by decide
  have hdescent : baseEnd_1895082 < baseStart_1895082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895087 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 2, 3]
def baseStart_1895087 : Nat := 118140960795 + 1895087 * 2 ^ 59
def prefixEnd_1895087 : Nat := 4983230072969 + 3 ^ 40 * 1895087 * 2
def baseEnd_1895087 : Nat := 648727008724754798064773

theorem tailTrace_1895087 : CollatzResearch.WordTrace tailWord_1895087 prefixEnd_1895087 648727008724754798064773 := by
  unfold tailWord_1895087
  simp only [CollatzResearch.WordTrace]
  refine ⟨69119501285430928937211515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46079667523620619291474343 69119501285430928937211515)
  ·
    refine ⟨103679251928146393405817273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69119501285430928937211515 103679251928146393405817273)
    ·
      refine ⟨77759438946109795054362955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103679251928146393405817273 77759438946109795054362955)
      ·
        refine ⟨116639158419164692581544433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77759438946109795054362955 116639158419164692581544433)
        ·
          refine ⟨87479368814373519436158325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116639158419164692581544433 87479368814373519436158325)
          ·
            refine ⟨8201190826347517447139843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87479368814373519436158325 8201190826347517447139843)
            ·
              refine ⟨12301786239521276170709765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8201190826347517447139843 12301786239521276170709765)
              ·
                refine ⟨2306584919910239282008081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12301786239521276170709765 2306584919910239282008081)
                ·
                  refine ⟨1729938689932679461506061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2306584919910239282008081 1729938689932679461506061)
                  ·
                    refine ⟨648727008724754798064773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1729938689932679461506061 648727008724754798064773)
                    ·
                      rfl

theorem cell22_1895087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_1895087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895087 prefixEnd_1895087 := by exact prefixLift 1895087
  have htrace : WordTrace (prefixWord ++ tailWord_1895087) baseStart_1895087 baseEnd_1895087 := by
    simpa [prefixWord, tailWord_1895087, baseEnd_1895087] using wordTrace_append hprefix tailTrace_1895087
  have hstable : (prefixWord ++ tailWord_1895087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895087).length < 2 ^ (prefixWord ++ tailWord_1895087).sum := by decide
  have hdescent : baseEnd_1895087 < baseStart_1895087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895149 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1895149 : Nat := 118140960795 + 1895149 * 2 ^ 59
def prefixEnd_1895149 : Nat := 4983230072969 + 3 ^ 40 * 1895149 * 2
def baseEnd_1895149 : Nat := 648748232591807303014583

theorem tailTrace_1895149 : CollatzResearch.WordTrace tailWord_1895149 prefixEnd_1895149 648748232591807303014583 := by
  unfold tailWord_1895149
  simp only [CollatzResearch.WordTrace]
  refine ⟨69121762611206313525968501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46081175074137542350645667 69121762611206313525968501)
  ·
    refine ⟨6480165244800591893059547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69121762611206313525968501 6480165244800591893059547)
    ·
      refine ⟨9720247867200887839589321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6480165244800591893059547 9720247867200887839589321)
      ·
        refine ⟨7290185900400665879691991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9720247867200887839589321 7290185900400665879691991)
        ·
          refine ⟨10935278850600998819537987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7290185900400665879691991 10935278850600998819537987)
          ·
            refine ⟨16402918275901498229306981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10935278850600998819537987 16402918275901498229306981)
            ·
              refine ⟨3075547176731530917995059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16402918275901498229306981 3075547176731530917995059)
              ·
                refine ⟨4613320765097296376992589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075547176731530917995059 4613320765097296376992589)
                ·
                  refine ⟨1729995286911486141372221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4613320765097296376992589 1729995286911486141372221)
                  ·
                    refine ⟨648748232591807303014583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1729995286911486141372221 648748232591807303014583)
                    ·
                      rfl

theorem cell22_1895149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1895149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895149 prefixEnd_1895149 := by exact prefixLift 1895149
  have htrace : WordTrace (prefixWord ++ tailWord_1895149) baseStart_1895149 baseEnd_1895149 := by
    simpa [prefixWord, tailWord_1895149, baseEnd_1895149] using wordTrace_append hprefix tailTrace_1895149
  have hstable : (prefixWord ++ tailWord_1895149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895149).length < 2 ^ (prefixWord ++ tailWord_1895149).sum := by decide
  have hdescent : baseEnd_1895149 < baseStart_1895149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895160 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_1895160 : Nat := 118140960795 + 1895160 * 2 ^ 59
def prefixEnd_1895160 : Nat := 4983230072969 + 3 ^ 40 * 1895160 * 2
def baseEnd_1895160 : Nat := 648751998116606940989549

theorem tailTrace_1895160 : CollatzResearch.WordTrace tailWord_1895160 prefixEnd_1895160 648751998116606940989549 := by
  unfold tailWord_1895160
  simp only [CollatzResearch.WordTrace]
  refine ⟨34561081907083231202309467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46081442542777641603079289 34561081907083231202309467)
  ·
    refine ⟨51841622860624846803464201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34561081907083231202309467 51841622860624846803464201)
    ·
      refine ⟨38881217145468635102598151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51841622860624846803464201 38881217145468635102598151)
      ·
        refine ⟨58321825718202952653897227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38881217145468635102598151 58321825718202952653897227)
        ·
          refine ⟨87482738577304428980845841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58321825718202952653897227 87482738577304428980845841)
          ·
            refine ⟨65612053932978321735634381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87482738577304428980845841 65612053932978321735634381)
            ·
              refine ⟨24604520224866870650862893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65612053932978321735634381 24604520224866870650862893)
              ·
                refine ⟨9226695084325076494073585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24604520224866870650862893 9226695084325076494073585)
                ·
                  refine ⟨6920021313243807370555189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9226695084325076494073585 6920021313243807370555189)
                  ·
                    refine ⟨648751998116606940989549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6920021313243807370555189 648751998116606940989549)
                    ·
                      rfl

theorem cell22_1895160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_1895160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895160 prefixEnd_1895160 := by exact prefixLift 1895160
  have htrace : WordTrace (prefixWord ++ tailWord_1895160) baseStart_1895160 baseEnd_1895160 := by
    simpa [prefixWord, tailWord_1895160, baseEnd_1895160] using wordTrace_append hprefix tailTrace_1895160
  have hstable : (prefixWord ++ tailWord_1895160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895160).length < 2 ^ (prefixWord ++ tailWord_1895160).sum := by decide
  have hdescent : baseEnd_1895160 < baseStart_1895160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895226 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_1895226 : Nat := 118140960795 + 1895226 * 2 ^ 59
def prefixEnd_1895226 : Nat := 4983230072969 + 3 ^ 40 * 1895226 * 2
def baseEnd_1895226 : Nat := 648774591265404768839347

theorem tailTrace_1895226 : CollatzResearch.WordTrace tailWord_1895226 prefixEnd_1895226 648774591265404768839347 := by
  unfold tailWord_1895226
  simp only [CollatzResearch.WordTrace]
  refine ⟨17281142757981838919130383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46083047354618237117681021 17281142757981838919130383)
  ·
    refine ⟨25921714136972758378695575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17281142757981838919130383 25921714136972758378695575)
    ·
      refine ⟨38882571205459137568043363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25921714136972758378695575 38882571205459137568043363)
      ·
        refine ⟨58323856808188706352065045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38882571205459137568043363 58323856808188706352065045)
        ·
          refine ⟨2733930787883845610253049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58323856808188706352065045 2733930787883845610253049)
          ·
            refine ⟨2050448090912884207689787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2733930787883845610253049 2050448090912884207689787)
            ·
              refine ⟨3075672136369326311534681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050448090912884207689787 3075672136369326311534681)
              ·
                refine ⟨2306754102276994733651011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075672136369326311534681 2306754102276994733651011)
                ·
                  refine ⟨3460131153415492100476517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306754102276994733651011 3460131153415492100476517)
                  ·
                    refine ⟨648774591265404768839347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3460131153415492100476517 648774591265404768839347)
                    ·
                      rfl

theorem cell22_1895226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_1895226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895226 prefixEnd_1895226 := by exact prefixLift 1895226
  have htrace : WordTrace (prefixWord ++ tailWord_1895226) baseStart_1895226 baseEnd_1895226 := by
    simpa [prefixWord, tailWord_1895226, baseEnd_1895226] using wordTrace_append hprefix tailTrace_1895226
  have hstable : (prefixWord ++ tailWord_1895226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895226).length < 2 ^ (prefixWord ++ tailWord_1895226).sum := by decide
  have hdescent : baseEnd_1895226 < baseStart_1895226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895235 : List Nat := [1, 1, 1, 3, 1, 4, 1, 10]
def baseStart_1895235 : Nat := 118140960795 + 1895235 * 2 ^ 59
def prefixEnd_1895235 : Nat := 4983230072969 + 3 ^ 40 * 1895235 * 2
def baseEnd_1895235 : Nat := 72086408016592416151591

theorem tailTrace_1895235 : CollatzResearch.WordTrace tailWord_1895235 prefixEnd_1895235 72086408016592416151591 := by
  unfold tailWord_1895235
  simp only [CollatzResearch.WordTrace]
  refine ⟨69124899288894750213599159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46083266192596500142399439 69124899288894750213599159)
  ·
    refine ⟨103687348933342125320398739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69124899288894750213599159 103687348933342125320398739)
    ·
      refine ⟨155531023400013187980598109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103687348933342125320398739 155531023400013187980598109)
      ·
        refine ⟨58324133775004945492724291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155531023400013187980598109 58324133775004945492724291)
        ·
          refine ⟨87486200662507418239086437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58324133775004945492724291 87486200662507418239086437)
          ·
            refine ⟨16403662624220140919828707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87486200662507418239086437 16403662624220140919828707)
            ·
              refine ⟨24605493936330211379743061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16403662624220140919828707 24605493936330211379743061)
              ·
                refine ⟨72086408016592416151591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24605493936330211379743061 72086408016592416151591)
                ·
                  rfl

theorem cell22_1895235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 10].length) (baseStart_1895235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895235 prefixEnd_1895235 := by exact prefixLift 1895235
  have htrace : WordTrace (prefixWord ++ tailWord_1895235) baseStart_1895235 baseEnd_1895235 := by
    simpa [prefixWord, tailWord_1895235, baseEnd_1895235] using wordTrace_append hprefix tailTrace_1895235
  have hstable : (prefixWord ++ tailWord_1895235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895235).length < 2 ^ (prefixWord ++ tailWord_1895235).sum := by decide
  have hdescent : baseEnd_1895235 < baseStart_1895235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895252 : List Nat := [2, 4, 1, 1, 4, 10]
def baseStart_1895252 : Nat := 118140960795 + 1895252 * 2 ^ 59
def prefixEnd_1895252 : Nat := 4983230072969 + 3 ^ 40 * 1895252 * 2
def baseEnd_1895252 : Nat := 8009672735762337872707

theorem tailTrace_1895252 : CollatzResearch.WordTrace tailWord_1895252 prefixEnd_1895252 8009672735762337872707 := by
  unfold tailWord_1895252
  simp only [CollatzResearch.WordTrace]
  refine ⟨34562759664916581058484005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46083679553222108077978673 34562759664916581058484005)
  ·
    refine ⟨6480517437171858948465751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34562759664916581058484005 6480517437171858948465751)
    ·
      refine ⟨9720776155757788422698627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6480517437171858948465751 9720776155757788422698627)
      ·
        refine ⟨14581164233636682634047941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9720776155757788422698627 14581164233636682634047941)
        ·
          refine ⟨2733968293806877993883989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14581164233636682634047941 2733968293806877993883989)
          ·
            refine ⟨8009672735762337872707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2733968293806877993883989 8009672735762337872707)
            ·
              rfl

theorem cell22_1895252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 10].length) (baseStart_1895252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895252 prefixEnd_1895252 := by exact prefixLift 1895252
  have htrace : WordTrace (prefixWord ++ tailWord_1895252) baseStart_1895252 baseEnd_1895252 := by
    simpa [prefixWord, tailWord_1895252, baseEnd_1895252] using wordTrace_append hprefix tailTrace_1895252
  have hstable : (prefixWord ++ tailWord_1895252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895252).length < 2 ^ (prefixWord ++ tailWord_1895252).sum := by decide
  have hdescent : baseEnd_1895252 < baseStart_1895252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895286 : List Nat := [5, 1, 1, 3, 1, 2, 3, 6]
def baseStart_1895286 : Nat := 118140960795 + 1895286 * 2 ^ 59
def prefixEnd_1895286 : Nat := 4983230072969 + 3 ^ 40 * 1895286 * 2
def baseEnd_1895286 : Nat := 72088347832398290259907

theorem tailTrace_1895286 : CollatzResearch.WordTrace tailWord_1895286 prefixEnd_1895286 72088347832398290259907 := by
  unfold tailWord_1895286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4320422463231874120231607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46084506274473323949137141 4320422463231874120231607)
  ·
    refine ⟨6480633694847811180347411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4320422463231874120231607 6480633694847811180347411)
    ·
      refine ⟨9720950542271716770521117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6480633694847811180347411 9720950542271716770521117)
      ·
        refine ⟨3645356453351893788945419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9720950542271716770521117 3645356453351893788945419)
        ·
          refine ⟨5468034680027840683418129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645356453351893788945419 5468034680027840683418129)
          ·
            refine ⟨4101026010020880512563597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468034680027840683418129 4101026010020880512563597)
            ·
              refine ⟨1537884753757830192211349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4101026010020880512563597 1537884753757830192211349)
              ·
                refine ⟨72088347832398290259907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1537884753757830192211349 72088347832398290259907)
                ·
                  rfl

theorem cell22_1895286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_1895286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895286 prefixEnd_1895286 := by exact prefixLift 1895286
  have htrace : WordTrace (prefixWord ++ tailWord_1895286) baseStart_1895286 baseEnd_1895286 := by
    simpa [prefixWord, tailWord_1895286, baseEnd_1895286] using wordTrace_append hprefix tailTrace_1895286
  have hstable : (prefixWord ++ tailWord_1895286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895286).length < 2 ^ (prefixWord ++ tailWord_1895286).sum := by decide
  have hdescent : baseEnd_1895286 < baseStart_1895286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895301 : List Nat := [1, 3, 1, 1, 3, 3, 1, 5, 1, 3]
def baseStart_1895301 : Nat := 118140960795 + 1895301 * 2 ^ 59
def prefixEnd_1895301 : Nat := 4983230072969 + 3 ^ 40 * 1895301 * 2
def baseEnd_1895301 : Nat := 648800265298129573214117

theorem tailTrace_1895301 : CollatzResearch.WordTrace tailWord_1895301 prefixEnd_1895301 648800265298129573214117 := by
  unfold tailWord_1895301
  simp only [CollatzResearch.WordTrace]
  refine ⟨69127306506655643485501757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46084871004437095657001171 69127306506655643485501757)
  ·
    refine ⟨25922739939995866307063159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69127306506655643485501757 25922739939995866307063159)
    ·
      refine ⟨38884109909993799460594739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25922739939995866307063159 38884109909993799460594739)
      ·
        refine ⟨58326164864990699190892109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38884109909993799460594739 58326164864990699190892109)
        ·
          refine ⟨21872311824371512196584541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58326164864990699190892109 21872311824371512196584541)
          ·
            refine ⟨8202116934139317073719203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21872311824371512196584541 8202116934139317073719203)
            ·
              refine ⟨12303175401208975610578805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8202116934139317073719203 12303175401208975610578805)
              ·
                refine ⟨1153422693863341463491763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12303175401208975610578805 1153422693863341463491763)
                ·
                  refine ⟨1730134040795012195237645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153422693863341463491763 1730134040795012195237645)
                  ·
                    refine ⟨648800265298129573214117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1730134040795012195237645 648800265298129573214117)
                    ·
                      rfl

theorem cell22_1895301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_1895301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895301 prefixEnd_1895301 := by exact prefixLift 1895301
  have htrace : WordTrace (prefixWord ++ tailWord_1895301) baseStart_1895301 baseEnd_1895301 := by
    simpa [prefixWord, tailWord_1895301, baseEnd_1895301] using wordTrace_append hprefix tailTrace_1895301
  have hstable : (prefixWord ++ tailWord_1895301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895301).length < 2 ^ (prefixWord ++ tailWord_1895301).sum := by decide
  have hdescent : baseEnd_1895301 < baseStart_1895301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895329 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1895329 : Nat := 118140960795 + 1895329 * 2 ^ 59
def prefixEnd_1895329 : Nat := 4983230072969 + 3 ^ 40 * 1895329 * 2
def baseEnd_1895329 : Nat := 648809850270346833514031

theorem tailTrace_1895329 : CollatzResearch.WordTrace tailWord_1895329 prefixEnd_1895329 648809850270346833514031 := by
  unfold tailWord_1895329
  simp only [CollatzResearch.WordTrace]
  refine ⟨69128327750554204267521041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46085551833702802845014027 69128327750554204267521041)
  ·
    refine ⟨51846245812915653200640781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69128327750554204267521041 51846245812915653200640781)
    ·
      refine ⟨19442342179843369950240293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51846245812915653200640781 19442342179843369950240293)
      ·
        refine ⟨3645439158720631865670055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19442342179843369950240293 3645439158720631865670055)
        ·
          refine ⟨5468158738080947798505083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645439158720631865670055 5468158738080947798505083)
          ·
            refine ⟨8202238107121421697757625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468158738080947798505083 8202238107121421697757625)
            ·
              refine ⟨6151678580341066273318219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8202238107121421697757625 6151678580341066273318219)
              ·
                refine ⟨9227517870511599409977329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6151678580341066273318219 9227517870511599409977329)
                ·
                  refine ⟨6920638402883699557482997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9227517870511599409977329 6920638402883699557482997)
                  ·
                    refine ⟨648809850270346833514031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6920638402883699557482997 648809850270346833514031)
                    ·
                      rfl

theorem cell22_1895329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1895329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895329 prefixEnd_1895329 := by exact prefixLift 1895329
  have htrace : WordTrace (prefixWord ++ tailWord_1895329) baseStart_1895329 baseEnd_1895329 := by
    simpa [prefixWord, tailWord_1895329, baseEnd_1895329] using wordTrace_append hprefix tailTrace_1895329
  have hstable : (prefixWord ++ tailWord_1895329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895329).length < 2 ^ (prefixWord ++ tailWord_1895329).sum := by decide
  have hdescent : baseEnd_1895329 < baseStart_1895329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895359 : List Nat := [1, 1, 2, 2, 2, 1, 2, 7, 4]
def baseStart_1895359 : Nat := 118140960795 + 1895359 * 2 ^ 59
def prefixEnd_1895359 : Nat := 4983230072969 + 3 ^ 40 * 1895359 * 2
def baseEnd_1895359 : Nat := 216273373294478918421313

theorem tailTrace_1895359 : CollatzResearch.WordTrace tailWord_1895359 prefixEnd_1895359 216273373294478918421313 := by
  unfold tailWord_1895359
  simp only [CollatzResearch.WordTrace]
  refine ⟨69129421940445519391113131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46086281293630346260742087 69129421940445519391113131)
  ·
    refine ⟨103694132910668279086669697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69129421940445519391113131 103694132910668279086669697)
    ·
      refine ⟨77770599683001209315002273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103694132910668279086669697 77770599683001209315002273)
      ·
        refine ⟨58327949762250906986251705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77770599683001209315002273 58327949762250906986251705)
        ·
          refine ⟨43745962321688180239688779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58327949762250906986251705 43745962321688180239688779)
          ·
            refine ⟨65618943482532270359533169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43745962321688180239688779 65618943482532270359533169)
            ·
              refine ⟨49214207611899202769649877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65618943482532270359533169 49214207611899202769649877)
              ·
                refine ⟨1153457990903887564913669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49214207611899202769649877 1153457990903887564913669)
                ·
                  refine ⟨216273373294478918421313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153457990903887564913669 216273373294478918421313)
                  ·
                    rfl

theorem cell22_1895359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 4].length) (baseStart_1895359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895359 prefixEnd_1895359 := by exact prefixLift 1895359
  have htrace : WordTrace (prefixWord ++ tailWord_1895359) baseStart_1895359 baseEnd_1895359 := by
    simpa [prefixWord, tailWord_1895359, baseEnd_1895359] using wordTrace_append hprefix tailTrace_1895359
  have hstable : (prefixWord ++ tailWord_1895359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895359).length < 2 ^ (prefixWord ++ tailWord_1895359).sum := by decide
  have hdescent : baseEnd_1895359 < baseStart_1895359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895434 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_1895434 : Nat := 118140960795 + 1895434 * 2 ^ 59
def prefixEnd_1895434 : Nat := 4983230072969 + 3 ^ 40 * 1895434 * 2
def baseEnd_1895434 : Nat := 648845793916161559638709

theorem tailTrace_1895434 : CollatzResearch.WordTrace tailWord_1895434 prefixEnd_1895434 648845793916161559638709 := by
  unfold tailWord_1895434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17283039353793451800023339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46088104943449204800062237 17283039353793451800023339)
  ·
    refine ⟨25924559030690177700035009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17283039353793451800023339 25924559030690177700035009)
    ·
      refine ⟨19443419273017633275026257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25924559030690177700035009 19443419273017633275026257)
      ·
        refine ⟨14582564454763224956269693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19443419273017633275026257 14582564454763224956269693)
        ·
          refine ⟨5468461670536209358601135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14582564454763224956269693 5468461670536209358601135)
          ·
            refine ⟨8202692505804314037901703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468461670536209358601135 8202692505804314037901703)
            ·
              refine ⟨12304038758706471056852555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8202692505804314037901703 12304038758706471056852555)
              ·
                refine ⟨18456058138059706585278833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12304038758706471056852555 18456058138059706585278833)
                ·
                  refine ⟨13842043603544779938959125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18456058138059706585278833 13842043603544779938959125)
                  ·
                    refine ⟨648845793916161559638709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13842043603544779938959125 648845793916161559638709)
                    ·
                      rfl

theorem cell22_1895434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_1895434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895434 prefixEnd_1895434 := by exact prefixLift 1895434
  have htrace : WordTrace (prefixWord ++ tailWord_1895434) baseStart_1895434 baseEnd_1895434 := by
    simpa [prefixWord, tailWord_1895434, baseEnd_1895434] using wordTrace_append hprefix tailTrace_1895434
  have hstable : (prefixWord ++ tailWord_1895434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895434).length < 2 ^ (prefixWord ++ tailWord_1895434).sum := by decide
  have hdescent : baseEnd_1895434 < baseStart_1895434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895449 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 5]
def baseStart_1895449 : Nat := 118140960795 + 1895449 * 2 ^ 59
def prefixEnd_1895449 : Nat := 4983230072969 + 3 ^ 40 * 1895449 * 2
def baseEnd_1895449 : Nat := 216283642907568840171221

theorem tailTrace_1895449 : CollatzResearch.WordTrace tailWord_1895449 prefixEnd_1895449 216283642907568840171221 := by
  unfold tailWord_1895449
  simp only [CollatzResearch.WordTrace]
  refine ⟨69132704510119464761889401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46088469673412976507926267 69132704510119464761889401)
  ·
    refine ⟨51849528382589598571417051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69132704510119464761889401 51849528382589598571417051)
    ·
      refine ⟨77774292573884397857125577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51849528382589598571417051 77774292573884397857125577)
      ·
        refine ⟨58330719430413298392844183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77774292573884397857125577 58330719430413298392844183)
        ·
          refine ⟨87496079145619947589266275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58330719430413298392844183 87496079145619947589266275)
          ·
            refine ⟨131244118718429921383899413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87496079145619947589266275 131244118718429921383899413)
            ·
              refine ⟨6152068064926402564870285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131244118718429921383899413 6152068064926402564870285)
              ·
                refine ⟨2307025524347400961826357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6152068064926402564870285 2307025524347400961826357)
                ·
                  refine ⟨216283642907568840171221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2307025524347400961826357 216283642907568840171221)
                  ·
                    rfl

theorem cell22_1895449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_1895449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895449 prefixEnd_1895449 := by exact prefixLift 1895449
  have htrace : WordTrace (prefixWord ++ tailWord_1895449) baseStart_1895449 baseEnd_1895449 := by
    simpa [prefixWord, tailWord_1895449, baseEnd_1895449] using wordTrace_append hprefix tailTrace_1895449
  have hstable : (prefixWord ++ tailWord_1895449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895449).length < 2 ^ (prefixWord ++ tailWord_1895449).sum := by decide
  have hdescent : baseEnd_1895449 < baseStart_1895449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895453 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_1895453 : Nat := 118140960795 + 1895453 * 2 ^ 59
def prefixEnd_1895453 : Nat := 4983230072969 + 3 ^ 40 * 1895453 * 2
def baseEnd_1895453 : Nat := 648852298004451843413651

theorem tailTrace_1895453 : CollatzResearch.WordTrace tailWord_1895453 prefixEnd_1895453 648852298004451843413651 := by
  unfold tailWord_1895453
  simp only [CollatzResearch.WordTrace]
  refine ⟨69132850402104973445035013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46088566934736648963356675 69132850402104973445035013)
  ·
    refine ⟨12962409450394682520944065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69132850402104973445035013 12962409450394682520944065)
    ·
      refine ⟨9721807087796011890708049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12962409450394682520944065 9721807087796011890708049)
      ·
        refine ⟨7291355315847008918031037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9721807087796011890708049 7291355315847008918031037)
        ·
          refine ⟨2734258243442628344261639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7291355315847008918031037 2734258243442628344261639)
          ·
            refine ⟨4101387365163942516392459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734258243442628344261639 4101387365163942516392459)
            ·
              refine ⟨6152081047745913774588689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101387365163942516392459 6152081047745913774588689)
              ·
                refine ⟨4614060785809435330941517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6152081047745913774588689 4614060785809435330941517)
                ·
                  refine ⟨1730272794678538249103069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4614060785809435330941517 1730272794678538249103069)
                  ·
                    refine ⟨648852298004451843413651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1730272794678538249103069 648852298004451843413651)
                    ·
                      rfl

theorem cell22_1895453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_1895453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895453 prefixEnd_1895453 := by exact prefixLift 1895453
  have htrace : WordTrace (prefixWord ++ tailWord_1895453) baseStart_1895453 baseEnd_1895453 := by
    simpa [prefixWord, tailWord_1895453, baseEnd_1895453] using wordTrace_append hprefix tailTrace_1895453
  have hstable : (prefixWord ++ tailWord_1895453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895453).length < 2 ^ (prefixWord ++ tailWord_1895453).sum := by decide
  have hdescent : baseEnd_1895453 < baseStart_1895453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895470 : List Nat := [4, 1, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_1895470 : Nat := 118140960795 + 1895470 * 2 ^ 59
def prefixEnd_1895470 : Nat := 4983230072969 + 3 ^ 40 * 1895470 * 2
def baseEnd_1895470 : Nat := 648858117451869465738599

theorem tailTrace_1895470 : CollatzResearch.WordTrace tailWord_1895470 prefixEnd_1895470 648858117451869465738599 := by
  unfold tailWord_1895470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8641683805380423168550483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46088980295362256898935909 8641683805380423168550483)
  ·
    refine ⟨12962525708070634752825725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8641683805380423168550483 12962525708070634752825725)
    ·
      refine ⟨4860947140526488032309647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12962525708070634752825725 4860947140526488032309647)
      ·
        refine ⟨7291420710789732048464471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4860947140526488032309647 7291420710789732048464471)
        ·
          refine ⟨10937131066184598072696707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291420710789732048464471 10937131066184598072696707)
          ·
            refine ⟨16405696599276897109045061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937131066184598072696707 16405696599276897109045061)
            ·
              refine ⟨3076068112364418207945949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16405696599276897109045061 3076068112364418207945949)
              ·
                refine ⟨1153525542136656827979731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3076068112364418207945949 1153525542136656827979731)
                ·
                  refine ⟨1730288313204985241969597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153525542136656827979731 1730288313204985241969597)
                  ·
                    refine ⟨648858117451869465738599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1730288313204985241969597 648858117451869465738599)
                    ·
                      rfl

theorem cell22_1895470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_1895470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895470 prefixEnd_1895470 := by exact prefixLift 1895470
  have htrace : WordTrace (prefixWord ++ tailWord_1895470) baseStart_1895470 baseEnd_1895470 := by
    simpa [prefixWord, tailWord_1895470, baseEnd_1895470] using wordTrace_append hprefix tailTrace_1895470
  have hstable : (prefixWord ++ tailWord_1895470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895470).length < 2 ^ (prefixWord ++ tailWord_1895470).sum := by decide
  have hdescent : baseEnd_1895470 < baseStart_1895470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895545 : List Nat := [1, 2, 1, 3, 5, 1, 3, 2, 4]
def baseStart_1895545 : Nat := 118140960795 + 1895545 * 2 ^ 59
def prefixEnd_1895545 : Nat := 4983230072969 + 3 ^ 40 * 1895545 * 2
def baseEnd_1895545 : Nat := 216294597161531423371123

theorem tailTrace_1895545 : CollatzResearch.WordTrace tailWord_1895545 prefixEnd_1895545 216294597161531423371123 := by
  unfold tailWord_1895545
  simp only [CollatzResearch.WordTrace]
  refine ⟨69136205917771673157384089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46090803945181115438256059 69136205917771673157384089)
  ·
    refine ⟨51852154438328754868038067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69136205917771673157384089 51852154438328754868038067)
    ·
      refine ⟨77778231657493132302057101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51852154438328754868038067 77778231657493132302057101)
      ·
        refine ⟨29166836871559924613271413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77778231657493132302057101 29166836871559924613271413)
        ·
          refine ⟨2734390956708742932494195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29166836871559924613271413 2734390956708742932494195)
          ·
            refine ⟨4101586435063114398741293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734390956708742932494195 4101586435063114398741293)
            ·
              refine ⟨1538094913148667899527985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4101586435063114398741293 1538094913148667899527985)
              ·
                refine ⟨1153571184861500924645989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538094913148667899527985 1153571184861500924645989)
                ·
                  refine ⟨216294597161531423371123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153571184861500924645989 216294597161531423371123)
                  ·
                    rfl

theorem cell22_1895545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 4].length) (baseStart_1895545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895545 prefixEnd_1895545 := by exact prefixLift 1895545
  have htrace : WordTrace (prefixWord ++ tailWord_1895545) baseStart_1895545 baseEnd_1895545 := by
    simpa [prefixWord, tailWord_1895545, baseEnd_1895545] using wordTrace_append hprefix tailTrace_1895545
  have hstable : (prefixWord ++ tailWord_1895545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895545).length < 2 ^ (prefixWord ++ tailWord_1895545).sum := by decide
  have hdescent : baseEnd_1895545 < baseStart_1895545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895556 : List Nat := [2, 3, 2, 1, 2, 3, 2, 7]
def baseStart_1895556 : Nat := 118140960795 + 1895556 * 2 ^ 59
def prefixEnd_1895556 : Nat := 4983230072969 + 3 ^ 40 * 1895556 * 2
def baseEnd_1895556 : Nat := 72098617445488212009815

theorem tailTrace_1895556 : CollatzResearch.WordTrace tailWord_1895556 prefixEnd_1895556 72098617445488212009815 := by
  unfold tailWord_1895556
  simp only [CollatzResearch.WordTrace]
  refine ⟨34568303560365911018017261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46091071413821214690689681 34568303560365911018017261)
  ·
    refine ⟨12963113835137216631756473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34568303560365911018017261 12963113835137216631756473)
    ·
      refine ⟨9722335376352912473817355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12963113835137216631756473 9722335376352912473817355)
      ·
        refine ⟨14583503064529368710726033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9722335376352912473817355 14583503064529368710726033)
        ·
          refine ⟨10937627298397026533044525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14583503064529368710726033 10937627298397026533044525)
          ·
            refine ⟨4101610236898884949891697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10937627298397026533044525 4101610236898884949891697)
            ·
              refine ⟨3076207677674163712418773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101610236898884949891697 3076207677674163712418773)
              ·
                refine ⟨72098617445488212009815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3076207677674163712418773 72098617445488212009815)
                ·
                  rfl

theorem cell22_1895556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 7].length) (baseStart_1895556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895556 prefixEnd_1895556 := by exact prefixLift 1895556
  have htrace : WordTrace (prefixWord ++ tailWord_1895556) baseStart_1895556 baseEnd_1895556 := by
    simpa [prefixWord, tailWord_1895556, baseEnd_1895556] using wordTrace_append hprefix tailTrace_1895556
  have hstable : (prefixWord ++ tailWord_1895556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895556).length < 2 ^ (prefixWord ++ tailWord_1895556).sum := by decide
  have hdescent : baseEnd_1895556 < baseStart_1895556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895560 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 2, 3]
def baseStart_1895560 : Nat := 118140960795 + 1895560 * 2 ^ 59
def prefixEnd_1895560 : Nat := 4983230072969 + 3 ^ 40 * 1895560 * 2
def baseEnd_1895560 : Nat := 648888926291139230988323

theorem tailTrace_1895560 : CollatzResearch.WordTrace tailWord_1895560 prefixEnd_1895560 648888926291139230988323 := by
  unfold tailWord_1895560
  simp only [CollatzResearch.WordTrace]
  refine ⟨34568376506358665359590067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46091168675144887146120089 34568376506358665359590067)
  ·
    refine ⟨51852564759537998039385101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34568376506358665359590067 51852564759537998039385101)
    ·
      refine ⟨19444711784826749264769413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51852564759537998039385101 19444711784826749264769413)
      ·
        refine ⟨3645883459655015487144265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19444711784826749264769413 3645883459655015487144265)
        ·
          refine ⟨2734412594741261615358199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3645883459655015487144265 2734412594741261615358199)
          ·
            refine ⟨4101618892111892423037299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734412594741261615358199 4101618892111892423037299)
            ·
              refine ⟨6152428338167838634555949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101618892111892423037299 6152428338167838634555949)
              ·
                refine ⟨2307160626812939487958481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6152428338167838634555949 2307160626812939487958481)
                ·
                  refine ⟨1730370470109704615968861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307160626812939487958481 1730370470109704615968861)
                  ·
                    refine ⟨648888926291139230988323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1730370470109704615968861 648888926291139230988323)
                    ·
                      rfl

theorem cell22_1895560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_1895560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895560 prefixEnd_1895560 := by exact prefixLift 1895560
  have htrace : WordTrace (prefixWord ++ tailWord_1895560) baseStart_1895560 baseEnd_1895560 := by
    simpa [prefixWord, tailWord_1895560, baseEnd_1895560] using wordTrace_append hprefix tailTrace_1895560
  have hstable : (prefixWord ++ tailWord_1895560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895560).length < 2 ^ (prefixWord ++ tailWord_1895560).sum := by decide
  have hdescent : baseEnd_1895560 < baseStart_1895560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895571 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 3, 3]
def baseStart_1895571 : Nat := 118140960795 + 1895571 * 2 ^ 59
def prefixEnd_1895571 : Nat := 4983230072969 + 3 ^ 40 * 1895571 * 2
def baseEnd_1895571 : Nat := 648892691815938868963289

theorem tailTrace_1895571 : CollatzResearch.WordTrace tailWord_1895571 prefixEnd_1895571 648892691815938868963289 := by
  unfold tailWord_1895571
  simp only [CollatzResearch.WordTrace]
  refine ⟨69137154215677479597830567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46091436143784986398553711 69137154215677479597830567)
  ·
    refine ⟨103705731323516219396745851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69137154215677479597830567 103705731323516219396745851)
    ·
      refine ⟨155558596985274329095118777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103705731323516219396745851 155558596985274329095118777)
      ·
        refine ⟨116668947738955746821339083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155558596985274329095118777 116668947738955746821339083)
        ·
          refine ⟨175003421608433620232008625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116668947738955746821339083 175003421608433620232008625)
          ·
            refine ⟨131252566206325215174006469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175003421608433620232008625 131252566206325215174006469)
            ·
              refine ⟨24609856163685977845126213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131252566206325215174006469 24609856163685977845126213)
              ·
                refine ⟨4614348030691120845961165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24609856163685977845126213 4614348030691120845961165)
                ·
                  refine ⟨1730380511509170317235437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4614348030691120845961165 1730380511509170317235437)
                  ·
                    refine ⟨648892691815938868963289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1730380511509170317235437 648892691815938868963289)
                    ·
                      rfl

theorem cell22_1895571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 3].length) (baseStart_1895571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895571 prefixEnd_1895571 := by exact prefixLift 1895571
  have htrace : WordTrace (prefixWord ++ tailWord_1895571) baseStart_1895571 baseEnd_1895571 := by
    simpa [prefixWord, tailWord_1895571, baseEnd_1895571] using wordTrace_append hprefix tailTrace_1895571
  have hstable : (prefixWord ++ tailWord_1895571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895571).length < 2 ^ (prefixWord ++ tailWord_1895571).sum := by decide
  have hdescent : baseEnd_1895571 < baseStart_1895571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895648 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_1895648 : Nat := 118140960795 + 1895648 * 2 ^ 59
def prefixEnd_1895648 : Nat := 4983230072969 + 3 ^ 40 * 1895648 * 2
def baseEnd_1895648 : Nat := 648919050489536334788053

theorem tailTrace_1895648 : CollatzResearch.WordTrace tailWord_1895648 prefixEnd_1895648 648919050489536334788053 := by
  unfold tailWord_1895648
  simp only [CollatzResearch.WordTrace]
  refine ⟨34569981318199260874191799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46093308424265681165589065 34569981318199260874191799)
  ·
    refine ⟨51854971977298891311287699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34569981318199260874191799 51854971977298891311287699)
    ·
      refine ⟨77782457965948336966931549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51854971977298891311287699 77782457965948336966931549)
      ·
        refine ⟨29168421737230626362599331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77782457965948336966931549 29168421737230626362599331)
        ·
          refine ⟨43752632605845939543898997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29168421737230626362599331 43752632605845939543898997)
          ·
            refine ⟨4101809306798056832240531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43752632605845939543898997 4101809306798056832240531)
            ·
              refine ⟨6152713960197085248360797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101809306798056832240531 6152713960197085248360797)
              ·
                refine ⟨2307267735073906968135299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6152713960197085248360797 2307267735073906968135299)
                ·
                  refine ⟨3460901602610860452202949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307267735073906968135299 3460901602610860452202949)
                  ·
                    refine ⟨648919050489536334788053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3460901602610860452202949 648919050489536334788053)
                    ·
                      rfl

theorem cell22_1895648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_1895648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895648 prefixEnd_1895648 := by exact prefixLift 1895648
  have htrace : WordTrace (prefixWord ++ tailWord_1895648) baseStart_1895648 baseEnd_1895648 := by
    simpa [prefixWord, tailWord_1895648, baseEnd_1895648] using wordTrace_append hprefix tailTrace_1895648
  have hstable : (prefixWord ++ tailWord_1895648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895648).length < 2 ^ (prefixWord ++ tailWord_1895648).sum := by decide
  have hdescent : baseEnd_1895648 < baseStart_1895648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895663 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 6]
def baseStart_1895663 : Nat := 118140960795 + 1895663 * 2 ^ 59
def prefixEnd_1895663 : Nat := 4983230072969 + 3 ^ 40 * 1895663 * 2
def baseEnd_1895663 : Nat := 216308061765360431887669

theorem tailTrace_1895663 : CollatzResearch.WordTrace tailWord_1895663 prefixEnd_1895663 216308061765360431887669 := by
  unfold tailWord_1895663
  simp only [CollatzResearch.WordTrace]
  refine ⟨69140509731344179310179643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46093673154229452873453095 69140509731344179310179643)
  ·
    refine ⟨103710764597016268965269465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69140509731344179310179643 103710764597016268965269465)
    ·
      refine ⟨77783073447762201723952099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103710764597016268965269465 77783073447762201723952099)
      ·
        refine ⟨116674610171643302585928149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77783073447762201723952099 116674610171643302585928149)
        ·
          refine ⟨2734561175897889904357691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 116674610171643302585928149 2734561175897889904357691)
          ·
            refine ⟨4101841763846834856536537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734561175897889904357691 4101841763846834856536537)
            ·
              refine ⟨3076381322885126142402403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101841763846834856536537 3076381322885126142402403)
              ·
                refine ⟨4614571984327689213603605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076381322885126142402403 4614571984327689213603605)
                ·
                  refine ⟨216308061765360431887669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4614571984327689213603605 216308061765360431887669)
                  ·
                    rfl

theorem cell22_1895663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 6].length) (baseStart_1895663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895663 prefixEnd_1895663 := by exact prefixLift 1895663
  have htrace : WordTrace (prefixWord ++ tailWord_1895663) baseStart_1895663 baseEnd_1895663 := by
    simpa [prefixWord, tailWord_1895663, baseEnd_1895663] using wordTrace_append hprefix tailTrace_1895663
  have hstable : (prefixWord ++ tailWord_1895663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895663).length < 2 ^ (prefixWord ++ tailWord_1895663).sum := by decide
  have hdescent : baseEnd_1895663 < baseStart_1895663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895682 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1895682 : Nat := 118140960795 + 1895682 * 2 ^ 59
def prefixEnd_1895682 : Nat := 4983230072969 + 3 ^ 40 * 1895682 * 2
def baseEnd_1895682 : Nat := 648930689384371579437949

theorem tailTrace_1895682 : CollatzResearch.WordTrace tailWord_1895682 prefixEnd_1895682 648930689384371579437949 := by
  unfold tailWord_1895682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17285300679568836388780325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46094135145516897036747533 17285300679568836388780325)
  ·
    refine ⟨3240993877419156822896311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17285300679568836388780325 3240993877419156822896311)
    ·
      refine ⟨4861490816128735234344467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3240993877419156822896311 4861490816128735234344467)
      ·
        refine ⟨7292236224193102851516701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4861490816128735234344467 7292236224193102851516701)
        ·
          refine ⟨2734588584072413569318763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7292236224193102851516701 2734588584072413569318763)
          ·
            refine ⟨4101882876108620353978145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734588584072413569318763 4101882876108620353978145)
            ·
              refine ⟨3076412157081465265483609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101882876108620353978145 3076412157081465265483609)
              ·
                refine ⟨2307309117811098949112707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076412157081465265483609 2307309117811098949112707)
                ·
                  refine ⟨3460963676716648423669061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307309117811098949112707 3460963676716648423669061)
                  ·
                    refine ⟨648930689384371579437949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3460963676716648423669061 648930689384371579437949)
                    ·
                      rfl

theorem cell22_1895682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1895682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895682 prefixEnd_1895682 := by exact prefixLift 1895682
  have htrace : WordTrace (prefixWord ++ tailWord_1895682) baseStart_1895682 baseEnd_1895682 := by
    simpa [prefixWord, tailWord_1895682, baseEnd_1895682] using wordTrace_append hprefix tailTrace_1895682
  have hstable : (prefixWord ++ tailWord_1895682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895682).length < 2 ^ (prefixWord ++ tailWord_1895682).sum := by decide
  have hdescent : baseEnd_1895682 < baseStart_1895682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895691 : List Nat := [1, 1, 1, 1, 5, 4, 1, 8]
def baseStart_1895691 : Nat := 118140960795 + 1895691 * 2 ^ 59
def prefixEnd_1895691 : Nat := 4983230072969 + 3 ^ 40 * 1895691 * 2
def baseEnd_1895691 : Nat := 72103752252033172884769

theorem tailTrace_1895691 : CollatzResearch.WordTrace tailWord_1895691 prefixEnd_1895691 72103752252033172884769 := by
  unfold tailWord_1895691
  simp only [CollatzResearch.WordTrace]
  refine ⟨69141530975242740092198927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46094353983495160061465951 69141530975242740092198927)
  ·
    refine ⟨103712296462864110138298391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69141530975242740092198927 103712296462864110138298391)
    ·
      refine ⟨155568444694296165207447587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103712296462864110138298391 155568444694296165207447587)
      ·
        refine ⟨233352667041444247811171381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155568444694296165207447587 233352667041444247811171381)
        ·
          refine ⟨21876812535135398232297317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233352667041444247811171381 21876812535135398232297317)
          ·
            refine ⟨4101902350337887168555747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21876812535135398232297317 4101902350337887168555747)
            ·
              refine ⟨6152853525506830752833621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101902350337887168555747 6152853525506830752833621)
              ·
                refine ⟨72103752252033172884769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6152853525506830752833621 72103752252033172884769)
                ·
                  rfl

theorem cell22_1895691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 8].length) (baseStart_1895691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895691 prefixEnd_1895691 := by exact prefixLift 1895691
  have htrace : WordTrace (prefixWord ++ tailWord_1895691) baseStart_1895691 baseEnd_1895691 := by
    simpa [prefixWord, tailWord_1895691, baseEnd_1895691] using wordTrace_append hprefix tailTrace_1895691
  have hstable : (prefixWord ++ tailWord_1895691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895691).length < 2 ^ (prefixWord ++ tailWord_1895691).sum := by decide
  have hdescent : baseEnd_1895691 < baseStart_1895691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895725 : List Nat := [1, 5, 3, 1, 1, 2, 2, 7]
def baseStart_1895725 : Nat := 118140960795 + 1895725 * 2 ^ 59
def prefixEnd_1895725 : Nat := 4983230072969 + 3 ^ 40 * 1895725 * 2
def baseEnd_1895725 : Nat := 72105045462570422290313

theorem tailTrace_1895725 : CollatzResearch.WordTrace tailWord_1895725 prefixEnd_1895725 72105045462570422290313 := by
  unfold tailWord_1895725
  simp only [CollatzResearch.WordTrace]
  refine ⟨69142771057119563898936629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46095180704746375932624419 69142771057119563898936629)
  ·
    refine ⟨6482134786604959115525309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69142771057119563898936629 6482134786604959115525309)
    ·
      refine ⟨2430800544976859668321991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6482134786604959115525309 2430800544976859668321991)
      ·
        refine ⟨3646200817465289502482987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430800544976859668321991 3646200817465289502482987)
        ·
          refine ⟨5469301226197934253724481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3646200817465289502482987 5469301226197934253724481)
          ·
            refine ⟨4101975919648450690293361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5469301226197934253724481 4101975919648450690293361)
            ·
              refine ⟨3076481939736338017720021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101975919648450690293361 3076481939736338017720021)
              ·
                refine ⟨72105045462570422290313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3076481939736338017720021 72105045462570422290313)
                ·
                  rfl

theorem cell22_1895725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 7].length) (baseStart_1895725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895725 prefixEnd_1895725 := by exact prefixLift 1895725
  have htrace : WordTrace (prefixWord ++ tailWord_1895725) baseStart_1895725 baseEnd_1895725 := by
    simpa [prefixWord, tailWord_1895725, baseEnd_1895725] using wordTrace_append hprefix tailTrace_1895725
  have hstable : (prefixWord ++ tailWord_1895725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895725).length < 2 ^ (prefixWord ++ tailWord_1895725).sum := by decide
  have hdescent : baseEnd_1895725 < baseStart_1895725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895813 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_1895813 : Nat := 118140960795 + 1895813 * 2 ^ 59
def prefixEnd_1895813 : Nat := 4983230072969 + 3 ^ 40 * 1895813 * 2
def baseEnd_1895813 : Nat := 648975533361530904412547

theorem tailTrace_1895813 : CollatzResearch.WordTrace tailWord_1895813 prefixEnd_1895813 648975533361530904412547 := by
  unfold tailWord_1895813
  simp only [CollatzResearch.WordTrace]
  refine ⟨69145980680800754928140093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46097320453867169952093395 69145980680800754928140093)
  ·
    refine ⟨25929742755300283098052535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69145980680800754928140093 25929742755300283098052535)
    ·
      refine ⟨38894614132950424647078803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25929742755300283098052535 38894614132950424647078803)
      ·
        refine ⟨58341921199425636970618205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38894614132950424647078803 58341921199425636970618205)
        ·
          refine ⟨21878220449784613863981827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58341921199425636970618205 21878220449784613863981827)
          ·
            refine ⟨32817330674676920795972741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21878220449784613863981827 32817330674676920795972741)
            ·
              refine ⟨6153249501501922649244889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32817330674676920795972741 6153249501501922649244889)
              ·
                refine ⟨4614937126126441986933667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6153249501501922649244889 4614937126126441986933667)
                ·
                  refine ⟨6922405689189662980400501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614937126126441986933667 6922405689189662980400501)
                  ·
                    refine ⟨648975533361530904412547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6922405689189662980400501 648975533361530904412547)
                    ·
                      rfl

theorem cell22_1895813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_1895813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895813 prefixEnd_1895813 := by exact prefixLift 1895813
  have htrace : WordTrace (prefixWord ++ tailWord_1895813) baseStart_1895813 baseEnd_1895813 := by
    simpa [prefixWord, tailWord_1895813, baseEnd_1895813] using wordTrace_append hprefix tailTrace_1895813
  have hstable : (prefixWord ++ tailWord_1895813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895813).length < 2 ^ (prefixWord ++ tailWord_1895813).sum := by decide
  have hdescent : baseEnd_1895813 < baseStart_1895813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895815 : List Nat := [1, 1, 4, 2, 2, 2, 1, 5, 4]
def baseStart_1895815 : Nat := 118140960795 + 1895815 * 2 ^ 59
def prefixEnd_1895815 : Nat := 4983230072969 + 3 ^ 40 * 1895815 * 2
def baseEnd_1895815 : Nat := 216325406000801188620847

theorem tailTrace_1895815 : CollatzResearch.WordTrace tailWord_1895815 prefixEnd_1895815 216325406000801188620847 := by
  unfold tailWord_1895815
  simp only [CollatzResearch.WordTrace]
  refine ⟨69146053626793509269712899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46097369084529006179808599 69146053626793509269712899)
  ·
    refine ⟨103719080440190263904569349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69146053626793509269712899 103719080440190263904569349)
    ·
      refine ⟨19447327582535674482106753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103719080440190263904569349 19447327582535674482106753)
      ·
        refine ⟨14585495686901755861580065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19447327582535674482106753 14585495686901755861580065)
        ·
          refine ⟨10939121765176316896185049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14585495686901755861580065 10939121765176316896185049)
          ·
            refine ⟨8204341323882237672138787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10939121765176316896185049 8204341323882237672138787)
            ·
              refine ⟨12306511985823356508208181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8204341323882237672138787 12306511985823356508208181)
              ·
                refine ⟨1153735498670939672644517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12306511985823356508208181 1153735498670939672644517)
                ·
                  refine ⟨216325406000801188620847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153735498670939672644517 216325406000801188620847)
                  ·
                    rfl

theorem cell22_1895815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 4].length) (baseStart_1895815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895815 prefixEnd_1895815 := by exact prefixLift 1895815
  have htrace : WordTrace (prefixWord ++ tailWord_1895815) baseStart_1895815 baseEnd_1895815 := by
    simpa [prefixWord, tailWord_1895815, baseEnd_1895815] using wordTrace_append hprefix tailTrace_1895815
  have hstable : (prefixWord ++ tailWord_1895815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895815).length < 2 ^ (prefixWord ++ tailWord_1895815).sum := by decide
  have hdescent : baseEnd_1895815 < baseStart_1895815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895903 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 1, 7]
def baseStart_1895903 : Nat := 118140960795 + 1895903 * 2 ^ 59
def prefixEnd_1895903 : Nat := 4983230072969 + 3 ^ 40 * 1895903 * 2
def baseEnd_1895903 : Nat := 649006342200800669662271

theorem tailTrace_1895903 : CollatzResearch.WordTrace tailWord_1895903 prefixEnd_1895903 649006342200800669662271 := by
  unfold tailWord_1895903
  simp only [CollatzResearch.WordTrace]
  refine ⟨69149263250474700298916363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46099508833649800199277575 69149263250474700298916363)
  ·
    refine ⟨103723894875712050448374545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69149263250474700298916363 103723894875712050448374545)
    ·
      refine ⟨77792921156784037836280909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103723894875712050448374545 77792921156784037836280909)
      ·
        refine ⟨29172345433794014188605341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77792921156784037836280909 29172345433794014188605341)
        ·
          refine ⟨10939629537672755320727003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29172345433794014188605341 10939629537672755320727003)
          ·
            refine ⟨16409444306509132981090505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10939629537672755320727003 16409444306509132981090505)
            ·
              refine ⟨12307083229881849735817879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16409444306509132981090505 12307083229881849735817879)
              ·
                refine ⟨18460624844822774603726819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307083229881849735817879 18460624844822774603726819)
                ·
                  refine ⟨27690937267234161905590229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18460624844822774603726819 27690937267234161905590229)
                  ·
                    refine ⟨649006342200800669662271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27690937267234161905590229 649006342200800669662271)
                    ·
                      rfl

theorem cell22_1895903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_1895903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895903 prefixEnd_1895903 := by exact prefixLift 1895903
  have htrace : WordTrace (prefixWord ++ tailWord_1895903) baseStart_1895903 baseEnd_1895903 := by
    simpa [prefixWord, tailWord_1895903, baseEnd_1895903] using wordTrace_append hprefix tailTrace_1895903
  have hstable : (prefixWord ++ tailWord_1895903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895903).length < 2 ^ (prefixWord ++ tailWord_1895903).sum := by decide
  have hdescent : baseEnd_1895903 < baseStart_1895903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895905 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 5]
def baseStart_1895905 : Nat := 118140960795 + 1895905 * 2 ^ 59
def prefixEnd_1895905 : Nat := 4983230072969 + 3 ^ 40 * 1895905 * 2
def baseEnd_1895905 : Nat := 216335675613891110370755

theorem tailTrace_1895905 : CollatzResearch.WordTrace tailWord_1895905 prefixEnd_1895905 216335675613891110370755 := by
  unfold tailWord_1895905
  simp only [CollatzResearch.WordTrace]
  refine ⟨69149336196467454640489169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46099557464311636426992779 69149336196467454640489169)
  ·
    refine ⟨51862002147350590980366877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69149336196467454640489169 51862002147350590980366877)
    ·
      refine ⟨19448250805256471617637579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51862002147350590980366877 19448250805256471617637579)
      ·
        refine ⟨29172376207884707426456369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19448250805256471617637579 29172376207884707426456369)
        ·
          refine ⟨21879282155913530569842277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29172376207884707426456369 21879282155913530569842277)
          ·
            refine ⟨4102365404233786981845427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21879282155913530569842277 4102365404233786981845427)
            ·
              refine ⟨6153548106350680472768141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4102365404233786981845427 6153548106350680472768141)
              ·
                refine ⟨2307580539881505177288053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6153548106350680472768141 2307580539881505177288053)
                ·
                  refine ⟨216335675613891110370755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2307580539881505177288053 216335675613891110370755)
                  ·
                    rfl

theorem cell22_1895905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_1895905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895905 prefixEnd_1895905 := by exact prefixLift 1895905
  have htrace : WordTrace (prefixWord ++ tailWord_1895905) baseStart_1895905 baseEnd_1895905 := by
    simpa [prefixWord, tailWord_1895905, baseEnd_1895905] using wordTrace_append hprefix tailTrace_1895905
  have hstable : (prefixWord ++ tailWord_1895905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895905).length < 2 ^ (prefixWord ++ tailWord_1895905).sum := by decide
  have hdescent : baseEnd_1895905 < baseStart_1895905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895982 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1895982 : Nat := 118140960795 + 1895982 * 2 ^ 59
def prefixEnd_1895982 : Nat := 4983230072969 + 3 ^ 40 * 1895982 * 2
def baseEnd_1895982 : Nat := 649033385515270796937029

theorem tailTrace_1895982 : CollatzResearch.WordTrace tailWord_1895982 prefixEnd_1895982 649033385515270796937029 := by
  unfold tailWord_1895982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8644018077148562098880275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46101429744792331194028133 8644018077148562098880275)
  ·
    refine ⟨12966027115722843148320413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8644018077148562098880275 12966027115722843148320413)
    ·
      refine ⟨4862260168396066180620155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12966027115722843148320413 4862260168396066180620155)
      ·
        refine ⟨7293390252594099270930233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862260168396066180620155 7293390252594099270930233)
        ·
          refine ⟨5470042689445574453197675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7293390252594099270930233 5470042689445574453197675)
          ·
            refine ⟨8205064034168361679796513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470042689445574453197675 8205064034168361679796513)
            ·
              refine ⟨6153798025626271259847385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8205064034168361679796513 6153798025626271259847385)
              ·
                refine ⟨4615348519219703444885539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6153798025626271259847385 4615348519219703444885539)
                ·
                  refine ⟨6923022778829555167328309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4615348519219703444885539 6923022778829555167328309)
                  ·
                    refine ⟨649033385515270796937029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6923022778829555167328309 649033385515270796937029)
                    ·
                      rfl

theorem cell22_1895982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1895982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895982 prefixEnd_1895982 := by exact prefixLift 1895982
  have htrace : WordTrace (prefixWord ++ tailWord_1895982) baseStart_1895982 baseEnd_1895982 := by
    simpa [prefixWord, tailWord_1895982, baseEnd_1895982] using wordTrace_append hprefix tailTrace_1895982
  have hstable : (prefixWord ++ tailWord_1895982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895982).length < 2 ^ (prefixWord ++ tailWord_1895982).sum := by decide
  have hdescent : baseEnd_1895982 < baseStart_1895982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895999 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 2, 3]
def baseStart_1895999 : Nat := 118140960795 + 1895999 * 2 ^ 59
def prefixEnd_1895999 : Nat := 4983230072969 + 3 ^ 40 * 1895999 * 2
def baseEnd_1895999 : Nat := 649039204962688419261977

theorem tailTrace_1895999 : CollatzResearch.WordTrace tailWord_1895999 prefixEnd_1895999 649039204962688419261977 := by
  unfold tailWord_1895999
  simp only [CollatzResearch.WordTrace]
  refine ⟨69152764658126908694411051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46101843105417939129607367 69152764658126908694411051)
  ·
    refine ⟨103729146987190363041616577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69152764658126908694411051 103729146987190363041616577)
    ·
      refine ⟨77796860240392772281212433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103729146987190363041616577 77796860240392772281212433)
      ·
        refine ⟨58347645180294579210909325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77796860240392772281212433 58347645180294579210909325)
        ·
          refine ⟨21880366942610467204090997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58347645180294579210909325 21880366942610467204090997)
          ·
            refine ⟨2051284400869731300383531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21880366942610467204090997 2051284400869731300383531)
            ·
              refine ⟨3076926601304596950575297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051284400869731300383531 3076926601304596950575297)
              ·
                refine ⟨2307694950978447712931473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076926601304596950575297 2307694950978447712931473)
                ·
                  refine ⟨1730771213233835784698605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307694950978447712931473 1730771213233835784698605)
                  ·
                    refine ⟨649039204962688419261977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1730771213233835784698605 649039204962688419261977)
                    ·
                      rfl

theorem cell22_1895999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_1895999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1895999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1895999 prefixEnd_1895999 := by exact prefixLift 1895999
  have htrace : WordTrace (prefixWord ++ tailWord_1895999) baseStart_1895999 baseEnd_1895999 := by
    simpa [prefixWord, tailWord_1895999, baseEnd_1895999] using wordTrace_append hprefix tailTrace_1895999
  have hstable : (prefixWord ++ tailWord_1895999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895999).length < 2 ^ (prefixWord ++ tailWord_1895999).sum := by decide
  have hdescent : baseEnd_1895999 < baseStart_1895999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896029 : List Nat := [1, 4, 4, 2, 1, 1, 1, 8]
def baseStart_1896029 : Nat := 118140960795 + 1896029 * 2 ^ 59
def prefixEnd_1896029 : Nat := 4983230072969 + 3 ^ 40 * 1896029 * 2
def baseEnd_1896029 : Nat := 72116608286197593445765

theorem tailTrace_1896029 : CollatzResearch.WordTrace tailWord_1896029 prefixEnd_1896029 72116608286197593445765 := by
  unfold tailWord_1896029
  simp only [CollatzResearch.WordTrace]
  refine ⟨69153858848018223818003141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46102572565345482545335427 69153858848018223818003141)
  ·
    refine ⟨12966348534003416965875589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69153858848018223818003141 12966348534003416965875589)
    ·
      refine ⟨2431190350125640681101673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12966348534003416965875589 2431190350125640681101673)
      ·
        refine ⟨1823392762594230510826255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2431190350125640681101673 1823392762594230510826255)
        ·
          refine ⟨2735089143891345766239383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823392762594230510826255 2735089143891345766239383)
          ·
            refine ⟨4102633715837018649359075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735089143891345766239383 4102633715837018649359075)
            ·
              refine ⟨6153950573755527974038613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4102633715837018649359075 6153950573755527974038613)
              ·
                refine ⟨72116608286197593445765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6153950573755527974038613 72116608286197593445765)
                ·
                  rfl

theorem cell22_1896029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 8].length) (baseStart_1896029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896029 prefixEnd_1896029 := by exact prefixLift 1896029
  have htrace : WordTrace (prefixWord ++ tailWord_1896029) baseStart_1896029 baseEnd_1896029 := by
    simpa [prefixWord, tailWord_1896029, baseEnd_1896029] using wordTrace_append hprefix tailTrace_1896029
  have hstable : (prefixWord ++ tailWord_1896029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896029).length < 2 ^ (prefixWord ++ tailWord_1896029).sum := by decide
  have hdescent : baseEnd_1896029 < baseStart_1896029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896074 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_1896074 : Nat := 118140960795 + 1896074 * 2 ^ 59
def prefixEnd_1896074 : Nat := 4983230072969 + 3 ^ 40 * 1896074 * 2
def baseEnd_1896074 : Nat := 216354959665137741212249

theorem tailTrace_1896074 : CollatzResearch.WordTrace tailWord_1896074 prefixEnd_1896074 216354959665137741212249 := by
  unfold tailWord_1896074
  simp only [CollatzResearch.WordTrace]
  refine ⟨17288875033213799125847819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46103666755236797668927517 17288875033213799125847819)
  ·
    refine ⟨25933312549820698688771729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17288875033213799125847819 25933312549820698688771729)
    ·
      refine ⟨19449984412365524016578797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25933312549820698688771729 19449984412365524016578797)
      ·
        refine ⟨7293744154637071506217049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19449984412365524016578797 7293744154637071506217049)
        ·
          refine ⟨5470308115977803629662787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7293744154637071506217049 5470308115977803629662787)
          ·
            refine ⟨8205462173966705444494181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470308115977803629662787 8205462173966705444494181)
            ·
              refine ⟨1538524157618757270842659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8205462173966705444494181 1538524157618757270842659)
              ·
                refine ⟨2307786236428135906263989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538524157618757270842659 2307786236428135906263989)
                ·
                  refine ⟨216354959665137741212249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2307786236428135906263989 216354959665137741212249)
                  ·
                    rfl

theorem cell22_1896074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_1896074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896074 prefixEnd_1896074 := by exact prefixLift 1896074
  have htrace : WordTrace (prefixWord ++ tailWord_1896074) baseStart_1896074 baseEnd_1896074 := by
    simpa [prefixWord, tailWord_1896074, baseEnd_1896074] using wordTrace_append hprefix tailTrace_1896074
  have hstable : (prefixWord ++ tailWord_1896074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896074).length < 2 ^ (prefixWord ++ tailWord_1896074).sum := by decide
  have hdescent : baseEnd_1896074 < baseStart_1896074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896085 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 6]
def baseStart_1896085 : Nat := 118140960795 + 1896085 * 2 ^ 59
def prefixEnd_1896085 : Nat := 4983230072969 + 3 ^ 40 * 1896085 * 2
def baseEnd_1896085 : Nat := 216356214840070953870571

theorem tailTrace_1896085 : CollatzResearch.WordTrace tailWord_1896085 prefixEnd_1896085 216356214840070953870571 := by
  unfold tailWord_1896085
  simp only [CollatzResearch.WordTrace]
  refine ⟨69155901335815345382041709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46103934223876896921361139 69155901335815345382041709)
  ·
    refine ⟨25933463000930754518265641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69155901335815345382041709 25933463000930754518265641)
    ·
      refine ⟨19450097250698065888699231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25933463000930754518265641 19450097250698065888699231)
      ·
        refine ⟨29175145876047098833048847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19450097250698065888699231 29175145876047098833048847)
        ·
          refine ⟨43762718814070648249573271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29175145876047098833048847 43762718814070648249573271)
          ·
            refine ⟨65644078221105972374359907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43762718814070648249573271 65644078221105972374359907)
            ·
              refine ⟨98466117331658958561539861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65644078221105972374359907 98466117331658958561539861)
              ·
                refine ⟨4615599249921513682572181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98466117331658958561539861 4615599249921513682572181)
                ·
                  refine ⟨216356214840070953870571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4615599249921513682572181 216356214840070953870571)
                  ·
                    rfl

theorem cell22_1896085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_1896085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896085 prefixEnd_1896085 := by exact prefixLift 1896085
  have htrace : WordTrace (prefixWord ++ tailWord_1896085) baseStart_1896085 baseEnd_1896085 := by
    simpa [prefixWord, tailWord_1896085, baseEnd_1896085] using wordTrace_append hprefix tailTrace_1896085
  have hstable : (prefixWord ++ tailWord_1896085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896085).length < 2 ^ (prefixWord ++ tailWord_1896085).sum := by decide
  have hdescent : baseEnd_1896085 < baseStart_1896085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896087 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 3, 4]
def baseStart_1896087 : Nat := 118140960795 + 1896087 * 2 ^ 59
def prefixEnd_1896087 : Nat := 4983230072969 + 3 ^ 40 * 1896087 * 2
def baseEnd_1896087 : Nat := 649069329161085523061707

theorem tailTrace_1896087 : CollatzResearch.WordTrace tailWord_1896087 prefixEnd_1896087 649069329161085523061707 := by
  unfold tailWord_1896087
  simp only [CollatzResearch.WordTrace]
  refine ⟨69155974281808099723614515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46103982854538733149076343 69155974281808099723614515)
  ·
    refine ⟨103733961422712149585421773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69155974281808099723614515 103733961422712149585421773)
    ·
      refine ⟨38900235533517056094533165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103733961422712149585421773 38900235533517056094533165)
      ·
        refine ⟨14587588325068896035449937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38900235533517056094533165 14587588325068896035449937)
        ·
          refine ⟨10940691243801672026587453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14587588325068896035449937 10940691243801672026587453)
          ·
            refine ⟨4102759216425627009970295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10940691243801672026587453 4102759216425627009970295)
            ·
              refine ⟨6154138824638440514955443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4102759216425627009970295 6154138824638440514955443)
              ·
                refine ⟨9231208236957660772433165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6154138824638440514955443 9231208236957660772433165)
                ·
                  refine ⟨3461703088859122789662437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9231208236957660772433165 3461703088859122789662437)
                  ·
                    refine ⟨649069329161085523061707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3461703088859122789662437 649069329161085523061707)
                    ·
                      rfl

theorem cell22_1896087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_1896087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896087 prefixEnd_1896087 := by exact prefixLift 1896087
  have htrace : WordTrace (prefixWord ++ tailWord_1896087) baseStart_1896087 baseEnd_1896087 := by
    simpa [prefixWord, tailWord_1896087, baseEnd_1896087] using wordTrace_append hprefix tailTrace_1896087
  have hstable : (prefixWord ++ tailWord_1896087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896087).length < 2 ^ (prefixWord ++ tailWord_1896087).sum := by decide
  have hdescent : baseEnd_1896087 < baseStart_1896087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896119 : List Nat := [1, 1, 3, 1, 5, 2, 1, 4, 4]
def baseStart_1896119 : Nat := 118140960795 + 1896119 * 2 ^ 59
def prefixEnd_1896119 : Nat := 4983230072969 + 3 ^ 40 * 1896119 * 2
def baseEnd_1896119 : Nat := 216360094471682702087203

theorem tailTrace_1896119 : CollatzResearch.WordTrace tailWord_1896119 prefixEnd_1896119 216360094471682702087203 := by
  unfold tailWord_1896119
  simp only [CollatzResearch.WordTrace]
  refine ⟨69157141417692169188779411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46104760945128112792519607 69157141417692169188779411)
  ·
    refine ⟨103735712126538253783169117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69157141417692169188779411 103735712126538253783169117)
    ·
      refine ⟨38900892047451845168688419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103735712126538253783169117 38900892047451845168688419)
      ·
        refine ⟨58351338071177767753032629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38900892047451845168688419 58351338071177767753032629)
        ·
          refine ⟨5470437944172915726846809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58351338071177767753032629 5470437944172915726846809)
          ·
            refine ⟨4102828458129686795135107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5470437944172915726846809 4102828458129686795135107)
            ·
              refine ⟨6154242687194530192702661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4102828458129686795135107 6154242687194530192702661)
              ·
                refine ⟨1153920503848974411131749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6154242687194530192702661 1153920503848974411131749)
                ·
                  refine ⟨216360094471682702087203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153920503848974411131749 216360094471682702087203)
                  ·
                    rfl

theorem cell22_1896119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 4].length) (baseStart_1896119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896119 prefixEnd_1896119 := by exact prefixLift 1896119
  have htrace : WordTrace (prefixWord ++ tailWord_1896119) baseStart_1896119 baseEnd_1896119 := by
    simpa [prefixWord, tailWord_1896119, baseEnd_1896119] using wordTrace_append hprefix tailTrace_1896119
  have hstable : (prefixWord ++ tailWord_1896119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896119).length < 2 ^ (prefixWord ++ tailWord_1896119).sum := by decide
  have hdescent : baseEnd_1896119 < baseStart_1896119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896132 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1896132 : Nat := 118140960795 + 1896132 * 2 ^ 59
def prefixEnd_1896132 : Nat := 4983230072969 + 3 ^ 40 * 1896132 * 2
def baseEnd_1896132 : Nat := 649084733580720405686569

theorem tailTrace_1896132 : CollatzResearch.WordTrace tailWord_1896132 prefixEnd_1896132 649084733580720405686569 := by
  unfold tailWord_1896132
  simp only [CollatzResearch.WordTrace]
  refine ⟨34578807783322536204501325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46105077044430048272668433 34578807783322536204501325)
  ·
    refine ⟨12967052918745951076687997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34578807783322536204501325 12967052918745951076687997)
    ·
      refine ⟨4862644844529731653757999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12967052918745951076687997 4862644844529731653757999)
      ·
        refine ⟨7293967266794597480636999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862644844529731653757999 7293967266794597480636999)
        ·
          refine ⟨10940950900191896220955499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7293967266794597480636999 10940950900191896220955499)
          ·
            refine ⟨16411426350287844331433249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10940950900191896220955499 16411426350287844331433249)
            ·
              refine ⟨12308569762715883248574937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16411426350287844331433249 12308569762715883248574937)
              ·
                refine ⟨9231427322036912436431203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12308569762715883248574937 9231427322036912436431203)
                ·
                  refine ⟨13847140983055368654646805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9231427322036912436431203 13847140983055368654646805)
                  ·
                    refine ⟨649084733580720405686569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13847140983055368654646805 649084733580720405686569)
                    ·
                      rfl

theorem cell22_1896132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1896132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896132 prefixEnd_1896132 := by exact prefixLift 1896132
  have htrace : WordTrace (prefixWord ++ tailWord_1896132) baseStart_1896132 baseEnd_1896132 := by
    simpa [prefixWord, tailWord_1896132, baseEnd_1896132] using wordTrace_append hprefix tailTrace_1896132
  have hstable : (prefixWord ++ tailWord_1896132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896132).length < 2 ^ (prefixWord ++ tailWord_1896132).sum := by decide
  have hdescent : baseEnd_1896132 < baseStart_1896132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896213 : List Nat := [1, 3, 2, 1, 2, 5, 1, 3, 1, 3]
def baseStart_1896213 : Nat := 118140960795 + 1896213 * 2 ^ 59
def prefixEnd_1896213 : Nat := 4983230072969 + 3 ^ 40 * 1896213 * 2
def baseEnd_1896213 : Nat := 649112461536063194411321

theorem tailTrace_1896213 : CollatzResearch.WordTrace tailWord_1896213 prefixEnd_1896213 649112461536063194411321 := by
  unfold tailWord_1896213
  simp only [CollatzResearch.WordTrace]
  refine ⟨69160569879351623242701293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46107046586234415495134195 69160569879351623242701293)
  ·
    refine ⟨25935213704756858716012985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69160569879351623242701293 25935213704756858716012985)
    ·
      refine ⟨19451410278567644037009739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25935213704756858716012985 19451410278567644037009739)
      ·
        refine ⟨29177115417851466055514609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19451410278567644037009739 29177115417851466055514609)
        ·
          refine ⟨21882836563388599541635957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29177115417851466055514609 21882836563388599541635957)
          ·
            refine ⟨2051515927817681207028371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21882836563388599541635957 2051515927817681207028371)
            ·
              refine ⟨3077273891726521810542557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051515927817681207028371 3077273891726521810542557)
              ·
                refine ⟨1153977709397445678953459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3077273891726521810542557 1153977709397445678953459)
                ·
                  refine ⟨1730966564096168518430189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153977709397445678953459 1730966564096168518430189)
                  ·
                    refine ⟨649112461536063194411321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1730966564096168518430189 649112461536063194411321)
                    ·
                      rfl

theorem cell22_1896213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_1896213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896213 prefixEnd_1896213 := by exact prefixLift 1896213
  have htrace : WordTrace (prefixWord ++ tailWord_1896213) baseStart_1896213 baseEnd_1896213 := by
    simpa [prefixWord, tailWord_1896213, baseEnd_1896213] using wordTrace_append hprefix tailTrace_1896213
  have hstable : (prefixWord ++ tailWord_1896213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896213).length < 2 ^ (prefixWord ++ tailWord_1896213).sum := by decide
  have hdescent : baseEnd_1896213 < baseStart_1896213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896243 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 5]
def baseStart_1896243 : Nat := 118140960795 + 1896243 * 2 ^ 59
def prefixEnd_1896243 : Nat := 4983230072969 + 3 ^ 40 * 1896243 * 2
def baseEnd_1896243 : Nat := 216374243716384372053743

theorem tailTrace_1896243 : CollatzResearch.WordTrace tailWord_1896243 prefixEnd_1896243 216374243716384372053743 := by
  unfold tailWord_1896243
  simp only [CollatzResearch.WordTrace]
  refine ⟨69161664069242938366293383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46107776046161958910862255 69161664069242938366293383)
  ·
    refine ⟨103742496103864407549440075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69161664069242938366293383 103742496103864407549440075)
    ·
      refine ⟨155613744155796611324160113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103742496103864407549440075 155613744155796611324160113)
      ·
        refine ⟨116710308116847458493120085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155613744155796611324160113 116710308116847458493120085)
        ·
          refine ⟨1367698923244306154216251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 116710308116847458493120085 1367698923244306154216251)
          ·
            refine ⟨2051548384866459231324377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367698923244306154216251 2051548384866459231324377)
            ·
              refine ⟨1538661288649844423493283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051548384866459231324377 1538661288649844423493283)
              ·
                refine ⟨2307991932974766635239925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538661288649844423493283 2307991932974766635239925)
                ·
                  refine ⟨216374243716384372053743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2307991932974766635239925 216374243716384372053743)
                  ·
                    rfl

theorem cell22_1896243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 5].length) (baseStart_1896243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896243 prefixEnd_1896243 := by exact prefixLift 1896243
  have htrace : WordTrace (prefixWord ++ tailWord_1896243) baseStart_1896243 baseEnd_1896243 := by
    simpa [prefixWord, tailWord_1896243, baseEnd_1896243] using wordTrace_append hprefix tailTrace_1896243
  have hstable : (prefixWord ++ tailWord_1896243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896243).length < 2 ^ (prefixWord ++ tailWord_1896243).sum := by decide
  have hdescent : baseEnd_1896243 < baseStart_1896243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896288 : List Nat := [2, 1, 1, 3, 3, 4, 2, 2, 4]
def baseStart_1896288 : Nat := 118140960795 + 1896288 * 2 ^ 59
def prefixEnd_1896288 : Nat := 4983230072969 + 3 ^ 40 * 1896288 * 2
def baseEnd_1896288 : Nat := 216379378522929332928697

theorem tailTrace_1896288 : CollatzResearch.WordTrace tailWord_1896288 prefixEnd_1896288 216379378522929332928697 := by
  unfold tailWord_1896288
  simp only [CollatzResearch.WordTrace]
  refine ⟨34581652677039955525840759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46108870236053274034454345 34581652677039955525840759)
  ·
    refine ⟨51872479015559933288761139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34581652677039955525840759 51872479015559933288761139)
    ·
      refine ⟨77808718523339899933141709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51872479015559933288761139 77808718523339899933141709)
      ·
        refine ⟨29178269446252462474928141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77808718523339899933141709 29178269446252462474928141)
        ·
          refine ⟨10941851042344673428098053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29178269446252462474928141 10941851042344673428098053)
          ·
            refine ⟨2051597070439626267768385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10941851042344673428098053 2051597070439626267768385)
            ·
              refine ⟨1538697802829719700826289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051597070439626267768385 1538697802829719700826289)
              ·
                refine ⟨1154023352122289775619717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538697802829719700826289 1154023352122289775619717)
                ·
                  refine ⟨216379378522929332928697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1154023352122289775619717 216379378522929332928697)
                  ·
                    rfl

theorem cell22_1896288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 4].length) (baseStart_1896288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896288 prefixEnd_1896288 := by exact prefixLift 1896288
  have htrace : WordTrace (prefixWord ++ tailWord_1896288) baseStart_1896288 baseEnd_1896288 := by
    simpa [prefixWord, tailWord_1896288, baseEnd_1896288] using wordTrace_append hprefix tailTrace_1896288
  have hstable : (prefixWord ++ tailWord_1896288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896288).length < 2 ^ (prefixWord ++ tailWord_1896288).sum := by decide
  have hdescent : baseEnd_1896288 < baseStart_1896288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896314 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_1896314 : Nat := 118140960795 + 1896314 * 2 ^ 59
def prefixEnd_1896314 : Nat := 4983230072969 + 3 ^ 40 * 1896314 * 2
def baseEnd_1896314 : Nat := 649147035900132597636011

theorem tailTrace_1896314 : CollatzResearch.WordTrace tailWord_1896314 prefixEnd_1896314 649147035900132597636011 := by
  unfold tailWord_1896314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17291063412996429373031999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46109502434657144994751997 17291063412996429373031999)
  ·
    refine ⟨25936595119494644059547999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17291063412996429373031999 25936595119494644059547999)
    ·
      refine ⟨38904892679241966089321999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25936595119494644059547999 38904892679241966089321999)
      ·
        refine ⟨58357339018862949133982999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38904892679241966089321999 58357339018862949133982999)
        ·
          refine ⟨87536008528294423700974499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58357339018862949133982999 87536008528294423700974499)
          ·
            refine ⟨131304012792441635551461749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87536008528294423700974499 131304012792441635551461749)
            ·
              refine ⟨12309751199291403332949539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131304012792441635551461749 12309751199291403332949539)
              ·
                refine ⟨18464626798937104999424309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12309751199291403332949539 18464626798937104999424309)
                ·
                  refine ⟨1731058762400353593696029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18464626798937104999424309 1731058762400353593696029)
                  ·
                    refine ⟨649147035900132597636011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731058762400353593696029 649147035900132597636011)
                    ·
                      rfl

theorem cell22_1896314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_1896314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896314 prefixEnd_1896314 := by exact prefixLift 1896314
  have htrace : WordTrace (prefixWord ++ tailWord_1896314) baseStart_1896314 baseEnd_1896314 := by
    simpa [prefixWord, tailWord_1896314, baseEnd_1896314] using wordTrace_append hprefix tailTrace_1896314
  have hstable : (prefixWord ++ tailWord_1896314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896314).length < 2 ^ (prefixWord ++ tailWord_1896314).sum := by decide
  have hdescent : baseEnd_1896314 < baseStart_1896314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896318 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1896318 : Nat := 118140960795 + 1896318 * 2 ^ 59
def prefixEnd_1896318 : Nat := 4983230072969 + 3 ^ 40 * 1896318 * 2
def baseEnd_1896318 : Nat := 649148405181877920535999

theorem tailTrace_1896318 : CollatzResearch.WordTrace tailWord_1896318 prefixEnd_1896318 649148405181877920535999 := by
  unfold tailWord_1896318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8645549942996403271909201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46109599695980817450182405 8645549942996403271909201)
  ·
    refine ⟨6484162457247302453931901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8645549942996403271909201 6484162457247302453931901)
    ·
      refine ⟨2431560921467738420224463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6484162457247302453931901 2431560921467738420224463)
      ·
        refine ⟨3647341382201607630336695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431560921467738420224463 3647341382201607630336695)
        ·
          refine ⟨5471012073302411445505043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3647341382201607630336695 5471012073302411445505043)
          ·
            refine ⟨8206518109953617168257565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471012073302411445505043 8206518109953617168257565)
            ·
              refine ⟨3077444291232606438096587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8206518109953617168257565 3077444291232606438096587)
              ·
                refine ⟨4616166436848909657144881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3077444291232606438096587 4616166436848909657144881)
                ·
                  refine ⟨3462124827636682242858661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4616166436848909657144881 3462124827636682242858661)
                  ·
                    refine ⟨649148405181877920535999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3462124827636682242858661 649148405181877920535999)
                    ·
                      rfl

theorem cell22_1896318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1896318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896318 prefixEnd_1896318 := by exact prefixLift 1896318
  have htrace : WordTrace (prefixWord ++ tailWord_1896318) baseStart_1896318 baseEnd_1896318 := by
    simpa [prefixWord, tailWord_1896318, baseEnd_1896318] using wordTrace_append hprefix tailTrace_1896318
  have hstable : (prefixWord ++ tailWord_1896318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896318).length < 2 ^ (prefixWord ++ tailWord_1896318).sum := by decide
  have hdescent : baseEnd_1896318 < baseStart_1896318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896348 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1896348 : Nat := 118140960795 + 1896348 * 2 ^ 59
def prefixEnd_1896348 : Nat := 4983230072969 + 3 ^ 40 * 1896348 * 2
def baseEnd_1896348 : Nat := 649158674794967842285907

theorem tailTrace_1896348 : CollatzResearch.WordTrace tailWord_1896348 prefixEnd_1896348 649158674794967842285907 := by
  unfold tailWord_1896348
  simp only [CollatzResearch.WordTrace]
  refine ⟨34582746866931270649432849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46110329155908360865910465 34582746866931270649432849)
  ·
    refine ⟨25937060150198452987074637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34582746866931270649432849 25937060150198452987074637)
    ·
      refine ⟨9726397556324419870152989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25937060150198452987074637 9726397556324419870152989)
      ·
        refine ⟨3647399083621657451307371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9726397556324419870152989 3647399083621657451307371)
        ·
          refine ⟨5471098625432486176961057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3647399083621657451307371 5471098625432486176961057)
          ·
            refine ⟨4103323969074364632720793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5471098625432486176961057 4103323969074364632720793)
            ·
              refine ⟨3077492976805773474540595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4103323969074364632720793 3077492976805773474540595)
              ·
                refine ⟨4616239465208660211810893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3077492976805773474540595 4616239465208660211810893)
                ·
                  refine ⟨1731089799453247579429085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4616239465208660211810893 1731089799453247579429085)
                  ·
                    refine ⟨649158674794967842285907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731089799453247579429085 649158674794967842285907)
                    ·
                      rfl

theorem cell22_1896348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1896348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896348 prefixEnd_1896348 := by exact prefixLift 1896348
  have htrace : WordTrace (prefixWord ++ tailWord_1896348) baseStart_1896348 baseEnd_1896348 := by
    simpa [prefixWord, tailWord_1896348, baseEnd_1896348] using wordTrace_append hprefix tailTrace_1896348
  have hstable : (prefixWord ++ tailWord_1896348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896348).length < 2 ^ (prefixWord ++ tailWord_1896348).sum := by decide
  have hdescent : baseEnd_1896348 < baseStart_1896348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896438 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_1896438 : Nat := 118140960795 + 1896438 * 2 ^ 59
def prefixEnd_1896438 : Nat := 4983230072969 + 3 ^ 40 * 1896438 * 2
def baseEnd_1896438 : Nat := 649189483634237607535631

theorem tailTrace_1896438 : CollatzResearch.WordTrace tailWord_1896438 prefixEnd_1896438 649189483634237607535631 := by
  unfold tailWord_1896438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4323048518971030416852623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46112517535690991113094645 4323048518971030416852623)
  ·
    refine ⟨6484572778456545625278935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4323048518971030416852623 6484572778456545625278935)
    ·
      refine ⟨9726859167684818437918403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6484572778456545625278935 9726859167684818437918403)
      ·
        refine ⟨14590288751527227656877605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9726859167684818437918403 14590288751527227656877605)
        ·
          refine ⟨2735679140911355185664551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14590288751527227656877605 2735679140911355185664551)
          ·
            refine ⟨4103518711367032778496827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735679140911355185664551 4103518711367032778496827)
            ·
              refine ⟨6155278067050549167745241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103518711367032778496827 6155278067050549167745241)
              ·
                refine ⟨4616458550287911875808931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6155278067050549167745241 4616458550287911875808931)
                ·
                  refine ⟨6924687825431867813713397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4616458550287911875808931 6924687825431867813713397)
                  ·
                    refine ⟨649189483634237607535631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6924687825431867813713397 649189483634237607535631)
                    ·
                      rfl

theorem cell22_1896438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_1896438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896438 prefixEnd_1896438 := by exact prefixLift 1896438
  have htrace : WordTrace (prefixWord ++ tailWord_1896438) baseStart_1896438 baseEnd_1896438 := by
    simpa [prefixWord, tailWord_1896438, baseEnd_1896438] using wordTrace_append hprefix tailTrace_1896438
  have hstable : (prefixWord ++ tailWord_1896438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896438).length < 2 ^ (prefixWord ++ tailWord_1896438).sum := by decide
  have hdescent : baseEnd_1896438 < baseStart_1896438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896487 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1896487 : Nat := 118140960795 + 1896487 * 2 ^ 59
def prefixEnd_1896487 : Nat := 4983230072969 + 3 ^ 40 * 1896487 * 2
def baseEnd_1896487 : Nat := 649206257335617813060481

theorem tailTrace_1896487 : CollatzResearch.WordTrace tailWord_1896487 prefixEnd_1896487 649206257335617813060481 := by
  unfold tailWord_1896487
  simp only [CollatzResearch.WordTrace]
  refine ⟨69170563480358968038175715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46113708986905978692117143 69170563480358968038175715)
  ·
    refine ⟨103755845220538452057263573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69170563480358968038175715 103755845220538452057263573)
    ·
      refine ⟨2431777622356369970092115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 103755845220538452057263573 2431777622356369970092115)
      ·
        refine ⟨3647666433534554955138173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431777622356369970092115 3647666433534554955138173)
        ·
          refine ⟨1367874912575458108176815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3647666433534554955138173 1367874912575458108176815)
          ·
            refine ⟨2051812368863187162265223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367874912575458108176815 2051812368863187162265223)
            ·
              refine ⟨3077718553294780743397835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051812368863187162265223 3077718553294780743397835)
              ·
                refine ⟨4616577829942171115096753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3077718553294780743397835 4616577829942171115096753)
                ·
                  refine ⟨3462433372456628336322565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4616577829942171115096753 3462433372456628336322565)
                  ·
                    refine ⟨649206257335617813060481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3462433372456628336322565 649206257335617813060481)
                    ·
                      rfl

theorem cell22_1896487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1896487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896487 prefixEnd_1896487 := by exact prefixLift 1896487
  have htrace : WordTrace (prefixWord ++ tailWord_1896487) baseStart_1896487 baseEnd_1896487 := by
    simpa [prefixWord, tailWord_1896487, baseEnd_1896487] using wordTrace_append hprefix tailTrace_1896487
  have hstable : (prefixWord ++ tailWord_1896487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896487).length < 2 ^ (prefixWord ++ tailWord_1896487).sum := by decide
  have hdescent : baseEnd_1896487 < baseStart_1896487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896513 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 5]
def baseStart_1896513 : Nat := 118140960795 + 1896513 * 2 ^ 59
def prefixEnd_1896513 : Nat := 4983230072969 + 3 ^ 40 * 1896513 * 2
def baseEnd_1896513 : Nat := 216405052555654137303467

theorem tailTrace_1896513 : CollatzResearch.WordTrace tailWord_1896513 prefixEnd_1896513 216405052555654137303467 := by
  unfold tailWord_1896513
  simp only [CollatzResearch.WordTrace]
  refine ⟨69171511778264774478622193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46114341185509849652414795 69171511778264774478622193)
  ·
    refine ⟨51878633833698580858966645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69171511778264774478622193 51878633833698580858966645)
    ·
      refine ⟨4863621921909241955528123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51878633833698580858966645 4863621921909241955528123)
      ·
        refine ⟨7295432882863862933292185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863621921909241955528123 7295432882863862933292185)
        ·
          refine ⟨5471574662147897199969139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7295432882863862933292185 5471574662147897199969139)
          ·
            refine ⟨8207361993221845799953709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471574662147897199969139 8207361993221845799953709)
            ·
              refine ⟨3077760747458192174982641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8207361993221845799953709 3077760747458192174982641)
              ·
                refine ⟨2308320560593644131236981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3077760747458192174982641 2308320560593644131236981)
                ·
                  refine ⟨216405052555654137303467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2308320560593644131236981 216405052555654137303467)
                  ·
                    rfl

theorem cell22_1896513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_1896513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896513 prefixEnd_1896513 := by exact prefixLift 1896513
  have htrace : WordTrace (prefixWord ++ tailWord_1896513) baseStart_1896513 baseEnd_1896513 := by
    simpa [prefixWord, tailWord_1896513, baseEnd_1896513] using wordTrace_append hprefix tailTrace_1896513
  have hstable : (prefixWord ++ tailWord_1896513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896513).length < 2 ^ (prefixWord ++ tailWord_1896513).sum := by decide
  have hdescent : baseEnd_1896513 < baseStart_1896513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896530 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_1896530 : Nat := 118140960795 + 1896530 * 2 ^ 59
def prefixEnd_1896530 : Nat := 4983230072969 + 3 ^ 40 * 1896530 * 2
def baseEnd_1896530 : Nat := 216406992371460011411783

theorem tailTrace_1896530 : CollatzResearch.WordTrace tailWord_1896530 prefixEnd_1896530 216406992371460011411783 := by
  unfold tailWord_1896530
  simp only [CollatzResearch.WordTrace]
  refine ⟨17293032954800796595497761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46114754546135457587994029 17293032954800796595497761)
  ·
    refine ⟨12969774716100597446623321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17293032954800796595497761 12969774716100597446623321)
    ·
      refine ⟨9727331037075448084967491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12969774716100597446623321 9727331037075448084967491)
      ·
        refine ⟨14590996555613172127451237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9727331037075448084967491 14590996555613172127451237)
        ·
          refine ⟨2735811854177469773897107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14590996555613172127451237 2735811854177469773897107)
          ·
            refine ⟨4103717781266204660845661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735811854177469773897107 4103717781266204660845661)
            ·
              refine ⟨1538894167974826747817123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4103717781266204660845661 1538894167974826747817123)
              ·
                refine ⟨2308341251962240121725685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538894167974826747817123 2308341251962240121725685)
                ·
                  refine ⟨216406992371460011411783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2308341251962240121725685 216406992371460011411783)
                  ·
                    rfl

theorem cell22_1896530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_1896530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896530 prefixEnd_1896530 := by exact prefixLift 1896530
  have htrace : WordTrace (prefixWord ++ tailWord_1896530) baseStart_1896530 baseEnd_1896530 := by
    simpa [prefixWord, tailWord_1896530, baseEnd_1896530] using wordTrace_append hprefix tailTrace_1896530
  have hstable : (prefixWord ++ tailWord_1896530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896530).length < 2 ^ (prefixWord ++ tailWord_1896530).sum := by decide
  have hdescent : baseEnd_1896530 < baseStart_1896530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896573 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_1896573 : Nat := 118140960795 + 1896573 * 2 ^ 59
def prefixEnd_1896573 : Nat := 4983230072969 + 3 ^ 40 * 1896573 * 2
def baseEnd_1896573 : Nat := 649235696893142255410217

theorem tailTrace_1896573 : CollatzResearch.WordTrace tailWord_1896573 prefixEnd_1896573 649235696893142255410217 := by
  unfold tailWord_1896573
  simp only [CollatzResearch.WordTrace]
  refine ⟨69173700158047404725806373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46115800105364936483870915 69173700158047404725806373)
  ·
    refine ⟨12970068779633888386088695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69173700158047404725806373 12970068779633888386088695)
    ·
      refine ⟨19455103169450832579133043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12970068779633888386088695 19455103169450832579133043)
      ·
        refine ⟨29182654754176248868699565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19455103169450832579133043 29182654754176248868699565)
        ·
          refine ⟨10943495532816093325762337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29182654754176248868699565 10943495532816093325762337)
          ·
            refine ⟨8207621649612069994321753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10943495532816093325762337 8207621649612069994321753)
            ·
              refine ⟨6155716237209052495741315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8207621649612069994321753 6155716237209052495741315)
              ·
                refine ⟨9233574355813578743611973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6155716237209052495741315 9233574355813578743611973)
                ·
                  refine ⟨1731295191715046014427245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9233574355813578743611973 1731295191715046014427245)
                  ·
                    refine ⟨649235696893142255410217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731295191715046014427245 649235696893142255410217)
                    ·
                      rfl

theorem cell22_1896573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_1896573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896573 prefixEnd_1896573 := by exact prefixLift 1896573
  have htrace : WordTrace (prefixWord ++ tailWord_1896573) baseStart_1896573 baseEnd_1896573 := by
    simpa [prefixWord, tailWord_1896573, baseEnd_1896573] using wordTrace_append hprefix tailTrace_1896573
  have hstable : (prefixWord ++ tailWord_1896573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896573).length < 2 ^ (prefixWord ++ tailWord_1896573).sum := by decide
  have hdescent : baseEnd_1896573 < baseStart_1896573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896586 : List Nat := [3, 1, 2, 3, 1, 2, 1, 9]
def baseStart_1896586 : Nat := 118140960795 + 1896586 * 2 ^ 59
def prefixEnd_1896586 : Nat := 4983230072969 + 3 ^ 40 * 1896586 * 2
def baseEnd_1896586 : Nat := 72137794117646061648353

theorem tailTrace_1896586 : CollatzResearch.WordTrace tailWord_1896586 prefixEnd_1896586 72137794117646061648353 := by
  unfold tailWord_1896586
  simp only [CollatzResearch.WordTrace]
  refine ⟨17293543576750076986507403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46116116204666871964019741 17293543576750076986507403)
  ·
    refine ⟨25940315365125115479761105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17293543576750076986507403 25940315365125115479761105)
    ·
      refine ⟨19455236523843836609820829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25940315365125115479761105 19455236523843836609820829)
      ·
        refine ⟨7295713696441438728682811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19455236523843836609820829 7295713696441438728682811)
        ·
          refine ⟨10943570544662158093024217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7295713696441438728682811 10943570544662158093024217)
          ·
            refine ⟨8207677908496618569768163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10943570544662158093024217 8207677908496618569768163)
            ·
              refine ⟨12311516862744927854652245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207677908496618569768163 12311516862744927854652245)
              ·
                refine ⟨72137794117646061648353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12311516862744927854652245 72137794117646061648353)
                ·
                  rfl

theorem cell22_1896586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_1896586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896586 prefixEnd_1896586 := by exact prefixLift 1896586
  have htrace : WordTrace (prefixWord ++ tailWord_1896586) baseStart_1896586 baseEnd_1896586 := by
    simpa [prefixWord, tailWord_1896586, baseEnd_1896586] using wordTrace_append hprefix tailTrace_1896586
  have hstable : (prefixWord ++ tailWord_1896586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896586).length < 2 ^ (prefixWord ++ tailWord_1896586).sum := by decide
  have hdescent : baseEnd_1896586 < baseStart_1896586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896635 : List Nat := [1, 1, 1, 1, 1, 2, 7, 4, 1, 3]
def baseStart_1896635 : Nat := 118140960795 + 1896635 * 2 ^ 59
def prefixEnd_1896635 : Nat := 4983230072969 + 3 ^ 40 * 1896635 * 2
def baseEnd_1896635 : Nat := 649256920760194760360027

theorem tailTrace_1896635 : CollatzResearch.WordTrace tailWord_1896635 prefixEnd_1896635 649256920760194760360027 := by
  unfold tailWord_1896635
  simp only [CollatzResearch.WordTrace]
  refine ⟨69175961483822789314563359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46117307655881859543042239 69175961483822789314563359)
  ·
    refine ⟨103763942225734183971845039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69175961483822789314563359 103763942225734183971845039)
    ·
      refine ⟨155645913338601275957767559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103763942225734183971845039 155645913338601275957767559)
      ·
        refine ⟨233468870007901913936651339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155645913338601275957767559 233468870007901913936651339)
        ·
          refine ⟨350203305011852870904977009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233468870007901913936651339 350203305011852870904977009)
          ·
            refine ⟨262652478758889653178732757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350203305011852870904977009 262652478758889653178732757)
            ·
              refine ⟨6155917470911476246376549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 262652478758889653178732757 6155917470911476246376549)
              ·
                refine ⟨1154234525795901796195603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6155917470911476246376549 1154234525795901796195603)
                ·
                  refine ⟨1731351788693852694293405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154234525795901796195603 1731351788693852694293405)
                  ·
                    refine ⟨649256920760194760360027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731351788693852694293405 649256920760194760360027)
                    ·
                      rfl

theorem cell22_1896635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 3].length) (baseStart_1896635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896635 prefixEnd_1896635 := by exact prefixLift 1896635
  have htrace : WordTrace (prefixWord ++ tailWord_1896635) baseStart_1896635 baseEnd_1896635 := by
    simpa [prefixWord, tailWord_1896635, baseEnd_1896635] using wordTrace_append hprefix tailTrace_1896635
  have hstable : (prefixWord ++ tailWord_1896635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896635).length < 2 ^ (prefixWord ++ tailWord_1896635).sum := by decide
  have hdescent : baseEnd_1896635 < baseStart_1896635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896652 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_1896652 : Nat := 118140960795 + 1896652 * 2 ^ 59
def prefixEnd_1896652 : Nat := 4983230072969 + 3 ^ 40 * 1896652 * 2
def baseEnd_1896652 : Nat := 649262740207612382684975

theorem tailTrace_1896652 : CollatzResearch.WordTrace tailWord_1896652 prefixEnd_1896652 649262740207612382684975 := by
  unfold tailWord_1896652
  simp only [CollatzResearch.WordTrace]
  refine ⟨34588290762380600608966105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46117721016507467478621473 34588290762380600608966105)
  ·
    refine ⟨25941218071785450456724579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34588290762380600608966105 25941218071785450456724579)
    ·
      refine ⟨38911827107678175685086869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25941218071785450456724579 38911827107678175685086869)
      ·
        refine ⟨1823991895672414485238447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38911827107678175685086869 1823991895672414485238447)
        ·
          refine ⟨2735987843508621727857671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823991895672414485238447 2735987843508621727857671)
          ·
            refine ⟨4103981765262932591786507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735987843508621727857671 4103981765262932591786507)
            ·
              refine ⟨6155972647894398887679761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103981765262932591786507 6155972647894398887679761)
              ·
                refine ⟨4616979485920799165759821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6155972647894398887679761 4616979485920799165759821)
                ·
                  refine ⟨1731367307220299687159933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4616979485920799165759821 1731367307220299687159933)
                  ·
                    refine ⟨649262740207612382684975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731367307220299687159933 649262740207612382684975)
                    ·
                      rfl

theorem cell22_1896652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_1896652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896652 prefixEnd_1896652 := by exact prefixLift 1896652
  have htrace : WordTrace (prefixWord ++ tailWord_1896652) baseStart_1896652 baseEnd_1896652 := by
    simpa [prefixWord, tailWord_1896652, baseEnd_1896652] using wordTrace_append hprefix tailTrace_1896652
  have hstable : (prefixWord ++ tailWord_1896652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896652).length < 2 ^ (prefixWord ++ tailWord_1896652).sum := by decide
  have hdescent : baseEnd_1896652 < baseStart_1896652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896669 : List Nat := [1, 4, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1896669 : Nat := 118140960795 + 1896669 * 2 ^ 59
def prefixEnd_1896669 : Nat := 4983230072969 + 3 ^ 40 * 1896669 * 2
def baseEnd_1896669 : Nat := 649268559655030005009923

theorem tailTrace_1896669 : CollatzResearch.WordTrace tailWord_1896669 prefixEnd_1896669 649268559655030005009923 := by
  unfold tailWord_1896669
  simp only [CollatzResearch.WordTrace]
  refine ⟨69177201565699613121301061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46118134377133075414200707 69177201565699613121301061)
  ·
    refine ⟨12970725293568677460243949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69177201565699613121301061 12970725293568677460243949)
    ·
      refine ⟨4864021985088254047591481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12970725293568677460243949 4864021985088254047591481)
      ·
        refine ⟨3648016488816190535693611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4864021985088254047591481 3648016488816190535693611)
        ·
          refine ⟨5472024733224285803540417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648016488816190535693611 5472024733224285803540417)
          ·
            refine ⟨4104018549918214352655313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5472024733224285803540417 4104018549918214352655313)
            ·
              refine ⟨3078013912438660764491485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4104018549918214352655313 3078013912438660764491485)
              ·
                refine ⟨1154255217164497786684307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3078013912438660764491485 1154255217164497786684307)
                ·
                  refine ⟨1731382825746746680026461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154255217164497786684307 1731382825746746680026461)
                  ·
                    refine ⟨649268559655030005009923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731382825746746680026461 649268559655030005009923)
                    ·
                      rfl

theorem cell22_1896669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1896669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896669 prefixEnd_1896669 := by exact prefixLift 1896669
  have htrace : WordTrace (prefixWord ++ tailWord_1896669) baseStart_1896669 baseEnd_1896669 := by
    simpa [prefixWord, tailWord_1896669, baseEnd_1896669] using wordTrace_append hprefix tailTrace_1896669
  have hstable : (prefixWord ++ tailWord_1896669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896669).length < 2 ^ (prefixWord ++ tailWord_1896669).sum := by decide
  have hdescent : baseEnd_1896669 < baseStart_1896669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896676 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 10]
def baseStart_1896676 : Nat := 118140960795 + 1896676 * 2 ^ 59
def prefixEnd_1896676 : Nat := 4983230072969 + 3 ^ 40 * 1896676 * 2
def baseEnd_1896676 : Nat := 216423651966028106694967

theorem tailTrace_1896676 : CollatzResearch.WordTrace tailWord_1896676 prefixEnd_1896676 216423651966028106694967 := by
  unfold tailWord_1896676
  simp only [CollatzResearch.WordTrace]
  refine ⟨34588728438337126658402941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46118304584449502211203921 34588728438337126658402941)
  ·
    refine ⟨12970773164376422496901103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34588728438337126658402941 12970773164376422496901103)
    ·
      refine ⟨19456159746564633745351655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12970773164376422496901103 19456159746564633745351655)
      ·
        refine ⟨29184239619846950618027483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19456159746564633745351655 29184239619846950618027483)
        ·
          refine ⟨43776359429770425927041225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29184239619846950618027483 43776359429770425927041225)
          ·
            refine ⟨32832269572327819445280919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43776359429770425927041225 32832269572327819445280919)
            ·
              refine ⟨49248404358491729167921379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32832269572327819445280919 49248404358491729167921379)
              ·
                refine ⟨73872606537737593751882069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49248404358491729167921379 73872606537737593751882069)
                ·
                  refine ⟨216423651966028106694967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 73872606537737593751882069 216423651966028106694967)
                  ·
                    rfl

theorem cell22_1896676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_1896676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896676 prefixEnd_1896676 := by exact prefixLift 1896676
  have htrace : WordTrace (prefixWord ++ tailWord_1896676) baseStart_1896676 baseEnd_1896676 := by
    simpa [prefixWord, tailWord_1896676, baseEnd_1896676] using wordTrace_append hprefix tailTrace_1896676
  have hstable : (prefixWord ++ tailWord_1896676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896676).length < 2 ^ (prefixWord ++ tailWord_1896676).sum := by decide
  have hdescent : baseEnd_1896676 < baseStart_1896676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896727 : List Nat := [1, 1, 3, 4, 1, 4, 1, 3, 4]
def baseStart_1896727 : Nat := 118140960795 + 1896727 * 2 ^ 59
def prefixEnd_1896727 : Nat := 4983230072969 + 3 ^ 40 * 1896727 * 2
def baseEnd_1896727 : Nat := 216429471413445729019915

theorem tailTrace_1896727 : CollatzResearch.WordTrace tailWord_1896727 prefixEnd_1896727 216429471413445729019915 := by
  unfold tailWord_1896727
  simp only [CollatzResearch.WordTrace]
  refine ⟨69179316999489489026912435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46119544666326326017941623 69179316999489489026912435)
  ·
    refine ⟨103768975499234233540368653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69179316999489489026912435 103768975499234233540368653)
    ·
      refine ⟨38913365812212837577638245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103768975499234233540368653 38913365812212837577638245)
      ·
        refine ⟨7296256089789907045807171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38913365812212837577638245 7296256089789907045807171)
        ·
          refine ⟨10944384134684860568710757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296256089789907045807171 10944384134684860568710757)
          ·
            refine ⟨2052072025253411356633267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10944384134684860568710757 2052072025253411356633267)
            ·
              refine ⟨3078108037880117034949901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052072025253411356633267 3078108037880117034949901)
              ·
                refine ⟨1154290514205043888106213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3078108037880117034949901 1154290514205043888106213)
                ·
                  refine ⟨216429471413445729019915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1154290514205043888106213 216429471413445729019915)
                  ·
                    rfl

theorem cell22_1896727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 4].length) (baseStart_1896727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896727 prefixEnd_1896727 := by exact prefixLift 1896727
  have htrace : WordTrace (prefixWord ++ tailWord_1896727) baseStart_1896727 baseEnd_1896727 := by
    simpa [prefixWord, tailWord_1896727, baseEnd_1896727] using wordTrace_append hprefix tailTrace_1896727
  have hstable : (prefixWord ++ tailWord_1896727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896727).length < 2 ^ (prefixWord ++ tailWord_1896727).sum := by decide
  have hdescent : baseEnd_1896727 < baseStart_1896727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896738 : List Nat := [3, 3, 1, 1, 3, 1, 10]
def baseStart_1896738 : Nat := 118140960795 + 1896738 * 2 ^ 59
def prefixEnd_1896738 : Nat := 4983230072969 + 3 ^ 40 * 1896738 * 2
def baseEnd_1896738 : Nat := 24047858509819882408693

theorem tailTrace_1896738 : CollatzResearch.WordTrace tailWord_1896738 prefixEnd_1896738 24047858509819882408693 := by
  unfold tailWord_1896738
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294929550612409476390717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46119812134966425270375245 17294929550612409476390717)
  ·
    refine ⟨6485598581479653553646519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17294929550612409476390717 6485598581479653553646519)
    ·
      refine ⟨9728397872219480330469779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6485598581479653553646519 9728397872219480330469779)
      ·
        refine ⟨14592596808329220495704669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9728397872219480330469779 14592596808329220495704669)
        ·
          refine ⟨5472223803123457685889251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14592596808329220495704669 5472223803123457685889251)
          ·
            refine ⟨8208335704685186528833877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472223803123457685889251 8208335704685186528833877)
            ·
              refine ⟨24047858509819882408693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8208335704685186528833877 24047858509819882408693)
              ·
                rfl

theorem cell22_1896738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 10].length) (baseStart_1896738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896738 prefixEnd_1896738 := by exact prefixLift 1896738
  have htrace : WordTrace (prefixWord ++ tailWord_1896738) baseStart_1896738 baseEnd_1896738 := by
    simpa [prefixWord, tailWord_1896738, baseEnd_1896738] using wordTrace_append hprefix tailTrace_1896738
  have hstable : (prefixWord ++ tailWord_1896738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896738).length < 2 ^ (prefixWord ++ tailWord_1896738).sum := by decide
  have hdescent : baseEnd_1896738 < baseStart_1896738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896740 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1896740 : Nat := 118140960795 + 1896740 * 2 ^ 59
def prefixEnd_1896740 : Nat := 4983230072969 + 3 ^ 40 * 1896740 * 2
def baseEnd_1896740 : Nat := 649292864406009486484705

theorem tailTrace_1896740 : CollatzResearch.WordTrace tailWord_1896740 prefixEnd_1896740 649292864406009486484705 := by
  unfold tailWord_1896740
  simp only [CollatzResearch.WordTrace]
  refine ⟨34589895574221196123567837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46119860765628261498090449 34589895574221196123567837)
  ·
    refine ⟨12971210840332948546337939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34589895574221196123567837 12971210840332948546337939)
    ·
      refine ⟨19456816260499422819506909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12971210840332948546337939 19456816260499422819506909)
      ·
        refine ⟨7296306097687283557315091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19456816260499422819506909 7296306097687283557315091)
        ·
          refine ⟨10944459146530925335972637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296306097687283557315091 10944459146530925335972637)
          ·
            refine ⟨4104172179949097000989739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10944459146530925335972637 4104172179949097000989739)
            ·
              refine ⟨6156258269923645501484609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104172179949097000989739 6156258269923645501484609)
              ·
                refine ⟨4617193702442734126113457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156258269923645501484609 4617193702442734126113457)
                ·
                  refine ⟨3462895276832050594585093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4617193702442734126113457 3462895276832050594585093)
                  ·
                    refine ⟨649292864406009486484705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3462895276832050594585093 649292864406009486484705)
                    ·
                      rfl

theorem cell22_1896740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1896740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896740 prefixEnd_1896740 := by exact prefixLift 1896740
  have htrace : WordTrace (prefixWord ++ tailWord_1896740) baseStart_1896740 baseEnd_1896740 := by
    simpa [prefixWord, tailWord_1896740, baseEnd_1896740] using wordTrace_append hprefix tailTrace_1896740
  have hstable : (prefixWord ++ tailWord_1896740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896740).length < 2 ^ (prefixWord ++ tailWord_1896740).sum := by decide
  have hdescent : baseEnd_1896740 < baseStart_1896740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896744 : List Nat := [2, 1, 5, 1, 3, 1, 3, 2, 4]
def baseStart_1896744 : Nat := 118140960795 + 1896744 * 2 ^ 59
def prefixEnd_1896744 : Nat := 4983230072969 + 3 ^ 40 * 1896744 * 2
def baseEnd_1896744 : Nat := 216431411229251603128231

theorem tailTrace_1896744 : CollatzResearch.WordTrace tailWord_1896744 prefixEnd_1896744 216431411229251603128231 := by
  unfold tailWord_1896744
  simp only [CollatzResearch.WordTrace]
  refine ⟨34589968520213950465140643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46119958026951933953520857 34589968520213950465140643)
  ·
    refine ⟨51884952780320925697710965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34589968520213950465140643 51884952780320925697710965)
    ·
      refine ⟨4864214323155086784160403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51884952780320925697710965 4864214323155086784160403)
      ·
        refine ⟨7296321484732630176240605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864214323155086784160403 7296321484732630176240605)
        ·
          refine ⟨2736120556774736316090227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7296321484732630176240605 2736120556774736316090227)
          ·
            refine ⟨4104180835162104474135341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736120556774736316090227 4104180835162104474135341)
            ·
              refine ⟨1539067813185789177800753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4104180835162104474135341 1539067813185789177800753)
              ·
                refine ⟨1154300859889341883350565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539067813185789177800753 1154300859889341883350565)
                ·
                  refine ⟨216431411229251603128231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1154300859889341883350565 216431411229251603128231)
                  ·
                    rfl

theorem cell22_1896744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 4].length) (baseStart_1896744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896744 prefixEnd_1896744 := by exact prefixLift 1896744
  have htrace : WordTrace (prefixWord ++ tailWord_1896744) baseStart_1896744 baseEnd_1896744 := by
    simpa [prefixWord, tailWord_1896744, baseEnd_1896744] using wordTrace_append hprefix tailTrace_1896744
  have hstable : (prefixWord ++ tailWord_1896744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896744).length < 2 ^ (prefixWord ++ tailWord_1896744).sum := by decide
  have hdescent : baseEnd_1896744 < baseStart_1896744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896862 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1896862 : Nat := 118140960795 + 1896862 * 2 ^ 59
def prefixEnd_1896862 : Nat := 4983230072969 + 3 ^ 40 * 1896862 * 2
def baseEnd_1896862 : Nat := 216444875833080611644777

theorem tailTrace_1896862 : CollatzResearch.WordTrace tailWord_1896862 prefixEnd_1896862 216444875833080611644777 := by
  unfold tailWord_1896862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8648030106750050885384605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46122827236000271388717893 8648030106750050885384605)
  ·
    refine ⟨3243011290031269082019227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8648030106750050885384605 3243011290031269082019227)
    ·
      refine ⟨4864516935046903623028841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3243011290031269082019227 4864516935046903623028841)
      ·
        refine ⟨3648387701285177717271631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4864516935046903623028841 3648387701285177717271631)
        ·
          refine ⟨5472581551927766575907447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648387701285177717271631 5472581551927766575907447)
          ·
            refine ⟨8208872327891649863861171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472581551927766575907447 8208872327891649863861171)
            ·
              refine ⟨12313308491837474795791757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208872327891649863861171 12313308491837474795791757)
              ·
                refine ⟨4617490684439053048421909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12313308491837474795791757 4617490684439053048421909)
                ·
                  refine ⟨216444875833080611644777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4617490684439053048421909 216444875833080611644777)
                  ·
                    rfl

theorem cell22_1896862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1896862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896862 prefixEnd_1896862 := by exact prefixLift 1896862
  have htrace : WordTrace (prefixWord ++ tailWord_1896862) baseStart_1896862 baseEnd_1896862 := by
    simpa [prefixWord, tailWord_1896862, baseEnd_1896862] using wordTrace_append hprefix tailTrace_1896862
  have hstable : (prefixWord ++ tailWord_1896862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896862).length < 2 ^ (prefixWord ++ tailWord_1896862).sum := by decide
  have hdescent : baseEnd_1896862 < baseStart_1896862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896888 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_1896888 : Nat := 118140960795 + 1896888 * 2 ^ 59
def prefixEnd_1896888 : Nat := 4983230072969 + 3 ^ 40 * 1896888 * 2
def baseEnd_1896888 : Nat := 649343527830586433784251

theorem tailTrace_1896888 : CollatzResearch.WordTrace tailWord_1896888 prefixEnd_1896888 649343527830586433784251 := by
  unfold tailWord_1896888
  simp only [CollatzResearch.WordTrace]
  refine ⟨34592594575953106761761659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46123459434604142349015545 34592594575953106761761659)
  ·
    refine ⟨51888891863929660142642489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34592594575953106761761659 51888891863929660142642489)
    ·
      refine ⟨38916668897947245106981867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51888891863929660142642489 38916668897947245106981867)
      ·
        refine ⟨58375003346920867660472801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38916668897947245106981867 58375003346920867660472801)
        ·
          refine ⟨43781252510190650745354601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58375003346920867660472801 43781252510190650745354601)
          ·
            refine ⟨32835939382642988059015951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43781252510190650745354601 32835939382642988059015951)
            ·
              refine ⟨49253909073964482088523927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32835939382642988059015951 49253909073964482088523927)
              ·
                refine ⟨73880863610946723132785891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49253909073964482088523927 73880863610946723132785891)
                ·
                  refine ⟨110821295416420084699178837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73880863610946723132785891 110821295416420084699178837)
                  ·
                    refine ⟨649343527830586433784251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 110821295416420084699178837 649343527830586433784251)
                    ·
                      rfl

theorem cell22_1896888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_1896888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896888 prefixEnd_1896888 := by exact prefixLift 1896888
  have htrace : WordTrace (prefixWord ++ tailWord_1896888) baseStart_1896888 baseEnd_1896888 := by
    simpa [prefixWord, tailWord_1896888, baseEnd_1896888] using wordTrace_append hprefix tailTrace_1896888
  have hstable : (prefixWord ++ tailWord_1896888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896888).length < 2 ^ (prefixWord ++ tailWord_1896888).sum := by decide
  have hdescent : baseEnd_1896888 < baseStart_1896888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896905 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 5, 3]
def baseStart_1896905 : Nat := 118140960795 + 1896905 * 2 ^ 59
def prefixEnd_1896905 : Nat := 4983230072969 + 3 ^ 40 * 1896905 * 2
def baseEnd_1896905 : Nat := 649349347278004056109199

theorem tailTrace_1896905 : CollatzResearch.WordTrace tailWord_1896905 prefixEnd_1896905 649349347278004056109199 := by
  unfold tailWord_1896905
  simp only [CollatzResearch.WordTrace]
  refine ⟨69185809192844625426892169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46123872795229750284594779 69185809192844625426892169)
  ·
    refine ⟨51889356894633469070169127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69185809192844625426892169 51889356894633469070169127)
    ·
      refine ⟨77834035341950203605253691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51889356894633469070169127 77834035341950203605253691)
      ·
        refine ⟨116751053012925305407880537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77834035341950203605253691 116751053012925305407880537)
        ·
          refine ⟨87563289759693979055910403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116751053012925305407880537 87563289759693979055910403)
          ·
            refine ⟨131344934639540968583865605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87563289759693979055910403 131344934639540968583865605)
            ·
              refine ⟨24627175244913931609474801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131344934639540968583865605 24627175244913931609474801)
              ·
                refine ⟨18470381433685448707106101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24627175244913931609474801 18470381433685448707106101)
                ·
                  refine ⟨1731598259408010816291197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18470381433685448707106101 1731598259408010816291197)
                  ·
                    refine ⟨649349347278004056109199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731598259408010816291197 649349347278004056109199)
                    ·
                      rfl

theorem cell22_1896905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_1896905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1896905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1896905 prefixEnd_1896905 := by exact prefixLift 1896905
  have htrace : WordTrace (prefixWord ++ tailWord_1896905) baseStart_1896905 baseEnd_1896905 := by
    simpa [prefixWord, tailWord_1896905, baseEnd_1896905] using wordTrace_append hprefix tailTrace_1896905
  have hstable : (prefixWord ++ tailWord_1896905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896905).length < 2 ^ (prefixWord ++ tailWord_1896905).sum := by decide
  have hdescent : baseEnd_1896905 < baseStart_1896905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897029 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_1897029 : Nat := 118140960795 + 1897029 * 2 ^ 59
def prefixEnd_1897029 : Nat := 4983230072969 + 3 ^ 40 * 1897029 * 2
def baseEnd_1897029 : Nat := 649391795012109066008819

theorem tailTrace_1897029 : CollatzResearch.WordTrace tailWord_1897029 prefixEnd_1897029 649391795012109066008819 := by
  unfold tailWord_1897029
  simp only [CollatzResearch.WordTrace]
  refine ⟨69190331844395394604406141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46126887896263596402937427 69190331844395394604406141)
  ·
    refine ⟨25946374441648272976652303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69190331844395394604406141 25946374441648272976652303)
    ·
      refine ⟨38919561662472409464978455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25946374441648272976652303 38919561662472409464978455)
      ·
        refine ⟨58379342493708614197467683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38919561662472409464978455 58379342493708614197467683)
        ·
          refine ⟨87569013740562921296201525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58379342493708614197467683 87569013740562921296201525)
          ·
            refine ⟨8209595038177773871518893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87569013740562921296201525 8209595038177773871518893)
            ·
              refine ⟨3078598139316665201819585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8209595038177773871518893 3078598139316665201819585)
              ·
                refine ⟨2308948604487498901364689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078598139316665201819585 2308948604487498901364689)
                ·
                  refine ⟨1731711453365624176023517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2308948604487498901364689 1731711453365624176023517)
                  ·
                    refine ⟨649391795012109066008819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731711453365624176023517 649391795012109066008819)
                    ·
                      rfl

theorem cell22_1897029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_1897029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897029 prefixEnd_1897029 := by exact prefixLift 1897029
  have htrace : WordTrace (prefixWord ++ tailWord_1897029) baseStart_1897029 baseEnd_1897029 := by
    simpa [prefixWord, tailWord_1897029, baseEnd_1897029] using wordTrace_append hprefix tailTrace_1897029
  have hstable : (prefixWord ++ tailWord_1897029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897029).length < 2 ^ (prefixWord ++ tailWord_1897029).sum := by decide
  have hdescent : baseEnd_1897029 < baseStart_1897029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897055 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 2, 6]
def baseStart_1897055 : Nat := 118140960795 + 1897055 * 2 ^ 59
def prefixEnd_1897055 : Nat := 4983230072969 + 3 ^ 40 * 1897055 * 2
def baseEnd_1897055 : Nat := 649400695343453664858739

theorem tailTrace_1897055 : CollatzResearch.WordTrace tailWord_1897055 prefixEnd_1897055 649400695343453664858739 := by
  unfold tailWord_1897055
  simp only [CollatzResearch.WordTrace]
  refine ⟨69191280142301201044852619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46127520094867467363235079 69191280142301201044852619)
  ·
    refine ⟨103786920213451801567278929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69191280142301201044852619 103786920213451801567278929)
    ·
      refine ⟨77840190160088851175459197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103786920213451801567278929 77840190160088851175459197)
      ·
        refine ⟨29190071310033319190797199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77840190160088851175459197 29190071310033319190797199)
        ·
          refine ⟨43785106965049978786195799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29190071310033319190797199 43785106965049978786195799)
          ·
            refine ⟨65677660447574968179293699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43785106965049978786195799 65677660447574968179293699)
            ·
              refine ⟨98516490671362452268940549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65677660447574968179293699 98516490671362452268940549)
              ·
                refine ⟨18471842000880459800426353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98516490671362452268940549 18471842000880459800426353)
                ·
                  refine ⟨13853881500660344850319765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18471842000880459800426353 13853881500660344850319765)
                  ·
                    refine ⟨649400695343453664858739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13853881500660344850319765 649400695343453664858739)
                    ·
                      rfl

theorem cell22_1897055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_1897055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897055 prefixEnd_1897055 := by exact prefixLift 1897055
  have htrace : WordTrace (prefixWord ++ tailWord_1897055) baseStart_1897055 baseEnd_1897055 := by
    simpa [prefixWord, tailWord_1897055, baseEnd_1897055] using wordTrace_append hprefix tailTrace_1897055
  have hstable : (prefixWord ++ tailWord_1897055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897055).length < 2 ^ (prefixWord ++ tailWord_1897055).sum := by decide
  have hdescent : baseEnd_1897055 < baseStart_1897055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897102 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1897102 : Nat := 118140960795 + 1897102 * 2 ^ 59
def prefixEnd_1897102 : Nat := 4983230072969 + 3 ^ 40 * 1897102 * 2
def baseEnd_1897102 : Nat := 649416784403961208933595

theorem tailTrace_1897102 : CollatzResearch.WordTrace tailWord_1897102 prefixEnd_1897102 649416784403961208933595 := by
  unfold tailWord_1897102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8649124296641366008976695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46128662915420618714542373 8649124296641366008976695)
  ·
    refine ⟨12973686444962049013465043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8649124296641366008976695 12973686444962049013465043)
    ·
      refine ⟨19460529667443073520197565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12973686444962049013465043 19460529667443073520197565)
      ·
        refine ⟨7297698625291152570074087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19460529667443073520197565 7297698625291152570074087)
        ·
          refine ⟨10946547937936728855111131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297698625291152570074087 10946547937936728855111131)
          ·
            refine ⟨16419821906905093282666697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10946547937936728855111131 16419821906905093282666697)
            ·
              refine ⟨12314866430178819962000023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16419821906905093282666697 12314866430178819962000023)
              ·
                refine ⟨18472299645268229943000035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12314866430178819962000023 18472299645268229943000035)
                ·
                  refine ⟨27708449467902344914500053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18472299645268229943000035 27708449467902344914500053)
                  ·
                    refine ⟨649416784403961208933595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27708449467902344914500053 649416784403961208933595)
                    ·
                      rfl

theorem cell22_1897102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1897102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897102 prefixEnd_1897102 := by exact prefixLift 1897102
  have htrace : WordTrace (prefixWord ++ tailWord_1897102) baseStart_1897102 baseEnd_1897102 := by
    simpa [prefixWord, tailWord_1897102, baseEnd_1897102] using wordTrace_append hprefix tailTrace_1897102
  have hstable : (prefixWord ++ tailWord_1897102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897102).length < 2 ^ (prefixWord ++ tailWord_1897102).sum := by decide
  have hdescent : baseEnd_1897102 < baseStart_1897102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897115 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 12]
def baseStart_1897115 : Nat := 118140960795 + 1897115 * 2 ^ 59
def prefixEnd_1897115 : Nat := 4983230072969 + 3 ^ 40 * 1897115 * 2
def baseEnd_1897115 : Nat := 216473744856544502786185

theorem tailTrace_1897115 : CollatzResearch.WordTrace tailWord_1897115 prefixEnd_1897115 216473744856544502786185 := by
  unfold tailWord_1897115
  simp only [CollatzResearch.WordTrace]
  refine ⟨69193468522083831292036799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46128979014722554194691199 69193468522083831292036799)
  ·
    refine ⟨103790202783125746938055199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69193468522083831292036799 103790202783125746938055199)
    ·
      refine ⟨155685304174688620407082799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103790202783125746938055199 155685304174688620407082799)
      ·
        refine ⟨233527956262032930610624199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155685304174688620407082799 233527956262032930610624199)
        ·
          refine ⟨350291934393049395915936299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233527956262032930610624199 350291934393049395915936299)
          ·
            refine ⟨525437901589574093873904449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350291934393049395915936299 525437901589574093873904449)
            ·
              refine ⟨394078426192180570405428337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525437901589574093873904449 394078426192180570405428337)
              ·
                refine ⟨295558819644135427804071253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394078426192180570405428337 295558819644135427804071253)
                ·
                  refine ⟨216473744856544502786185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 295558819644135427804071253 216473744856544502786185)
                  ·
                    rfl

theorem cell22_1897115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 12].length) (baseStart_1897115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897115 prefixEnd_1897115 := by exact prefixLift 1897115
  have htrace : WordTrace (prefixWord ++ tailWord_1897115) baseStart_1897115 baseEnd_1897115 := by
    simpa [prefixWord, tailWord_1897115, baseEnd_1897115] using wordTrace_append hprefix tailTrace_1897115
  have hstable : (prefixWord ++ tailWord_1897115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897115).length < 2 ^ (prefixWord ++ tailWord_1897115).sum := by decide
  have hdescent : baseEnd_1897115 < baseStart_1897115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897164 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_1897164 : Nat := 118140960795 + 1897164 * 2 ^ 59
def prefixEnd_1897164 : Nat := 4983230072969 + 3 ^ 40 * 1897164 * 2
def baseEnd_1897164 : Nat := 649438008271013713883405

theorem tailTrace_1897164 : CollatzResearch.WordTrace tailWord_1897164 prefixEnd_1897164 649438008271013713883405 := by
  unfold tailWord_1897164
  simp only [CollatzResearch.WordTrace]
  refine ⟨34597627849453156330285273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46130170465937541773713697 34597627849453156330285273)
  ·
    refine ⟨25948220887089867247713955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34597627849453156330285273 25948220887089867247713955)
    ·
      refine ⟨38922331330634800871570933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25948220887089867247713955 38922331330634800871570933)
      ·
        refine ⟨3648968562247012581709775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38922331330634800871570933 3648968562247012581709775)
        ·
          refine ⟨5473452843370518872564663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648968562247012581709775 5473452843370518872564663)
          ·
            refine ⟨8210179265055778308846995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473452843370518872564663 8210179265055778308846995)
            ·
              refine ⟨12315268897583667463270493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8210179265055778308846995 12315268897583667463270493)
              ·
                refine ⟨4618225836593875298726435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12315268897583667463270493 4618225836593875298726435)
                ·
                  refine ⟨6927338754890812948089653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618225836593875298726435 6927338754890812948089653)
                  ·
                    refine ⟨649438008271013713883405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6927338754890812948089653 649438008271013713883405)
                    ·
                      rfl

theorem cell22_1897164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_1897164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897164 prefixEnd_1897164 := by exact prefixLift 1897164
  have htrace : WordTrace (prefixWord ++ tailWord_1897164) baseStart_1897164 baseEnd_1897164 := by
    simpa [prefixWord, tailWord_1897164, baseEnd_1897164] using wordTrace_append hprefix tailTrace_1897164
  have hstable : (prefixWord ++ tailWord_1897164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897164).length < 2 ^ (prefixWord ++ tailWord_1897164).sum := by decide
  have hdescent : baseEnd_1897164 < baseStart_1897164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897198 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_1897198 : Nat := 118140960795 + 1897198 * 2 ^ 59
def prefixEnd_1897198 : Nat := 4983230072969 + 3 ^ 40 * 1897198 * 2
def baseEnd_1897198 : Nat := 649449647165848958533301

theorem tailTrace_1897198 : CollatzResearch.WordTrace tailWord_1897198 prefixEnd_1897198 649449647165848958533301 := by
  unfold tailWord_1897198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8649561972597892058413531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46130997187188757644872165 8649561972597892058413531)
  ·
    refine ⟨12974342958896838087620297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8649561972597892058413531 12974342958896838087620297)
    ·
      refine ⟨9730757219172628565715223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12974342958896838087620297 9730757219172628565715223)
      ·
        refine ⟨14596135828758942848572835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9730757219172628565715223 14596135828758942848572835)
        ·
          refine ⟨21894203743138414272859253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14596135828758942848572835 21894203743138414272859253)
          ·
            refine ⟨2052581600919226338080555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21894203743138414272859253 2052581600919226338080555)
            ·
              refine ⟨3078872401378839507120833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052581600919226338080555 3078872401378839507120833)
              ·
                refine ⟨2309154301034129630340625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078872401378839507120833 2309154301034129630340625)
                ·
                  refine ⟨1731865725775597222755469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309154301034129630340625 1731865725775597222755469)
                  ·
                    refine ⟨649449647165848958533301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731865725775597222755469 649449647165848958533301)
                    ·
                      rfl

theorem cell22_1897198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_1897198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897198 prefixEnd_1897198 := by exact prefixLift 1897198
  have htrace : WordTrace (prefixWord ++ tailWord_1897198) baseStart_1897198 baseEnd_1897198 := by
    simpa [prefixWord, tailWord_1897198, baseEnd_1897198] using wordTrace_append hprefix tailTrace_1897198
  have hstable : (prefixWord ++ tailWord_1897198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897198).length < 2 ^ (prefixWord ++ tailWord_1897198).sum := by decide
  have hdescent : baseEnd_1897198 < baseStart_1897198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897299 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 6, 3]
def baseStart_1897299 : Nat := 118140960795 + 1897299 * 2 ^ 59
def prefixEnd_1897299 : Nat := 4983230072969 + 3 ^ 40 * 1897299 * 2
def baseEnd_1897299 : Nat := 649484221529918361757991

theorem tailTrace_1897299 : CollatzResearch.WordTrace tailWord_1897299 prefixEnd_1897299 649484221529918361757991 := by
  unfold tailWord_1897299
  simp only [CollatzResearch.WordTrace]
  refine ⟨69200179553417230716734951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46133453035611487144489967 69200179553417230716734951)
  ·
    refine ⟨103800269330125846075102427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69200179553417230716734951 103800269330125846075102427)
    ·
      refine ⟨155700403995188769112653641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103800269330125846075102427 155700403995188769112653641)
      ·
        refine ⟨116775302996391576834490231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155700403995188769112653641 116775302996391576834490231)
        ·
          refine ⟨175162954494587365251735347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116775302996391576834490231 175162954494587365251735347)
          ·
            refine ⟨262744431741881047877603021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175162954494587365251735347 262744431741881047877603021)
            ·
              refine ⟨98529161903205392954101133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262744431741881047877603021 98529161903205392954101133)
              ·
                refine ⟨36948435713702022357787925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98529161903205392954101133 36948435713702022357787925)
                ·
                  refine ⟨1731957924079782298021309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36948435713702022357787925 1731957924079782298021309)
                  ·
                    refine ⟨649484221529918361757991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731957924079782298021309 649484221529918361757991)
                    ·
                      rfl

theorem cell22_1897299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 3].length) (baseStart_1897299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897299 prefixEnd_1897299 := by exact prefixLift 1897299
  have htrace : WordTrace (prefixWord ++ tailWord_1897299) baseStart_1897299 baseEnd_1897299 := by
    simpa [prefixWord, tailWord_1897299, baseEnd_1897299] using wordTrace_append hprefix tailTrace_1897299
  have hstable : (prefixWord ++ tailWord_1897299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897299).length < 2 ^ (prefixWord ++ tailWord_1897299).sum := by decide
  have hdescent : baseEnd_1897299 < baseStart_1897299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897301 : List Nat := [1, 3, 2, 2, 2, 1, 2, 5, 4]
def baseStart_1897301 : Nat := 118140960795 + 1897301 * 2 ^ 59
def prefixEnd_1897301 : Nat := 4983230072969 + 3 ^ 40 * 1897301 * 2
def baseEnd_1897301 : Nat := 216494968723597007735995

theorem tailTrace_1897301 : CollatzResearch.WordTrace tailWord_1897301 prefixEnd_1897301 216494968723597007735995 := by
  unfold tailWord_1897301
  simp only [CollatzResearch.WordTrace]
  refine ⟨69200252499409985058307757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46133501666273323372205171 69200252499409985058307757)
  ·
    refine ⟨25950094687278744396865409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69200252499409985058307757 25950094687278744396865409)
    ·
      refine ⟨19462571015459058297649057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25950094687278744396865409 19462571015459058297649057)
      ·
        refine ⟨14596928261594293723236793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19462571015459058297649057 14596928261594293723236793)
        ·
          refine ⟨10947696196195720292427595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14596928261594293723236793 10947696196195720292427595)
          ·
            refine ⟨16421544294293580438641393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10947696196195720292427595 16421544294293580438641393)
            ·
              refine ⟨12316158220720185328981045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16421544294293580438641393 12316158220720185328981045)
              ·
                refine ⟨1154639833192517374591973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12316158220720185328981045 1154639833192517374591973)
                ·
                  refine ⟨216494968723597007735995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1154639833192517374591973 216494968723597007735995)
                  ·
                    rfl

theorem cell22_1897301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_1897301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897301 prefixEnd_1897301 := by exact prefixLift 1897301
  have htrace : WordTrace (prefixWord ++ tailWord_1897301) baseStart_1897301 baseEnd_1897301 := by
    simpa [prefixWord, tailWord_1897301, baseEnd_1897301] using wordTrace_append hprefix tailTrace_1897301
  have hstable : (prefixWord ++ tailWord_1897301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897301).length < 2 ^ (prefixWord ++ tailWord_1897301).sum := by decide
  have hdescent : baseEnd_1897301 < baseStart_1897301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897303 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 1, 4]
def baseStart_1897303 : Nat := 118140960795 + 1897303 * 2 ^ 59
def prefixEnd_1897303 : Nat := 4983230072969 + 3 ^ 40 * 1897303 * 2
def baseEnd_1897303 : Nat := 649485590811663684657979

theorem tailTrace_1897303 : CollatzResearch.WordTrace tailWord_1897303 prefixEnd_1897303 649485590811663684657979 := by
  unfold tailWord_1897303
  simp only [CollatzResearch.WordTrace]
  refine ⟨69200325445402739399880563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46133550296935159599920375 69200325445402739399880563)
  ·
    refine ⟨103800488168104109099820845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69200325445402739399880563 103800488168104109099820845)
    ·
      refine ⟨38925183063039040912432817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103800488168104109099820845 38925183063039040912432817)
      ·
        refine ⟨29193887297279280684324613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38925183063039040912432817 29193887297279280684324613)
        ·
          refine ⟨5473853868239865128310865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29193887297279280684324613 5473853868239865128310865)
          ·
            refine ⟨4105390401179898846233149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5473853868239865128310865 4105390401179898846233149)
            ·
              refine ⟨1539521400442462067337431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4105390401179898846233149 1539521400442462067337431)
              ·
                refine ⟨2309282100663693101006147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539521400442462067337431 2309282100663693101006147)
                ·
                  refine ⟨3463923150995539651509221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309282100663693101006147 3463923150995539651509221)
                  ·
                    refine ⟨649485590811663684657979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3463923150995539651509221 649485590811663684657979)
                    ·
                      rfl

theorem cell22_1897303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_1897303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897303 prefixEnd_1897303 := by exact prefixLift 1897303
  have htrace : WordTrace (prefixWord ++ tailWord_1897303) baseStart_1897303 baseEnd_1897303 := by
    simpa [prefixWord, tailWord_1897303, baseEnd_1897303] using wordTrace_append hprefix tailTrace_1897303
  have hstable : (prefixWord ++ tailWord_1897303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897303).length < 2 ^ (prefixWord ++ tailWord_1897303).sum := by decide
  have hdescent : baseEnd_1897303 < baseStart_1897303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897329 : List Nat := [1, 2, 2, 2, 1, 4, 3, 7]
def baseStart_1897329 : Nat := 118140960795 + 1897329 * 2 ^ 59
def prefixEnd_1897329 : Nat := 4983230072969 + 3 ^ 40 * 1897329 * 2
def baseEnd_1897329 : Nat := 72166054571445364834211

theorem tailTrace_1897329 : CollatzResearch.WordTrace tailWord_1897329 prefixEnd_1897329 72166054571445364834211 := by
  unfold tailWord_1897329
  simp only [CollatzResearch.WordTrace]
  refine ⟨69201273743308545840327041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46134182495539030560218027 69201273743308545840327041)
  ·
    refine ⟨51900955307481409380245281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69201273743308545840327041 51900955307481409380245281)
    ·
      refine ⟨38925716480611057035183961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51900955307481409380245281 38925716480611057035183961)
      ·
        refine ⟨29194287360458292776387971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38925716480611057035183961 29194287360458292776387971)
        ·
          refine ⟨43791431040687439164581957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29194287360458292776387971 43791431040687439164581957)
          ·
            refine ⟨8210893320128894843359117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43791431040687439164581957 8210893320128894843359117)
            ·
              refine ⟨3079084995048335566259669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8210893320128894843359117 3079084995048335566259669)
              ·
                refine ⟨72166054571445364834211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3079084995048335566259669 72166054571445364834211)
                ·
                  rfl

theorem cell22_1897329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 7].length) (baseStart_1897329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897329 prefixEnd_1897329 := by exact prefixLift 1897329
  have htrace : WordTrace (prefixWord ++ tailWord_1897329) baseStart_1897329 baseEnd_1897329 := by
    simpa [prefixWord, tailWord_1897329, baseEnd_1897329] using wordTrace_append hprefix tailTrace_1897329
  have hstable : (prefixWord ++ tailWord_1897329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897329).length < 2 ^ (prefixWord ++ tailWord_1897329).sum := by decide
  have hdescent : baseEnd_1897329 < baseStart_1897329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897333 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1897333 : Nat := 118140960795 + 1897333 * 2 ^ 59
def prefixEnd_1897333 : Nat := 4983230072969 + 3 ^ 40 * 1897333 * 2
def baseEnd_1897333 : Nat := 649495860424753606407887

theorem tailTrace_1897333 : CollatzResearch.WordTrace tailWord_1897333 prefixEnd_1897333 649495860424753606407887 := by
  unfold tailWord_1897333
  simp only [CollatzResearch.WordTrace]
  refine ⟨69201419635294054523472653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46134279756862703015648435 69201419635294054523472653)
  ·
    refine ⟨25950532363235270446302245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69201419635294054523472653 25950532363235270446302245)
    ·
      refine ⟨4865724818106613208681671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25950532363235270446302245 4865724818106613208681671)
      ·
        refine ⟨7298587227159919813022507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865724818106613208681671 7298587227159919813022507)
        ·
          refine ⟨10947880840739879719533761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7298587227159919813022507 10947880840739879719533761)
          ·
            refine ⟨8210910630554909789650321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10947880840739879719533761 8210910630554909789650321)
            ·
              refine ⟨6158182972916182342237741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8210910630554909789650321 6158182972916182342237741)
              ·
                refine ⟨2309318614843568378339153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6158182972916182342237741 2309318614843568378339153)
                ·
                  refine ⟨1731988961132676283754365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309318614843568378339153 1731988961132676283754365)
                  ·
                    refine ⟨649495860424753606407887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1731988961132676283754365 649495860424753606407887)
                    ·
                      rfl

theorem cell22_1897333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1897333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897333 prefixEnd_1897333 := by exact prefixLift 1897333
  have htrace : WordTrace (prefixWord ++ tailWord_1897333) baseStart_1897333 baseEnd_1897333 := by
    simpa [prefixWord, tailWord_1897333, baseEnd_1897333] using wordTrace_append hprefix tailTrace_1897333
  have hstable : (prefixWord ++ tailWord_1897333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897333).length < 2 ^ (prefixWord ++ tailWord_1897333).sum := by decide
  have hdescent : baseEnd_1897333 < baseStart_1897333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897378 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1897378 : Nat := 118140960795 + 1897378 * 2 ^ 59
def prefixEnd_1897378 : Nat := 4983230072969 + 3 ^ 40 * 1897378 * 2
def baseEnd_1897378 : Nat := 649511264844388489032749

theorem tailTrace_1897378 : CollatzResearch.WordTrace tailWord_1897378 prefixEnd_1897378 649511264844388489032749 := by
  unfold tailWord_1897378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300765230032756802215197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46135373946754018139240525 17300765230032756802215197)
  ·
    refine ⟨6487786961262283800830699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17300765230032756802215197 6487786961262283800830699)
    ·
      refine ⟨9731680441893425701246049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6487786961262283800830699 9731680441893425701246049)
      ·
        refine ⟨7298760331420069275934537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9731680441893425701246049 7298760331420069275934537)
        ·
          refine ⟨5474070248565051956950903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7298760331420069275934537 5474070248565051956950903)
          ·
            refine ⟨8211105372847577935426355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474070248565051956950903 8211105372847577935426355)
            ·
              refine ⟨12316658059271366903139533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211105372847577935426355 12316658059271366903139533)
              ·
                refine ⟨4618746772226762588677325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12316658059271366903139533 4618746772226762588677325)
                ·
                  refine ⟨1732030039585035970753997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4618746772226762588677325 1732030039585035970753997)
                  ·
                    refine ⟨649511264844388489032749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732030039585035970753997 649511264844388489032749)
                    ·
                      rfl

theorem cell22_1897378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1897378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897378 prefixEnd_1897378 := by exact prefixLift 1897378
  have htrace : WordTrace (prefixWord ++ tailWord_1897378) baseStart_1897378 baseEnd_1897378 := by
    simpa [prefixWord, tailWord_1897378, baseEnd_1897378] using wordTrace_append hprefix tailTrace_1897378
  have hstable : (prefixWord ++ tailWord_1897378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897378).length < 2 ^ (prefixWord ++ tailWord_1897378).sum := by decide
  have hdescent : baseEnd_1897378 < baseStart_1897378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897414 : List Nat := [6, 1, 3, 1, 2, 1, 8]
def baseStart_1897414 : Nat := 118140960795 + 1897414 * 2 ^ 59
def prefixEnd_1897414 : Nat := 4983230072969 + 3 ^ 40 * 1897414 * 2
def baseEnd_1897414 : Nat := 24056429199262829449357

theorem tailTrace_1897414 : CollatzResearch.WordTrace tailWord_1897414 prefixEnd_1897414 24056429199262829449357 := by
  unfold tailWord_1897414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162636685875018917411603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46136249298667070238114197 2162636685875018917411603)
  ·
    refine ⟨3243955028812528376117405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2162636685875018917411603 3243955028812528376117405)
    ·
      refine ⟨1216483135804698141044027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3243955028812528376117405 1216483135804698141044027)
      ·
        refine ⟨1824724703707047211566041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216483135804698141044027 1824724703707047211566041)
        ·
          refine ⟨1368543527780285408674531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824724703707047211566041 1368543527780285408674531)
          ·
            refine ⟨2052815291670428113011797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368543527780285408674531 2052815291670428113011797)
            ·
              refine ⟨24056429199262829449357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2052815291670428113011797 24056429199262829449357)
              ·
                rfl

theorem cell22_1897414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 8].length) (baseStart_1897414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897414 prefixEnd_1897414 := by exact prefixLift 1897414
  have htrace : WordTrace (prefixWord ++ tailWord_1897414) baseStart_1897414 baseEnd_1897414 := by
    simpa [prefixWord, tailWord_1897414, baseEnd_1897414] using wordTrace_append hprefix tailTrace_1897414
  have hstable : (prefixWord ++ tailWord_1897414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897414).length < 2 ^ (prefixWord ++ tailWord_1897414).sum := by decide
  have hdescent : baseEnd_1897414 < baseStart_1897414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897442 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1897442 : Nat := 118140960795 + 1897442 * 2 ^ 59
def prefixEnd_1897442 : Nat := 4983230072969 + 3 ^ 40 * 1897442 * 2
def baseEnd_1897442 : Nat := 216511057784104551810851

theorem tailTrace_1897442 : CollatzResearch.WordTrace tailWord_1897442 prefixEnd_1897442 216511057784104551810851 := by
  unfold tailWord_1897442
  simp only [CollatzResearch.WordTrace]
  refine ⟨17301348797974791534797645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46136930127932777426127053 17301348797974791534797645)
  ·
    refine ⟨6488005799240546825549117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17301348797974791534797645 6488005799240546825549117)
    ·
      refine ⟨2433002174715205059580919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6488005799240546825549117 2433002174715205059580919)
      ·
        refine ⟨3649503262072807589371379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433002174715205059580919 3649503262072807589371379)
        ·
          refine ⟨5474254893109211384057069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649503262072807589371379 5474254893109211384057069)
          ·
            refine ⟨2052845584915954269021401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5474254893109211384057069 2052845584915954269021401)
            ·
              refine ⟨1539634188686965701766051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052845584915954269021401 1539634188686965701766051)
              ·
                refine ⟨2309451283030448552649077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539634188686965701766051 2309451283030448552649077)
                ·
                  refine ⟨216511057784104551810851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2309451283030448552649077 216511057784104551810851)
                  ·
                    rfl

theorem cell22_1897442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1897442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897442 prefixEnd_1897442 := by exact prefixLift 1897442
  have htrace : WordTrace (prefixWord ++ tailWord_1897442) baseStart_1897442 baseEnd_1897442 := by
    simpa [prefixWord, tailWord_1897442, baseEnd_1897442] using wordTrace_append hprefix tailTrace_1897442
  have hstable : (prefixWord ++ tailWord_1897442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897442).length < 2 ^ (prefixWord ++ tailWord_1897442).sum := by decide
  have hdescent : baseEnd_1897442 < baseStart_1897442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897530 : List Nat := [3, 1, 1, 1, 3, 1, 3, 5, 1, 3]
def baseStart_1897530 : Nat := 118140960795 + 1897530 * 2 ^ 59
def prefixEnd_1897530 : Nat := 4983230072969 + 3 ^ 40 * 1897530 * 2
def baseEnd_1897530 : Nat := 649563297550710759232283

theorem tailTrace_1897530 : CollatzResearch.WordTrace tailWord_1897530 prefixEnd_1897530 649563297550710759232283 := by
  unfold tailWord_1897530
  simp only [CollatzResearch.WordTrace]
  refine ⟨17302151203895089292098511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46139069877053571445596029 17302151203895089292098511)
  ·
    refine ⟨25953226805842633938147767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17302151203895089292098511 25953226805842633938147767)
    ·
      refine ⟨38929840208763950907221651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25953226805842633938147767 38929840208763950907221651)
      ·
        refine ⟨58394760313145926360832477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38929840208763950907221651 58394760313145926360832477)
        ·
          refine ⟨21898035117429722385312179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58394760313145926360832477 21898035117429722385312179)
          ·
            refine ⟨32847052676144583577968269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21898035117429722385312179 32847052676144583577968269)
            ·
              refine ⟨12317644753554218841738101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32847052676144583577968269 12317644753554218841738101)
              ·
                refine ⟨1154779195645708016412947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12317644753554218841738101 1154779195645708016412947)
                ·
                  refine ⟨1732168793468562024619421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154779195645708016412947 1732168793468562024619421)
                  ·
                    refine ⟨649563297550710759232283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732168793468562024619421 649563297550710759232283)
                    ·
                      rfl

theorem cell22_1897530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_1897530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897530 prefixEnd_1897530 := by exact prefixLift 1897530
  have htrace : WordTrace (prefixWord ++ tailWord_1897530) baseStart_1897530 baseEnd_1897530 := by
    simpa [prefixWord, tailWord_1897530, baseEnd_1897530] using wordTrace_append hprefix tailTrace_1897530
  have hstable : (prefixWord ++ tailWord_1897530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897530).length < 2 ^ (prefixWord ++ tailWord_1897530).sum := by decide
  have hdescent : baseEnd_1897530 < baseStart_1897530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897541 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_1897541 : Nat := 118140960795 + 1897541 * 2 ^ 59
def prefixEnd_1897541 : Nat := 4983230072969 + 3 ^ 40 * 1897541 * 2
def baseEnd_1897541 : Nat := 649567063075510397207249

theorem tailTrace_1897541 : CollatzResearch.WordTrace tailWord_1897541 prefixEnd_1897541 649567063075510397207249 := by
  unfold tailWord_1897541
  simp only [CollatzResearch.WordTrace]
  refine ⟨69209006018540506047044477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46139337345693670698029651 69209006018540506047044477)
  ·
    refine ⟨25953377256952689767641679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69209006018540506047044477 25953377256952689767641679)
    ·
      refine ⟨38930065885429034651462519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25953377256952689767641679 38930065885429034651462519)
      ·
        refine ⟨58395098828143551977193779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38930065885429034651462519 58395098828143551977193779)
        ·
          refine ⟨87592648242215327965790669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58395098828143551977193779 87592648242215327965790669)
          ·
            refine ⟨32847243090830747987171501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87592648242215327965790669 32847243090830747987171501)
            ·
              refine ⟨12317716159061530495189313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32847243090830747987171501 12317716159061530495189313)
              ·
                refine ⟨9238287119296147871391985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12317716159061530495189313 9238287119296147871391985)
                ·
                  refine ⟨6928715339472110903543989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9238287119296147871391985 6928715339472110903543989)
                  ·
                    refine ⟨649567063075510397207249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6928715339472110903543989 649567063075510397207249)
                    ·
                      rfl

theorem cell22_1897541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_1897541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897541 prefixEnd_1897541 := by exact prefixLift 1897541
  have htrace : WordTrace (prefixWord ++ tailWord_1897541) baseStart_1897541 baseEnd_1897541 := by
    simpa [prefixWord, tailWord_1897541, baseEnd_1897541] using wordTrace_append hprefix tailTrace_1897541
  have hstable : (prefixWord ++ tailWord_1897541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897541).length < 2 ^ (prefixWord ++ tailWord_1897541).sum := by decide
  have hdescent : baseEnd_1897541 < baseStart_1897541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897543 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 5]
def baseStart_1897543 : Nat := 118140960795 + 1897543 * 2 ^ 59
def prefixEnd_1897543 : Nat := 4983230072969 + 3 ^ 40 * 1897543 * 2
def baseEnd_1897543 : Nat := 216522582572127686219081

theorem tailTrace_1897543 : CollatzResearch.WordTrace tailWord_1897543 prefixEnd_1897543 216522582572127686219081 := by
  unfold tailWord_1897543
  simp only [CollatzResearch.WordTrace]
  refine ⟨69209078964533260388617283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46139385976355506925744855 69209078964533260388617283)
  ·
    refine ⟨103813618446799890582925925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69209078964533260388617283 103813618446799890582925925)
    ·
      refine ⟨19465053458774979484298611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103813618446799890582925925 19465053458774979484298611)
      ·
        refine ⟨29197580188162469226447917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19465053458774979484298611 29197580188162469226447917)
        ·
          refine ⟨10949092570560925959917969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29197580188162469226447917 10949092570560925959917969)
          ·
            refine ⟨8211819427920694469938477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10949092570560925959917969 8211819427920694469938477)
            ·
              refine ⟨3079432285470260426226929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8211819427920694469938477 3079432285470260426226929)
              ·
                refine ⟨2309574214102695319670197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3079432285470260426226929 2309574214102695319670197)
                ·
                  refine ⟨216522582572127686219081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2309574214102695319670197 216522582572127686219081)
                  ·
                    rfl

theorem cell22_1897543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 5].length) (baseStart_1897543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897543 prefixEnd_1897543 := by exact prefixLift 1897543
  have htrace : WordTrace (prefixWord ++ tailWord_1897543) baseStart_1897543 baseEnd_1897543 := by
    simpa [prefixWord, tailWord_1897543, baseEnd_1897543] using wordTrace_append hprefix tailTrace_1897543
  have hstable : (prefixWord ++ tailWord_1897543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897543).length < 2 ^ (prefixWord ++ tailWord_1897543).sum := by decide
  have hdescent : baseEnd_1897543 < baseStart_1897543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897590 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_1897590 : Nat := 118140960795 + 1897590 * 2 ^ 59
def prefixEnd_1897590 : Nat := 4983230072969 + 3 ^ 40 * 1897590 * 2
def baseEnd_1897590 : Nat := 649583836776890602732099

theorem tailTrace_1897590 : CollatzResearch.WordTrace tailWord_1897590 prefixEnd_1897590 649583836776890602732099 := by
  unfold tailWord_1897590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325674574710186713473639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46140528796908658277052149 4325674574710186713473639)
  ·
    refine ⟨6488511862065280070210459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4325674574710186713473639 6488511862065280070210459)
    ·
      refine ⟨9732767793097920105315689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6488511862065280070210459 9732767793097920105315689)
      ·
        refine ⟨7299575844823440078986767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9732767793097920105315689 7299575844823440078986767)
        ·
          refine ⟨10949363767235160118480151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299575844823440078986767 10949363767235160118480151)
          ·
            refine ⟨16424045650852740177720227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10949363767235160118480151 16424045650852740177720227)
            ·
              refine ⟨24636068476279110266580341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16424045650852740177720227 24636068476279110266580341)
              ·
                refine ⟨2309631419651166587491907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24636068476279110266580341 2309631419651166587491907)
                ·
                  refine ⟨3464447129476749881237861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309631419651166587491907 3464447129476749881237861)
                  ·
                    refine ⟨649583836776890602732099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464447129476749881237861 649583836776890602732099)
                    ·
                      rfl

theorem cell22_1897590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_1897590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897590 prefixEnd_1897590 := by exact prefixLift 1897590
  have htrace : WordTrace (prefixWord ++ tailWord_1897590) baseStart_1897590 baseEnd_1897590 := by
    simpa [prefixWord, tailWord_1897590, baseEnd_1897590] using wordTrace_append hprefix tailTrace_1897590
  have hstable : (prefixWord ++ tailWord_1897590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897590).length < 2 ^ (prefixWord ++ tailWord_1897590).sum := by decide
  have hdescent : baseEnd_1897590 < baseStart_1897590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897598 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1897598 : Nat := 118140960795 + 1897598 * 2 ^ 59
def prefixEnd_1897598 : Nat := 4983230072969 + 3 ^ 40 * 1897598 * 2
def baseEnd_1897598 : Nat := 649586575340381248532075

theorem tailTrace_1897598 : CollatzResearch.WordTrace tailWord_1897598 prefixEnd_1897598 649586575340381248532075 := by
  unfold tailWord_1897598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8651385622416750597733681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46140723319556003187912965 8651385622416750597733681)
  ·
    refine ⟨6488539216812562948300261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8651385622416750597733681 6488539216812562948300261)
    ·
      refine ⟨1216601103152355552806299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6488539216812562948300261 1216601103152355552806299)
      ·
        refine ⟨1824901654728533329209449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216601103152355552806299 1824901654728533329209449)
        ·
          refine ⟨1368676241046399996907087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824901654728533329209449 1368676241046399996907087)
          ·
            refine ⟨2053014361569599995360631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368676241046399996907087 2053014361569599995360631)
            ·
              refine ⟨3079521542354399993040947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053014361569599995360631 3079521542354399993040947)
              ·
                refine ⟨4619282313531599989561421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079521542354399993040947 4619282313531599989561421)
                ·
                  refine ⟨1732230867574349996085533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4619282313531599989561421 1732230867574349996085533)
                  ·
                    refine ⟨649586575340381248532075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732230867574349996085533 649586575340381248532075)
                    ·
                      rfl

theorem cell22_1897598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1897598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897598 prefixEnd_1897598 := by exact prefixLift 1897598
  have htrace : WordTrace (prefixWord ++ tailWord_1897598) baseStart_1897598 baseEnd_1897598 := by
    simpa [prefixWord, tailWord_1897598, baseEnd_1897598] using wordTrace_append hprefix tailTrace_1897598
  have hstable : (prefixWord ++ tailWord_1897598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897598).length < 2 ^ (prefixWord ++ tailWord_1897598).sum := by decide
  have hdescent : baseEnd_1897598 < baseStart_1897598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897603 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 4, 3]
def baseStart_1897603 : Nat := 118140960795 + 1897603 * 2 ^ 59
def prefixEnd_1897603 : Nat := 4983230072969 + 3 ^ 40 * 1897603 * 2
def baseEnd_1897603 : Nat := 649588286942562902157059

theorem tailTrace_1897603 : CollatzResearch.WordTrace tailWord_1897603 prefixEnd_1897603 649588286942562902157059 := by
  unfold tailWord_1897603
  simp only [CollatzResearch.WordTrace]
  refine ⟨69211267344315890635801463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46140844896210593757200975 69211267344315890635801463)
  ·
    refine ⟨103816901016473835953702195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69211267344315890635801463 103816901016473835953702195)
    ·
      refine ⟨155725351524710753930553293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103816901016473835953702195 155725351524710753930553293)
      ·
        refine ⟨58397006821766532723957485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155725351524710753930553293 58397006821766532723957485)
        ·
          refine ⟨21898877558162449771484057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58397006821766532723957485 21898877558162449771484057)
          ·
            refine ⟨16424158168621837328613043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21898877558162449771484057 16424158168621837328613043)
            ·
              refine ⟨24636237252932755992919565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16424158168621837328613043 24636237252932755992919565)
              ·
                refine ⟨9238588969849783497344837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24636237252932755992919565 9238588969849783497344837)
                ·
                  refine ⟨1732235431846834405752157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9238588969849783497344837 1732235431846834405752157)
                  ·
                    refine ⟨649588286942562902157059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732235431846834405752157 649588286942562902157059)
                    ·
                      rfl

theorem cell22_1897603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 3].length) (baseStart_1897603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897603 prefixEnd_1897603 := by exact prefixLift 1897603
  have htrace : WordTrace (prefixWord ++ tailWord_1897603) baseStart_1897603 baseEnd_1897603 := by
    simpa [prefixWord, tailWord_1897603, baseEnd_1897603] using wordTrace_append hprefix tailTrace_1897603
  have hstable : (prefixWord ++ tailWord_1897603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897603).length < 2 ^ (prefixWord ++ tailWord_1897603).sum := by decide
  have hdescent : baseEnd_1897603 < baseStart_1897603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897605 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 6]
def baseStart_1897605 : Nat := 118140960795 + 1897605 * 2 ^ 59
def prefixEnd_1897605 : Nat := 4983230072969 + 3 ^ 40 * 1897605 * 2
def baseEnd_1897605 : Nat := 216529657194478521202351

theorem tailTrace_1897605 : CollatzResearch.WordTrace tailWord_1897605 prefixEnd_1897605 216529657194478521202351 := by
  unfold tailWord_1897605
  simp only [CollatzResearch.WordTrace]
  refine ⟨69211340290308644977374269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46140893526872429984916179 69211340290308644977374269)
  ·
    refine ⟨25954252608865741866515351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69211340290308644977374269 25954252608865741866515351)
    ·
      refine ⟨38931378913298612799773027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25954252608865741866515351 38931378913298612799773027)
      ·
        refine ⟨58397068369947919199659541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38931378913298612799773027 58397068369947919199659541)
        ·
          refine ⟨2737362579841308712484041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58397068369947919199659541 2737362579841308712484041)
          ·
            refine ⟨2053021934880981534363031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2737362579841308712484041 2053021934880981534363031)
            ·
              refine ⟨3079532902321472301544547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053021934880981534363031 3079532902321472301544547)
              ·
                refine ⟨4619299353482208452316821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079532902321472301544547 4619299353482208452316821)
                ·
                  refine ⟨216529657194478521202351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4619299353482208452316821 216529657194478521202351)
                  ·
                    rfl

theorem cell22_1897605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_1897605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897605 prefixEnd_1897605 := by exact prefixLift 1897605
  have htrace : WordTrace (prefixWord ++ tailWord_1897605) baseStart_1897605 baseEnd_1897605 := by
    simpa [prefixWord, tailWord_1897605, baseEnd_1897605] using wordTrace_append hprefix tailTrace_1897605
  have hstable : (prefixWord ++ tailWord_1897605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897605).length < 2 ^ (prefixWord ++ tailWord_1897605).sum := by decide
  have hdescent : baseEnd_1897605 < baseStart_1897605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897648 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 5, 3]
def baseStart_1897648 : Nat := 118140960795 + 1897648 * 2 ^ 59
def prefixEnd_1897648 : Nat := 4983230072969 + 3 ^ 40 * 1897648 * 2
def baseEnd_1897648 : Nat := 649603691362197784781921

theorem tailTrace_1897648 : CollatzResearch.WordTrace tailWord_1897648 prefixEnd_1897648 649603691362197784781921 := by
  unfold tailWord_1897648
  simp only [CollatzResearch.WordTrace]
  refine ⟨34606454314576431660594799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46141939086101908880793065 34606454314576431660594799)
  ·
    refine ⟨51909681471864647490892199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34606454314576431660594799 51909681471864647490892199)
    ·
      refine ⟨77864522207796971236338299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51909681471864647490892199 77864522207796971236338299)
      ·
        refine ⟨116796783311695456854507449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77864522207796971236338299 116796783311695456854507449)
        ·
          refine ⟨87597587483771592640880587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116796783311695456854507449 87597587483771592640880587)
          ·
            refine ⟨131396381225657388961320881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87597587483771592640880587 131396381225657388961320881)
            ·
              refine ⟨98547285919243041720990661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131396381225657388961320881 98547285919243041720990661)
              ·
                refine ⟨18477616109858070322685749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98547285919243041720990661 18477616109858070322685749)
                ·
                  refine ⟨1732276510299194092751789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18477616109858070322685749 1732276510299194092751789)
                  ·
                    refine ⟨649603691362197784781921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732276510299194092751789 649603691362197784781921)
                    ·
                      rfl

theorem cell22_1897648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_1897648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897648 prefixEnd_1897648 := by exact prefixLift 1897648
  have htrace : WordTrace (prefixWord ++ tailWord_1897648) baseStart_1897648 baseEnd_1897648 := by
    simpa [prefixWord, tailWord_1897648, baseEnd_1897648] using wordTrace_append hprefix tailTrace_1897648
  have hstable : (prefixWord ++ tailWord_1897648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897648).length < 2 ^ (prefixWord ++ tailWord_1897648).sum := by decide
  have hdescent : baseEnd_1897648 < baseStart_1897648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897686 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_1897686 : Nat := 118140960795 + 1897686 * 2 ^ 59
def prefixEnd_1897686 : Nat := 4983230072969 + 3 ^ 40 * 1897686 * 2
def baseEnd_1897686 : Nat := 649616699538778352331805

theorem tailTrace_1897686 : CollatzResearch.WordTrace tailWord_1897686 prefixEnd_1897686 649616699538778352331805 := by
  unfold tailWord_1897686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325893412688449738192057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46142863068676797207381941 4325893412688449738192057)
  ·
    refine ⟨3244420059516337303644043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4325893412688449738192057 3244420059516337303644043)
    ·
      refine ⟨4866630089274505955466065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3244420059516337303644043 4866630089274505955466065)
      ·
        refine ⟨3649972566955879466599549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4866630089274505955466065 3649972566955879466599549)
        ·
          refine ⟨1368739712608454799974831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3649972566955879466599549 1368739712608454799974831)
          ·
            refine ⟨2053109568912682199962247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368739712608454799974831 2053109568912682199962247)
            ·
              refine ⟨3079664353369023299943371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053109568912682199962247 3079664353369023299943371)
              ·
                refine ⟨4619496530053534949915057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079664353369023299943371 4619496530053534949915057)
                ·
                  refine ⟨3464622397540151212436293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4619496530053534949915057 3464622397540151212436293)
                  ·
                    refine ⟨649616699538778352331805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464622397540151212436293 649616699538778352331805)
                    ·
                      rfl

theorem cell22_1897686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_1897686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897686 prefixEnd_1897686 := by exact prefixLift 1897686
  have htrace : WordTrace (prefixWord ++ tailWord_1897686) baseStart_1897686 baseEnd_1897686 := by
    simpa [prefixWord, tailWord_1897686, baseEnd_1897686] using wordTrace_append hprefix tailTrace_1897686
  have hstable : (prefixWord ++ tailWord_1897686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897686).length < 2 ^ (prefixWord ++ tailWord_1897686).sum := by decide
  have hdescent : baseEnd_1897686 < baseStart_1897686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897742 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_1897742 : Nat := 118140960795 + 1897742 * 2 ^ 59
def prefixEnd_1897742 : Nat := 4983230072969 + 3 ^ 40 * 1897742 * 2
def baseEnd_1897742 : Nat := 649635869483212872931633

theorem tailTrace_1897742 : CollatzResearch.WordTrace tailWord_1897742 prefixEnd_1897742 649635869483212872931633 := by
  unfold tailWord_1897742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652042136351539671888935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46144224727208211583407653 8652042136351539671888935)
  ·
    refine ⟨12978063204527309507833403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8652042136351539671888935 12978063204527309507833403)
    ·
      refine ⟨19467094806790964261750105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12978063204527309507833403 19467094806790964261750105)
      ·
        refine ⟨14600321105093223196312579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19467094806790964261750105 14600321105093223196312579)
        ·
          refine ⟨21900481657639834794468869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14600321105093223196312579 21900481657639834794468869)
          ·
            refine ⟨4106340310807469023962913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21900481657639834794468869 4106340310807469023962913)
            ·
              refine ⟨3079755233105601767972185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4106340310807469023962913 3079755233105601767972185)
              ·
                refine ⟨2309816424829201325979139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3079755233105601767972185 2309816424829201325979139)
                ·
                  refine ⟨3464724637243801988968709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309816424829201325979139 3464724637243801988968709)
                  ·
                    refine ⟨649635869483212872931633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464724637243801988968709 649635869483212872931633)
                    ·
                      rfl

theorem cell22_1897742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_1897742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897742 prefixEnd_1897742 := by exact prefixLift 1897742
  have htrace : WordTrace (prefixWord ++ tailWord_1897742) baseStart_1897742 baseEnd_1897742 := by
    simpa [prefixWord, tailWord_1897742, baseEnd_1897742] using wordTrace_append hprefix tailTrace_1897742
  have hstable : (prefixWord ++ tailWord_1897742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897742).length < 2 ^ (prefixWord ++ tailWord_1897742).sum := by decide
  have hdescent : baseEnd_1897742 < baseStart_1897742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897753 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_1897753 : Nat := 118140960795 + 1897753 * 2 ^ 59
def prefixEnd_1897753 : Nat := 4983230072969 + 3 ^ 40 * 1897753 * 2
def baseEnd_1897753 : Nat := 649639635008012510906599

theorem tailTrace_1897753 : CollatzResearch.WordTrace tailWord_1897753 prefixEnd_1897753 649639635008012510906599 := by
  unfold tailWord_1897753
  simp only [CollatzResearch.WordTrace]
  refine ⟨69216738293772466253761913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46144492195848310835841275 69216738293772466253761913)
  ·
    refine ⟨51912553720329349690321435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69216738293772466253761913 51912553720329349690321435)
    ·
      refine ⟨77868830580494024535482153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51912553720329349690321435 77868830580494024535482153)
      ·
        refine ⟨58401622935370518401611615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77868830580494024535482153 58401622935370518401611615)
        ·
          refine ⟨87602434403055777602417423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58401622935370518401611615 87602434403055777602417423)
          ·
            refine ⟨131403651604583666403626135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87602434403055777602417423 131403651604583666403626135)
            ·
              refine ⟨197105477406875499605439203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131403651604583666403626135 197105477406875499605439203)
              ·
                refine ⟨295658216110313249408158805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197105477406875499605439203 295658216110313249408158805)
                ·
                  refine ⟨3464744720042733391501861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 295658216110313249408158805 3464744720042733391501861)
                  ·
                    refine ⟨649639635008012510906599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3464744720042733391501861 649639635008012510906599)
                    ·
                      rfl

theorem cell22_1897753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_1897753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897753 prefixEnd_1897753 := by exact prefixLift 1897753
  have htrace : WordTrace (prefixWord ++ tailWord_1897753) baseStart_1897753 baseEnd_1897753 := by
    simpa [prefixWord, tailWord_1897753, baseEnd_1897753] using wordTrace_append hprefix tailTrace_1897753
  have hstable : (prefixWord ++ tailWord_1897753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897753).length < 2 ^ (prefixWord ++ tailWord_1897753).sum := by decide
  have hdescent : baseEnd_1897753 < baseStart_1897753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897800 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 5, 3]
def baseStart_1897800 : Nat := 118140960795 + 1897800 * 2 ^ 59
def prefixEnd_1897800 : Nat := 4983230072969 + 3 ^ 40 * 1897800 * 2
def baseEnd_1897800 : Nat := 649655724068520054981455

theorem tailTrace_1897800 : CollatzResearch.WordTrace tailWord_1897800 prefixEnd_1897800 649655724068520054981455 := by
  unfold tailWord_1897800
  simp only [CollatzResearch.WordTrace]
  refine ⟨34609226262301096640361427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46145635016401462187148569 34609226262301096640361427)
  ·
    refine ⟨51913839393451644960542141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34609226262301096640361427 51913839393451644960542141)
    ·
      refine ⟨19467689772544366860203303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51913839393451644960542141 19467689772544366860203303)
      ·
        refine ⟨29201534658816550290304955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19467689772544366860203303 29201534658816550290304955)
        ·
          refine ⟨43802301988224825435457433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29201534658816550290304955 43802301988224825435457433)
          ·
            refine ⟨32851726491168619076593075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43802301988224825435457433 32851726491168619076593075)
            ·
              refine ⟨49277589736752928614889613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32851726491168619076593075 49277589736752928614889613)
              ·
                refine ⟨18479096151282348230583605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49277589736752928614889613 18479096151282348230583605)
                ·
                  refine ⟨1732415264182720146617213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18479096151282348230583605 1732415264182720146617213)
                  ·
                    refine ⟨649655724068520054981455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732415264182720146617213 649655724068520054981455)
                    ·
                      rfl

theorem cell22_1897800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_1897800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897800 prefixEnd_1897800 := by exact prefixLift 1897800
  have htrace : WordTrace (prefixWord ++ tailWord_1897800) baseStart_1897800 baseEnd_1897800 := by
    simpa [prefixWord, tailWord_1897800, baseEnd_1897800] using wordTrace_append hprefix tailTrace_1897800
  have hstable : (prefixWord ++ tailWord_1897800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897800).length < 2 ^ (prefixWord ++ tailWord_1897800).sum := by decide
  have hdescent : baseEnd_1897800 < baseStart_1897800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897843 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 10]
def baseStart_1897843 : Nat := 118140960795 + 1897843 * 2 ^ 59
def prefixEnd_1897843 : Nat := 4983230072969 + 3 ^ 40 * 1897843 * 2
def baseEnd_1897843 : Nat := 649670443847282276156323

theorem tailTrace_1897843 : CollatzResearch.WordTrace tailWord_1897843 prefixEnd_1897843 649670443847282276156323 := by
  unfold tailWord_1897843
  simp only [CollatzResearch.WordTrace]
  refine ⟨69220020863446411624538183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46146680575630941083025455 69220020863446411624538183)
  ·
    refine ⟨103830031295169617436807275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69220020863446411624538183 103830031295169617436807275)
    ·
      refine ⟨155745046942754426155210913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103830031295169617436807275 155745046942754426155210913)
      ·
        refine ⟨116808785207065819616408185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155745046942754426155210913 116808785207065819616408185)
        ·
          refine ⟨87606588905299364712306139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116808785207065819616408185 87606588905299364712306139)
          ·
            refine ⟨131409883357949047068459209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87606588905299364712306139 131409883357949047068459209)
            ·
              refine ⟨98557412518461785301344407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131409883357949047068459209 98557412518461785301344407)
              ·
                refine ⟨147836118777692677952016611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98557412518461785301344407 147836118777692677952016611)
                ·
                  refine ⟨221754178166539016928024917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147836118777692677952016611 221754178166539016928024917)
                  ·
                    refine ⟨649670443847282276156323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 221754178166539016928024917 649670443847282276156323)
                    ·
                      rfl

theorem cell22_1897843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_1897843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897843 prefixEnd_1897843 := by exact prefixLift 1897843
  have htrace : WordTrace (prefixWord ++ tailWord_1897843) baseStart_1897843 baseEnd_1897843 := by
    simpa [prefixWord, tailWord_1897843, baseEnd_1897843] using wordTrace_append hprefix tailTrace_1897843
  have hstable : (prefixWord ++ tailWord_1897843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897843).length < 2 ^ (prefixWord ++ tailWord_1897843).sum := by decide
  have hdescent : baseEnd_1897843 < baseStart_1897843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897905 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_1897905 : Nat := 118140960795 + 1897905 * 2 ^ 59
def prefixEnd_1897905 : Nat := 4983230072969 + 3 ^ 40 * 1897905 * 2
def baseEnd_1897905 : Nat := 649691667714334781106133

theorem tailTrace_1897905 : CollatzResearch.WordTrace tailWord_1897905 prefixEnd_1897905 649691667714334781106133 := by
  unfold tailWord_1897905
  simp only [CollatzResearch.WordTrace]
  refine ⟨69222282189221796213295169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46148188126147864142196779 69222282189221796213295169)
  ·
    refine ⟨51916711641916347159971377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69222282189221796213295169 51916711641916347159971377)
    ·
      refine ⟨38937533731437260369978533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51916711641916347159971377 38937533731437260369978533)
      ·
        refine ⟨7300787574644486319370975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38937533731437260369978533 7300787574644486319370975)
        ·
          refine ⟨10951181361966729479056463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7300787574644486319370975 10951181361966729479056463)
          ·
            refine ⟨16426772042950094218584695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10951181361966729479056463 16426772042950094218584695)
            ·
              refine ⟨24640158064425141327877043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16426772042950094218584695 24640158064425141327877043)
              ·
                refine ⟨36960237096637711991815565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24640158064425141327877043 36960237096637711991815565)
                ·
                  refine ⟨13860088911239141996930837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36960237096637711991815565 13860088911239141996930837)
                  ·
                    refine ⟨649691667714334781106133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13860088911239141996930837 649691667714334781106133)
                    ·
                      rfl

theorem cell22_1897905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_1897905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897905 prefixEnd_1897905 := by exact prefixLift 1897905
  have htrace : WordTrace (prefixWord ++ tailWord_1897905) baseStart_1897905 baseEnd_1897905 := by
    simpa [prefixWord, tailWord_1897905, baseEnd_1897905] using wordTrace_append hprefix tailTrace_1897905
  have hstable : (prefixWord ++ tailWord_1897905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897905).length < 2 ^ (prefixWord ++ tailWord_1897905).sum := by decide
  have hdescent : baseEnd_1897905 < baseStart_1897905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897907 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 2, 3]
def baseStart_1897907 : Nat := 118140960795 + 1897907 * 2 ^ 59
def prefixEnd_1897907 : Nat := 4983230072969 + 3 ^ 40 * 1897907 * 2
def baseEnd_1897907 : Nat := 649692352355207442556127

theorem tailTrace_1897907 : CollatzResearch.WordTrace tailWord_1897907 prefixEnd_1897907 649692352355207442556127 := by
  unfold tailWord_1897907
  simp only [CollatzResearch.WordTrace]
  refine ⟨69222355135214550554867975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46148236756809700369911983 69222355135214550554867975)
  ·
    refine ⟨103833532702821825832301963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69222355135214550554867975 103833532702821825832301963)
    ·
      refine ⟨155750299054232738748452945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103833532702821825832301963 155750299054232738748452945)
      ·
        refine ⟨116812724290674554061339709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155750299054232738748452945 116812724290674554061339709)
        ·
          refine ⟨43804771609002957773002391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116812724290674554061339709 43804771609002957773002391)
          ·
            refine ⟨65707157413504436659503587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43804771609002957773002391 65707157413504436659503587)
            ·
              refine ⟨98560736120256654989255381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65707157413504436659503587 98560736120256654989255381)
              ·
                refine ⟨2310017252818515351310673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98560736120256654989255381 2310017252818515351310673)
                ·
                  refine ⟨1732512939613886513483005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2310017252818515351310673 1732512939613886513483005)
                  ·
                    refine ⟨649692352355207442556127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732512939613886513483005 649692352355207442556127)
                    ·
                      rfl

theorem cell22_1897907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 3].length) (baseStart_1897907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897907 prefixEnd_1897907 := by exact prefixLift 1897907
  have htrace : WordTrace (prefixWord ++ tailWord_1897907) baseStart_1897907 baseEnd_1897907 := by
    simpa [prefixWord, tailWord_1897907, baseEnd_1897907] using wordTrace_append hprefix tailTrace_1897907
  have hstable : (prefixWord ++ tailWord_1897907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897907).length < 2 ^ (prefixWord ++ tailWord_1897907).sum := by decide
  have hdescent : baseEnd_1897907 < baseStart_1897907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897924 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1897924 : Nat := 118140960795 + 1897924 * 2 ^ 59
def prefixEnd_1897924 : Nat := 4983230072969 + 3 ^ 40 * 1897924 * 2
def baseEnd_1897924 : Nat := 649698171802625064881075

theorem tailTrace_1897924 : CollatzResearch.WordTrace tailWord_1897924 prefixEnd_1897924 649698171802625064881075 := by
  unfold tailWord_1897924
  simp only [CollatzResearch.WordTrace]
  refine ⟨34611487588076481229118413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46148650117435308305491217 34611487588076481229118413)
  ·
    refine ⟨12979307845528680460919405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34611487588076481229118413 12979307845528680460919405)
    ·
      refine ⟨4867240442073255172844777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12979307845528680460919405 4867240442073255172844777)
      ·
        refine ⟨3650430331554941379633583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4867240442073255172844777 3650430331554941379633583)
        ·
          refine ⟨5475645497332412069450375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3650430331554941379633583 5475645497332412069450375)
          ·
            refine ⟨8213468245998618104175563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5475645497332412069450375 8213468245998618104175563)
            ·
              refine ⟨12320202368997927156263345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8213468245998618104175563 12320202368997927156263345)
              ·
                refine ⟨9240151776748445367197509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12320202368997927156263345 9240151776748445367197509)
                ·
                  refine ⟨1732528458140333506349533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9240151776748445367197509 1732528458140333506349533)
                  ·
                    refine ⟨649698171802625064881075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732528458140333506349533 649698171802625064881075)
                    ·
                      rfl

theorem cell22_1897924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1897924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897924 prefixEnd_1897924 := by exact prefixLift 1897924
  have htrace : WordTrace (prefixWord ++ tailWord_1897924) baseStart_1897924 baseEnd_1897924 := by
    simpa [prefixWord, tailWord_1897924, baseEnd_1897924] using wordTrace_append hprefix tailTrace_1897924
  have hstable : (prefixWord ++ tailWord_1897924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897924).length < 2 ^ (prefixWord ++ tailWord_1897924).sum := by decide
  have hdescent : baseEnd_1897924 < baseStart_1897924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897952 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 3, 3]
def baseStart_1897952 : Nat := 118140960795 + 1897952 * 2 ^ 59
def prefixEnd_1897952 : Nat := 4983230072969 + 3 ^ 40 * 1897952 * 2
def baseEnd_1897952 : Nat := 649707756774842325180989

theorem tailTrace_1897952 : CollatzResearch.WordTrace tailWord_1897952 prefixEnd_1897952 649707756774842325180989 := by
  unfold tailWord_1897952
  simp only [CollatzResearch.WordTrace]
  refine ⟨34611998210025761620128055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46149330946701015493504073 34611998210025761620128055)
  ·
    refine ⟨51917997315038642430192083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34611998210025761620128055 51917997315038642430192083)
    ·
      refine ⟨77876995972557963645288125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51917997315038642430192083 77876995972557963645288125)
      ·
        refine ⟨29203873489709236366983047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77876995972557963645288125 29203873489709236366983047)
        ·
          refine ⟨43805810234563854550474571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29203873489709236366983047 43805810234563854550474571)
          ·
            refine ⟨65708715351845781825711857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43805810234563854550474571 65708715351845781825711857)
            ·
              refine ⟨49281536513884336369283893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65708715351845781825711857 49281536513884336369283893)
              ·
                refine ⟨4620144048176656534620365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49281536513884336369283893 4620144048176656534620365)
                ·
                  refine ⟨1732554018066246200482637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4620144048176656534620365 1732554018066246200482637)
                  ·
                    refine ⟨649707756774842325180989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732554018066246200482637 649707756774842325180989)
                    ·
                      rfl

theorem cell22_1897952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_1897952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1897952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1897952 prefixEnd_1897952 := by exact prefixLift 1897952
  have htrace : WordTrace (prefixWord ++ tailWord_1897952) baseStart_1897952 baseEnd_1897952 := by
    simpa [prefixWord, tailWord_1897952, baseEnd_1897952] using wordTrace_append hprefix tailTrace_1897952
  have hstable : (prefixWord ++ tailWord_1897952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897952).length < 2 ^ (prefixWord ++ tailWord_1897952).sum := by decide
  have hdescent : baseEnd_1897952 < baseStart_1897952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898003 : List Nat := [1, 1, 1, 2, 1, 8, 2, 2, 1, 3]
def baseStart_1898003 : Nat := 118140960795 + 1898003 * 2 ^ 59
def prefixEnd_1898003 : Nat := 4983230072969 + 3 ^ 40 * 1898003 * 2
def baseEnd_1898003 : Nat := 649725215117095192155833

theorem tailTrace_1898003 : CollatzResearch.WordTrace tailWord_1898003 prefixEnd_1898003 649725215117095192155833 := by
  unfold tailWord_1898003
  simp only [CollatzResearch.WordTrace]
  refine ⟨69225856542866758950362663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46150571028577839300241775 69225856542866758950362663)
  ·
    refine ⟨103838784814300138425543995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69225856542866758950362663 103838784814300138425543995)
    ·
      refine ⟨155758177221450207638315993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103838784814300138425543995 155758177221450207638315993)
      ·
        refine ⟨116818632916087655728736995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155758177221450207638315993 116818632916087655728736995)
        ·
          refine ⟨175227949374131483593105493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116818632916087655728736995 175227949374131483593105493)
          ·
            refine ⟨2053452531728103323356705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 175227949374131483593105493 2053452531728103323356705)
            ·
              refine ⟨1540089398796077492517529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053452531728103323356705 1540089398796077492517529)
              ·
                refine ⟨1155067049097058119388147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540089398796077492517529 1155067049097058119388147)
                ·
                  refine ⟨1732600573645587179082221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155067049097058119388147 1732600573645587179082221)
                  ·
                    refine ⟨649725215117095192155833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732600573645587179082221 649725215117095192155833)
                    ·
                      rfl

theorem cell22_1898003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 3].length) (baseStart_1898003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898003 prefixEnd_1898003 := by exact prefixLift 1898003
  have htrace : WordTrace (prefixWord ++ tailWord_1898003) baseStart_1898003 baseEnd_1898003 := by
    simpa [prefixWord, tailWord_1898003, baseEnd_1898003] using wordTrace_append hprefix tailTrace_1898003
  have hstable : (prefixWord ++ tailWord_1898003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898003).length < 2 ^ (prefixWord ++ tailWord_1898003).sum := by decide
  have hdescent : baseEnd_1898003 < baseStart_1898003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898012 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1898012 : Nat := 118140960795 + 1898012 * 2 ^ 59
def prefixEnd_1898012 : Nat := 4983230072969 + 3 ^ 40 * 1898012 * 2
def baseEnd_1898012 : Nat := 649728296001022168680805

theorem tailTrace_1898012 : CollatzResearch.WordTrace tailWord_1898012 prefixEnd_1898012 649728296001022168680805 := by
  unfold tailWord_1898012
  simp only [CollatzResearch.WordTrace]
  refine ⟨34613092399917076743720145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46150789866556102324960193 34613092399917076743720145)
  ·
    refine ⟨25959819299937807557790109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34613092399917076743720145 25959819299937807557790109)
    ·
      refine ⟨9734932237476677834171291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25959819299937807557790109 9734932237476677834171291)
      ·
        refine ⟨14602398356215016751256937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9734932237476677834171291 14602398356215016751256937)
        ·
          refine ⟨10951798767161262563442703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14602398356215016751256937 10951798767161262563442703)
          ·
            refine ⟨16427698150741893845164055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10951798767161262563442703 16427698150741893845164055)
            ·
              refine ⟨24641547226112840767746083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16427698150741893845164055 24641547226112840767746083)
              ·
                refine ⟨36962320839169261151619125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24641547226112840767746083 36962320839169261151619125)
                ·
                  refine ⟨3465217578672118232964293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36962320839169261151619125 3465217578672118232964293)
                  ·
                    refine ⟨649728296001022168680805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3465217578672118232964293 649728296001022168680805)
                    ·
                      rfl

theorem cell22_1898012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1898012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898012 prefixEnd_1898012 := by exact prefixLift 1898012
  have htrace : WordTrace (prefixWord ++ tailWord_1898012) baseStart_1898012 baseEnd_1898012 := by
    simpa [prefixWord, tailWord_1898012, baseEnd_1898012] using wordTrace_append hprefix tailTrace_1898012
  have hstable : (prefixWord ++ tailWord_1898012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898012).length < 2 ^ (prefixWord ++ tailWord_1898012).sum := by decide
  have hdescent : baseEnd_1898012 < baseStart_1898012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898042 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_1898042 : Nat := 118140960795 + 1898042 * 2 ^ 59
def prefixEnd_1898042 : Nat := 4983230072969 + 3 ^ 40 * 1898042 * 2
def baseEnd_1898042 : Nat := 649738565614112090430713

theorem tailTrace_1898042 : CollatzResearch.WordTrace tailWord_1898042 prefixEnd_1898042 649738565614112090430713 := by
  unfold tailWord_1898042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17306819747431367152758095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46151519326483645740688253 17306819747431367152758095)
  ·
    refine ⟨25960229621147050729137143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17306819747431367152758095 25960229621147050729137143)
    ·
      refine ⟨38940344431720576093705715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25960229621147050729137143 38940344431720576093705715)
      ·
        refine ⟨58410516647580864140558573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38940344431720576093705715 58410516647580864140558573)
        ·
          refine ⟨21903943742842824052709465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58410516647580864140558573 21903943742842824052709465)
          ·
            refine ⟨16427957807132118039532099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21903943742842824052709465 16427957807132118039532099)
            ·
              refine ⟨24641936710698177059298149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16427957807132118039532099 24641936710698177059298149)
              ·
                refine ⟨4620363133255908198618403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24641936710698177059298149 4620363133255908198618403)
                ·
                  refine ⟨6930544699883862297927605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620363133255908198618403 6930544699883862297927605)
                  ·
                    refine ⟨649738565614112090430713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6930544699883862297927605 649738565614112090430713)
                    ·
                      rfl

theorem cell22_1898042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_1898042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898042 prefixEnd_1898042 := by exact prefixLift 1898042
  have htrace : WordTrace (prefixWord ++ tailWord_1898042) baseStart_1898042 baseEnd_1898042 := by
    simpa [prefixWord, tailWord_1898042, baseEnd_1898042] using wordTrace_append hprefix tailTrace_1898042
  have hstable : (prefixWord ++ tailWord_1898042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898042).length < 2 ^ (prefixWord ++ tailWord_1898042).sum := by decide
  have hdescent : baseEnd_1898042 < baseStart_1898042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898057 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_1898057 : Nat := 118140960795 + 1898057 * 2 ^ 59
def prefixEnd_1898057 : Nat := 4983230072969 + 3 ^ 40 * 1898057 * 2
def baseEnd_1898057 : Nat := 649743700420657051305667

theorem tailTrace_1898057 : CollatzResearch.WordTrace tailWord_1898057 prefixEnd_1898057 649743700420657051305667 := by
  unfold tailWord_1898057
  simp only [CollatzResearch.WordTrace]
  refine ⟨69227826084671126172828425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46151884056447417448552283 69227826084671126172828425)
  ·
    refine ⟨51920869563503344629621319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69227826084671126172828425 51920869563503344629621319)
    ·
      refine ⟨77881304345255016944431979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51920869563503344629621319 77881304345255016944431979)
      ·
        refine ⟨116821956517882525416647969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77881304345255016944431979 116821956517882525416647969)
        ·
          refine ⟨87616467388411894062485977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116821956517882525416647969 87616467388411894062485977)
          ·
            refine ⟨65712350541308920546864483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87616467388411894062485977 65712350541308920546864483)
            ·
              refine ⟨98568525811963380820296725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65712350541308920546864483 98568525811963380820296725)
              ·
                refine ⟨4620399647435783475951409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98568525811963380820296725 4620399647435783475951409)
                ·
                  refine ⟨3465299735576837606963557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4620399647435783475951409 3465299735576837606963557)
                  ·
                    refine ⟨649743700420657051305667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3465299735576837606963557 649743700420657051305667)
                    ·
                      rfl

theorem cell22_1898057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_1898057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898057 prefixEnd_1898057 := by exact prefixLift 1898057
  have htrace : WordTrace (prefixWord ++ tailWord_1898057) baseStart_1898057 baseEnd_1898057 := by
    simpa [prefixWord, tailWord_1898057, baseEnd_1898057] using wordTrace_append hprefix tailTrace_1898057
  have hstable : (prefixWord ++ tailWord_1898057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898057).length < 2 ^ (prefixWord ++ tailWord_1898057).sum := by decide
  have hdescent : baseEnd_1898057 < baseStart_1898057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898061 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1898061 : Nat := 118140960795 + 1898061 * 2 ^ 59
def prefixEnd_1898061 : Nat := 4983230072969 + 3 ^ 40 * 1898061 * 2
def baseEnd_1898061 : Nat := 216581689900800791401885

theorem tailTrace_1898061 : CollatzResearch.WordTrace tailWord_1898061 prefixEnd_1898061 216581689900800791401885 := by
  unfold tailWord_1898061
  simp only [CollatzResearch.WordTrace]
  refine ⟨69227971976656634855974037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46151981317771089903982691 69227971976656634855974037)
  ·
    refine ⟨3245061186405779758873783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69227971976656634855974037 3245061186405779758873783)
    ·
      refine ⟨4867591779608669638310675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3245061186405779758873783 4867591779608669638310675)
      ·
        refine ⟨7301387669413004457466013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867591779608669638310675 7301387669413004457466013)
        ·
          refine ⟨2738020376029876671549755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7301387669413004457466013 2738020376029876671549755)
          ·
            refine ⟨4107030564044815007324633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738020376029876671549755 4107030564044815007324633)
            ·
              refine ⟨3080272923033611255493475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4107030564044815007324633 3080272923033611255493475)
              ·
                refine ⟨4620409384550416883240213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3080272923033611255493475 4620409384550416883240213)
                ·
                  refine ⟨216581689900800791401885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4620409384550416883240213 216581689900800791401885)
                  ·
                    rfl

theorem cell22_1898061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1898061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898061 prefixEnd_1898061 := by exact prefixLift 1898061
  have htrace : WordTrace (prefixWord ++ tailWord_1898061) baseStart_1898061 baseEnd_1898061 := by
    simpa [prefixWord, tailWord_1898061, baseEnd_1898061] using wordTrace_append hprefix tailTrace_1898061
  have hstable : (prefixWord ++ tailWord_1898061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898061).length < 2 ^ (prefixWord ++ tailWord_1898061).sum := by decide
  have hdescent : baseEnd_1898061 < baseStart_1898061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898076 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1898076 : Nat := 118140960795 + 1898076 * 2 ^ 59
def prefixEnd_1898076 : Nat := 4983230072969 + 3 ^ 40 * 1898076 * 2
def baseEnd_1898076 : Nat := 649750204508947335080609

theorem tailTrace_1898076 : CollatzResearch.WordTrace tailWord_1898076 prefixEnd_1898076 649750204508947335080609 := by
  unfold tailWord_1898076
  simp only [CollatzResearch.WordTrace]
  refine ⟨34614259535801146208885041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46152346047734861611846721 34614259535801146208885041)
  ·
    refine ⟨25960694651850859656663781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34614259535801146208885041 25960694651850859656663781)
    ·
      refine ⟨4867630247222036185624459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25960694651850859656663781 4867630247222036185624459)
      ·
        refine ⟨7301445370833054278436689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867630247222036185624459 7301445370833054278436689)
        ·
          refine ⟨5476084028124790708827517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7301445370833054278436689 5476084028124790708827517)
          ·
            refine ⟨2053531510546796515810319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5476084028124790708827517 2053531510546796515810319)
            ·
              refine ⟨3080297265820194773715479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053531510546796515810319 3080297265820194773715479)
              ·
                refine ⟨4620445898730292160573219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3080297265820194773715479 4620445898730292160573219)
                ·
                  refine ⟨6930668848095438240859829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620445898730292160573219 6930668848095438240859829)
                  ·
                    refine ⟨649750204508947335080609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6930668848095438240859829 649750204508947335080609)
                    ·
                      rfl

theorem cell22_1898076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1898076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898076 prefixEnd_1898076 := by exact prefixLift 1898076
  have htrace : WordTrace (prefixWord ++ tailWord_1898076) baseStart_1898076 baseEnd_1898076 := by
    simpa [prefixWord, tailWord_1898076, baseEnd_1898076] using wordTrace_append hprefix tailTrace_1898076
  have hstable : (prefixWord ++ tailWord_1898076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898076).length < 2 ^ (prefixWord ++ tailWord_1898076).sum := by decide
  have hdescent : baseEnd_1898076 < baseStart_1898076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898117 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 7]
def baseStart_1898117 : Nat := 118140960795 + 1898117 * 2 ^ 59
def prefixEnd_1898117 : Nat := 4983230072969 + 3 ^ 40 * 1898117 * 2
def baseEnd_1898117 : Nat := 216588079882278964935161

theorem tailTrace_1898117 : CollatzResearch.WordTrace tailWord_1898117 prefixEnd_1898117 216588079882278964935161 := by
  unfold tailWord_1898117
  simp only [CollatzResearch.WordTrace]
  refine ⟨69230014464453756420012605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46153342976302504280008403 69230014464453756420012605)
  ·
    refine ⟨25961255424170158657504727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69230014464453756420012605 25961255424170158657504727)
    ·
      refine ⟨38941883136255237986257091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25961255424170158657504727 38941883136255237986257091)
      ·
        refine ⟨58412824704382856979385637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38941883136255237986257091 58412824704382856979385637)
        ·
          refine ⟨10952404632071785683634807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58412824704382856979385637 10952404632071785683634807)
          ·
            refine ⟨16428606948107678525452211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10952404632071785683634807 16428606948107678525452211)
            ·
              refine ⟨24642910422161517788178317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16428606948107678525452211 24642910422161517788178317)
              ·
                refine ⟨9241091408310569170566869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24642910422161517788178317 9241091408310569170566869)
                ·
                  refine ⟨216588079882278964935161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9241091408310569170566869 216588079882278964935161)
                  ·
                    rfl

theorem cell22_1898117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_1898117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898117 prefixEnd_1898117 := by exact prefixLift 1898117
  have htrace : WordTrace (prefixWord ++ tailWord_1898117) baseStart_1898117 baseEnd_1898117 := by
    simpa [prefixWord, tailWord_1898117, baseEnd_1898117] using wordTrace_append hprefix tailTrace_1898117
  have hstable : (prefixWord ++ tailWord_1898117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898117).length < 2 ^ (prefixWord ++ tailWord_1898117).sum := by decide
  have hdescent : baseEnd_1898117 < baseStart_1898117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898121 : List Nat := [1, 2, 1, 1, 4, 1, 2, 6, 1, 3]
def baseStart_1898121 : Nat := 118140960795 + 1898121 * 2 ^ 59
def prefixEnd_1898121 : Nat := 4983230072969 + 3 ^ 40 * 1898121 * 2
def baseEnd_1898121 : Nat := 649765608928582217705471

theorem tailTrace_1898121 : CollatzResearch.WordTrace tailWord_1898121 prefixEnd_1898121 649765608928582217705471 := by
  unfold tailWord_1898121
  simp only [CollatzResearch.WordTrace]
  refine ⟨69230160356439265103158217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46153440237626176735438811 69230160356439265103158217)
  ·
    refine ⟨51922620267329448827368663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69230160356439265103158217 51922620267329448827368663)
    ·
      refine ⟨77883930400994173241052995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51922620267329448827368663 77883930400994173241052995)
      ·
        refine ⟨116825895601491259861579493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77883930400994173241052995 116825895601491259861579493)
        ·
          refine ⟨21904855425279611224046155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116825895601491259861579493 21904855425279611224046155)
          ·
            refine ⟨32857283137919416836069233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21904855425279611224046155 32857283137919416836069233)
            ·
              refine ⟨24642962353439562627051925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32857283137919416836069233 24642962353439562627051925)
              ·
                refine ⟨1155138860317479498143059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24642962353439562627051925 1155138860317479498143059)
                ·
                  refine ⟨1732708290476219247214589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155138860317479498143059 1732708290476219247214589)
                  ·
                    refine ⟨649765608928582217705471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1732708290476219247214589 649765608928582217705471)
                    ·
                      rfl

theorem cell22_1898121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 3].length) (baseStart_1898121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898121 prefixEnd_1898121 := by exact prefixLift 1898121
  have htrace : WordTrace (prefixWord ++ tailWord_1898121) baseStart_1898121 baseEnd_1898121 := by
    simpa [prefixWord, tailWord_1898121, baseEnd_1898121] using wordTrace_append hprefix tailTrace_1898121
  have hstable : (prefixWord ++ tailWord_1898121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898121).length < 2 ^ (prefixWord ++ tailWord_1898121).sum := by decide
  have hdescent : baseEnd_1898121 < baseStart_1898121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898196 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 6]
def baseStart_1898196 : Nat := 118140960795 + 1898196 * 2 ^ 59
def prefixEnd_1898196 : Nat := 4983230072969 + 3 ^ 40 * 1898196 * 2
def baseEnd_1898196 : Nat := 216597094320435674026747

theorem tailTrace_1898196 : CollatzResearch.WordTrace tailWord_1898196 prefixEnd_1898196 216597094320435674026747 := by
  unfold tailWord_1898196
  simp only [CollatzResearch.WordTrace]
  refine ⟨34616447915583776456069221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46155263887445035274758961 34616447915583776456069221)
  ·
    refine ⟨6490583984171958085512979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34616447915583776456069221 6490583984171958085512979)
    ·
      refine ⟨9735875976257937128269469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6490583984171958085512979 9735875976257937128269469)
      ·
        refine ⟨3650953491096726423101051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9735875976257937128269469 3650953491096726423101051)
        ·
          refine ⟨5476430236645089634651577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3650953491096726423101051 5476430236645089634651577)
          ·
            refine ⟨4107322677483817225988683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5476430236645089634651577 4107322677483817225988683)
            ·
              refine ⟨6160984016225725838983025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4107322677483817225988683 6160984016225725838983025)
              ·
                refine ⟨4620738012169294379237269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6160984016225725838983025 4620738012169294379237269)
                ·
                  refine ⟨216597094320435674026747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4620738012169294379237269 216597094320435674026747)
                  ·
                    rfl

theorem cell22_1898196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_1898196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898196 prefixEnd_1898196 := by exact prefixLift 1898196
  have htrace : WordTrace (prefixWord ++ tailWord_1898196) baseStart_1898196 baseEnd_1898196 := by
    simpa [prefixWord, tailWord_1898196, baseEnd_1898196] using wordTrace_append hprefix tailTrace_1898196
  have hstable : (prefixWord ++ tailWord_1898196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898196).length < 2 ^ (prefixWord ++ tailWord_1898196).sum := by decide
  have hdescent : baseEnd_1898196 < baseStart_1898196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898254 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1898254 : Nat := 118140960795 + 1898254 * 2 ^ 59
def prefixEnd_1898254 : Nat := 4983230072969 + 3 ^ 40 * 1898254 * 2
def baseEnd_1898254 : Nat := 649811137546614204130063

theorem tailTrace_1898254 : CollatzResearch.WordTrace tailWord_1898254 prefixEnd_1898254 649811137546614204130063 := by
  unfold tailWord_1898254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654376408119678602218727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46156674176638285878499877 8654376408119678602218727)
  ·
    refine ⟨12981564612179517903328091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8654376408119678602218727 12981564612179517903328091)
    ·
      refine ⟨19472346918269276854992137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12981564612179517903328091 19472346918269276854992137)
      ·
        refine ⟨14604260188701957641244103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19472346918269276854992137 14604260188701957641244103)
        ·
          refine ⟨21906390283052936461866155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14604260188701957641244103 21906390283052936461866155)
          ·
            refine ⟨32859585424579404692799233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21906390283052936461866155 32859585424579404692799233)
            ·
              refine ⟨24644689068434553519599425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32859585424579404692799233 24644689068434553519599425)
              ·
                refine ⟨18483516801325915139699569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24644689068434553519599425 18483516801325915139699569)
                ·
                  refine ⟨13862637600994436354774677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18483516801325915139699569 13862637600994436354774677)
                  ·
                    refine ⟨649811137546614204130063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13862637600994436354774677 649811137546614204130063)
                    ·
                      rfl

theorem cell22_1898254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1898254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898254 prefixEnd_1898254 := by exact prefixLift 1898254
  have htrace : WordTrace (prefixWord ++ tailWord_1898254) baseStart_1898254 baseEnd_1898254 := by
    simpa [prefixWord, tailWord_1898254, baseEnd_1898254] using wordTrace_append hprefix tailTrace_1898254
  have hstable : (prefixWord ++ tailWord_1898254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898254).length < 2 ^ (prefixWord ++ tailWord_1898254).sum := by decide
  have hdescent : baseEnd_1898254 < baseStart_1898254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898258 : List Nat := [3, 2, 4, 1, 1, 1, 4, 6]
def baseStart_1898258 : Nat := 118140960795 + 1898258 * 2 ^ 59
def prefixEnd_1898258 : Nat := 4983230072969 + 3 ^ 40 * 1898258 * 2
def baseEnd_1898258 : Nat := 72201389647595503003339

theorem tailTrace_1898258 : CollatzResearch.WordTrace tailWord_1898258 prefixEnd_1898258 72201389647595503003339 := by
  unfold tailWord_1898258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17308789289235734375223857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46156771437961958333930285 17308789289235734375223857)
  ·
    refine ⟨12981591966926800781417893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17308789289235734375223857 12981591966926800781417893)
    ·
      refine ⟨2434048493798775146515855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12981591966926800781417893 2434048493798775146515855)
      ·
        refine ⟨3651072740698162719773783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434048493798775146515855 3651072740698162719773783)
        ·
          refine ⟨5476609111047244079660675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3651072740698162719773783 5476609111047244079660675)
          ·
            refine ⟨8214913666570866119491013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476609111047244079660675 8214913666570866119491013)
            ·
              refine ⟨1540296312482037397404565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8214913666570866119491013 1540296312482037397404565)
              ·
                refine ⟨72201389647595503003339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1540296312482037397404565 72201389647595503003339)
                ·
                  rfl

theorem cell22_1898258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_1898258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898258 prefixEnd_1898258 := by exact prefixLift 1898258
  have htrace : WordTrace (prefixWord ++ tailWord_1898258) baseStart_1898258 baseEnd_1898258 := by
    simpa [prefixWord, tailWord_1898258, baseEnd_1898258] using wordTrace_append hprefix tailTrace_1898258
  have hstable : (prefixWord ++ tailWord_1898258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898258).length < 2 ^ (prefixWord ++ tailWord_1898258).sum := by decide
  have hdescent : baseEnd_1898258 < baseStart_1898258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898314 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_1898314 : Nat := 118140960795 + 1898314 * 2 ^ 59
def prefixEnd_1898314 : Nat := 4983230072969 + 3 ^ 40 * 1898314 * 2
def baseEnd_1898314 : Nat := 216610558924264682543293

theorem tailTrace_1898314 : CollatzResearch.WordTrace tailWord_1898314 prefixEnd_1898314 216610558924264682543293 := by
  unfold tailWord_1898314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309299911185014766233499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46158133096493372709955997 17309299911185014766233499)
  ·
    refine ⟨25963949866777522149350249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17309299911185014766233499 25963949866777522149350249)
    ·
      refine ⟨19472962400083141612012687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25963949866777522149350249 19472962400083141612012687)
      ·
        refine ⟨29209443600124712418019031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19472962400083141612012687 29209443600124712418019031)
        ·
          refine ⟨43814165400187068627028547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29209443600124712418019031 43814165400187068627028547)
          ·
            refine ⟨65721248100280602940542821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43814165400187068627028547 65721248100280602940542821)
            ·
              refine ⟨12322734018802613051351779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65721248100280602940542821 12322734018802613051351779)
              ·
                refine ⟨18484101028203919577027669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12322734018802613051351779 18484101028203919577027669)
                ·
                  refine ⟨216610558924264682543293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18484101028203919577027669 216610558924264682543293)
                  ·
                    rfl

theorem cell22_1898314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_1898314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898314 prefixEnd_1898314 := by exact prefixLift 1898314
  have htrace : WordTrace (prefixWord ++ tailWord_1898314) baseStart_1898314 baseEnd_1898314 := by
    simpa [prefixWord, tailWord_1898314, baseEnd_1898314] using wordTrace_append hprefix tailTrace_1898314
  have hstable : (prefixWord ++ tailWord_1898314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898314).length < 2 ^ (prefixWord ++ tailWord_1898314).sum := by decide
  have hdescent : baseEnd_1898314 < baseStart_1898314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898348 : List Nat := [2, 2, 1, 1, 4, 3, 1, 4, 4]
def baseStart_1898348 : Nat := 118140960795 + 1898348 * 2 ^ 59
def prefixEnd_1898348 : Nat := 4983230072969 + 3 ^ 40 * 1898348 * 2
def baseEnd_1898348 : Nat := 216614438555876430759925

theorem tailTrace_1898348 : CollatzResearch.WordTrace tailWord_1898348 prefixEnd_1898348 216614438555876430759925 := by
  unfold tailWord_1898348
  simp only [CollatzResearch.WordTrace]
  refine ⟨34619219863308441435835849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46158959817744588581114465 34619219863308441435835849)
  ·
    refine ⟨25964414897481331076876887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34619219863308441435835849 25964414897481331076876887)
    ·
      refine ⟨38946622346221996615315331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25964414897481331076876887 38946622346221996615315331)
      ·
        refine ⟨58419933519332994922972997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38946622346221996615315331 58419933519332994922972997)
        ·
          refine ⟨10953737534874936548057437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58419933519332994922972997 10953737534874936548057437)
          ·
            refine ⟨4107651575578101205521539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10953737534874936548057437 4107651575578101205521539)
            ·
              refine ⟨6161477363367151808282309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4107651575578101205521539 6161477363367151808282309)
              ·
                refine ⟨1155277005631340964052933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6161477363367151808282309 1155277005631340964052933)
                ·
                  refine ⟨216614438555876430759925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1155277005631340964052933 216614438555876430759925)
                  ·
                    rfl

theorem cell22_1898348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_1898348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898348 prefixEnd_1898348 := by exact prefixLift 1898348
  have htrace : WordTrace (prefixWord ++ tailWord_1898348) baseStart_1898348 baseEnd_1898348 := by
    simpa [prefixWord, tailWord_1898348, baseEnd_1898348] using wordTrace_append hprefix tailTrace_1898348
  have hstable : (prefixWord ++ tailWord_1898348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898348).length < 2 ^ (prefixWord ++ tailWord_1898348).sum := by decide
  have hdescent : baseEnd_1898348 < baseStart_1898348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898378 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_1898378 : Nat := 118140960795 + 1898378 * 2 ^ 59
def prefixEnd_1898378 : Nat := 4983230072969 + 3 ^ 40 * 1898378 * 2
def baseEnd_1898378 : Nat := 649853585280719214029683

theorem tailTrace_1898378 : CollatzResearch.WordTrace tailWord_1898378 prefixEnd_1898378 649853585280719214029683 := by
  unfold tailWord_1898378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309883479127049498815947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46159689277672131996842525 17309883479127049498815947)
  ·
    refine ⟨25964825218690574248223921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17309883479127049498815947 25964825218690574248223921)
    ·
      refine ⟨19473618914017930686167941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25964825218690574248223921 19473618914017930686167941)
      ·
        refine ⟨3651303546378362003656489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19473618914017930686167941 3651303546378362003656489)
        ·
          refine ⟨2738477659783771502742367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3651303546378362003656489 2738477659783771502742367)
          ·
            refine ⟨4107716489675657254113551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738477659783771502742367 4107716489675657254113551)
            ·
              refine ⟨6161574734513485881170327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4107716489675657254113551 6161574734513485881170327)
              ·
                refine ⟨9242362101770228821755491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6161574734513485881170327 9242362101770228821755491)
                ·
                  refine ⟨13863543152655343232633237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9242362101770228821755491 13863543152655343232633237)
                  ·
                    refine ⟨649853585280719214029683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13863543152655343232633237 649853585280719214029683)
                    ·
                      rfl

theorem cell22_1898378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_1898378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898378 prefixEnd_1898378 := by exact prefixLift 1898378
  have htrace : WordTrace (prefixWord ++ tailWord_1898378) baseStart_1898378 baseEnd_1898378 := by
    simpa [prefixWord, tailWord_1898378, baseEnd_1898378] using wordTrace_append hprefix tailTrace_1898378
  have hstable : (prefixWord ++ tailWord_1898378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898378).length < 2 ^ (prefixWord ++ tailWord_1898378).sum := by decide
  have hdescent : baseEnd_1898378 < baseStart_1898378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898382 : List Nat := [4, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_1898382 : Nat := 118140960795 + 1898382 * 2 ^ 59
def prefixEnd_1898382 : Nat := 4983230072969 + 3 ^ 40 * 1898382 * 2
def baseEnd_1898382 : Nat := 216618318187488178976557

theorem tailTrace_1898382 : CollatzResearch.WordTrace tailWord_1898382 prefixEnd_1898382 216618318187488178976557 := by
  unfold tailWord_1898382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654959976061713334801175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46159786538995804452272933 8654959976061713334801175)
  ·
    refine ⟨12982439964092570002201763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8654959976061713334801175 12982439964092570002201763)
    ·
      refine ⟨19473659946138855003302645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12982439964092570002201763 19473659946138855003302645)
      ·
        refine ⟨1825655619950517656559623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19473659946138855003302645 1825655619950517656559623)
        ·
          refine ⟨2738483429925776484839435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825655619950517656559623 2738483429925776484839435)
          ·
            refine ⟨4107725144888664727259153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738483429925776484839435 4107725144888664727259153)
            ·
              refine ⟨3080793858666498545444365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4107725144888664727259153 3080793858666498545444365)
              ·
                refine ⟨1155297696999936954541637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3080793858666498545444365 1155297696999936954541637)
                ·
                  refine ⟨216618318187488178976557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1155297696999936954541637 216618318187488178976557)
                  ·
                    rfl

theorem cell22_1898382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_1898382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898382 prefixEnd_1898382 := by exact prefixLift 1898382
  have htrace : WordTrace (prefixWord ++ tailWord_1898382) baseStart_1898382 baseEnd_1898382 := by
    simpa [prefixWord, tailWord_1898382, baseEnd_1898382] using wordTrace_append hprefix tailTrace_1898382
  have hstable : (prefixWord ++ tailWord_1898382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898382).length < 2 ^ (prefixWord ++ tailWord_1898382).sum := by decide
  have hdescent : baseEnd_1898382 < baseStart_1898382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898414 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1898414 : Nat := 118140960795 + 1898414 * 2 ^ 59
def prefixEnd_1898414 : Nat := 4983230072969 + 3 ^ 40 * 1898414 * 2
def baseEnd_1898414 : Nat := 649865908816427120129573

theorem tailTrace_1898414 : CollatzResearch.WordTrace tailWord_1898414 prefixEnd_1898414 649865908816427120129573 := by
  unfold tailWord_1898414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655105868047222017946787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46160564629585184095716197 8655105868047222017946787)
  ·
    refine ⟨12982658802070833026920181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8655105868047222017946787 12982658802070833026920181)
    ·
      refine ⟨1217124262694140596273767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12982658802070833026920181 1217124262694140596273767)
      ·
        refine ⟨1825686394041210894410651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217124262694140596273767 1825686394041210894410651)
        ·
          refine ⟨2738529591061816341615977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825686394041210894410651 2738529591061816341615977)
          ·
            refine ⟨2053897193296362256211983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2738529591061816341615977 2053897193296362256211983)
            ·
              refine ⟨3080845789944543384317975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053897193296362256211983 3080845789944543384317975)
              ·
                refine ⟨4621268684916815076476963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3080845789944543384317975 4621268684916815076476963)
                ·
                  refine ⟨6931903027375222614715445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621268684916815076476963 6931903027375222614715445)
                  ·
                    refine ⟨649865908816427120129573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6931903027375222614715445 649865908816427120129573)
                    ·
                      rfl

theorem cell22_1898414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1898414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898414 prefixEnd_1898414 := by exact prefixLift 1898414
  have htrace : WordTrace (prefixWord ++ tailWord_1898414) baseStart_1898414 baseEnd_1898414 := by
    simpa [prefixWord, tailWord_1898414, baseEnd_1898414] using wordTrace_append hprefix tailTrace_1898414
  have hstable : (prefixWord ++ tailWord_1898414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898414).length < 2 ^ (prefixWord ++ tailWord_1898414).sum := by decide
  have hdescent : baseEnd_1898414 < baseStart_1898414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898571 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 3, 7]
def baseStart_1898571 : Nat := 118140960795 + 1898571 * 2 ^ 59
def prefixEnd_1898571 : Nat := 4983230072969 + 3 ^ 40 * 1898571 * 2
def baseEnd_1898571 : Nat := 649919653124931043954091

theorem tailTrace_1898571 : CollatzResearch.WordTrace tailWord_1898571 prefixEnd_1898571 649919653124931043954091 := by
  unfold tailWord_1898571
  simp only [CollatzResearch.WordTrace]
  refine ⟨69246573204808991957039567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46164382136539327971359711 69246573204808991957039567)
  ·
    refine ⟨103869859807213487935559351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69246573204808991957039567 103869859807213487935559351)
    ·
      refine ⟨155804789710820231903339027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103869859807213487935559351 155804789710820231903339027)
      ·
        refine ⟨233707184566230347855008541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155804789710820231903339027 233707184566230347855008541)
        ·
          refine ⟨87640194212336380445628203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233707184566230347855008541 87640194212336380445628203)
          ·
            refine ⟨131460291318504570668442305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87640194212336380445628203 131460291318504570668442305)
            ·
              refine ⟨98595218488878428001331729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131460291318504570668442305 98595218488878428001331729)
              ·
                refine ⟨73946413866658821000998797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98595218488878428001331729 73946413866658821000998797)
                ·
                  refine ⟨27729905199997057875374549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73946413866658821000998797 27729905199997057875374549)
                  ·
                    refine ⟨649919653124931043954091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27729905199997057875374549 649919653124931043954091)
                    ·
                      rfl

theorem cell22_1898571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_1898571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898571 prefixEnd_1898571 := by exact prefixLift 1898571
  have htrace : WordTrace (prefixWord ++ tailWord_1898571) baseStart_1898571 baseEnd_1898571 := by
    simpa [prefixWord, tailWord_1898571, baseEnd_1898571] using wordTrace_append hprefix tailTrace_1898571
  have hstable : (prefixWord ++ tailWord_1898571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898571).length < 2 ^ (prefixWord ++ tailWord_1898571).sum := by decide
  have hdescent : baseEnd_1898571 < baseStart_1898571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898620 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_1898620 : Nat := 118140960795 + 1898620 * 2 ^ 59
def prefixEnd_1898620 : Nat := 4983230072969 + 3 ^ 40 * 1898620 * 2
def baseEnd_1898620 : Nat := 649936426826311249478941

theorem tailTrace_1898620 : CollatzResearch.WordTrace tailWord_1898620 prefixEnd_1898620 649936426826311249478941 := by
  unfold tailWord_1898620
  simp only [CollatzResearch.WordTrace]
  refine ⟨34624180190815736662786657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46165573587754315550382209 34624180190815736662786657)
  ·
    refine ⟨25968135143111802497089993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34624180190815736662786657 25968135143111802497089993)
    ·
      refine ⟨19476101357333851872817495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25968135143111802497089993 19476101357333851872817495)
      ·
        refine ⟨29214152036000777809226243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19476101357333851872817495 29214152036000777809226243)
        ·
          refine ⟨43821228054001166713839365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29214152036000777809226243 43821228054001166713839365)
          ·
            refine ⟨8216480260125218758844881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43821228054001166713839365 8216480260125218758844881)
            ·
              refine ⟨6162360195093914069133661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8216480260125218758844881 6162360195093914069133661)
              ·
                refine ⟨2310885073160217775925123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6162360195093914069133661 2310885073160217775925123)
                ·
                  refine ⟨3466327609740326663887685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310885073160217775925123 3466327609740326663887685)
                  ·
                    refine ⟨649936426826311249478941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3466327609740326663887685 649936426826311249478941)
                    ·
                      rfl

theorem cell22_1898620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_1898620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898620 prefixEnd_1898620 := by exact prefixLift 1898620
  have htrace : WordTrace (prefixWord ++ tailWord_1898620) baseStart_1898620 baseEnd_1898620 := by
    simpa [prefixWord, tailWord_1898620, baseEnd_1898620] using wordTrace_append hprefix tailTrace_1898620
  have hstable : (prefixWord ++ tailWord_1898620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898620).length < 2 ^ (prefixWord ++ tailWord_1898620).sum := by decide
  have hdescent : baseEnd_1898620 < baseStart_1898620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898684 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_1898684 : Nat := 118140960795 + 1898684 * 2 ^ 59
def prefixEnd_1898684 : Nat := 4983230072969 + 3 ^ 40 * 1898684 * 2
def baseEnd_1898684 : Nat := 649958335334236415878745

theorem tailTrace_1898684 : CollatzResearch.WordTrace tailWord_1898684 prefixEnd_1898684 649958335334236415878745 := by
  unfold tailWord_1898684
  simp only [CollatzResearch.WordTrace]
  refine ⟨34625347326699806127951553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46167129768933074837268737 34625347326699806127951553)
  ·
    refine ⟨25969010495024854595963665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34625347326699806127951553 25969010495024854595963665)
    ·
      refine ⟨19476757871268640946972749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25969010495024854595963665 19476757871268640946972749)
      ·
        refine ⟨7303784201725740355114781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19476757871268640946972749 7303784201725740355114781)
        ·
          refine ⟨2738919075647152633168043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7303784201725740355114781 2738919075647152633168043)
          ·
            refine ⟨4108378613470728949752065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738919075647152633168043 4108378613470728949752065)
            ·
              refine ⟨3081283960103046712314049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108378613470728949752065 3081283960103046712314049)
              ·
                refine ⟨2310962970077285034235537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081283960103046712314049 2310962970077285034235537)
                ·
                  refine ⟨1733222227557963775676653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2310962970077285034235537 1733222227557963775676653)
                  ·
                    refine ⟨649958335334236415878745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1733222227557963775676653 649958335334236415878745)
                    ·
                      rfl

theorem cell22_1898684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_1898684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898684 prefixEnd_1898684 := by exact prefixLift 1898684
  have htrace : WordTrace (prefixWord ++ tailWord_1898684) baseStart_1898684 baseEnd_1898684 := by
    simpa [prefixWord, tailWord_1898684, baseEnd_1898684] using wordTrace_append hprefix tailTrace_1898684
  have hstable : (prefixWord ++ tailWord_1898684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898684).length < 2 ^ (prefixWord ++ tailWord_1898684).sum := by decide
  have hdescent : baseEnd_1898684 < baseStart_1898684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898686 : List Nat := [4, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1898686 : Nat := 118140960795 + 1898686 * 2 ^ 59
def prefixEnd_1898686 : Nat := 4983230072969 + 3 ^ 40 * 1898686 * 2
def baseEnd_1898686 : Nat := 216653006658369692442913

theorem tailTrace_1898686 : CollatzResearch.WordTrace tailWord_1898686 prefixEnd_1898686 216653006658369692442913 := by
  unfold tailWord_1898686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8656345949924045824684489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46167178399594911064983941 8656345949924045824684489)
  ·
    refine ⟨6492259462443034368513367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8656345949924045824684489 6492259462443034368513367)
    ·
      refine ⟨9738389193664551552770051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6492259462443034368513367 9738389193664551552770051)
      ·
        refine ⟨14607583790496827329155077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9738389193664551552770051 14607583790496827329155077)
        ·
          refine ⟨2738921960718155124216577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14607583790496827329155077 2738921960718155124216577)
          ·
            refine ⟨2054191470538616343162433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2738921960718155124216577 2054191470538616343162433)
            ·
              refine ⟨1540643602903962257371825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2054191470538616343162433 1540643602903962257371825)
              ·
                refine ⟨1155482702177971693028869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540643602903962257371825 1155482702177971693028869)
                ·
                  refine ⟨216653006658369692442913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1155482702177971693028869 216653006658369692442913)
                  ·
                    rfl

theorem cell22_1898686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1898686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898686 prefixEnd_1898686 := by exact prefixLift 1898686
  have htrace : WordTrace (prefixWord ++ tailWord_1898686) baseStart_1898686 baseEnd_1898686 := by
    simpa [prefixWord, tailWord_1898686, baseEnd_1898686] using wordTrace_append hprefix tailTrace_1898686
  have hstable : (prefixWord ++ tailWord_1898686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898686).length < 2 ^ (prefixWord ++ tailWord_1898686).sum := by decide
  have hdescent : baseEnd_1898686 < baseStart_1898686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898693 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_1898693 : Nat := 118140960795 + 1898693 * 2 ^ 59
def prefixEnd_1898693 : Nat := 4983230072969 + 3 ^ 40 * 1898693 * 2
def baseEnd_1898693 : Nat := 649961416218163392403717

theorem tailTrace_1898693 : CollatzResearch.WordTrace tailWord_1898693 prefixEnd_1898693 649961416218163392403717 := by
  unfold tailWord_1898693
  simp only [CollatzResearch.WordTrace]
  refine ⟨69251022910367006792980733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46167348606911337861987155 69251022910367006792980733)
  ·
    refine ⟨25969133591387627547367775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69251022910367006792980733 25969133591387627547367775)
    ·
      refine ⟨38953700387081441321051663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25969133591387627547367775 38953700387081441321051663)
      ·
        refine ⟨58430550580622161981577495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38953700387081441321051663 58430550580622161981577495)
        ·
          refine ⟨87645825870933242972366243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58430550580622161981577495 87645825870933242972366243)
          ·
            refine ⟨131468738806399864458549365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87645825870933242972366243 131468738806399864458549365)
            ·
              refine ⟨12325194263099987292989003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131468738806399864458549365 12325194263099987292989003)
              ·
                refine ⟨18487791394649980939483505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12325194263099987292989003 18487791394649980939483505)
                ·
                  refine ⟨13865843545987485704612629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18487791394649980939483505 13865843545987485704612629)
                  ·
                    refine ⟨649961416218163392403717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13865843545987485704612629 649961416218163392403717)
                    ·
                      rfl

theorem cell22_1898693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_1898693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898693 prefixEnd_1898693 := by exact prefixLift 1898693
  have htrace : WordTrace (prefixWord ++ tailWord_1898693) baseStart_1898693 baseEnd_1898693 := by
    simpa [prefixWord, tailWord_1898693, baseEnd_1898693] using wordTrace_append hprefix tailTrace_1898693
  have hstable : (prefixWord ++ tailWord_1898693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898693).length < 2 ^ (prefixWord ++ tailWord_1898693).sum := by decide
  have hdescent : baseEnd_1898693 < baseStart_1898693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898712 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 3, 3]
def baseStart_1898712 : Nat := 118140960795 + 1898712 * 2 ^ 59
def prefixEnd_1898712 : Nat := 4983230072969 + 3 ^ 40 * 1898712 * 2
def baseEnd_1898712 : Nat := 649967920306453676178659

theorem tailTrace_1898712 : CollatzResearch.WordTrace tailWord_1898712 prefixEnd_1898712 649967920306453676178659 := by
  unfold tailWord_1898712
  simp only [CollatzResearch.WordTrace]
  refine ⟨34625857948649086518961195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46167810598198782025281593 34625857948649086518961195)
  ·
    refine ⟨51938786922973629778441793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34625857948649086518961195 51938786922973629778441793)
    ·
      refine ⟨38954090192230222333831345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51938786922973629778441793 38954090192230222333831345)
      ·
        refine ⟨29215567644172666750373509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38954090192230222333831345 29215567644172666750373509)
        ·
          refine ⟨5477918933282375015695033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29215567644172666750373509 5477918933282375015695033)
          ·
            refine ⟨4108439199961781261771275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5477918933282375015695033 4108439199961781261771275)
            ·
              refine ⟨6162658799942671892656913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108439199961781261771275 6162658799942671892656913)
              ·
                refine ⟨4621994099957003919492685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6162658799942671892656913 4621994099957003919492685)
                ·
                  refine ⟨1733247787483876469809757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4621994099957003919492685 1733247787483876469809757)
                  ·
                    refine ⟨649967920306453676178659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1733247787483876469809757 649967920306453676178659)
                    ·
                      rfl

theorem cell22_1898712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_1898712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898712 prefixEnd_1898712 := by exact prefixLift 1898712
  have htrace : WordTrace (prefixWord ++ tailWord_1898712) baseStart_1898712 baseEnd_1898712 := by
    simpa [prefixWord, tailWord_1898712, baseEnd_1898712] using wordTrace_append hprefix tailTrace_1898712
  have hstable : (prefixWord ++ tailWord_1898712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898712).length < 2 ^ (prefixWord ++ tailWord_1898712).sum := by decide
  have hdescent : baseEnd_1898712 < baseStart_1898712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898716 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1898716 : Nat := 118140960795 + 1898716 * 2 ^ 59
def prefixEnd_1898716 : Nat := 4983230072969 + 3 ^ 40 * 1898716 * 2
def baseEnd_1898716 : Nat := 649969289588198999078647

theorem tailTrace_1898716 : CollatzResearch.WordTrace tailWord_1898716 prefixEnd_1898716 649969289588198999078647 := by
  unfold tailWord_1898716
  simp only [CollatzResearch.WordTrace]
  refine ⟨34625930894641840860534001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46167907859522454480712001 34625930894641840860534001)
  ·
    refine ⟨25969448170981380645400501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34625930894641840860534001 25969448170981380645400501)
    ·
      refine ⟨2434635766029504435506297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25969448170981380645400501 2434635766029504435506297)
      ·
        refine ⟨1825976824522128326629723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2434635766029504435506297 1825976824522128326629723)
        ·
          refine ⟨2738965236783192489944585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825976824522128326629723 2738965236783192489944585)
          ·
            refine ⟨2054223927587394367458439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2738965236783192489944585 2054223927587394367458439)
            ·
              refine ⟨3081335891381091551187659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054223927587394367458439 3081335891381091551187659)
              ·
                refine ⟨4622003837071637326781489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081335891381091551187659 4622003837071637326781489)
                ·
                  refine ⟨3466502877803727995086117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622003837071637326781489 3466502877803727995086117)
                  ·
                    refine ⟨649969289588198999078647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3466502877803727995086117 649969289588198999078647)
                    ·
                      rfl

theorem cell22_1898716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1898716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898716 prefixEnd_1898716 := by exact prefixLift 1898716
  have htrace : WordTrace (prefixWord ++ tailWord_1898716) baseStart_1898716 baseEnd_1898716 := by
    simpa [prefixWord, tailWord_1898716, baseEnd_1898716] using wordTrace_append hprefix tailTrace_1898716
  have hstable : (prefixWord ++ tailWord_1898716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898716).length < 2 ^ (prefixWord ++ tailWord_1898716).sum := by decide
  have hdescent : baseEnd_1898716 < baseStart_1898716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898742 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_1898742 : Nat := 118140960795 + 1898742 * 2 ^ 59
def prefixEnd_1898742 : Nat := 4983230072969 + 3 ^ 40 * 1898742 * 2
def baseEnd_1898742 : Nat := 216659396639847865976189

theorem tailTrace_1898742 : CollatzResearch.WordTrace tailWord_1898742 prefixEnd_1898742 216659396639847865976189 := by
  unfold tailWord_1898742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328300630449343010094655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46168540058126325441009653 4328300630449343010094655)
  ·
    refine ⟨6492450945674014515141983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4328300630449343010094655 6492450945674014515141983)
    ·
      refine ⟨9738676418511021772712975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6492450945674014515141983 9738676418511021772712975)
      ·
        refine ⟨14608014627766532659069463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9738676418511021772712975 14608014627766532659069463)
        ·
          refine ⟨21912021941649798988604195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14608014627766532659069463 21912021941649798988604195)
          ·
            refine ⟨32868032912474698482906293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21912021941649798988604195 32868032912474698482906293)
            ·
              refine ⟨3081378085544502982772465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32868032912474698482906293 3081378085544502982772465)
              ·
                refine ⟨2311033564158377237079349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081378085544502982772465 2311033564158377237079349)
                ·
                  refine ⟨216659396639847865976189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2311033564158377237079349 216659396639847865976189)
                  ·
                    rfl

theorem cell22_1898742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_1898742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898742 prefixEnd_1898742 := by exact prefixLift 1898742
  have htrace : WordTrace (prefixWord ++ tailWord_1898742) baseStart_1898742 baseEnd_1898742 := by
    simpa [prefixWord, tailWord_1898742, baseEnd_1898742] using wordTrace_append hprefix tailTrace_1898742
  have hstable : (prefixWord ++ tailWord_1898742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898742).length < 2 ^ (prefixWord ++ tailWord_1898742).sum := by decide
  have hdescent : baseEnd_1898742 < baseStart_1898742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898785 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1898785 : Nat := 118140960795 + 1898785 * 2 ^ 59
def prefixEnd_1898785 : Nat := 4983230072969 + 3 ^ 40 * 1898785 * 2
def baseEnd_1898785 : Nat := 649992909698305819103435

theorem tailTrace_1898785 : CollatzResearch.WordTrace tailWord_1898785 prefixEnd_1898785 649992909698305819103435 := by
  unfold tailWord_1898785
  simp only [CollatzResearch.WordTrace]
  refine ⟨69254378426033706505329809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46169585617355804336886539 69254378426033706505329809)
  ·
    refine ⟨51940783819525279878997357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69254378426033706505329809 51940783819525279878997357)
    ·
      refine ⟨19477793932321979954624009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51940783819525279878997357 19477793932321979954624009)
      ·
        refine ⟨14608345449241484965968007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19477793932321979954624009 14608345449241484965968007)
        ·
          refine ⟨21912518173862227448952011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14608345449241484965968007 21912518173862227448952011)
          ·
            refine ⟨32868777260793341173428017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21912518173862227448952011 32868777260793341173428017)
            ·
              refine ⟨24651582945595005880071013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32868777260793341173428017 24651582945595005880071013)
              ·
                refine ⟨4622171802299063602513315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24651582945595005880071013 4622171802299063602513315)
                ·
                  refine ⟨6933257703448595403769973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622171802299063602513315 6933257703448595403769973)
                  ·
                    refine ⟨649992909698305819103435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6933257703448595403769973 649992909698305819103435)
                    ·
                      rfl

theorem cell22_1898785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1898785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898785 prefixEnd_1898785 := by exact prefixLift 1898785
  have htrace : WordTrace (prefixWord ++ tailWord_1898785) baseStart_1898785 baseEnd_1898785 := by
    simpa [prefixWord, tailWord_1898785, baseEnd_1898785] using wordTrace_append hprefix tailTrace_1898785
  have hstable : (prefixWord ++ tailWord_1898785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898785).length < 2 ^ (prefixWord ++ tailWord_1898785).sum := by decide
  have hdescent : baseEnd_1898785 < baseStart_1898785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898804 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1898804 : Nat := 118140960795 + 1898804 * 2 ^ 59
def prefixEnd_1898804 : Nat := 4983230072969 + 3 ^ 40 * 1898804 * 2
def baseEnd_1898804 : Nat := 216666471262198700959459

theorem tailTrace_1898804 : CollatzResearch.WordTrace tailWord_1898804 prefixEnd_1898804 216666471262198700959459 := by
  unfold tailWord_1898804
  simp only [CollatzResearch.WordTrace]
  refine ⟨34627535706482436375135733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46170047608643248500180977 34627535706482436375135733)
  ·
    refine ⟨3246331472482728410168975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34627535706482436375135733 3246331472482728410168975)
    ·
      refine ⟨4869497208724092615253463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3246331472482728410168975 4869497208724092615253463)
      ·
        refine ⟨7304245813086138922880195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869497208724092615253463 7304245813086138922880195)
        ·
          refine ⟨10956368719629208384320293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304245813086138922880195 10956368719629208384320293)
          ·
            refine ⟨2054319134930476572060055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10956368719629208384320293 2054319134930476572060055)
            ·
              refine ⟨3081478702395714858090083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054319134930476572060055 3081478702395714858090083)
              ·
                refine ⟨4622218053593572287135125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081478702395714858090083 4622218053593572287135125)
                ·
                  refine ⟨216666471262198700959459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4622218053593572287135125 216666471262198700959459)
                  ·
                    rfl

theorem cell22_1898804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1898804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898804 prefixEnd_1898804 := by exact prefixLift 1898804
  have htrace : WordTrace (prefixWord ++ tailWord_1898804) baseStart_1898804 baseEnd_1898804 := by
    simpa [prefixWord, tailWord_1898804, baseEnd_1898804] using wordTrace_append hprefix tailTrace_1898804
  have hstable : (prefixWord ++ tailWord_1898804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898804).length < 2 ^ (prefixWord ++ tailWord_1898804).sum := by decide
  have hdescent : baseEnd_1898804 < baseStart_1898804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898815 : List Nat := [1, 1, 2, 2, 4, 1, 4, 7]
def baseStart_1898815 : Nat := 118140960795 + 1898815 * 2 ^ 59
def prefixEnd_1898815 : Nat := 4983230072969 + 3 ^ 40 * 1898815 * 2
def baseEnd_1898815 : Nat := 72222575479043971205927

theorem tailTrace_1898815 : CollatzResearch.WordTrace tailWord_1898815 prefixEnd_1898815 72222575479043971205927 := by
  unfold tailWord_1898815
  simp only [CollatzResearch.WordTrace]
  refine ⟨69255472615925021628921899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46170315077283347752614599 69255472615925021628921899)
  ·
    refine ⟨103883208923887532443382849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69255472615925021628921899 103883208923887532443382849)
    ·
      refine ⟨77912406692915649332537137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103883208923887532443382849 77912406692915649332537137)
      ·
        refine ⟨58434305019686736999402853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77912406692915649332537137 58434305019686736999402853)
        ·
          refine ⟨10956432191191263187388035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58434305019686736999402853 10956432191191263187388035)
          ·
            refine ⟨16434648286786894781082053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956432191191263187388035 16434648286786894781082053)
            ·
              refine ⟨3081496553772542771452885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16434648286786894781082053 3081496553772542771452885)
              ·
                refine ⟨72222575479043971205927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3081496553772542771452885 72222575479043971205927)
                ·
                  rfl

theorem cell22_1898815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 7].length) (baseStart_1898815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898815 prefixEnd_1898815 := by exact prefixLift 1898815
  have htrace : WordTrace (prefixWord ++ tailWord_1898815) baseStart_1898815 baseEnd_1898815 := by
    simpa [prefixWord, tailWord_1898815, baseEnd_1898815] using wordTrace_append hprefix tailTrace_1898815
  have hstable : (prefixWord ++ tailWord_1898815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898815).length < 2 ^ (prefixWord ++ tailWord_1898815).sum := by decide
  have hdescent : baseEnd_1898815 < baseStart_1898815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898819 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 2, 3]
def baseStart_1898819 : Nat := 118140960795 + 1898819 * 2 ^ 59
def prefixEnd_1898819 : Nat := 4983230072969 + 3 ^ 40 * 1898819 * 2
def baseEnd_1898819 : Nat := 650004548593141063753331

theorem tailTrace_1898819 : CollatzResearch.WordTrace tailWord_1898819 prefixEnd_1898819 650004548593141063753331 := by
  unfold tailWord_1898819
  simp only [CollatzResearch.WordTrace]
  refine ⟨69255618507910530312067511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46170412338607020208045007 69255618507910530312067511)
  ·
    refine ⟨103883427761865795468101267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69255618507910530312067511 103883427761865795468101267)
    ·
      refine ⟨155825141642798693202151901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103883427761865795468101267 155825141642798693202151901)
      ·
        refine ⟨58434428116049509950806963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155825141642798693202151901 58434428116049509950806963)
        ·
          refine ⟨87651642174074264926210445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58434428116049509950806963 87651642174074264926210445)
          ·
            refine ⟨32869365815277849347328917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87651642174074264926210445 32869365815277849347328917)
            ·
              refine ⟨1540751522591149188156043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32869365815277849347328917 1540751522591149188156043)
              ·
                refine ⟨2311127283886723782234065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540751522591149188156043 2311127283886723782234065)
                ·
                  refine ⟨1733345462915042836675549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2311127283886723782234065 1733345462915042836675549)
                  ·
                    refine ⟨650004548593141063753331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1733345462915042836675549 650004548593141063753331)
                    ·
                      rfl

theorem cell22_1898819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 3].length) (baseStart_1898819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898819 prefixEnd_1898819 := by exact prefixLift 1898819
  have htrace : WordTrace (prefixWord ++ tailWord_1898819) baseStart_1898819 baseEnd_1898819 := by
    simpa [prefixWord, tailWord_1898819, baseEnd_1898819] using wordTrace_append hprefix tailTrace_1898819
  have hstable : (prefixWord ++ tailWord_1898819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898819).length < 2 ^ (prefixWord ++ tailWord_1898819).sum := by decide
  have hdescent : baseEnd_1898819 < baseStart_1898819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898875 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 1, 7]
def baseStart_1898875 : Nat := 118140960795 + 1898875 * 2 ^ 59
def prefixEnd_1898875 : Nat := 4983230072969 + 3 ^ 40 * 1898875 * 2
def baseEnd_1898875 : Nat := 650023718537575584353159

theorem tailTrace_1898875 : CollatzResearch.WordTrace tailWord_1898875 prefixEnd_1898875 650023718537575584353159 := by
  unfold tailWord_1898875
  simp only [CollatzResearch.WordTrace]
  refine ⟨69257660995707651876106079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46171773997138434584070719 69257660995707651876106079)
  ·
    refine ⟨103886491493561477814159119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69257660995707651876106079 103886491493561477814159119)
    ·
      refine ⟨155829737240342216721238679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103886491493561477814159119 155829737240342216721238679)
      ·
        refine ⟨233744605860513325081858019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155829737240342216721238679 233744605860513325081858019)
        ·
          refine ⟨350616908790769987622787029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233744605860513325081858019 350616908790769987622787029)
          ·
            refine ⟨8217583799783671584909071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 350616908790769987622787029 8217583799783671584909071)
            ·
              refine ⟨12326375699675507377363607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8217583799783671584909071 12326375699675507377363607)
              ·
                refine ⟨18489563549513261066045411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12326375699675507377363607 18489563549513261066045411)
                ·
                  refine ⟨27734345324269891599068117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18489563549513261066045411 27734345324269891599068117)
                  ·
                    refine ⟨650023718537575584353159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27734345324269891599068117 650023718537575584353159)
                    ·
                      rfl

theorem cell22_1898875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_1898875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898875 prefixEnd_1898875 := by exact prefixLift 1898875
  have htrace : WordTrace (prefixWord ++ tailWord_1898875) baseStart_1898875 baseEnd_1898875 := by
    simpa [prefixWord, tailWord_1898875, baseEnd_1898875] using wordTrace_append hprefix tailTrace_1898875
  have hstable : (prefixWord ++ tailWord_1898875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898875).length < 2 ^ (prefixWord ++ tailWord_1898875).sum := by decide
  have hdescent : baseEnd_1898875 < baseStart_1898875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898877 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 5]
def baseStart_1898877 : Nat := 118140960795 + 1898877 * 2 ^ 59
def prefixEnd_1898877 : Nat := 4983230072969 + 3 ^ 40 * 1898877 * 2
def baseEnd_1898877 : Nat := 216674801059482748601051

theorem tailTrace_1898877 : CollatzResearch.WordTrace tailWord_1898877 prefixEnd_1898877 216674801059482748601051 := by
  unfold tailWord_1898877
  simp only [CollatzResearch.WordTrace]
  refine ⟨69257733941700406217678885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46171822627800270811785923 69257733941700406217678885)
  ·
    refine ⟨12985825114068826165814791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69257733941700406217678885 12985825114068826165814791)
    ·
      refine ⟨19478737671103239248722187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12985825114068826165814791 19478737671103239248722187)
      ·
        refine ⟨29218106506654858873083281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19478737671103239248722187 29218106506654858873083281)
        ·
          refine ⟨21913579879991144154812461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29218106506654858873083281 21913579879991144154812461)
          ·
            refine ⟨8217592454996679058054673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21913579879991144154812461 8217592454996679058054673)
            ·
              refine ⟨6163194341247509293541005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8217592454996679058054673 6163194341247509293541005)
              ·
                refine ⟨2311197877967815985077877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6163194341247509293541005 2311197877967815985077877)
                ·
                  refine ⟨216674801059482748601051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2311197877967815985077877 216674801059482748601051)
                  ·
                    rfl

theorem cell22_1898877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_1898877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898877 prefixEnd_1898877 := by exact prefixLift 1898877
  have htrace : WordTrace (prefixWord ++ tailWord_1898877) baseStart_1898877 baseEnd_1898877 := by
    simpa [prefixWord, tailWord_1898877, baseEnd_1898877] using wordTrace_append hprefix tailTrace_1898877
  have hstable : (prefixWord ++ tailWord_1898877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898877).length < 2 ^ (prefixWord ++ tailWord_1898877).sum := by decide
  have hdescent : baseEnd_1898877 < baseStart_1898877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898905 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 8]
def baseStart_1898905 : Nat := 118140960795 + 1898905 * 2 ^ 59
def prefixEnd_1898905 : Nat := 4983230072969 + 3 ^ 40 * 1898905 * 2
def baseEnd_1898905 : Nat := 216677996050221835367689

theorem tailTrace_1898905 : CollatzResearch.WordTrace tailWord_1898905 prefixEnd_1898905 216677996050221835367689 := by
  unfold tailWord_1898905
  simp only [CollatzResearch.WordTrace]
  refine ⟨69258755185598966999698169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46172503457065977999798779 69258755185598966999698169)
  ·
    refine ⟨51944066389199225249773627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69258755185598966999698169 51944066389199225249773627)
    ·
      refine ⟨77916099583798837874660441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51944066389199225249773627 77916099583798837874660441)
      ·
        refine ⟨58437074687849128405995331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77916099583798837874660441 58437074687849128405995331)
        ·
          refine ⟨87655612031773692608992997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58437074687849128405995331 87655612031773692608992997)
          ·
            refine ⟨16435427255957567364186187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87655612031773692608992997 16435427255957567364186187)
            ·
              refine ⟨24653140883936351046279281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16435427255957567364186187 24653140883936351046279281)
              ·
                refine ⟨18489855662952263284709461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24653140883936351046279281 18489855662952263284709461)
                ·
                  refine ⟨216677996050221835367689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18489855662952263284709461 216677996050221835367689)
                  ·
                    rfl

theorem cell22_1898905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_1898905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898905 prefixEnd_1898905 := by exact prefixLift 1898905
  have htrace : WordTrace (prefixWord ++ tailWord_1898905) baseStart_1898905 baseEnd_1898905 := by
    simpa [prefixWord, tailWord_1898905, baseEnd_1898905] using wordTrace_append hprefix tailTrace_1898905
  have hstable : (prefixWord ++ tailWord_1898905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898905).length < 2 ^ (prefixWord ++ tailWord_1898905).sum := by decide
  have hdescent : baseEnd_1898905 < baseStart_1898905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898952 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_1898952 : Nat := 118140960795 + 1898952 * 2 ^ 59
def prefixEnd_1898952 : Nat := 4983230072969 + 3 ^ 40 * 1898952 * 2
def baseEnd_1898952 : Nat := 650050077211173050177923

theorem tailTrace_1898952 : CollatzResearch.WordTrace tailWord_1898952 prefixEnd_1898952 650050077211173050177923 := by
  unfold tailWord_1898952
  simp only [CollatzResearch.WordTrace]
  refine ⟨34630234708214347013329555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46173646277619129351106073 34630234708214347013329555)
  ·
    refine ⟨51945352062321520519994333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34630234708214347013329555 51945352062321520519994333)
    ·
      refine ⟨19479507023370570194997875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51945352062321520519994333 19479507023370570194997875)
      ·
        refine ⟨29219260535055855292496813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19479507023370570194997875 29219260535055855292496813)
        ·
          refine ⟨10957222700645945734686305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29219260535055855292496813 10957222700645945734686305)
          ·
            refine ⟨8217917025484459301014729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10957222700645945734686305 8217917025484459301014729)
            ·
              refine ⟨6163437769113344475761047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8217917025484459301014729 6163437769113344475761047)
              ·
                refine ⟨9245156653670016713641571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6163437769113344475761047 9245156653670016713641571)
                ·
                  refine ⟨13867734980505025070462357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9245156653670016713641571 13867734980505025070462357)
                  ·
                    refine ⟨650050077211173050177923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13867734980505025070462357 650050077211173050177923)
                    ·
                      rfl

theorem cell22_1898952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_1898952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1898952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1898952 prefixEnd_1898952 := by exact prefixLift 1898952
  have htrace : WordTrace (prefixWord ++ tailWord_1898952) baseStart_1898952 baseEnd_1898952 := by
    simpa [prefixWord, tailWord_1898952, baseEnd_1898952] using wordTrace_append hprefix tailTrace_1898952
  have hstable : (prefixWord ++ tailWord_1898952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898952).length < 2 ^ (prefixWord ++ tailWord_1898952).sum := by decide
  have hdescent : baseEnd_1898952 < baseStart_1898952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899016 : List Nat := [2, 1, 3, 2, 1, 1, 1, 7, 1, 3]
def baseStart_1899016 : Nat := 118140960795 + 1899016 * 2 ^ 59
def prefixEnd_1899016 : Nat := 4983230072969 + 3 ^ 40 * 1899016 * 2
def baseEnd_1899016 : Nat := 650071985719098216577727

theorem tailTrace_1899016 : CollatzResearch.WordTrace tailWord_1899016 prefixEnd_1899016 650071985719098216577727 := by
  unfold tailWord_1899016
  simp only [CollatzResearch.WordTrace]
  refine ⟨34631401844098416478494451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46175202458797888637992601 34631401844098416478494451)
  ·
    refine ⟨51947102766147624717741677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34631401844098416478494451 51947102766147624717741677)
    ·
      refine ⟨19480163537305359269153129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51947102766147624717741677 19480163537305359269153129)
      ·
        refine ⟨14610122652979019451864847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19480163537305359269153129 14610122652979019451864847)
        ·
          refine ⟨21915183979468529177797271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14610122652979019451864847 21915183979468529177797271)
          ·
            refine ⟨32872775969202793766695907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21915183979468529177797271 32872775969202793766695907)
            ·
              refine ⟨49309163953804190650043861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32872775969202793766695907 49309163953804190650043861)
              ·
                refine ⟨1155683530167285718360403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49309163953804190650043861 1155683530167285718360403)
                ·
                  refine ⟨1733525295250928577540605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155683530167285718360403 1733525295250928577540605)
                  ·
                    refine ⟨650071985719098216577727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1733525295250928577540605 650071985719098216577727)
                    ·
                      rfl

theorem cell22_1899016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_1899016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899016 prefixEnd_1899016 := by exact prefixLift 1899016
  have htrace : WordTrace (prefixWord ++ tailWord_1899016) baseStart_1899016 baseEnd_1899016 := by
    simpa [prefixWord, tailWord_1899016, baseEnd_1899016] using wordTrace_append hprefix tailTrace_1899016
  have hstable : (prefixWord ++ tailWord_1899016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899016).length < 2 ^ (prefixWord ++ tailWord_1899016).sum := by decide
  have hdescent : baseEnd_1899016 < baseStart_1899016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899027 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 2, 5]
def baseStart_1899027 : Nat := 118140960795 + 1899027 * 2 ^ 59
def prefixEnd_1899027 : Nat := 4983230072969 + 3 ^ 40 * 1899027 * 2
def baseEnd_1899027 : Nat := 650075751243897854552693

theorem tailTrace_1899027 : CollatzResearch.WordTrace tailWord_1899027 prefixEnd_1899027 650075751243897854552693 := by
  unfold tailWord_1899027
  simp only [CollatzResearch.WordTrace]
  refine ⟨69263204891156981835639335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46175469927437987890426223 69263204891156981835639335)
  ·
    refine ⟨103894807336735472753459003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69263204891156981835639335 103894807336735472753459003)
    ·
      refine ⟨155842211005103209130188505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103894807336735472753459003 155842211005103209130188505)
      ·
        refine ⟨116881658253827406847641379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155842211005103209130188505 116881658253827406847641379)
        ·
          refine ⟨175322487380741110271462069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116881658253827406847641379 175322487380741110271462069)
          ·
            refine ⟨16436483191944479087949569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175322487380741110271462069 16436483191944479087949569)
            ·
              refine ⟨12327362393958359315962177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16436483191944479087949569 12327362393958359315962177)
              ·
                refine ⟨9245521795468769486971633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12327362393958359315962177 9245521795468769486971633)
                ·
                  refine ⟨6934141346601577115228725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9245521795468769486971633 6934141346601577115228725)
                  ·
                    refine ⟨650075751243897854552693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6934141346601577115228725 650075751243897854552693)
                    ·
                      rfl

theorem cell22_1899027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_1899027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899027 prefixEnd_1899027 := by exact prefixLift 1899027
  have htrace : WordTrace (prefixWord ++ tailWord_1899027) baseStart_1899027 baseEnd_1899027 := by
    simpa [prefixWord, tailWord_1899027, baseEnd_1899027] using wordTrace_append hprefix tailTrace_1899027
  have hstable : (prefixWord ++ tailWord_1899027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899027).length < 2 ^ (prefixWord ++ tailWord_1899027).sum := by decide
  have hdescent : baseEnd_1899027 < baseStart_1899027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899029 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 5]
def baseStart_1899029 : Nat := 118140960795 + 1899029 * 2 ^ 59
def prefixEnd_1899029 : Nat := 4983230072969 + 3 ^ 40 * 1899029 * 2
def baseEnd_1899029 : Nat := 216692145294923505334229

theorem tailTrace_1899029 : CollatzResearch.WordTrace tailWord_1899029 prefixEnd_1899029 216692145294923505334229 := by
  unfold tailWord_1899029
  simp only [CollatzResearch.WordTrace]
  refine ⟨69263277837149736177212141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46175518558099824118141427 69263277837149736177212141)
  ·
    refine ⟨25973729188931151066454553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69263277837149736177212141 25973729188931151066454553)
    ·
      refine ⟨19480296891698363299840915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25973729188931151066454553 19480296891698363299840915)
      ·
        refine ⟨29220445337547544949761373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19480296891698363299840915 29220445337547544949761373)
        ·
          refine ⟨10957667001580329356160515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29220445337547544949761373 10957667001580329356160515)
          ·
            refine ⟨16436500502370494034240773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10957667001580329356160515 16436500502370494034240773)
            ·
              refine ⟨3081843844194467631420145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16436500502370494034240773 3081843844194467631420145)
              ·
                refine ⟨2311382883145850723565109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081843844194467631420145 2311382883145850723565109)
                ·
                  refine ⟨216692145294923505334229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2311382883145850723565109 216692145294923505334229)
                  ·
                    rfl

theorem cell22_1899029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_1899029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899029 prefixEnd_1899029 := by exact prefixLift 1899029
  have htrace : WordTrace (prefixWord ++ tailWord_1899029) baseStart_1899029 baseEnd_1899029 := by
    simpa [prefixWord, tailWord_1899029, baseEnd_1899029] using wordTrace_append hprefix tailTrace_1899029
  have hstable : (prefixWord ++ tailWord_1899029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899029).length < 2 ^ (prefixWord ++ tailWord_1899029).sum := by decide
  have hdescent : baseEnd_1899029 < baseStart_1899029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899057 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 8]
def baseStart_1899057 : Nat := 118140960795 + 1899057 * 2 ^ 59
def prefixEnd_1899057 : Nat := 4983230072969 + 3 ^ 40 * 1899057 * 2
def baseEnd_1899057 : Nat := 216695340285662592100867

theorem tailTrace_1899057 : CollatzResearch.WordTrace tailWord_1899057 prefixEnd_1899057 216695340285662592100867 := by
  unfold tailWord_1899057
  simp only [CollatzResearch.WordTrace]
  refine ⟨69264299081048296959231425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46176199387365531306154283 69264299081048296959231425)
  ·
    refine ⟨51948224310786222719423569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69264299081048296959231425 51948224310786222719423569)
    ·
      refine ⟨38961168233089667039567677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51948224310786222719423569 38961168233089667039567677)
      ·
        refine ⟨14610438087408625139837879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38961168233089667039567677 14610438087408625139837879)
        ·
          refine ⟨21915657131112937709756819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14610438087408625139837879 21915657131112937709756819)
          ·
            refine ⟨32873485696669406564635229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21915657131112937709756819 32873485696669406564635229)
            ·
              refine ⟨12327557136251027461738211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32873485696669406564635229 12327557136251027461738211)
              ·
                refine ⟨18491335704376541192607317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12327557136251027461738211 18491335704376541192607317)
                ·
                  refine ⟨216695340285662592100867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18491335704376541192607317 216695340285662592100867)
                  ·
                    rfl

theorem cell22_1899057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_1899057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899057 prefixEnd_1899057 := by exact prefixLift 1899057
  have htrace : WordTrace (prefixWord ++ tailWord_1899057) baseStart_1899057 baseEnd_1899057 := by
    simpa [prefixWord, tailWord_1899057, baseEnd_1899057] using wordTrace_append hprefix tailTrace_1899057
  have hstable : (prefixWord ++ tailWord_1899057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899057).length < 2 ^ (prefixWord ++ tailWord_1899057).sum := by decide
  have hdescent : baseEnd_1899057 < baseStart_1899057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899059 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 1, 4]
def baseStart_1899059 : Nat := 118140960795 + 1899059 * 2 ^ 59
def prefixEnd_1899059 : Nat := 4983230072969 + 3 ^ 40 * 1899059 * 2
def baseEnd_1899059 : Nat := 650086705497860437752595

theorem tailTrace_1899059 : CollatzResearch.WordTrace tailWord_1899059 prefixEnd_1899059 650086705497860437752595 := by
  unfold tailWord_1899059
  simp only [CollatzResearch.WordTrace]
  refine ⟨69264372027041051300804231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46176248018027367533869487 69264372027041051300804231)
  ·
    refine ⟨103896558040561576951206347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69264372027041051300804231 103896558040561576951206347)
    ·
      refine ⟨155844837060842365426809521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103896558040561576951206347 155844837060842365426809521)
      ·
        refine ⟨116883627795631774070107141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155844837060842365426809521 116883627795631774070107141)
        ·
          refine ⟨21915680211680957638145089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116883627795631774070107141 21915680211680957638145089)
          ·
            refine ⟨16436760158760718228608817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21915680211680957638145089 16436760158760718228608817)
            ·
              refine ⟨12327570119070538671456613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16436760158760718228608817 12327570119070538671456613)
              ·
                refine ⟨2311419397325726000898115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12327570119070538671456613 2311419397325726000898115)
                ·
                  refine ⟨3467129095988589001347173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311419397325726000898115 3467129095988589001347173)
                  ·
                    refine ⟨650086705497860437752595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467129095988589001347173 650086705497860437752595)
                    ·
                      rfl

theorem cell22_1899059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 4].length) (baseStart_1899059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899059 prefixEnd_1899059 := by exact prefixLift 1899059
  have htrace : WordTrace (prefixWord ++ tailWord_1899059) baseStart_1899059 baseEnd_1899059 := by
    simpa [prefixWord, tailWord_1899059, baseEnd_1899059] using wordTrace_append hprefix tailTrace_1899059
  have hstable : (prefixWord ++ tailWord_1899059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899059).length < 2 ^ (prefixWord ++ tailWord_1899059).sum := by decide
  have hdescent : baseEnd_1899059 < baseStart_1899059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899119 : List Nat := [1, 1, 2, 1, 3, 2, 6, 6]
def baseStart_1899119 : Nat := 118140960795 + 1899119 * 2 ^ 59
def prefixEnd_1899119 : Nat := 4983230072969 + 3 ^ 40 * 1899119 * 2
def baseEnd_1899119 : Nat := 72234138302671142361379

theorem tailTrace_1899119 : CollatzResearch.WordTrace tailWord_1899119 prefixEnd_1899119 72234138302671142361379 := by
  unfold tailWord_1899119
  simp only [CollatzResearch.WordTrace]
  refine ⟨69266560406823681547988411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46177706937882454365325607 69266560406823681547988411)
  ·
    refine ⟨103899840610235522321982617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69266560406823681547988411 103899840610235522321982617)
    ·
      refine ⟨77924880457676641741486963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103899840610235522321982617 77924880457676641741486963)
      ·
        refine ⟨116887320686514962612230445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77924880457676641741486963 116887320686514962612230445)
        ·
          refine ⟨43832745257443110979586417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116887320686514962612230445 43832745257443110979586417)
          ·
            refine ⟨32874558943082333234689813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43832745257443110979586417 32874558943082333234689813)
            ·
              refine ⟨1540994950456984370376085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32874558943082333234689813 1540994950456984370376085)
              ·
                refine ⟨72234138302671142361379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1540994950456984370376085 72234138302671142361379)
                ·
                  rfl

theorem cell22_1899119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 6].length) (baseStart_1899119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899119 prefixEnd_1899119 := by exact prefixLift 1899119
  have htrace : WordTrace (prefixWord ++ tailWord_1899119) baseStart_1899119 baseEnd_1899119 := by
    simpa [prefixWord, tailWord_1899119, baseEnd_1899119] using wordTrace_append hprefix tailTrace_1899119
  have hstable : (prefixWord ++ tailWord_1899119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899119).length < 2 ^ (prefixWord ++ tailWord_1899119).sum := by decide
  have hdescent : baseEnd_1899119 < baseStart_1899119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899125 : List Nat := [1, 3, 4, 2, 2, 2, 1, 3, 4]
def baseStart_1899125 : Nat := 118140960795 + 1899125 * 2 ^ 59
def prefixEnd_1899125 : Nat := 4983230072969 + 3 ^ 40 * 1899125 * 2
def baseEnd_1899125 : Nat := 216703099548886088534131

theorem tailTrace_1899125 : CollatzResearch.WordTrace tailWord_1899125 prefixEnd_1899125 216703099548886088534131 := by
  unfold tailWord_1899125
  simp only [CollatzResearch.WordTrace]
  refine ⟨69266779244801944572706829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46177852829867963048471219 69266779244801944572706829)
  ·
    refine ⟨25975042216800729214765061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69266779244801944572706829 25975042216800729214765061)
    ·
      refine ⟨4870320415650136727768449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25975042216800729214765061 4870320415650136727768449)
      ·
        refine ⟨3652740311737602545826337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4870320415650136727768449 3652740311737602545826337)
        ·
          refine ⟨2739555233803201909369753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3652740311737602545826337 2739555233803201909369753)
          ·
            refine ⟨2054666425352401432027315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2739555233803201909369753 2054666425352401432027315)
            ·
              refine ⟨3081999638028602148040973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054666425352401432027315 3081999638028602148040973)
              ·
                refine ⟨1155749864260725805515365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3081999638028602148040973 1155749864260725805515365)
                ·
                  refine ⟨216703099548886088534131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1155749864260725805515365 216703099548886088534131)
                  ·
                    rfl

theorem cell22_1899125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_1899125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899125 prefixEnd_1899125 := by exact prefixLift 1899125
  have htrace : WordTrace (prefixWord ++ tailWord_1899125) baseStart_1899125 baseEnd_1899125 := by
    simpa [prefixWord, tailWord_1899125, baseEnd_1899125] using wordTrace_append hprefix tailTrace_1899125
  have hstable : (prefixWord ++ tailWord_1899125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899125).length < 2 ^ (prefixWord ++ tailWord_1899125).sum := by decide
  have hdescent : baseEnd_1899125 < baseStart_1899125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899228 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1899228 : Nat := 118140960795 + 1899228 * 2 ^ 59
def prefixEnd_1899228 : Nat := 4983230072969 + 3 ^ 40 * 1899228 * 2
def baseEnd_1899228 : Nat := 650144557651600330277077

theorem tailTrace_1899228 : CollatzResearch.WordTrace tailWord_1899228 prefixEnd_1899228 650144557651600330277077 := by
  unfold tailWord_1899228
  simp only [CollatzResearch.WordTrace]
  refine ⟨34635267981714396581853169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46180357308952528775804225 34635267981714396581853169)
  ·
    refine ⟨25976450986285797436389877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34635267981714396581853169 25976450986285797436389877)
    ·
      refine ⟨2435292279964293509661551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25976450986285797436389877 2435292279964293509661551)
      ·
        refine ⟨3652938419946440264492327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435292279964293509661551 3652938419946440264492327)
        ·
          refine ⟨5479407629919660396738491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652938419946440264492327 5479407629919660396738491)
          ·
            refine ⟨8219111444879490595107737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479407629919660396738491 8219111444879490595107737)
            ·
              refine ⟨6164333583659617946330803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8219111444879490595107737 6164333583659617946330803)
              ·
                refine ⟨9246500375489426919496205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6164333583659617946330803 9246500375489426919496205)
                ·
                  refine ⟨3467437640808535094811077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9246500375489426919496205 3467437640808535094811077)
                  ·
                    refine ⟨650144557651600330277077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467437640808535094811077 650144557651600330277077)
                    ·
                      rfl

theorem cell22_1899228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1899228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899228 prefixEnd_1899228 := by exact prefixLift 1899228
  have htrace : WordTrace (prefixWord ++ tailWord_1899228) baseStart_1899228 baseEnd_1899228 := by
    simpa [prefixWord, tailWord_1899228, baseEnd_1899228] using wordTrace_append hprefix tailTrace_1899228
  have hstable : (prefixWord ++ tailWord_1899228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899228).length < 2 ^ (prefixWord ++ tailWord_1899228).sum := by decide
  have hdescent : baseEnd_1899228 < baseStart_1899228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899258 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_1899258 : Nat := 118140960795 + 1899258 * 2 ^ 59
def prefixEnd_1899258 : Nat := 4983230072969 + 3 ^ 40 * 1899258 * 2
def baseEnd_1899258 : Nat := 650154827264690252026985

theorem tailTrace_1899258 : CollatzResearch.WordTrace tailWord_1899258 prefixEnd_1899258 650154827264690252026985 := by
  unfold tailWord_1899258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17317907538330027071824607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46181086768880072191532285 17317907538330027071824607)
  ·
    refine ⟨25976861307495040607736911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17317907538330027071824607 25976861307495040607736911)
    ·
      refine ⟨38965291961242560911605367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25976861307495040607736911 38965291961242560911605367)
      ·
        refine ⟨58447937941863841367408051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38965291961242560911605367 58447937941863841367408051)
        ·
          refine ⟨87671906912795762051112077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58447937941863841367408051 87671906912795762051112077)
          ·
            refine ⟨32876965092298410769167029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87671906912795762051112077 32876965092298410769167029)
            ·
              refine ⟨3082215477402976009609409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32876965092298410769167029 3082215477402976009609409)
              ·
                refine ⟨2311661608052232007207057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3082215477402976009609409 2311661608052232007207057)
                ·
                  refine ⟨1733746206039174005405293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2311661608052232007207057 1733746206039174005405293)
                  ·
                    refine ⟨650154827264690252026985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1733746206039174005405293 650154827264690252026985)
                    ·
                      rfl

theorem cell22_1899258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_1899258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899258 prefixEnd_1899258 := by exact prefixLift 1899258
  have htrace : WordTrace (prefixWord ++ tailWord_1899258) baseStart_1899258 baseEnd_1899258 := by
    simpa [prefixWord, tailWord_1899258, baseEnd_1899258] using wordTrace_append hprefix tailTrace_1899258
  have hstable : (prefixWord ++ tailWord_1899258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899258).length < 2 ^ (prefixWord ++ tailWord_1899258).sum := by decide
  have hdescent : baseEnd_1899258 < baseStart_1899258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899391 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 4, 4]
def baseStart_1899391 : Nat := 118140960795 + 1899391 * 2 ^ 59
def prefixEnd_1899391 : Nat := 4983230072969 + 3 ^ 40 * 1899391 * 2
def baseEnd_1899391 : Nat := 650200355882722238451577

theorem tailTrace_1899391 : CollatzResearch.WordTrace tailWord_1899391 prefixEnd_1899391 650200355882722238451577 := by
  unfold tailWord_1899391
  simp only [CollatzResearch.WordTrace]
  refine ⟨69276481061838272001890027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46184320707892181334593351 69276481061838272001890027)
  ·
    refine ⟨103914721592757408002835041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69276481061838272001890027 103914721592757408002835041)
    ·
      refine ⟨77936041194568056002126281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103914721592757408002835041 77936041194568056002126281)
      ·
        refine ⟨58452030895926042001594711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77936041194568056002126281 58452030895926042001594711)
        ·
          refine ⟨87678046343889063002392067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58452030895926042001594711 87678046343889063002392067)
          ·
            refine ⟨131517069515833594503588101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87678046343889063002392067 131517069515833594503588101)
            ·
              refine ⟨24659450534218798969422769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131517069515833594503588101 24659450534218798969422769)
              ·
                refine ⟨18494587900664099227067077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24659450534218798969422769 18494587900664099227067077)
                ·
                  refine ⟨3467735231374518605075077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18494587900664099227067077 3467735231374518605075077)
                  ·
                    refine ⟨650200355882722238451577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467735231374518605075077 650200355882722238451577)
                    ·
                      rfl

theorem cell22_1899391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_1899391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899391 prefixEnd_1899391 := by exact prefixLift 1899391
  have htrace : WordTrace (prefixWord ++ tailWord_1899391) baseStart_1899391 baseEnd_1899391 := by
    simpa [prefixWord, tailWord_1899391, baseEnd_1899391] using wordTrace_append hprefix tailTrace_1899391
  have hstable : (prefixWord ++ tailWord_1899391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899391).length < 2 ^ (prefixWord ++ tailWord_1899391).sum := by decide
  have hdescent : baseEnd_1899391 < baseStart_1899391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899414 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1899414 : Nat := 118140960795 + 1899414 * 2 ^ 59
def prefixEnd_1899414 : Nat := 4983230072969 + 3 ^ 40 * 1899414 * 2
def baseEnd_1899414 : Nat := 650208229252757845126507

theorem tailTrace_1899414 : CollatzResearch.WordTrace tailWord_1899414 prefixEnd_1899414 650208229252757845126507 := by
  unfold tailWord_1899414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329832496297184183123581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46184879960503297953318197 4329832496297184183123581)
  ·
    refine ⟨1623687186111444068671343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4329832496297184183123581 1623687186111444068671343)
    ·
      refine ⟨2435530779167166103007015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623687186111444068671343 2435530779167166103007015)
      ·
        refine ⟨3653296168750749154510523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435530779167166103007015 3653296168750749154510523)
        ·
          refine ⟨5479944253126123731765785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653296168750749154510523 5479944253126123731765785)
          ·
            refine ⟨4109958189844592798824339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5479944253126123731765785 4109958189844592798824339)
            ·
              refine ⟨6164937284766889198236509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4109958189844592798824339 6164937284766889198236509)
              ·
                refine ⟨2311851481787583449338691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6164937284766889198236509 2311851481787583449338691)
                ·
                  refine ⟨3467777222681375174008037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311851481787583449338691 3467777222681375174008037)
                  ·
                    refine ⟨650208229252757845126507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467777222681375174008037 650208229252757845126507)
                    ·
                      rfl

theorem cell22_1899414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1899414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899414 prefixEnd_1899414 := by exact prefixLift 1899414
  have htrace : WordTrace (prefixWord ++ tailWord_1899414) baseStart_1899414 baseEnd_1899414 := by
    simpa [prefixWord, tailWord_1899414, baseEnd_1899414] using wordTrace_append hprefix tailTrace_1899414
  have hstable : (prefixWord ++ tailWord_1899414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899414).length < 2 ^ (prefixWord ++ tailWord_1899414).sum := by decide
  have hdescent : baseEnd_1899414 < baseStart_1899414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899528 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_1899528 : Nat := 118140960795 + 1899528 * 2 ^ 59
def prefixEnd_1899528 : Nat := 4983230072969 + 3 ^ 40 * 1899528 * 2
def baseEnd_1899528 : Nat := 650247253782499547776157

theorem tailTrace_1899528 : CollatzResearch.WordTrace tailWord_1899528 prefixEnd_1899528 650247253782499547776157 := by
  unfold tailWord_1899528
  simp only [CollatzResearch.WordTrace]
  refine ⟨34640738931170972199813619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46187651908227962933084825 34640738931170972199813619)
  ·
    refine ⟨51961108396756458299720429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34640738931170972199813619 51961108396756458299720429)
    ·
      refine ⟨19485415648783671862395161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51961108396756458299720429 19485415648783671862395161)
      ·
        refine ⟨14614061736587753896796371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19485415648783671862395161 14614061736587753896796371)
        ·
          refine ⟨21921092604881630845194557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14614061736587753896796371 21921092604881630845194557)
          ·
            refine ⟨8220409726830611566947959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21921092604881630845194557 8220409726830611566947959)
            ·
              refine ⟨12330614590245917350421939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8220409726830611566947959 12330614590245917350421939)
              ·
                refine ⟨18495921885368876025632909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12330614590245917350421939 18495921885368876025632909)
                ·
                  refine ⟨6935970707013328509612341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18495921885368876025632909 6935970707013328509612341)
                  ·
                    refine ⟨650247253782499547776157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6935970707013328509612341 650247253782499547776157)
                    ·
                      rfl

theorem cell22_1899528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_1899528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899528 prefixEnd_1899528 := by exact prefixLift 1899528
  have htrace : WordTrace (prefixWord ++ tailWord_1899528) baseStart_1899528 baseEnd_1899528 := by
    simpa [prefixWord, tailWord_1899528, baseEnd_1899528] using wordTrace_append hprefix tailTrace_1899528
  have hstable : (prefixWord ++ tailWord_1899528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899528).length < 2 ^ (prefixWord ++ tailWord_1899528).sum := by decide
  have hdescent : baseEnd_1899528 < baseStart_1899528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899532 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 1, 4]
def baseStart_1899532 : Nat := 118140960795 + 1899532 * 2 ^ 59
def prefixEnd_1899532 : Nat := 4983230072969 + 3 ^ 40 * 1899532 * 2
def baseEnd_1899532 : Nat := 650248623064244870676145

theorem tailTrace_1899532 : CollatzResearch.WordTrace tailWord_1899532 prefixEnd_1899532 650248623064244870676145 := by
  unfold tailWord_1899532
  simp only [CollatzResearch.WordTrace]
  refine ⟨34640811877163726541386425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46187749169551635388515233 34640811877163726541386425)
  ·
    refine ⟨25980608907872794906039819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34640811877163726541386425 25980608907872794906039819)
    ·
      refine ⟨38970913361809192359059729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25980608907872794906039819 38970913361809192359059729)
      ·
        refine ⟨29228185021356894269294797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38970913361809192359059729 29228185021356894269294797)
        ·
          refine ⟨10960569383008835350985549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29228185021356894269294797 10960569383008835350985549)
          ·
            refine ⟨4110213518628313256619581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10960569383008835350985549 4110213518628313256619581)
            ·
              refine ⟨1541330069485617471232343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4110213518628313256619581 1541330069485617471232343)
              ·
                refine ⟨2311995104228426206848515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541330069485617471232343 2311995104228426206848515)
                ·
                  refine ⟨3467992656342639310272773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311995104228426206848515 3467992656342639310272773)
                  ·
                    refine ⟨650248623064244870676145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467992656342639310272773 650248623064244870676145)
                    ·
                      rfl

theorem cell22_1899532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_1899532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899532 prefixEnd_1899532 := by exact prefixLift 1899532
  have htrace : WordTrace (prefixWord ++ tailWord_1899532) baseStart_1899532 baseEnd_1899532 := by
    simpa [prefixWord, tailWord_1899532, baseEnd_1899532] using wordTrace_append hprefix tailTrace_1899532
  have hstable : (prefixWord ++ tailWord_1899532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899532).length < 2 ^ (prefixWord ++ tailWord_1899532).sum := by decide
  have hdescent : baseEnd_1899532 < baseStart_1899532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899545 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 2, 3]
def baseStart_1899545 : Nat := 118140960795 + 1899545 * 2 ^ 59
def prefixEnd_1899545 : Nat := 4983230072969 + 3 ^ 40 * 1899545 * 2
def baseEnd_1899545 : Nat := 650253073229917170101105

theorem tailTrace_1899545 : CollatzResearch.WordTrace tailWord_1899545 prefixEnd_1899545 650253073229917170101105 := by
  unfold tailWord_1899545
  simp only [CollatzResearch.WordTrace]
  refine ⟨69282097903280356302996089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46188065268853570868664059 69282097903280356302996089)
  ·
    refine ⟨51961573427460267227247067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69282097903280356302996089 51961573427460267227247067)
    ·
      refine ⟨77942360141190400840870601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51961573427460267227247067 77942360141190400840870601)
      ·
        refine ⟨58456770105892800630652951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77942360141190400840870601 58456770105892800630652951)
        ·
          refine ⟨87685155158839200945979427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58456770105892800630652951 87685155158839200945979427)
          ·
            refine ⟨131527732738258801418969141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87685155158839200945979427 131527732738258801418969141)
            ·
              refine ⟨12330724944211762633028357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131527732738258801418969141 12330724944211762633028357)
              ·
                refine ⟨2312010927039705493692817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12330724944211762633028357 2312010927039705493692817)
                ·
                  refine ⟨1734008195279779120269613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2312010927039705493692817 1734008195279779120269613)
                  ·
                    refine ⟨650253073229917170101105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734008195279779120269613 650253073229917170101105)
                    ·
                      rfl

theorem cell22_1899545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_1899545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899545 prefixEnd_1899545 := by exact prefixLift 1899545
  have htrace : WordTrace (prefixWord ++ tailWord_1899545) baseStart_1899545 baseEnd_1899545 := by
    simpa [prefixWord, tailWord_1899545, baseEnd_1899545] using wordTrace_append hprefix tailTrace_1899545
  have hstable : (prefixWord ++ tailWord_1899545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899545).length < 2 ^ (prefixWord ++ tailWord_1899545).sum := by decide
  have hdescent : baseEnd_1899545 < baseStart_1899545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899562 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1899562 : Nat := 118140960795 + 1899562 * 2 ^ 59
def prefixEnd_1899562 : Nat := 4983230072969 + 3 ^ 40 * 1899562 * 2
def baseEnd_1899562 : Nat := 650258892677334792426053

theorem tailTrace_1899562 : CollatzResearch.WordTrace tailWord_1899562 prefixEnd_1899562 650258892677334792426053 := by
  unfold tailWord_1899562
  simp only [CollatzResearch.WordTrace]
  refine ⟨17320679486054692051591235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46188478629479178804243293 17320679486054692051591235)
  ·
    refine ⟨25981019229082038077386853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17320679486054692051591235 25981019229082038077386853)
    ·
      refine ⟨4871441105452882139510035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25981019229082038077386853 4871441105452882139510035)
      ·
        refine ⟨7307161658179323209265053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4871441105452882139510035 7307161658179323209265053)
        ·
          refine ⟨2740185621817246203474395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7307161658179323209265053 2740185621817246203474395)
          ·
            refine ⟨4110278432725869305211593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740185621817246203474395 4110278432725869305211593)
            ·
              refine ⟨3082708824544401978908695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110278432725869305211593 3082708824544401978908695)
              ·
                refine ⟨4624063236816602968363043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082708824544401978908695 4624063236816602968363043)
                ·
                  refine ⟨6936094855224904452544565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624063236816602968363043 6936094855224904452544565)
                  ·
                    refine ⟨650258892677334792426053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6936094855224904452544565 650258892677334792426053)
                    ·
                      rfl

theorem cell22_1899562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1899562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899562 prefixEnd_1899562 := by exact prefixLift 1899562
  have htrace : WordTrace (prefixWord ++ tailWord_1899562) baseStart_1899562 baseEnd_1899562 := by
    simpa [prefixWord, tailWord_1899562, baseEnd_1899562] using wordTrace_append hprefix tailTrace_1899562
  have hstable : (prefixWord ++ tailWord_1899562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899562).length < 2 ^ (prefixWord ++ tailWord_1899562).sum := by decide
  have hdescent : baseEnd_1899562 < baseStart_1899562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899577 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 2, 4]
def baseStart_1899577 : Nat := 118140960795 + 1899577 * 2 ^ 59
def prefixEnd_1899577 : Nat := 4983230072969 + 3 ^ 40 * 1899577 * 2
def baseEnd_1899577 : Nat := 650264027483879753301007

theorem tailTrace_1899577 : CollatzResearch.WordTrace tailWord_1899577 prefixEnd_1899577 650264027483879753301007 := by
  unfold tailWord_1899577
  simp only [CollatzResearch.WordTrace]
  refine ⟨69283265039164425768160985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46188843359442950512107323 69283265039164425768160985)
  ·
    refine ⟨51962448779373319326120739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69283265039164425768160985 51962448779373319326120739)
    ·
      refine ⟨77943673169059978989181109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51962448779373319326120739 77943673169059978989181109)
      ·
        refine ⟨7307219359599373030235729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77943673169059978989181109 7307219359599373030235729)
        ·
          refine ⟨5480414519699529772676797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7307219359599373030235729 5480414519699529772676797)
          ·
            refine ⟨2055155444887323664753799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5480414519699529772676797 2055155444887323664753799)
            ·
              refine ⟨3082733167330985497130699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055155444887323664753799 3082733167330985497130699)
              ·
                refine ⟨4624099750996478245696049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082733167330985497130699 4624099750996478245696049)
                ·
                  refine ⟨3468074813247358684272037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4624099750996478245696049 3468074813247358684272037)
                  ·
                    refine ⟨650264027483879753301007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468074813247358684272037 650264027483879753301007)
                    ·
                      rfl

theorem cell22_1899577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_1899577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899577 prefixEnd_1899577 := by exact prefixLift 1899577
  have htrace : WordTrace (prefixWord ++ tailWord_1899577) baseStart_1899577 baseEnd_1899577 := by
    simpa [prefixWord, tailWord_1899577, baseEnd_1899577] using wordTrace_append hprefix tailTrace_1899577
  have hstable : (prefixWord ++ tailWord_1899577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899577).length < 2 ^ (prefixWord ++ tailWord_1899577).sum := by decide
  have hdescent : baseEnd_1899577 < baseStart_1899577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899641 : List Nat := [1, 2, 1, 3, 5, 2, 1, 3, 1, 3]
def baseStart_1899641 : Nat := 118140960795 + 1899641 * 2 ^ 59
def prefixEnd_1899641 : Nat := 4983230072969 + 3 ^ 40 * 1899641 * 2
def baseEnd_1899641 : Nat := 650285935991804919700811

theorem tailTrace_1899641 : CollatzResearch.WordTrace tailWord_1899641 prefixEnd_1899641 650285935991804919700811 := by
  unfold tailWord_1899641
  simp only [CollatzResearch.WordTrace]
  refine ⟨69285599310932564698490777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46190399540621709798993851 69285599310932564698490777)
  ·
    refine ⟨51964199483199423523868083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69285599310932564698490777 51964199483199423523868083)
    ·
      refine ⟨77946299224799135285802125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51964199483199423523868083 77946299224799135285802125)
      ·
        refine ⟨29229862209299675732175797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77946299224799135285802125 29229862209299675732175797)
        ·
          refine ⟨2740299582121844599891481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29229862209299675732175797 2740299582121844599891481)
          ·
            refine ⟨2055224686591383449918611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2740299582121844599891481 2055224686591383449918611)
            ·
              refine ⟨3082837029887075174877917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055224686591383449918611 3082837029887075174877917)
              ·
                refine ⟨1156063886207653190579219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3082837029887075174877917 1156063886207653190579219)
                ·
                  refine ⟨1734095829311479785868829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156063886207653190579219 1734095829311479785868829)
                  ·
                    refine ⟨650285935991804919700811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1734095829311479785868829 650285935991804919700811)
                    ·
                      rfl

theorem cell22_1899641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 3].length) (baseStart_1899641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899641 prefixEnd_1899641 := by exact prefixLift 1899641
  have htrace : WordTrace (prefixWord ++ tailWord_1899641) baseStart_1899641 baseEnd_1899641 := by
    simpa [prefixWord, tailWord_1899641, baseEnd_1899641] using wordTrace_append hprefix tailTrace_1899641
  have hstable : (prefixWord ++ tailWord_1899641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899641).length < 2 ^ (prefixWord ++ tailWord_1899641).sum := by decide
  have hdescent : baseEnd_1899641 < baseStart_1899641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899648 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 8]
def baseStart_1899648 : Nat := 118140960795 + 1899648 * 2 ^ 59
def prefixEnd_1899648 : Nat := 4983230072969 + 3 ^ 40 * 1899648 * 2
def baseEnd_1899648 : Nat := 216762777411619744925263

theorem tailTrace_1899648 : CollatzResearch.WordTrace tailWord_1899648 prefixEnd_1899648 216762777411619744925263 := by
  unfold tailWord_1899648
  simp only [CollatzResearch.WordTrace]
  refine ⟨34642927310953602446997799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46190569747938136595997065 34642927310953602446997799)
  ·
    refine ⟨51964390966430403670496699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34642927310953602446997799 51964390966430403670496699)
    ·
      refine ⟨77946586449645605505745049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51964390966430403670496699 77946586449645605505745049)
      ·
        refine ⟨58459939837234204129308787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77946586449645605505745049 58459939837234204129308787)
        ·
          refine ⟨87689909755851306193963181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58459939837234204129308787 87689909755851306193963181)
          ·
            refine ⟨32883716158444239822736193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87689909755851306193963181 32883716158444239822736193)
            ·
              refine ⟨24662787118833179867052145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32883716158444239822736193 24662787118833179867052145)
              ·
                refine ⟨18497090339124884900289109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24662787118833179867052145 18497090339124884900289109)
                ·
                  refine ⟨216762777411619744925263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18497090339124884900289109 216762777411619744925263)
                  ·
                    rfl

theorem cell22_1899648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_1899648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899648 prefixEnd_1899648 := by exact prefixLift 1899648
  have htrace : WordTrace (prefixWord ++ tailWord_1899648) baseStart_1899648 baseEnd_1899648 := by
    simpa [prefixWord, tailWord_1899648, baseEnd_1899648] using wordTrace_append hprefix tailTrace_1899648
  have hstable : (prefixWord ++ tailWord_1899648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899648).length < 2 ^ (prefixWord ++ tailWord_1899648).sum := by decide
  have hdescent : baseEnd_1899648 < baseStart_1899648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899680 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_1899680 : Nat := 118140960795 + 1899680 * 2 ^ 59
def prefixEnd_1899680 : Nat := 4983230072969 + 3 ^ 40 * 1899680 * 2
def baseEnd_1899680 : Nat := 650299286488821817975691

theorem tailTrace_1899680 : CollatzResearch.WordTrace tailWord_1899680 prefixEnd_1899680 650299286488821817975691 := by
  unfold tailWord_1899680
  simp only [CollatzResearch.WordTrace]
  refine ⟨34643510878895637179580247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46191347838527516239440329 34643510878895637179580247)
  ·
    refine ⟨51965266318343455769370371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34643510878895637179580247 51965266318343455769370371)
    ·
      refine ⟨77947899477515183654055557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51965266318343455769370371 77947899477515183654055557)
      ·
        refine ⟨14615231152034096935135417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77947899477515183654055557 14615231152034096935135417)
        ·
          refine ⟨10961423364025572701351563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14615231152034096935135417 10961423364025572701351563)
          ·
            refine ⟨16442135046038359052027345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961423364025572701351563 16442135046038359052027345)
            ·
              refine ⟨12331601284528769289020509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16442135046038359052027345 12331601284528769289020509)
              ·
                refine ⟨4624350481698288483382691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12331601284528769289020509 4624350481698288483382691)
                ·
                  refine ⟨6936525722547432725074037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624350481698288483382691 6936525722547432725074037)
                  ·
                    refine ⟨650299286488821817975691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6936525722547432725074037 650299286488821817975691)
                    ·
                      rfl

theorem cell22_1899680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_1899680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899680 prefixEnd_1899680 := by exact prefixLift 1899680
  have htrace : WordTrace (prefixWord ++ tailWord_1899680) baseStart_1899680 baseEnd_1899680 := by
    simpa [prefixWord, tailWord_1899680, baseEnd_1899680] using wordTrace_append hprefix tailTrace_1899680
  have hstable : (prefixWord ++ tailWord_1899680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899680).length < 2 ^ (prefixWord ++ tailWord_1899680).sum := by decide
  have hdescent : baseEnd_1899680 < baseStart_1899680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899684 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_1899684 : Nat := 118140960795 + 1899684 * 2 ^ 59
def prefixEnd_1899684 : Nat := 4983230072969 + 3 ^ 40 * 1899684 * 2
def baseEnd_1899684 : Nat := 650300655770567140875679

theorem tailTrace_1899684 : CollatzResearch.WordTrace tailWord_1899684 prefixEnd_1899684 650300655770567140875679 := by
  unfold tailWord_1899684
  simp only [CollatzResearch.WordTrace]
  refine ⟨34643583824888391521153053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46191445099851188694870737 34643583824888391521153053)
  ·
    refine ⟨12991343934333146820432395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34643583824888391521153053 12991343934333146820432395)
    ·
      refine ⟨19487015901499720230648593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12991343934333146820432395 19487015901499720230648593)
      ·
        refine ⟨14615261926124790172986445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19487015901499720230648593 14615261926124790172986445)
        ·
          refine ⟨5480723222296796314869917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14615261926124790172986445 5480723222296796314869917)
          ·
            refine ⟨2055271208361298618076219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5480723222296796314869917 2055271208361298618076219)
            ·
              refine ⟨3082906812541947927114329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055271208361298618076219 3082906812541947927114329)
              ·
                refine ⟨2312180109406460945335747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3082906812541947927114329 2312180109406460945335747)
                ·
                  refine ⟨3468270164109691418003621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312180109406460945335747 3468270164109691418003621)
                  ·
                    refine ⟨650300655770567140875679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468270164109691418003621 650300655770567140875679)
                    ·
                      rfl

theorem cell22_1899684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_1899684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899684 prefixEnd_1899684 := by exact prefixLift 1899684
  have htrace : WordTrace (prefixWord ++ tailWord_1899684) baseStart_1899684 baseEnd_1899684 := by
    simpa [prefixWord, tailWord_1899684, baseEnd_1899684] using wordTrace_append hprefix tailTrace_1899684
  have hstable : (prefixWord ++ tailWord_1899684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899684).length < 2 ^ (prefixWord ++ tailWord_1899684).sum := by decide
  have hdescent : baseEnd_1899684 < baseStart_1899684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899695 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 2, 4]
def baseStart_1899695 : Nat := 118140960795 + 1899695 * 2 ^ 59
def prefixEnd_1899695 : Nat := 4983230072969 + 3 ^ 40 * 1899695 * 2
def baseEnd_1899695 : Nat := 650304421295366778850645

theorem tailTrace_1899695 : CollatzResearch.WordTrace tailWord_1899695 prefixEnd_1899695 650304421295366778850645 := by
  unfold tailWord_1899695
  simp only [CollatzResearch.WordTrace]
  refine ⟨69287568852736931920956539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46191712568491287947304359 69287568852736931920956539)
  ·
    refine ⟨103931353279105397881434809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69287568852736931920956539 103931353279105397881434809)
    ·
      refine ⟨77948514959329048411076107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103931353279105397881434809 77948514959329048411076107)
      ·
        refine ⟨116922772438993572616614161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77948514959329048411076107 116922772438993572616614161)
        ·
          refine ⟨87692079329245179462460621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116922772438993572616614161 87692079329245179462460621)
          ·
            refine ⟨32884529748466942298422733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87692079329245179462460621 32884529748466942298422733)
            ·
              refine ⟨12331698655675103361908525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32884529748466942298422733 12331698655675103361908525)
              ·
                refine ⟨4624386995878163760715697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12331698655675103361908525 4624386995878163760715697)
                ·
                  refine ⟨3468290246908622820536773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4624386995878163760715697 3468290246908622820536773)
                  ·
                    refine ⟨650304421295366778850645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468290246908622820536773 650304421295366778850645)
                    ·
                      rfl

theorem cell22_1899695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_1899695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899695 prefixEnd_1899695 := by exact prefixLift 1899695
  have htrace : WordTrace (prefixWord ++ tailWord_1899695) baseStart_1899695 baseEnd_1899695 := by
    simpa [prefixWord, tailWord_1899695, baseEnd_1899695] using wordTrace_append hprefix tailTrace_1899695
  have hstable : (prefixWord ++ tailWord_1899695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899695).length < 2 ^ (prefixWord ++ tailWord_1899695).sum := by decide
  have hdescent : baseEnd_1899695 < baseStart_1899695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899697 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_1899697 : Nat := 118140960795 + 1899697 * 2 ^ 59
def prefixEnd_1899697 : Nat := 4983230072969 + 3 ^ 40 * 1899697 * 2
def baseEnd_1899697 : Nat := 650305105936239440300639

theorem tailTrace_1899697 : CollatzResearch.WordTrace tailWord_1899697 prefixEnd_1899697 650305105936239440300639 := by
  unfold tailWord_1899697
  simp only [CollatzResearch.WordTrace]
  refine ⟨69287641798729686262529345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46191761199153124175019563 69287641798729686262529345)
  ·
    refine ⟨51965731349047264696897009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69287641798729686262529345 51965731349047264696897009)
    ·
      refine ⟨38974298511785448522672757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51965731349047264696897009 38974298511785448522672757)
      ·
        refine ⟨3653840485479885799000571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38974298511785448522672757 3653840485479885799000571)
        ·
          refine ⟨5480760728219828698500857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653840485479885799000571 5480760728219828698500857)
          ·
            refine ⟨4110570546164871523875643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5480760728219828698500857 4110570546164871523875643)
            ·
              refine ⟨6165855819247307285813465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110570546164871523875643 6165855819247307285813465)
              ·
                refine ⟨4624391864435480464360099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6165855819247307285813465 4624391864435480464360099)
                ·
                  refine ⟨6936587796653220696540149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624391864435480464360099 6936587796653220696540149)
                  ·
                    refine ⟨650305105936239440300639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6936587796653220696540149 650305105936239440300639)
                    ·
                      rfl

theorem cell22_1899697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_1899697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1899697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1899697 prefixEnd_1899697 := by exact prefixLift 1899697
  have htrace : WordTrace (prefixWord ++ tailWord_1899697) baseStart_1899697 baseEnd_1899697 := by
    simpa [prefixWord, tailWord_1899697, baseEnd_1899697] using wordTrace_append hprefix tailTrace_1899697
  have hstable : (prefixWord ++ tailWord_1899697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899697).length < 2 ^ (prefixWord ++ tailWord_1899697).sum := by decide
  have hdescent : baseEnd_1899697 < baseStart_1899697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
