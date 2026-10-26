import V185TrunkScan22Chunk024

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_222236 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_222236 : Nat := 118140960795 + 222236 * 2 ^ 59
def prefixEnd_222236 : Nat := 4983230072969 + 3 ^ 40 * 222236 * 2
def baseEnd_222236 : Nat := 76075924488465156218641

theorem tailTrace_222236 : CollatzResearch.WordTrace tailWord_222236 prefixEnd_222236 76075924488465156218641 := by
  unfold tailWord_222236
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052806411442200866083281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5403741881922934488111041 4052806411442200866083281)
  ·
    refine ⟨3039604808581650649562461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4052806411442200866083281 3039604808581650649562461)
    ·
      refine ⟨1139851803218118993585923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3039604808581650649562461 1139851803218118993585923)
      ·
        refine ⟨1709777704827178490378885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139851803218118993585923 1709777704827178490378885)
        ·
          refine ⟨320583319655095966946041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1709777704827178490378885 320583319655095966946041)
          ·
            refine ⟨240437489741321975209531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320583319655095966946041 240437489741321975209531)
            ·
              refine ⟨360656234611982962814297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240437489741321975209531 360656234611982962814297)
              ·
                refine ⟨270492175958987222110723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360656234611982962814297 270492175958987222110723)
                ·
                  refine ⟨405738263938480833166085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270492175958987222110723 405738263938480833166085)
                  ·
                    refine ⟨76075924488465156218641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 405738263938480833166085 76075924488465156218641)
                    ·
                      rfl

theorem cell22_222236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_222236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222236 prefixEnd_222236 := by exact prefixLift 222236
  have htrace : WordTrace (prefixWord ++ tailWord_222236) baseStart_222236 baseEnd_222236 := by
    simpa [prefixWord, tailWord_222236, baseEnd_222236] using wordTrace_append hprefix tailTrace_222236
  have hstable : (prefixWord ++ tailWord_222236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222236).length < 2 ^ (prefixWord ++ tailWord_222236).sum := by decide
  have hdescent : baseEnd_222236 < baseStart_222236 := by decide
  rcases family_descends (prefixWord ++ tailWord_222236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222245 : List Nat := [1, 3, 1, 2, 2, 2, 1, 10]
def baseStart_222245 : Nat := 118140960795 + 222245 * 2 ^ 59
def prefixEnd_222245 : Nat := 4983230072969 + 3 ^ 40 * 222245 * 2
def baseEnd_222245 : Nat := 8453222819154681415957

theorem tailTrace_222245 : CollatzResearch.WordTrace tailWord_222245 prefixEnd_222245 8453222819154681415957 := by
  unfold tailWord_222245
  simp only [CollatzResearch.WordTrace]
  refine ⟨8105941079851796269244189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5403960719901197512829459 8105941079851796269244189)
  ·
    refine ⟨3039727904944423600966571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8105941079851796269244189 3039727904944423600966571)
    ·
      refine ⟨4559591857416635401449857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3039727904944423600966571 4559591857416635401449857)
      ·
        refine ⟨3419693893062476551087393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4559591857416635401449857 3419693893062476551087393)
        ·
          refine ⟨2564770419796857413315545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3419693893062476551087393 2564770419796857413315545)
          ·
            refine ⟨1923577814847643059986659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564770419796857413315545 1923577814847643059986659)
            ·
              refine ⟨2885366722271464589979989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923577814847643059986659 2885366722271464589979989)
              ·
                refine ⟨8453222819154681415957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2885366722271464589979989 8453222819154681415957)
                ·
                  rfl

theorem cell22_222245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 10].length) (baseStart_222245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222245 prefixEnd_222245 := by exact prefixLift 222245
  have htrace : WordTrace (prefixWord ++ tailWord_222245) baseStart_222245 baseEnd_222245 := by
    simpa [prefixWord, tailWord_222245, baseEnd_222245] using wordTrace_append hprefix tailTrace_222245
  have hstable : (prefixWord ++ tailWord_222245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222245).length < 2 ^ (prefixWord ++ tailWord_222245).sum := by decide
  have hdescent : baseEnd_222245 < baseStart_222245 := by decide
  rcases family_descends (prefixWord ++ tailWord_222245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222262 : List Nat := [5, 1, 2, 1, 1, 12]
def baseStart_222262 : Nat := 118140960795 + 222262 * 2 ^ 59
def prefixEnd_222262 : Nat := 4983230072969 + 3 ^ 40 * 222262 * 2
def baseEnd_222262 : Nat := 939318824935922902081

theorem tailTrace_222262 : CollatzResearch.WordTrace tailWord_222262 prefixEnd_222262 939318824935922902081 := by
  unfold tailWord_222262
  simp only [CollatzResearch.WordTrace]
  refine ⟨506660070049388010788315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5404374080526805448408693 506660070049388010788315)
  ·
    refine ⟨759990105074082016182473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 506660070049388010788315 759990105074082016182473)
    ·
      refine ⟨569992578805561512136855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 759990105074082016182473 569992578805561512136855)
      ·
        refine ⟨854988868208342268205283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569992578805561512136855 854988868208342268205283)
        ·
          refine ⟨1282483302312513402307925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854988868208342268205283 1282483302312513402307925)
          ·
            refine ⟨939318824935922902081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1282483302312513402307925 939318824935922902081)
            ·
              rfl

theorem cell22_222262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 12].length) (baseStart_222262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222262 prefixEnd_222262 := by exact prefixLift 222262
  have htrace : WordTrace (prefixWord ++ tailWord_222262) baseStart_222262 baseEnd_222262 := by
    simpa [prefixWord, tailWord_222262, baseEnd_222262] using wordTrace_append hprefix tailTrace_222262
  have hstable : (prefixWord ++ tailWord_222262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222262).length < 2 ^ (prefixWord ++ tailWord_222262).sum := by decide
  have hdescent : baseEnd_222262 < baseStart_222262 := by decide
  rcases family_descends (prefixWord ++ tailWord_222262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222275 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 1, 8]
def baseStart_222275 : Nat := 118140960795 + 222275 * 2 ^ 59
def prefixEnd_222275 : Nat := 4983230072969 + 3 ^ 40 * 222275 * 2
def baseEnd_222275 : Nat := 76089274985482054493521

theorem tailTrace_222275 : CollatzResearch.WordTrace tailWord_222275 prefixEnd_222275 76089274985482054493521 := by
  unfold tailWord_222275
  simp only [CollatzResearch.WordTrace]
  refine ⟨8107035269743111392836279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5404690179828740928557519 8107035269743111392836279)
  ·
    refine ⟨12160552904614667089254419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8107035269743111392836279 12160552904614667089254419)
    ·
      refine ⟨18240829356922000633881629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12160552904614667089254419 18240829356922000633881629)
      ·
        refine ⟨6840311008845750237705611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18240829356922000633881629 6840311008845750237705611)
        ·
          refine ⟨10260466513268625356558417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840311008845750237705611 10260466513268625356558417)
          ·
            refine ⟨7695349884951469017418813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10260466513268625356558417 7695349884951469017418813)
            ·
              refine ⟨2885756206856800881532055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7695349884951469017418813 2885756206856800881532055)
              ·
                refine ⟨4328634310285201322298083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885756206856800881532055 4328634310285201322298083)
                ·
                  refine ⟨6492951465427801983447125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4328634310285201322298083 6492951465427801983447125)
                  ·
                    refine ⟨76089274985482054493521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6492951465427801983447125 76089274985482054493521)
                    ·
                      rfl

theorem cell22_222275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_222275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222275 prefixEnd_222275 := by exact prefixLift 222275
  have htrace : WordTrace (prefixWord ++ tailWord_222275) baseStart_222275 baseEnd_222275 := by
    simpa [prefixWord, tailWord_222275, baseEnd_222275] using wordTrace_append hprefix tailTrace_222275
  have hstable : (prefixWord ++ tailWord_222275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222275).length < 2 ^ (prefixWord ++ tailWord_222275).sum := by decide
  have hdescent : baseEnd_222275 < baseStart_222275 := by decide
  rcases family_descends (prefixWord ++ tailWord_222275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222311 : List Nat := [1, 1, 5, 1, 1, 3, 1, 5, 1, 3]
def baseStart_222311 : Nat := 118140960795 + 222311 * 2 ^ 59
def prefixEnd_222311 : Nat := 4983230072969 + 3 ^ 40 * 222311 * 2
def baseEnd_222311 : Nat := 76101598521189960593411

theorem tailTrace_222311 : CollatzResearch.WordTrace tailWord_222311 prefixEnd_222311 76101598521189960593411 := by
  unfold tailWord_222311
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108348297612689541146787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5405565531741793027431191 8108348297612689541146787)
  ·
    refine ⟨12162522446419034311720181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8108348297612689541146787 12162522446419034311720181)
    ·
      refine ⟨1140236479351784466723767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12162522446419034311720181 1140236479351784466723767)
      ·
        refine ⟨1710354719027676700085651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1140236479351784466723767 1710354719027676700085651)
        ·
          refine ⟨2565532078541515050128477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710354719027676700085651 2565532078541515050128477)
          ·
            refine ⟨962074529453068143798179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2565532078541515050128477 962074529453068143798179)
            ·
              refine ⟨1443111794179602215697269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962074529453068143798179 1443111794179602215697269)
              ·
                refine ⟨135291730704337707721619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1443111794179602215697269 135291730704337707721619)
                ·
                  refine ⟨202937596056506561582429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135291730704337707721619 202937596056506561582429)
                  ·
                    refine ⟨76101598521189960593411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202937596056506561582429 76101598521189960593411)
                    ·
                      rfl

theorem cell22_222311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_222311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222311 prefixEnd_222311 := by exact prefixLift 222311
  have htrace : WordTrace (prefixWord ++ tailWord_222311) baseStart_222311 baseEnd_222311 := by
    simpa [prefixWord, tailWord_222311, baseEnd_222311] using wordTrace_append hprefix tailTrace_222311
  have hstable : (prefixWord ++ tailWord_222311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222311).length < 2 ^ (prefixWord ++ tailWord_222311).sum := by decide
  have hdescent : baseEnd_222311 < baseStart_222311 := by decide
  rcases family_descends (prefixWord ++ tailWord_222311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222322 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_222322 : Nat := 118140960795 + 222322 * 2 ^ 59
def prefixEnd_222322 : Nat := 4983230072969 + 3 ^ 40 * 222322 * 2
def baseEnd_222322 : Nat := 76105364045989598568377

theorem tailTrace_222322 : CollatzResearch.WordTrace tailWord_222322 prefixEnd_222322 76105364045989598568377 := by
  unfold tailWord_222322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2027187375143209604949305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5405833000381892279864813 2027187375143209604949305)
  ·
    refine ⟨1520390531357407203711979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2027187375143209604949305 1520390531357407203711979)
    ·
      refine ⟨2280585797036110805567969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520390531357407203711979 2280585797036110805567969)
      ·
        refine ⟨1710439347777083104175977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2280585797036110805567969 1710439347777083104175977)
        ·
          refine ⟨1282829510832812328131983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1710439347777083104175977 1282829510832812328131983)
          ·
            refine ⟨1924244266249218492197975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282829510832812328131983 1924244266249218492197975)
            ·
              refine ⟨2886366399373827738296963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924244266249218492197975 2886366399373827738296963)
              ·
                refine ⟨4329549599060741607445445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886366399373827738296963 4329549599060741607445445)
                ·
                  refine ⟨811790549823889051396021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4329549599060741607445445 811790549823889051396021)
                  ·
                    refine ⟨76105364045989598568377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 811790549823889051396021 76105364045989598568377)
                    ·
                      rfl

theorem cell22_222322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_222322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222322 prefixEnd_222322 := by exact prefixLift 222322
  have htrace : WordTrace (prefixWord ++ tailWord_222322) baseStart_222322 baseEnd_222322 := by
    simpa [prefixWord, tailWord_222322, baseEnd_222322] using wordTrace_append hprefix tailTrace_222322
  have hstable : (prefixWord ++ tailWord_222322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222322).length < 2 ^ (prefixWord ++ tailWord_222322).sum := by decide
  have hdescent : baseEnd_222322 < baseStart_222322 := by decide
  rcases family_descends (prefixWord ++ tailWord_222322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222341 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 5]
def baseStart_222341 : Nat := 118140960795 + 222341 * 2 ^ 59
def prefixEnd_222341 : Nat := 4983230072969 + 3 ^ 40 * 222341 * 2
def baseEnd_222341 : Nat := 25370622711426627447773

theorem tailTrace_222341 : CollatzResearch.WordTrace tailWord_222341 prefixEnd_222341 25370622711426627447773 := by
  unfold tailWord_222341
  simp only [CollatzResearch.WordTrace]
  refine ⟨8109442487504004664738877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5406294991669336443159251 8109442487504004664738877)
  ·
    refine ⟨3041040932814001749277079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8109442487504004664738877 3041040932814001749277079)
    ·
      refine ⟨4561561399221002623915619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3041040932814001749277079 4561561399221002623915619)
      ·
        refine ⟨6842342098831503935873429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561561399221002623915619 6842342098831503935873429)
        ·
          refine ⟨320734785882726746994067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6842342098831503935873429 320734785882726746994067)
          ·
            refine ⟨481102178824090120491101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320734785882726746994067 481102178824090120491101)
            ·
              refine ⟨180413317059033795184163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481102178824090120491101 180413317059033795184163)
              ·
                refine ⟨270619975588550692776245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180413317059033795184163 270619975588550692776245)
                ·
                  refine ⟨25370622711426627447773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270619975588550692776245 25370622711426627447773)
                  ·
                    rfl

theorem cell22_222341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_222341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222341 prefixEnd_222341 := by exact prefixLift 222341
  have htrace : WordTrace (prefixWord ++ tailWord_222341) baseStart_222341 baseEnd_222341 := by
    simpa [prefixWord, tailWord_222341, baseEnd_222341] using wordTrace_append hprefix tailTrace_222341
  have hstable : (prefixWord ++ tailWord_222341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222341).length < 2 ^ (prefixWord ++ tailWord_222341).sum := by decide
  have hdescent : baseEnd_222341 < baseStart_222341 := by decide
  rcases family_descends (prefixWord ++ tailWord_222341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222397 : List Nat := [1, 4, 1, 2, 1, 1, 3, 9]
def baseStart_222397 : Nat := 118140960795 + 222397 * 2 ^ 59
def prefixEnd_222397 : Nat := 4983230072969 + 3 ^ 40 * 222397 * 2
def baseEnd_222397 : Nat := 8459004230968266993683

theorem tailTrace_222397 : CollatzResearch.WordTrace tailWord_222397 prefixEnd_222397 8459004230968266993683 := by
  unfold tailWord_222397
  simp only [CollatzResearch.WordTrace]
  refine ⟨8111484975301126228777445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5407656650200750819184963 8111484975301126228777445)
  ·
    refine ⟨1520903432868961167895771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8111484975301126228777445 1520903432868961167895771)
    ·
      refine ⟨2281355149303441751843657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520903432868961167895771 2281355149303441751843657)
      ·
        refine ⟨1711016361977581313882743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2281355149303441751843657 1711016361977581313882743)
        ·
          refine ⟨2566524542966371970824115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711016361977581313882743 2566524542966371970824115)
          ·
            refine ⟨3849786814449557956236173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566524542966371970824115 3849786814449557956236173)
            ·
              refine ⟨1443670055418584233588565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3849786814449557956236173 1443670055418584233588565)
              ·
                refine ⟨8459004230968266993683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1443670055418584233588565 8459004230968266993683)
                ·
                  rfl

theorem cell22_222397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 9].length) (baseStart_222397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222397 prefixEnd_222397 := by exact prefixLift 222397
  have htrace : WordTrace (prefixWord ++ tailWord_222397) baseStart_222397 baseEnd_222397 := by
    simpa [prefixWord, tailWord_222397, baseEnd_222397] using wordTrace_append hprefix tailTrace_222397
  have hstable : (prefixWord ++ tailWord_222397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222397).length < 2 ^ (prefixWord ++ tailWord_222397).sum := by decide
  have hdescent : baseEnd_222397 < baseStart_222397 := by decide
  rcases family_descends (prefixWord ++ tailWord_222397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222493 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 5]
def baseStart_222493 : Nat := 118140960795 + 222493 * 2 ^ 59
def prefixEnd_222493 : Nat := 4983230072969 + 3 ^ 40 * 222493 * 2
def baseEnd_222493 : Nat := 25387966946867384180951

theorem tailTrace_222493 : CollatzResearch.WordTrace tailWord_222493 prefixEnd_222493 25387966946867384180951 := by
  unfold tailWord_222493
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114986382953334624272133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5409990921968889749514755 8114986382953334624272133)
  ·
    refine ⟨1521559946803750242051025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8114986382953334624272133 1521559946803750242051025)
    ·
      refine ⟨1141169960102812681538269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1521559946803750242051025 1141169960102812681538269)
      ·
        refine ⟨427938735038554755576851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1141169960102812681538269 427938735038554755576851)
        ·
          refine ⟨641908102557832133365277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427938735038554755576851 641908102557832133365277)
          ·
            refine ⟨240715538459187050011979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 641908102557832133365277 240715538459187050011979)
            ·
              refine ⟨361073307688780575017969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240715538459187050011979 361073307688780575017969)
              ·
                refine ⟨270804980766585431263477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361073307688780575017969 270804980766585431263477)
                ·
                  refine ⟨25387966946867384180951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270804980766585431263477 25387966946867384180951)
                  ·
                    rfl

theorem cell22_222493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_222493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222493 prefixEnd_222493 := by exact prefixLift 222493
  have htrace : WordTrace (prefixWord ++ tailWord_222493) baseStart_222493 baseEnd_222493 := by
    simpa [prefixWord, tailWord_222493, baseEnd_222493] using wordTrace_append hprefix tailTrace_222493
  have hstable : (prefixWord ++ tailWord_222493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222493).length < 2 ^ (prefixWord ++ tailWord_222493).sum := by decide
  have hdescent : baseEnd_222493 < baseStart_222493 := by decide
  rcases family_descends (prefixWord ++ tailWord_222493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222549 : List Nat := [1, 3, 2, 2, 3, 1, 10]
def baseStart_222549 : Nat := 118140960795 + 222549 * 2 ^ 59
def prefixEnd_222549 : Nat := 4983230072969 + 3 ^ 40 * 222549 * 2
def baseEnd_222549 : Nat := 2821595214260617523803

theorem tailTrace_222549 : CollatzResearch.WordTrace tailWord_222549 prefixEnd_222549 2821595214260617523803 := by
  unfold tailWord_222549
  simp only [CollatzResearch.WordTrace]
  refine ⟨8117028870750456188310701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5411352580500304125540467 8117028870750456188310701)
  ·
    refine ⟨3043885826531421070616513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8117028870750456188310701 3043885826531421070616513)
    ·
      refine ⟨2282914369898565802962385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3043885826531421070616513 2282914369898565802962385)
      ·
        refine ⟨1712185777423924352221789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2282914369898565802962385 1712185777423924352221789)
        ·
          refine ⟨642069666533971632083171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1712185777423924352221789 642069666533971632083171)
          ·
            refine ⟨963104499800957448124757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642069666533971632083171 963104499800957448124757)
            ·
              refine ⟨2821595214260617523803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 963104499800957448124757 2821595214260617523803)
              ·
                rfl

theorem cell22_222549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 10].length) (baseStart_222549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222549 prefixEnd_222549 := by exact prefixLift 222549
  have htrace : WordTrace (prefixWord ++ tailWord_222549) baseStart_222549 baseEnd_222549 := by
    simpa [prefixWord, tailWord_222549, baseEnd_222549] using wordTrace_append hprefix tailTrace_222549
  have hstable : (prefixWord ++ tailWord_222549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222549).length < 2 ^ (prefixWord ++ tailWord_222549).sum := by decide
  have hdescent : baseEnd_222549 < baseStart_222549 := by decide
  rcases family_descends (prefixWord ++ tailWord_222549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222551 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 2, 4]
def baseStart_222551 : Nat := 118140960795 + 222551 * 2 ^ 59
def prefixEnd_222551 : Nat := 4983230072969 + 3 ^ 40 * 222551 * 2
def baseEnd_222551 : Nat := 76183755425909334592675

theorem tailTrace_222551 : CollatzResearch.WordTrace tailWord_222551 prefixEnd_222551 76183755425909334592675 := by
  unfold tailWord_222551
  simp only [CollatzResearch.WordTrace]
  refine ⟨8117101816743210529883507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5411401211162140353255671 8117101816743210529883507)
  ·
    refine ⟨12175652725114815794825261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8117101816743210529883507 12175652725114815794825261)
    ·
      refine ⟨4565869771918055923059473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12175652725114815794825261 4565869771918055923059473)
      ·
        refine ⟨3424402328938541942294605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4565869771918055923059473 3424402328938541942294605)
        ·
          refine ⟨1284150873351953228360477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3424402328938541942294605 1284150873351953228360477)
          ·
            refine ⟨481556577506982460635179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1284150873351953228360477 481556577506982460635179)
            ·
              refine ⟨722334866260473690952769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481556577506982460635179 722334866260473690952769)
              ·
                refine ⟨541751149695355268214577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722334866260473690952769 541751149695355268214577)
                ·
                  refine ⟨406313362271516451160933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541751149695355268214577 406313362271516451160933)
                  ·
                    refine ⟨76183755425909334592675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406313362271516451160933 76183755425909334592675)
                    ·
                      rfl

theorem cell22_222551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_222551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222551 prefixEnd_222551 := by exact prefixLift 222551
  have htrace : WordTrace (prefixWord ++ tailWord_222551) baseStart_222551 baseEnd_222551 := by
    simpa [prefixWord, tailWord_222551, baseEnd_222551] using wordTrace_append hprefix tailTrace_222551
  have hstable : (prefixWord ++ tailWord_222551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222551).length < 2 ^ (prefixWord ++ tailWord_222551).sum := by decide
  have hdescent : baseEnd_222551 < baseStart_222551 := by decide
  rcases family_descends (prefixWord ++ tailWord_222551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222570 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_222570 : Nat := 118140960795 + 222570 * 2 ^ 59
def prefixEnd_222570 : Nat := 4983230072969 + 3 ^ 40 * 222570 * 2
def baseEnd_222570 : Nat := 76190259514199618367617

theorem tailTrace_222570 : CollatzResearch.WordTrace tailWord_222570 prefixEnd_222570 76190259514199618367617 := by
  unfold tailWord_222570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029448700918594193706291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5411863202449584516550109 2029448700918594193706291)
  ·
    refine ⟨3044173051377891290559437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2029448700918594193706291 3044173051377891290559437)
    ·
      refine ⟨1141564894266709233959789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3044173051377891290559437 1141564894266709233959789)
      ·
        refine ⟨428086835350015962734921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1141564894266709233959789 428086835350015962734921)
        ·
          refine ⟨321065126512511972051191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428086835350015962734921 321065126512511972051191)
          ·
            refine ⟨481597689768767958076787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321065126512511972051191 481597689768767958076787)
            ·
              refine ⟨722396534653151937115181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481597689768767958076787 722396534653151937115181)
              ·
                refine ⟨270898700494931976418193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 722396534653151937115181 270898700494931976418193)
                ·
                  refine ⟨203174025371198982313645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270898700494931976418193 203174025371198982313645)
                  ·
                    refine ⟨76190259514199618367617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203174025371198982313645 76190259514199618367617)
                    ·
                      rfl

theorem cell22_222570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_222570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222570 prefixEnd_222570 := by exact prefixLift 222570
  have htrace : WordTrace (prefixWord ++ tailWord_222570) baseStart_222570 baseEnd_222570 := by
    simpa [prefixWord, tailWord_222570, baseEnd_222570] using wordTrace_append hprefix tailTrace_222570
  have hstable : (prefixWord ++ tailWord_222570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222570).length < 2 ^ (prefixWord ++ tailWord_222570).sum := by decide
  have hdescent : baseEnd_222570 < baseStart_222570 := by decide
  rcases family_descends (prefixWord ++ tailWord_222570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222609 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_222609 : Nat := 118140960795 + 222609 * 2 ^ 59
def prefixEnd_222609 : Nat := 4983230072969 + 3 ^ 40 * 222609 * 2
def baseEnd_222609 : Nat := 76203610011216516642497

theorem tailTrace_222609 : CollatzResearch.WordTrace tailWord_222609 prefixEnd_222609 76203610011216516642497 := by
  unfold tailWord_222609
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119217250533086435494881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5412811500355390956996587 8119217250533086435494881)
  ·
    refine ⟨6089412937899814826621161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8119217250533086435494881 6089412937899814826621161)
    ·
      refine ⟨4567059703424861119965871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6089412937899814826621161 4567059703424861119965871)
      ·
        refine ⟨6850589555137291679948807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4567059703424861119965871 6850589555137291679948807)
        ·
          refine ⟨10275884332705937519923211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6850589555137291679948807 10275884332705937519923211)
          ·
            refine ⟨15413826499058906279884817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10275884332705937519923211 15413826499058906279884817)
            ·
              refine ⟨11560369874294179709913613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15413826499058906279884817 11560369874294179709913613)
              ·
                refine ⟨4335138702860317391217605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11560369874294179709913613 4335138702860317391217605)
                ·
                  refine ⟨812838506786309510853301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4335138702860317391217605 812838506786309510853301)
                  ·
                    refine ⟨76203610011216516642497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 812838506786309510853301 76203610011216516642497)
                    ·
                      rfl

theorem cell22_222609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_222609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222609 prefixEnd_222609 := by exact prefixLift 222609
  have htrace : WordTrace (prefixWord ++ tailWord_222609) baseStart_222609 baseEnd_222609 := by
    simpa [prefixWord, tailWord_222609, baseEnd_222609] using wordTrace_append hprefix tailTrace_222609
  have hstable : (prefixWord ++ tailWord_222609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222609).length < 2 ^ (prefixWord ++ tailWord_222609).sum := by decide
  have hdescent : baseEnd_222609 < baseStart_222609 := by decide
  rcases family_descends (prefixWord ++ tailWord_222609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222626 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_222626 : Nat := 118140960795 + 222626 * 2 ^ 59
def prefixEnd_222626 : Nat := 4983230072969 + 3 ^ 40 * 222626 * 2
def baseEnd_222626 : Nat := 76209429458634138967445

theorem tailTrace_222626 : CollatzResearch.WordTrace tailWord_222626 prefixEnd_222626 76209429458634138967445 := by
  unfold tailWord_222626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029959322867874584715933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5413224860980998892575821 2029959322867874584715933)
  ·
    refine ⟨761234746075452969268475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2029959322867874584715933 761234746075452969268475)
    ·
      refine ⟨1141852119113179453902713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 761234746075452969268475 1141852119113179453902713)
      ·
        refine ⟨856389089334884590427035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1141852119113179453902713 856389089334884590427035)
        ·
          refine ⟨1284583634002326885640553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856389089334884590427035 1284583634002326885640553)
          ·
            refine ⟨963437725501745164230415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284583634002326885640553 963437725501745164230415)
            ·
              refine ⟨1445156588252617746345623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963437725501745164230415 1445156588252617746345623)
              ·
                refine ⟨2167734882378926619518435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445156588252617746345623 2167734882378926619518435)
                ·
                  refine ⟨3251602323568389929277653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167734882378926619518435 3251602323568389929277653)
                  ·
                    refine ⟨76209429458634138967445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3251602323568389929277653 76209429458634138967445)
                    ·
                      rfl

theorem cell22_222626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_222626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222626 prefixEnd_222626 := by exact prefixLift 222626
  have htrace : WordTrace (prefixWord ++ tailWord_222626) baseStart_222626 baseEnd_222626 := by
    simpa [prefixWord, tailWord_222626, baseEnd_222626] using wordTrace_append hprefix tailTrace_222626
  have hstable : (prefixWord ++ tailWord_222626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222626).length < 2 ^ (prefixWord ++ tailWord_222626).sum := by decide
  have hdescent : baseEnd_222626 < baseStart_222626 := by decide
  rcases family_descends (prefixWord ++ tailWord_222626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222641 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_222641 : Nat := 118140960795 + 222641 * 2 ^ 59
def prefixEnd_222641 : Nat := 4983230072969 + 3 ^ 40 * 222641 * 2
def baseEnd_222641 : Nat := 76214564265179099842399

theorem tailTrace_222641 : CollatzResearch.WordTrace tailWord_222641 prefixEnd_222641 76214564265179099842399 := by
  unfold tailWord_222641
  simp only [CollatzResearch.WordTrace]
  refine ⟨8120384386417155900659777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5413589590944770600439851 8120384386417155900659777)
  ·
    refine ⟨6090288289812866925494833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8120384386417155900659777 6090288289812866925494833)
    ·
      refine ⟨4567716217359650194121125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6090288289812866925494833 4567716217359650194121125)
      ·
        refine ⟨856446790754934411397711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4567716217359650194121125 856446790754934411397711)
        ·
          refine ⟨1284670186132401617096567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856446790754934411397711 1284670186132401617096567)
          ·
            refine ⟨1927005279198602425644851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284670186132401617096567 1927005279198602425644851)
            ·
              refine ⟨2890507918797903638467277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927005279198602425644851 2890507918797903638467277)
              ·
                refine ⟨1083940469549213864425229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2890507918797903638467277 1083940469549213864425229)
                ·
                  refine ⟨406477676080955199159461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1083940469549213864425229 406477676080955199159461)
                  ·
                    refine ⟨76214564265179099842399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406477676080955199159461 76214564265179099842399)
                    ·
                      rfl

theorem cell22_222641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_222641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222641 prefixEnd_222641 := by exact prefixLift 222641
  have htrace : WordTrace (prefixWord ++ tailWord_222641) baseStart_222641 baseEnd_222641 := by
    simpa [prefixWord, tailWord_222641, baseEnd_222641] using wordTrace_append hprefix tailTrace_222641
  have hstable : (prefixWord ++ tailWord_222641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222641).length < 2 ^ (prefixWord ++ tailWord_222641).sum := by decide
  have hdescent : baseEnd_222641 < baseStart_222641 := by decide
  rcases family_descends (prefixWord ++ tailWord_222641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222780 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 5]
def baseStart_222780 : Nat := 118140960795 + 222780 * 2 ^ 59
def prefixEnd_222780 : Nat := 4983230072969 + 3 ^ 40 * 222780 * 2
def baseEnd_222780 : Nat := 25420715601943023538991

theorem tailTrace_222780 : CollatzResearch.WordTrace tailWord_222780 prefixEnd_222780 25420715601943023538991 := by
  unfold tailWord_222780
  simp only [CollatzResearch.WordTrace]
  refine ⟨4062727066456791319984897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5416969421942388426646529 4062727066456791319984897)
  ·
    refine ⟨3047045299842593489988673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4062727066456791319984897 3047045299842593489988673)
    ·
      refine ⟨2285283974881945117491505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3047045299842593489988673 2285283974881945117491505)
      ·
        refine ⟨1713962981161458838118629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2285283974881945117491505 1713962981161458838118629)
        ·
          refine ⟨321368058967773532147243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1713962981161458838118629 321368058967773532147243)
          ·
            refine ⟨482052088451660298220865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321368058967773532147243 482052088451660298220865)
            ·
              refine ⟨361539066338745223665649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482052088451660298220865 361539066338745223665649)
              ·
                refine ⟨271154299754058917749237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361539066338745223665649 271154299754058917749237)
                ·
                  refine ⟨25420715601943023538991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271154299754058917749237 25420715601943023538991)
                  ·
                    rfl

theorem cell22_222780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_222780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222780 prefixEnd_222780 := by exact prefixLift 222780
  have htrace : WordTrace (prefixWord ++ tailWord_222780) baseStart_222780 baseEnd_222780 := by
    simpa [prefixWord, tailWord_222780, baseEnd_222780] using wordTrace_append hprefix tailTrace_222780
  have hstable : (prefixWord ++ tailWord_222780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222780).length < 2 ^ (prefixWord ++ tailWord_222780).sum := by decide
  have hdescent : baseEnd_222780 < baseStart_222780 := by decide
  rcases family_descends (prefixWord ++ tailWord_222780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222823 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 1, 5]
def baseStart_222823 : Nat := 118140960795 + 222823 * 2 ^ 59
def prefixEnd_222823 : Nat := 4983230072969 + 3 ^ 40 * 222823 * 2
def baseEnd_222823 : Nat := 76276866584591291791841

theorem tailTrace_222823 : CollatzResearch.WordTrace tailWord_222823 prefixEnd_222823 76276866584591291791841 := by
  unfold tailWord_222823
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127022471757800983785123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5418014981171867322523415 8127022471757800983785123)
  ·
    refine ⟨12190533707636701475677685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8127022471757800983785123 12190533707636701475677685)
    ·
      refine ⟨1142862535090940763344783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12190533707636701475677685 1142862535090940763344783)
      ·
        refine ⟨1714293802636411145017175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1142862535090940763344783 1714293802636411145017175)
        ·
          refine ⟨2571440703954616717525763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714293802636411145017175 2571440703954616717525763)
          ·
            refine ⟨3857161055931925076288645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571440703954616717525763 3857161055931925076288645)
            ·
              refine ⟨723217697987235951804121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3857161055931925076288645 723217697987235951804121)
              ·
                refine ⟨542413273490426963853091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723217697987235951804121 542413273490426963853091)
                ·
                  refine ⟨813619910235640445779637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542413273490426963853091 813619910235640445779637)
                  ·
                    refine ⟨76276866584591291791841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 813619910235640445779637 76276866584591291791841)
                    ·
                      rfl

theorem cell22_222823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_222823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222823 prefixEnd_222823 := by exact prefixLift 222823
  have htrace : WordTrace (prefixWord ++ tailWord_222823) baseStart_222823 baseEnd_222823 := by
    simpa [prefixWord, tailWord_222823, baseEnd_222823] using wordTrace_append hprefix tailTrace_222823
  have hstable : (prefixWord ++ tailWord_222823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222823).length < 2 ^ (prefixWord ++ tailWord_222823).sum := by decide
  have hdescent : baseEnd_222823 < baseStart_222823 := by decide
  rcases family_descends (prefixWord ++ tailWord_222823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222898 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_222898 : Nat := 118140960795 + 222898 * 2 ^ 59
def prefixEnd_222898 : Nat := 4983230072969 + 3 ^ 40 * 222898 * 2
def baseEnd_222898 : Nat := 25434180205772032055537

theorem tailTrace_222898 : CollatzResearch.WordTrace tailWord_222898 prefixEnd_222898 25434180205772032055537 := by
  unfold tailWord_222898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032439486621522198191337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5419838630990725861843565 2032439486621522198191337)
  ·
    refine ⟨1524329614966141648643503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2032439486621522198191337 1524329614966141648643503)
    ·
      refine ⟨2286494422449212472965255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1524329614966141648643503 2286494422449212472965255)
      ·
        refine ⟨3429741633673818709447883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286494422449212472965255 3429741633673818709447883)
        ·
          refine ⟨5144612450510728064171825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429741633673818709447883 5144612450510728064171825)
          ·
            refine ⟨3858459337883046048128869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5144612450510728064171825 3858459337883046048128869)
            ·
              refine ⟨723461125853071134024163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3858459337883046048128869 723461125853071134024163)
              ·
                refine ⟨1085191688779606701036245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723461125853071134024163 1085191688779606701036245)
                ·
                  refine ⟨25434180205772032055537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1085191688779606701036245 25434180205772032055537)
                  ·
                    rfl

theorem cell22_222898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_222898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222898 prefixEnd_222898 := by exact prefixLift 222898
  have htrace : WordTrace (prefixWord ++ tailWord_222898) baseStart_222898 baseEnd_222898 := by
    simpa [prefixWord, tailWord_222898, baseEnd_222898] using wordTrace_append hprefix tailTrace_222898
  have hstable : (prefixWord ++ tailWord_222898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222898).length < 2 ^ (prefixWord ++ tailWord_222898).sum := by decide
  have hdescent : baseEnd_222898 < baseStart_222898 := by decide
  rcases family_descends (prefixWord ++ tailWord_222898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222964 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_222964 : Nat := 118140960795 + 222964 * 2 ^ 59
def prefixEnd_222964 : Nat := 4983230072969 + 3 ^ 40 * 222964 * 2
def baseEnd_222964 : Nat := 76325133766113924016409

theorem tailTrace_222964 : CollatzResearch.WordTrace tailWord_222964 prefixEnd_222964 76325133766113924016409 := by
  unfold tailWord_222964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4066082582123491032333973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5421443442831321376445297 4066082582123491032333973)
  ·
    refine ⟨190597621037038642140655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4066082582123491032333973 190597621037038642140655)
    ·
      refine ⟨285896431555557963210983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190597621037038642140655 285896431555557963210983)
      ·
        refine ⟨428844647333336944816475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285896431555557963210983 428844647333336944816475)
        ·
          refine ⟨643266971000005417224713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428844647333336944816475 643266971000005417224713)
          ·
            refine ⟨482450228250004062918535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643266971000005417224713 482450228250004062918535)
            ·
              refine ⟨723675342375006094377803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482450228250004062918535 723675342375006094377803)
              ·
                refine ⟨1085513013562509141566705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723675342375006094377803 1085513013562509141566705)
                ·
                  refine ⟨814134760171881856175029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1085513013562509141566705 814134760171881856175029)
                  ·
                    refine ⟨76325133766113924016409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 814134760171881856175029 76325133766113924016409)
                    ·
                      rfl

theorem cell22_222964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_222964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222964 prefixEnd_222964 := by exact prefixLift 222964
  have htrace : WordTrace (prefixWord ++ tailWord_222964) baseStart_222964 baseEnd_222964 := by
    simpa [prefixWord, tailWord_222964, baseEnd_222964] using wordTrace_append hprefix tailTrace_222964
  have hstable : (prefixWord ++ tailWord_222964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222964).length < 2 ^ (prefixWord ++ tailWord_222964).sum := by decide
  have hdescent : baseEnd_222964 < baseStart_222964 := by decide
  rcases family_descends (prefixWord ++ tailWord_222964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222988 : List Nat := [2, 2, 1, 2, 2, 1, 2, 10]
def baseStart_222988 : Nat := 118140960795 + 222988 * 2 ^ 59
def prefixEnd_222988 : Nat := 4983230072969 + 3 ^ 40 * 222988 * 2
def baseEnd_222988 : Nat := 8481483272953984601815

theorem tailTrace_222988 : CollatzResearch.WordTrace tailWord_222988 prefixEnd_222988 8481483272953984601815 := by
  unfold tailWord_222988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4066520258080017081770809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5422027010773356109027745 4066520258080017081770809)
  ·
    refine ⟨3049890193560012811328107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4066520258080017081770809 3049890193560012811328107)
    ·
      refine ⟨4574835290340019216992161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3049890193560012811328107 4574835290340019216992161)
      ·
        refine ⟨3431126467755014412744121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4574835290340019216992161 3431126467755014412744121)
        ·
          refine ⟨2573344850816260809558091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3431126467755014412744121 2573344850816260809558091)
          ·
            refine ⟨3860017276224391214337137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573344850816260809558091 3860017276224391214337137)
            ·
              refine ⟨2895012957168293410752853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3860017276224391214337137 2895012957168293410752853)
              ·
                refine ⟨8481483272953984601815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2895012957168293410752853 8481483272953984601815)
                ·
                  rfl

theorem cell22_222988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 10].length) (baseStart_222988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222988 prefixEnd_222988 := by exact prefixLift 222988
  have htrace : WordTrace (prefixWord ++ tailWord_222988) baseStart_222988 baseEnd_222988 := by
    simpa [prefixWord, tailWord_222988, baseEnd_222988] using wordTrace_append hprefix tailTrace_222988
  have hstable : (prefixWord ++ tailWord_222988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222988).length < 2 ^ (prefixWord ++ tailWord_222988).sum := by decide
  have hdescent : baseEnd_222988 < baseStart_222988 := by decide
  rcases family_descends (prefixWord ++ tailWord_222988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222994 : List Nat := [3, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_222994 : Nat := 118140960795 + 222994 * 2 ^ 59
def prefixEnd_222994 : Nat := 4983230072969 + 3 ^ 40 * 222994 * 2
def baseEnd_222994 : Nat := 25445134459734615255439

theorem tailTrace_222994 : CollatzResearch.WordTrace tailWord_222994 prefixEnd_222994 25445134459734615255439 := by
  unfold tailWord_222994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2033314838534574297065009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5422172902758864792173357 2033314838534574297065009)
  ·
    refine ⟨1524986128900930722798757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2033314838534574297065009 1524986128900930722798757)
    ·
      refine ⟨285934899168924510524767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1524986128900930722798757 285934899168924510524767)
      ·
        refine ⟨428902348753386765787151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285934899168924510524767 428902348753386765787151)
        ·
          refine ⟨643353523130080148680727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428902348753386765787151 643353523130080148680727)
          ·
            refine ⟨965030284695120223021091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643353523130080148680727 965030284695120223021091)
            ·
              refine ⟨1447545427042680334531637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965030284695120223021091 1447545427042680334531637)
              ·
                refine ⟨135707383785251281362341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1447545427042680334531637 135707383785251281362341)
                ·
                  refine ⟨25445134459734615255439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135707383785251281362341 25445134459734615255439)
                  ·
                    rfl

theorem cell22_222994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_222994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_222994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_222994 prefixEnd_222994 := by exact prefixLift 222994
  have htrace : WordTrace (prefixWord ++ tailWord_222994) baseStart_222994 baseEnd_222994 := by
    simpa [prefixWord, tailWord_222994, baseEnd_222994] using wordTrace_append hprefix tailTrace_222994
  have hstable : (prefixWord ++ tailWord_222994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222994).length < 2 ^ (prefixWord ++ tailWord_222994).sum := by decide
  have hdescent : baseEnd_222994 < baseStart_222994 := by decide
  rcases family_descends (prefixWord ++ tailWord_222994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223009 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 2, 3]
def baseStart_223009 : Nat := 118140960795 + 223009 * 2 ^ 59
def prefixEnd_223009 : Nat := 4983230072969 + 3 ^ 40 * 223009 * 2
def baseEnd_223009 : Nat := 76340538185748806641271

theorem tailTrace_223009 : CollatzResearch.WordTrace tailWord_223009 prefixEnd_223009 76340538185748806641271 := by
  unfold tailWord_223009
  simp only [CollatzResearch.WordTrace]
  refine ⟨8133806449083954750056081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5422537632722636500037387 8133806449083954750056081)
  ·
    refine ⟨6100354836812966062542061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8133806449083954750056081 6100354836812966062542061)
    ·
      refine ⟨2287633063804862273453273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6100354836812966062542061 2287633063804862273453273)
      ·
        refine ⟨1715724797853646705089955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2287633063804862273453273 1715724797853646705089955)
        ·
          refine ⟨2573587196780470057634933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715724797853646705089955 2573587196780470057634933)
          ·
            refine ⟨241273799698169067903275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2573587196780470057634933 241273799698169067903275)
            ·
              refine ⟨361910699547253601854913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241273799698169067903275 361910699547253601854913)
              ·
                refine ⟨271433024660440201391185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361910699547253601854913 271433024660440201391185)
                ·
                  refine ⟨203574768495330151043389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271433024660440201391185 203574768495330151043389)
                  ·
                    refine ⟨76340538185748806641271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203574768495330151043389 76340538185748806641271)
                    ·
                      rfl

theorem cell22_223009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_223009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223009 prefixEnd_223009 := by exact prefixLift 223009
  have htrace : WordTrace (prefixWord ++ tailWord_223009) baseStart_223009 baseEnd_223009 := by
    simpa [prefixWord, tailWord_223009, baseEnd_223009] using wordTrace_append hprefix tailTrace_223009
  have hstable : (prefixWord ++ tailWord_223009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223009).length < 2 ^ (prefixWord ++ tailWord_223009).sum := by decide
  have hdescent : baseEnd_223009 < baseStart_223009 := by decide
  rcases family_descends (prefixWord ++ tailWord_223009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223039 : List Nat := [1, 1, 2, 2, 7, 1, 2, 6]
def baseStart_223039 : Nat := 118140960795 + 223039 * 2 ^ 59
def prefixEnd_223039 : Nat := 4983230072969 + 3 ^ 40 * 223039 * 2
def baseEnd_223039 : Nat := 8483423088759858710131

theorem tailTrace_223039 : CollatzResearch.WordTrace tailWord_223039 prefixEnd_223039 8483423088759858710131 := by
  unfold tailWord_223039
  simp only [CollatzResearch.WordTrace]
  refine ⟨8134900638975269873648171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5423267092650179915765447 8134900638975269873648171)
  ·
    refine ⟨12202350958462904810472257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8134900638975269873648171 12202350958462904810472257)
    ·
      refine ⟨9151763218847178607854193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12202350958462904810472257 9151763218847178607854193)
      ·
        refine ⟨6863822414135383955890645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9151763218847178607854193 6863822414135383955890645)
        ·
          refine ⟨160870837831298061466187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6863822414135383955890645 160870837831298061466187)
          ·
            refine ⟨241306256746947092199281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160870837831298061466187 241306256746947092199281)
            ·
              refine ⟨180979692560210319149461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241306256746947092199281 180979692560210319149461)
              ·
                refine ⟨8483423088759858710131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180979692560210319149461 8483423088759858710131)
                ·
                  rfl

theorem cell22_223039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 6].length) (baseStart_223039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223039 prefixEnd_223039 := by exact prefixLift 223039
  have htrace : WordTrace (prefixWord ++ tailWord_223039) baseStart_223039 baseEnd_223039 := by
    simpa [prefixWord, tailWord_223039, baseEnd_223039] using wordTrace_append hprefix tailTrace_223039
  have hstable : (prefixWord ++ tailWord_223039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223039).length < 2 ^ (prefixWord ++ tailWord_223039).sum := by decide
  have hdescent : baseEnd_223039 < baseStart_223039 := by decide
  rcases family_descends (prefixWord ++ tailWord_223039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223071 : List Nat := [1, 1, 2, 3, 1, 5, 3, 2, 1, 3]
def baseStart_223071 : Nat := 118140960795 + 223071 * 2 ^ 59
def prefixEnd_223071 : Nat := 4983230072969 + 3 ^ 40 * 223071 * 2
def baseEnd_223071 : Nat := 76361762052801311591081

theorem tailTrace_223071 : CollatzResearch.WordTrace tailWord_223071 prefixEnd_223071 76361762052801311591081 := by
  unfold tailWord_223071
  simp only [CollatzResearch.WordTrace]
  refine ⟨8136067774859339338813067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5424045183239559559208711 8136067774859339338813067)
  ·
    refine ⟨12204101662289009008219601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8136067774859339338813067 12204101662289009008219601)
    ·
      refine ⟨9153076246716756756164701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12204101662289009008219601 9153076246716756756164701)
      ·
        refine ⟨3432403592518783783561763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9153076246716756756164701 3432403592518783783561763)
        ·
          refine ⟨5148605388778175675342645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3432403592518783783561763 5148605388778175675342645)
          ·
            refine ⟨482681755197953969563373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5148605388778175675342645 482681755197953969563373)
            ·
              refine ⟨181005658199232738586265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482681755197953969563373 181005658199232738586265)
              ·
                refine ⟨135754243649424553939699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181005658199232738586265 135754243649424553939699)
                ·
                  refine ⟨203631365474136830909549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135754243649424553939699 203631365474136830909549)
                  ·
                    refine ⟨76361762052801311591081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203631365474136830909549 76361762052801311591081)
                    ·
                      rfl

theorem cell22_223071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 3].length) (baseStart_223071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223071 prefixEnd_223071 := by exact prefixLift 223071
  have htrace : WordTrace (prefixWord ++ tailWord_223071) baseStart_223071 baseEnd_223071 := by
    simpa [prefixWord, tailWord_223071, baseEnd_223071] using wordTrace_append hprefix tailTrace_223071
  have hstable : (prefixWord ++ tailWord_223071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223071).length < 2 ^ (prefixWord ++ tailWord_223071).sum := by decide
  have hdescent : baseEnd_223071 < baseStart_223071 := by decide
  rcases family_descends (prefixWord ++ tailWord_223071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223084 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 5]
def baseStart_223084 : Nat := 118140960795 + 223084 * 2 ^ 59
def prefixEnd_223084 : Nat := 4983230072969 + 3 ^ 40 * 223084 * 2
def baseEnd_223084 : Nat := 25455404072824537005347

theorem tailTrace_223084 : CollatzResearch.WordTrace tailWord_223084 prefixEnd_223084 25455404072824537005347 := by
  unfold tailWord_223084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068270961906121279518153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5424361282541495039357537 4068270961906121279518153)
  ·
    refine ⟨3051203221429590959638615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4068270961906121279518153 3051203221429590959638615)
    ·
      refine ⟨4576804832144386439457923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051203221429590959638615 4576804832144386439457923)
      ·
        refine ⟨6865207248216579659186885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576804832144386439457923 6865207248216579659186885)
        ·
          refine ⟨1287226359040608686097541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6865207248216579659186885 1287226359040608686097541)
          ·
            refine ⟨241354942320114128643289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1287226359040608686097541 241354942320114128643289)
            ·
              refine ⟨181016206740085596482467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241354942320114128643289 181016206740085596482467)
              ·
                refine ⟨271524310110128394723701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181016206740085596482467 271524310110128394723701)
                ·
                  refine ⟨25455404072824537005347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271524310110128394723701 25455404072824537005347)
                  ·
                    rfl

theorem cell22_223084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_223084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223084 prefixEnd_223084 := by exact prefixLift 223084
  have htrace : WordTrace (prefixWord ++ tailWord_223084) baseStart_223084 baseEnd_223084 := by
    simpa [prefixWord, tailWord_223084, baseEnd_223084] using wordTrace_append hprefix tailTrace_223084
  have hstable : (prefixWord ++ tailWord_223084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223084).length < 2 ^ (prefixWord ++ tailWord_223084).sum := by decide
  have hdescent : baseEnd_223084 < baseStart_223084 := by decide
  rcases family_descends (prefixWord ++ tailWord_223084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223129 : List Nat := [1, 2, 1, 2, 1, 3, 6, 2, 4]
def baseStart_223129 : Nat := 118140960795 + 223129 * 2 ^ 59
def prefixEnd_223129 : Nat := 4983230072969 + 3 ^ 40 * 223129 * 2
def baseEnd_223129 : Nat := 25460538879369497880301

theorem tailTrace_223129 : CollatzResearch.WordTrace tailWord_223129 prefixEnd_223129 25460538879369497880301 := by
  unfold tailWord_223129
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138183208649215244424441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5425455472432810162949627 8138183208649215244424441)
  ·
    refine ⟨6103637406486911433318331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8138183208649215244424441 6103637406486911433318331)
    ·
      refine ⟨9155456109730367149977497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6103637406486911433318331 9155456109730367149977497)
      ·
        refine ⟨6866592082297775362483123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9155456109730367149977497 6866592082297775362483123)
        ·
          refine ⟨10299888123446663043724685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6866592082297775362483123 10299888123446663043724685)
          ·
            refine ⟨3862458046292498641396757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10299888123446663043724685 3862458046292498641396757)
            ·
              refine ⟨181052720919960873815473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3862458046292498641396757 181052720919960873815473)
              ·
                refine ⟨135789540689970655361605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181052720919960873815473 135789540689970655361605)
                ·
                  refine ⟨25460538879369497880301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135789540689970655361605 25460538879369497880301)
                  ·
                    rfl

theorem cell22_223129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 4].length) (baseStart_223129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223129 prefixEnd_223129 := by exact prefixLift 223129
  have htrace : WordTrace (prefixWord ++ tailWord_223129) baseStart_223129 baseEnd_223129 := by
    simpa [prefixWord, tailWord_223129, baseEnd_223129] using wordTrace_append hprefix tailTrace_223129
  have hstable : (prefixWord ++ tailWord_223129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223129).length < 2 ^ (prefixWord ++ tailWord_223129).sum := by decide
  have hdescent : baseEnd_223129 < baseStart_223129 := by decide
  rcases family_descends (prefixWord ++ tailWord_223129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223189 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_223189 : Nat := 118140960795 + 223189 * 2 ^ 59
def prefixEnd_223189 : Nat := 4983230072969 + 3 ^ 40 * 223189 * 2
def baseEnd_223189 : Nat := 76402155864288337140719

theorem tailTrace_223189 : CollatzResearch.WordTrace tailWord_223189 prefixEnd_223189 76402155864288337140719 := by
  unfold tailWord_223189
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140371588431845491608621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5426914392287896994405747 8140371588431845491608621)
  ·
    refine ⟨3052639345661942059353233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8140371588431845491608621 3052639345661942059353233)
    ·
      refine ⟨2289479509246456544514925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3052639345661942059353233 2289479509246456544514925)
      ·
        refine ⟨858554815967421204193097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2289479509246456544514925 858554815967421204193097)
        ·
          refine ⟨643916111975565903144823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858554815967421204193097 643916111975565903144823)
          ·
            refine ⟨965874167963348854717235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643916111975565903144823 965874167963348854717235)
            ·
              refine ⟨1448811251945023282075853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965874167963348854717235 1448811251945023282075853)
              ·
                refine ⟨543304219479383730778445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1448811251945023282075853 543304219479383730778445)
                ·
                  refine ⟨203739082304768899041917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543304219479383730778445 203739082304768899041917)
                  ·
                    refine ⟨76402155864288337140719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203739082304768899041917 76402155864288337140719)
                    ·
                      rfl

theorem cell22_223189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_223189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223189 prefixEnd_223189 := by exact prefixLift 223189
  have htrace : WordTrace (prefixWord ++ tailWord_223189) baseStart_223189 baseEnd_223189 := by
    simpa [prefixWord, tailWord_223189, baseEnd_223189] using wordTrace_append hprefix tailTrace_223189
  have hstable : (prefixWord ++ tailWord_223189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223189).length < 2 ^ (prefixWord ++ tailWord_223189).sum := by decide
  have hdescent : baseEnd_223189 < baseStart_223189 := by decide
  rcases family_descends (prefixWord ++ tailWord_223189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223253 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 5]
def baseStart_223253 : Nat := 118140960795 + 223253 * 2 ^ 59
def prefixEnd_223253 : Nat := 4983230072969 + 3 ^ 40 * 223253 * 2
def baseEnd_223253 : Nat := 25474688124071167846841

theorem tailTrace_223253 : CollatzResearch.WordTrace tailWord_223253 prefixEnd_223253 25474688124071167846841 := by
  unfold tailWord_223253
  simp only [CollatzResearch.WordTrace]
  refine ⟨8142705860199984421938413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5428470573466656281292275 8142705860199984421938413)
  ·
    refine ⟨3053514697574994158226905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8142705860199984421938413 3053514697574994158226905)
    ·
      refine ⟨2290136023181245618670179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3053514697574994158226905 2290136023181245618670179)
      ·
        refine ⟨3435204034771868428005269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290136023181245618670179 3435204034771868428005269)
        ·
          refine ⟨161025189129931332562747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3435204034771868428005269 161025189129931332562747)
          ·
            refine ⟨241537783694896998844121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161025189129931332562747 241537783694896998844121)
            ·
              refine ⟨181153337771172749133091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241537783694896998844121 181153337771172749133091)
              ·
                refine ⟨271730006656759123699637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181153337771172749133091 271730006656759123699637)
                ·
                  refine ⟨25474688124071167846841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271730006656759123699637 25474688124071167846841)
                  ·
                    rfl

theorem cell22_223253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_223253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223253 prefixEnd_223253 := by exact prefixLift 223253
  have htrace : WordTrace (prefixWord ++ tailWord_223253) baseStart_223253 baseEnd_223253 := by
    simpa [prefixWord, tailWord_223253, baseEnd_223253] using wordTrace_append hprefix tailTrace_223253
  have hstable : (prefixWord ++ tailWord_223253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223253).length < 2 ^ (prefixWord ++ tailWord_223253).sum := by decide
  have hdescent : baseEnd_223253 < baseStart_223253 := by decide
  rcases family_descends (prefixWord ++ tailWord_223253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223296 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 2, 3]
def baseStart_223296 : Nat := 118140960795 + 223296 * 2 ^ 59
def prefixEnd_223296 : Nat := 4983230072969 + 3 ^ 40 * 223296 * 2
def baseEnd_223296 : Nat := 76438784150975724715391

theorem tailTrace_223296 : CollatzResearch.WordTrace tailWord_223296 prefixEnd_223296 76438784150975724715391 := by
  unfold tailWord_223296
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072137099522101382876871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5429516132696135177169161 4072137099522101382876871)
  ·
    refine ⟨6108205649283152074315307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4072137099522101382876871 6108205649283152074315307)
    ·
      refine ⟨9162308473924728111472961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6108205649283152074315307 9162308473924728111472961)
      ·
        refine ⟨6871731355443546083604721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9162308473924728111472961 6871731355443546083604721)
        ·
          refine ⟨5153798516582659562703541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6871731355443546083604721 5153798516582659562703541)
          ·
            refine ⟨483168610929624334003457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5153798516582659562703541 483168610929624334003457)
            ·
              refine ⟨362376458197218250502593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483168610929624334003457 362376458197218250502593)
              ·
                refine ⟨271782343647913687876945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362376458197218250502593 271782343647913687876945)
                ·
                  refine ⟨203836757735935265907709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271782343647913687876945 203836757735935265907709)
                  ·
                    refine ⟨76438784150975724715391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203836757735935265907709 76438784150975724715391)
                    ·
                      rfl

theorem cell22_223296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_223296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223296 prefixEnd_223296 := by exact prefixLift 223296
  have htrace : WordTrace (prefixWord ++ tailWord_223296) baseStart_223296 baseEnd_223296 := by
    simpa [prefixWord, tailWord_223296, baseEnd_223296] using wordTrace_append hprefix tailTrace_223296
  have hstable : (prefixWord ++ tailWord_223296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223296).length < 2 ^ (prefixWord ++ tailWord_223296).sum := by decide
  have hdescent : baseEnd_223296 < baseStart_223296 := by decide
  rcases family_descends (prefixWord ++ tailWord_223296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223322 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_223322 : Nat := 118140960795 + 223322 * 2 ^ 59
def prefixEnd_223322 : Nat := 4983230072969 + 3 ^ 40 * 223322 * 2
def baseEnd_223322 : Nat := 76447684482320323565311

theorem tailTrace_223322 : CollatzResearch.WordTrace tailWord_223322 prefixEnd_223322 76447684482320323565311 := by
  unfold tailWord_223322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036305624237502301550055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5430148331300006137466813 2036305624237502301550055)
  ·
    refine ⟨3054458436356253452325083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2036305624237502301550055 3054458436356253452325083)
    ·
      refine ⟨4581687654534380178487625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3054458436356253452325083 4581687654534380178487625)
      ·
        refine ⟨3436265740900785133865719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4581687654534380178487625 3436265740900785133865719)
        ·
          refine ⟨5154398611351177700798579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436265740900785133865719 5154398611351177700798579)
          ·
            refine ⟨7731597917026766551197869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154398611351177700798579 7731597917026766551197869)
            ·
              refine ⟨2899349218885037456699201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7731597917026766551197869 2899349218885037456699201)
              ·
                refine ⟨2174511914163778092524401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2899349218885037456699201 2174511914163778092524401)
                ·
                  refine ⟨1630883935622833569393301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2174511914163778092524401 1630883935622833569393301)
                  ·
                    refine ⟨76447684482320323565311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1630883935622833569393301 76447684482320323565311)
                    ·
                      rfl

theorem cell22_223322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_223322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223322 prefixEnd_223322 := by exact prefixLift 223322
  have htrace : WordTrace (prefixWord ++ tailWord_223322) baseStart_223322 baseEnd_223322 := by
    simpa [prefixWord, tailWord_223322, baseEnd_223322] using wordTrace_append hprefix tailTrace_223322
  have hstable : (prefixWord ++ tailWord_223322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223322).length < 2 ^ (prefixWord ++ tailWord_223322).sum := by decide
  have hdescent : baseEnd_223322 < baseStart_223322 := by decide
  rcases family_descends (prefixWord ++ tailWord_223322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223337 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 7]
def baseStart_223337 : Nat := 118140960795 + 223337 * 2 ^ 59
def prefixEnd_223337 : Nat := 4983230072969 + 3 ^ 40 * 223337 * 2
def baseEnd_223337 : Nat := 25484273096288428146755

theorem tailTrace_223337 : CollatzResearch.WordTrace tailWord_223337 prefixEnd_223337 25484273096288428146755 := by
  unfold tailWord_223337
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145769591895666767996265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5430513061263777845330843 8145769591895666767996265)
  ·
    refine ⟨6109327193921750075997199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8145769591895666767996265 6109327193921750075997199)
    ·
      refine ⟨9163990790882625113995799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6109327193921750075997199 9163990790882625113995799)
      ·
        refine ⟨13745986186323937670993699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9163990790882625113995799 13745986186323937670993699)
        ·
          refine ⟨20618979279485906506490549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13745986186323937670993699 20618979279485906506490549)
          ·
            refine ⟨1933029307451803734983489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20618979279485906506490549 1933029307451803734983489)
            ·
              refine ⟨1449771980588852801237617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933029307451803734983489 1449771980588852801237617)
              ·
                refine ⟨1087328985441639600928213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449771980588852801237617 1087328985441639600928213)
                ·
                  refine ⟨25484273096288428146755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1087328985441639600928213 25484273096288428146755)
                  ·
                    rfl

theorem cell22_223337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_223337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223337 prefixEnd_223337 := by exact prefixLift 223337
  have htrace : WordTrace (prefixWord ++ tailWord_223337) baseStart_223337 baseEnd_223337 := by
    simpa [prefixWord, tailWord_223337, baseEnd_223337] using wordTrace_append hprefix tailTrace_223337
  have hstable : (prefixWord ++ tailWord_223337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223337).length < 2 ^ (prefixWord ++ tailWord_223337).sum := by decide
  have hdescent : baseEnd_223337 < baseStart_223337 := by decide
  rcases family_descends (prefixWord ++ tailWord_223337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223452 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 1, 4]
def baseStart_223452 : Nat := 118140960795 + 223452 * 2 ^ 59
def prefixEnd_223452 : Nat := 4983230072969 + 3 ^ 40 * 223452 * 2
def baseEnd_223452 : Nat := 76492186139043317814913

theorem tailTrace_223452 : CollatzResearch.WordTrace tailWord_223452 prefixEnd_223452 76492186139043317814913 := by
  unfold tailWord_223452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4074981993239520704216305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5433309324319360938955073 4074981993239520704216305)
  ·
    refine ⟨3056236494929640528162229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4074981993239520704216305 3056236494929640528162229)
    ·
      refine ⟨286522171399653799515209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3056236494929640528162229 286522171399653799515209)
      ·
        refine ⟨214891628549740349636407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286522171399653799515209 214891628549740349636407)
        ·
          refine ⟨322337442824610524454611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214891628549740349636407 322337442824610524454611)
          ·
            refine ⟨483506164236915786681917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322337442824610524454611 483506164236915786681917)
            ·
              refine ⟨181314811588843420005719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483506164236915786681917 181314811588843420005719)
              ·
                refine ⟨271972217383265130008579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181314811588843420005719 271972217383265130008579)
                ·
                  refine ⟨407958326074897695012869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271972217383265130008579 407958326074897695012869)
                  ·
                    refine ⟨76492186139043317814913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 407958326074897695012869 76492186139043317814913)
                    ·
                      rfl

theorem cell22_223452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_223452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223452 prefixEnd_223452 := by exact prefixLift 223452
  have htrace : WordTrace (prefixWord ++ tailWord_223452) baseStart_223452 baseEnd_223452 := by
    simpa [prefixWord, tailWord_223452, baseEnd_223452] using wordTrace_append hprefix tailTrace_223452
  have hstable : (prefixWord ++ tailWord_223452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223452).length < 2 ^ (prefixWord ++ tailWord_223452).sum := by decide
  have hdescent : baseEnd_223452 < baseStart_223452 := by decide
  rcases family_descends (prefixWord ++ tailWord_223452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223540 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 5]
def baseStart_223540 : Nat := 118140960795 + 223540 * 2 ^ 59
def prefixEnd_223540 : Nat := 4983230072969 + 3 ^ 40 * 223540 * 2
def baseEnd_223540 : Nat := 25507436779146807204881

theorem tailTrace_223540 : CollatzResearch.WordTrace tailWord_223540 prefixEnd_223540 25507436779146807204881 := by
  unfold tailWord_223540
  simp only [CollatzResearch.WordTrace]
  refine ⟨4076586805080116218818037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5435449073440154958424049 4076586805080116218818037)
  ·
    refine ⟨382180012976260895514191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4076586805080116218818037 382180012976260895514191)
    ·
      refine ⟨573270019464391343271287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382180012976260895514191 573270019464391343271287)
      ·
        refine ⟨859905029196587014906931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573270019464391343271287 859905029196587014906931)
        ·
          refine ⟨1289857543794880522360397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859905029196587014906931 1289857543794880522360397)
          ·
            refine ⟨483696578923080195885149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1289857543794880522360397 483696578923080195885149)
            ·
              refine ⟨181386217096155073456931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483696578923080195885149 181386217096155073456931)
              ·
                refine ⟨272079325644232610185397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181386217096155073456931 272079325644232610185397)
                ·
                  refine ⟨25507436779146807204881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272079325644232610185397 25507436779146807204881)
                  ·
                    rfl

theorem cell22_223540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_223540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223540 prefixEnd_223540 := by exact prefixLift 223540
  have htrace : WordTrace (prefixWord ++ tailWord_223540) baseStart_223540 baseEnd_223540 := by
    simpa [prefixWord, tailWord_223540, baseEnd_223540] using wordTrace_append hprefix tailTrace_223540
  have hstable : (prefixWord ++ tailWord_223540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223540).length < 2 ^ (prefixWord ++ tailWord_223540).sum := by decide
  have hdescent : baseEnd_223540 < baseStart_223540 := by decide
  rcases family_descends (prefixWord ++ tailWord_223540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223568 : List Nat := [2, 1, 1, 1, 1, 6, 3, 3, 4]
def baseStart_223568 : Nat := 118140960795 + 223568 * 2 ^ 59
def prefixEnd_223568 : Nat := 4983230072969 + 3 ^ 40 * 223568 * 2
def baseEnd_223568 : Nat := 25510631769885893971519

theorem tailTrace_223568 : CollatzResearch.WordTrace tailWord_223568 prefixEnd_223568 25510631769885893971519 := by
  unfold tailWord_223568
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077097427029396609827679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5436129902705862146436905 4077097427029396609827679)
  ·
    refine ⟨6115646140544094914741519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4077097427029396609827679 6115646140544094914741519)
    ·
      refine ⟨9173469210816142372112279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6115646140544094914741519 9173469210816142372112279)
      ·
        refine ⟨13760203816224213558168419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9173469210816142372112279 13760203816224213558168419)
        ·
          refine ⟨20640305724336320337252629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13760203816224213558168419 20640305724336320337252629)
          ·
            refine ⟨967514330828265015808717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20640305724336320337252629 967514330828265015808717)
            ·
              refine ⟨362817874060599380928269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 967514330828265015808717 362817874060599380928269)
              ·
                refine ⟨136056702772724767848101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362817874060599380928269 136056702772724767848101)
                ·
                  refine ⟨25510631769885893971519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136056702772724767848101 25510631769885893971519)
                  ·
                    rfl

theorem cell22_223568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 4].length) (baseStart_223568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223568 prefixEnd_223568 := by exact prefixLift 223568
  have htrace : WordTrace (prefixWord ++ tailWord_223568) baseStart_223568 baseEnd_223568 := by
    simpa [prefixWord, tailWord_223568, baseEnd_223568] using wordTrace_append hprefix tailTrace_223568
  have hstable : (prefixWord ++ tailWord_223568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223568).length < 2 ^ (prefixWord ++ tailWord_223568).sum := by decide
  have hdescent : baseEnd_223568 < baseStart_223568 := by decide
  rcases family_descends (prefixWord ++ tailWord_223568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223600 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 2, 3]
def baseStart_223600 : Nat := 118140960795 + 223600 * 2 ^ 59
def prefixEnd_223600 : Nat := 4983230072969 + 3 ^ 40 * 223600 * 2
def baseEnd_223600 : Nat := 76542849563620265114459

theorem tailTrace_223600 : CollatzResearch.WordTrace tailWord_223600 prefixEnd_223600 76542849563620265114459 := by
  unfold tailWord_223600
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077680994971431342410127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5436907993295241789880169 4077680994971431342410127)
  ·
    refine ⟨6116521492457147013615191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4077680994971431342410127 6116521492457147013615191)
    ·
      refine ⟨9174782238685720520422787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116521492457147013615191 9174782238685720520422787)
      ·
        refine ⟨13762173358028580780634181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174782238685720520422787 13762173358028580780634181)
        ·
          refine ⟨2580407504630358896368909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13762173358028580780634181 2580407504630358896368909)
          ·
            refine ⟨967652814236384586138341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2580407504630358896368909 967652814236384586138341)
            ·
              refine ⟨181434902669322109900939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 967652814236384586138341 181434902669322109900939)
              ·
                refine ⟨272152354003983164851409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181434902669322109900939 272152354003983164851409)
                ·
                  refine ⟨204114265502987373638557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272152354003983164851409 204114265502987373638557)
                  ·
                    refine ⟨76542849563620265114459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204114265502987373638557 76542849563620265114459)
                    ·
                      rfl

theorem cell22_223600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 3].length) (baseStart_223600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223600 prefixEnd_223600 := by exact prefixLift 223600
  have htrace : WordTrace (prefixWord ++ tailWord_223600) baseStart_223600 baseEnd_223600 := by
    simpa [prefixWord, tailWord_223600, baseEnd_223600] using wordTrace_append hprefix tailTrace_223600
  have hstable : (prefixWord ++ tailWord_223600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223600).length < 2 ^ (prefixWord ++ tailWord_223600).sum := by decide
  have hdescent : baseEnd_223600 < baseStart_223600 := by decide
  rcases family_descends (prefixWord ++ tailWord_223600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223692 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 5]
def baseStart_223692 : Nat := 118140960795 + 223692 * 2 ^ 59
def prefixEnd_223692 : Nat := 4983230072969 + 3 ^ 40 * 223692 * 2
def baseEnd_223692 : Nat := 25524781014587563938059

theorem tailTrace_223692 : CollatzResearch.WordTrace tailWord_223692 prefixEnd_223692 25524781014587563938059 := by
  unfold tailWord_223692
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079358752804781198584665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5439145003739708264779553 4079358752804781198584665)
  ·
    refine ⟨3059519064603585898938499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4079358752804781198584665 3059519064603585898938499)
    ·
      refine ⟨4589278596905378848407749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059519064603585898938499 4589278596905378848407749)
      ·
        refine ⟨860489736919758534076453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4589278596905378848407749 860489736919758534076453)
        ·
          refine ⟨161341825672454725139335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 860489736919758534076453 161341825672454725139335)
          ·
            refine ⟨242012738508682087709003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161341825672454725139335 242012738508682087709003)
            ·
              refine ⟨363019107763023131563505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242012738508682087709003 363019107763023131563505)
              ·
                refine ⟨272264330822267348672629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363019107763023131563505 272264330822267348672629)
                ·
                  refine ⟨25524781014587563938059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272264330822267348672629 25524781014587563938059)
                  ·
                    rfl

theorem cell22_223692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_223692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223692 prefixEnd_223692 := by exact prefixLift 223692
  have htrace : WordTrace (prefixWord ++ tailWord_223692) baseStart_223692 baseEnd_223692 := by
    simpa [prefixWord, tailWord_223692, baseEnd_223692] using wordTrace_append hprefix tailTrace_223692
  have hstable : (prefixWord ++ tailWord_223692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223692).length < 2 ^ (prefixWord ++ tailWord_223692).sum := by decide
  have hdescent : baseEnd_223692 < baseStart_223692 := by decide
  rcases family_descends (prefixWord ++ tailWord_223692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223731 : List Nat := [1, 1, 1, 2, 2, 2, 5, 8]
def baseStart_223731 : Nat := 118140960795 + 223731 * 2 ^ 59
def prefixEnd_223731 : Nat := 4983230072969 + 3 ^ 40 * 223731 * 2
def baseEnd_223731 : Nat := 8509743726753287787673

theorem tailTrace_223731 : CollatzResearch.WordTrace tailWord_223731 prefixEnd_223731 8509743726753287787673 := by
  unfold tailWord_223731
  simp only [CollatzResearch.WordTrace]
  refine ⟨8160139952468272057839047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5440093301645514705226031 8160139952468272057839047)
  ·
    refine ⟨12240209928702408086758571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8160139952468272057839047 12240209928702408086758571)
    ·
      refine ⟨18360314893053612130137857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12240209928702408086758571 18360314893053612130137857)
      ·
        refine ⟨13770236169790209097603393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18360314893053612130137857 13770236169790209097603393)
        ·
          refine ⟨10327677127342656823202545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13770236169790209097603393 10327677127342656823202545)
          ·
            refine ⟨7745757845506992617401909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10327677127342656823202545 7745757845506992617401909)
            ·
              refine ⟨726164798016280557881429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7745757845506992617401909 726164798016280557881429)
              ·
                refine ⟨8509743726753287787673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 726164798016280557881429 8509743726753287787673)
                ·
                  rfl

theorem cell22_223731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 8].length) (baseStart_223731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223731 prefixEnd_223731 := by exact prefixLift 223731
  have htrace : WordTrace (prefixWord ++ tailWord_223731) baseStart_223731 baseEnd_223731 := by
    simpa [prefixWord, tailWord_223731, baseEnd_223731] using wordTrace_append hprefix tailTrace_223731
  have hstable : (prefixWord ++ tailWord_223731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223731).length < 2 ^ (prefixWord ++ tailWord_223731).sum := by decide
  have hdescent : baseEnd_223731 < baseStart_223731 := by decide
  rcases family_descends (prefixWord ++ tailWord_223731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223748 : List Nat := [2, 3, 2, 3, 1, 1, 10]
def baseStart_223748 : Nat := 118140960795 + 223748 * 2 ^ 59
def prefixEnd_223748 : Nat := 4983230072969 + 3 ^ 40 * 223748 * 2
def baseEnd_223748 : Nat := 2836796777340637496815

theorem tailTrace_223748 : CollatzResearch.WordTrace tailWord_223748 prefixEnd_223748 2836796777340637496815 := by
  unfold tailWord_223748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080379996703341980603949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5440506662271122640805265 4080379996703341980603949)
  ·
    refine ⟨1530142498763753242726481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4080379996703341980603949 1530142498763753242726481)
    ·
      refine ⟨1147606874072814932044861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1530142498763753242726481 1147606874072814932044861)
      ·
        refine ⟨430352577777305599516823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1147606874072814932044861 430352577777305599516823)
        ·
          refine ⟨645528866665958399275235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430352577777305599516823 645528866665958399275235)
          ·
            refine ⟨968293299998937598912853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645528866665958399275235 968293299998937598912853)
            ·
              refine ⟨2836796777340637496815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 968293299998937598912853 2836796777340637496815)
              ·
                rfl

theorem cell22_223748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 10].length) (baseStart_223748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223748 prefixEnd_223748 := by exact prefixLift 223748
  have htrace : WordTrace (prefixWord ++ tailWord_223748) baseStart_223748 baseEnd_223748 := by
    simpa [prefixWord, tailWord_223748, baseEnd_223748] using wordTrace_append hprefix tailTrace_223748
  have hstable : (prefixWord ++ tailWord_223748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223748).length < 2 ^ (prefixWord ++ tailWord_223748).sum := by decide
  have hdescent : baseEnd_223748 < baseStart_223748 := by decide
  rcases family_descends (prefixWord ++ tailWord_223748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223797 : List Nat := [1, 3, 3, 1, 1, 2, 2, 5, 1, 3]
def baseStart_223797 : Nat := 118140960795 + 223797 * 2 ^ 59
def prefixEnd_223797 : Nat := 4983230072969 + 3 ^ 40 * 223797 * 2
def baseEnd_223797 : Nat := 76610286689577417938855

theorem tailTrace_223797 : CollatzResearch.WordTrace tailWord_223797 prefixEnd_223797 76610286689577417938855 := by
  unfold tailWord_223797
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162547170229165329741645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5441698113486110219827763 8162547170229165329741645)
  ·
    refine ⟨3060955188835936998653117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8162547170229165329741645 3060955188835936998653117)
    ·
      refine ⟨1147858195813476374494919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3060955188835936998653117 1147858195813476374494919)
      ·
        refine ⟨1721787293720214561742379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147858195813476374494919 1721787293720214561742379)
        ·
          refine ⟨2582680940580321842613569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721787293720214561742379 2582680940580321842613569)
          ·
            refine ⟨1937010705435241381960177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582680940580321842613569 1937010705435241381960177)
            ·
              refine ⟨1452758029076431036470133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937010705435241381960177 1452758029076431036470133)
              ·
                refine ⟨136196065225915409669075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1452758029076431036470133 136196065225915409669075)
                ·
                  refine ⟨204294097838873114503613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136196065225915409669075 204294097838873114503613)
                  ·
                    refine ⟨76610286689577417938855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204294097838873114503613 76610286689577417938855)
                    ·
                      rfl

theorem cell22_223797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_223797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223797 prefixEnd_223797 := by exact prefixLift 223797
  have htrace : WordTrace (prefixWord ++ tailWord_223797) baseStart_223797 baseEnd_223797 := by
    simpa [prefixWord, tailWord_223797, baseEnd_223797] using wordTrace_append hprefix tailTrace_223797
  have hstable : (prefixWord ++ tailWord_223797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223797).length < 2 ^ (prefixWord ++ tailWord_223797).sum := by decide
  have hdescent : baseEnd_223797 < baseStart_223797 := by decide
  rcases family_descends (prefixWord ++ tailWord_223797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223823 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 3, 4]
def baseStart_223823 : Nat := 118140960795 + 223823 * 2 ^ 59
def prefixEnd_223823 : Nat := 4983230072969 + 3 ^ 40 * 223823 * 2
def baseEnd_223823 : Nat := 76619187020922016788775

theorem tailTrace_223823 : CollatzResearch.WordTrace tailWord_223823 prefixEnd_223823 76619187020922016788775 := by
  unfold tailWord_223823
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163495468134971770188123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5442330312089981180125415 8163495468134971770188123)
  ·
    refine ⟨12245243202202457655282185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8163495468134971770188123 12245243202202457655282185)
    ·
      refine ⟨9183932401651843241461639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12245243202202457655282185 9183932401651843241461639)
      ·
        refine ⟨13775898602477764862192459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9183932401651843241461639 13775898602477764862192459)
        ·
          refine ⟨20663847903716647293288689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13775898602477764862192459 20663847903716647293288689)
          ·
            refine ⟨15497885927787485469966517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20663847903716647293288689 15497885927787485469966517)
            ·
              refine ⟨1452926805730076762809361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15497885927787485469966517 1452926805730076762809361)
              ·
                refine ⟨1089695104297557572107021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452926805730076762809361 1089695104297557572107021)
                ·
                  refine ⟨408635664111584089540133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089695104297557572107021 408635664111584089540133)
                  ·
                    refine ⟨76619187020922016788775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 408635664111584089540133 76619187020922016788775)
                    ·
                      rfl

theorem cell22_223823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_223823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223823 prefixEnd_223823 := by exact prefixLift 223823
  have htrace : WordTrace (prefixWord ++ tailWord_223823) baseStart_223823 baseEnd_223823 := by
    simpa [prefixWord, tailWord_223823, baseEnd_223823] using wordTrace_append hprefix tailTrace_223823
  have hstable : (prefixWord ++ tailWord_223823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223823).length < 2 ^ (prefixWord ++ tailWord_223823).sum := by decide
  have hdescent : baseEnd_223823 < baseStart_223823 := by decide
  rcases family_descends (prefixWord ++ tailWord_223823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223855 : List Nat := [1, 1, 2, 1, 3, 2, 3, 5, 4]
def baseStart_223855 : Nat := 118140960795 + 223855 * 2 ^ 59
def prefixEnd_223855 : Nat := 4983230072969 + 3 ^ 40 * 223855 * 2
def baseEnd_223855 : Nat := 25543380424961533329559

theorem tailTrace_223855 : CollatzResearch.WordTrace tailWord_223855 prefixEnd_223855 25543380424961533329559 := by
  unfold tailWord_223855
  simp only [CollatzResearch.WordTrace]
  refine ⟨8164662604019041235353019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5443108402679360823568679 8164662604019041235353019)
  ·
    refine ⟨12246993906028561853029529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8164662604019041235353019 12246993906028561853029529)
    ·
      refine ⟨9185245429521421389772147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12246993906028561853029529 9185245429521421389772147)
      ·
        refine ⟨13777868144282132084658221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9185245429521421389772147 13777868144282132084658221)
        ·
          refine ⟨5166700554105799531746833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13777868144282132084658221 5166700554105799531746833)
          ·
            refine ⟨3875025415579349648810125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5166700554105799531746833 3875025415579349648810125)
            ·
              refine ⟨1453134530842256118303797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3875025415579349648810125 1453134530842256118303797)
              ·
                refine ⟨136231362266461511090981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1453134530842256118303797 136231362266461511090981)
                ·
                  refine ⟨25543380424961533329559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136231362266461511090981 25543380424961533329559)
                  ·
                    rfl

theorem cell22_223855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 4].length) (baseStart_223855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223855 prefixEnd_223855 := by exact prefixLift 223855
  have htrace : WordTrace (prefixWord ++ tailWord_223855) baseStart_223855 baseEnd_223855 := by
    simpa [prefixWord, tailWord_223855, baseEnd_223855] using wordTrace_append hprefix tailTrace_223855
  have hstable : (prefixWord ++ tailWord_223855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223855).length < 2 ^ (prefixWord ++ tailWord_223855).sum := by decide
  have hdescent : baseEnd_223855 < baseStart_223855 := by decide
  rcases family_descends (prefixWord ++ tailWord_223855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223900 : List Nat := [2, 2, 3, 2, 2, 2, 1, 8]
def baseStart_223900 : Nat := 118140960795 + 223900 * 2 ^ 59
def prefixEnd_223900 : Nat := 4983230072969 + 3 ^ 40 * 223900 * 2
def baseEnd_223900 : Nat := 8516171743835498068171

theorem tailTrace_223900 : CollatzResearch.WordTrace tailWord_223900 prefixEnd_223900 8516171743835498068171 := by
  unfold tailWord_223900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4083151944428006960370577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5444202592570675947160769 4083151944428006960370577)
  ·
    refine ⟨3062363958321005220277933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4083151944428006960370577 3062363958321005220277933)
    ·
      refine ⟨1148386484370376957604225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3062363958321005220277933 1148386484370376957604225)
      ·
        refine ⟨861289863277782718203169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1148386484370376957604225 861289863277782718203169)
        ·
          refine ⟨645967397458337038652377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861289863277782718203169 645967397458337038652377)
          ·
            refine ⟨484475548093752778989283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645967397458337038652377 484475548093752778989283)
            ·
              refine ⟨726713322140629168483925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484475548093752778989283 726713322140629168483925)
              ·
                refine ⟨8516171743835498068171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 726713322140629168483925 8516171743835498068171)
                ·
                  rfl

theorem cell22_223900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 8].length) (baseStart_223900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223900 prefixEnd_223900 := by exact prefixLift 223900
  have htrace : WordTrace (prefixWord ++ tailWord_223900) baseStart_223900 baseEnd_223900 := by
    simpa [prefixWord, tailWord_223900, baseEnd_223900] using wordTrace_append hprefix tailTrace_223900
  have hstable : (prefixWord ++ tailWord_223900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223900).length < 2 ^ (prefixWord ++ tailWord_223900).sum := by decide
  have hdescent : baseEnd_223900 < baseStart_223900 := by decide
  rcases family_descends (prefixWord ++ tailWord_223900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223902 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_223902 : Nat := 118140960795 + 223902 * 2 ^ 59
def prefixEnd_223902 : Nat := 4983230072969 + 3 ^ 40 * 223902 * 2
def baseEnd_223902 : Nat := 76646230335392144063533

theorem tailTrace_223902 : CollatzResearch.WordTrace tailWord_223902 prefixEnd_223902 76646230335392144063533 := by
  unfold tailWord_223902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020797104356096032789245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5444251223232512174875973 1020797104356096032789245)
  ·
    refine ⟨382798914133536012295967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1020797104356096032789245 382798914133536012295967)
    ·
      refine ⟨574198371200304018443951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382798914133536012295967 574198371200304018443951)
      ·
        refine ⟨861297556800456027665927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574198371200304018443951 861297556800456027665927)
        ·
          refine ⟨1291946335200684041498891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861297556800456027665927 1291946335200684041498891)
          ·
            refine ⟨1937919502801026062248337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291946335200684041498891 1937919502801026062248337)
            ·
              refine ⟨1453439627100769546686253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937919502801026062248337 1453439627100769546686253)
              ·
                refine ⟨545039860162788580007345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1453439627100769546686253 545039860162788580007345)
                ·
                  refine ⟨408779895122091435005509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545039860162788580007345 408779895122091435005509)
                  ·
                    refine ⟨76646230335392144063533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 408779895122091435005509 76646230335392144063533)
                    ·
                      rfl

theorem cell22_223902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_223902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_223902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_223902 prefixEnd_223902 := by exact prefixLift 223902
  have htrace : WordTrace (prefixWord ++ tailWord_223902) baseStart_223902 baseEnd_223902 := by
    simpa [prefixWord, tailWord_223902, baseEnd_223902] using wordTrace_append hprefix tailTrace_223902
  have hstable : (prefixWord ++ tailWord_223902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223902).length < 2 ^ (prefixWord ++ tailWord_223902).sum := by decide
  have hdescent : baseEnd_223902 < baseStart_223902 := by decide
  rcases family_descends (prefixWord ++ tailWord_223902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224007 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 6]
def baseStart_224007 : Nat := 118140960795 + 224007 * 2 ^ 59
def prefixEnd_224007 : Nat := 4983230072969 + 3 ^ 40 * 224007 * 2
def baseEnd_224007 : Nat := 25560724660402290062737

theorem tailTrace_224007 : CollatzResearch.WordTrace tailWord_224007 prefixEnd_224007 25560724660402290062737 := by
  unfold tailWord_224007
  simp only [CollatzResearch.WordTrace]
  refine ⟨8170206499468371194886275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5446804332978914129924183 8170206499468371194886275)
  ·
    refine ⟨12255309749202556792329413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8170206499468371194886275 12255309749202556792329413)
    ·
      refine ⟨2297870577975479398561765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12255309749202556792329413 2297870577975479398561765)
      ·
        refine ⟨430850733370402387230331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2297870577975479398561765 430850733370402387230331)
        ·
          refine ⟨646276100055603580845497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430850733370402387230331 646276100055603580845497)
          ·
            refine ⟨484707075041702685634123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646276100055603580845497 484707075041702685634123)
            ·
              refine ⟨727060612562554028451185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484707075041702685634123 727060612562554028451185)
              ·
                refine ⟨545295459421915521338389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727060612562554028451185 545295459421915521338389)
                ·
                  refine ⟨25560724660402290062737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 545295459421915521338389 25560724660402290062737)
                  ·
                    rfl

theorem cell22_224007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 6].length) (baseStart_224007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224007 prefixEnd_224007 := by exact prefixLift 224007
  have htrace : WordTrace (prefixWord ++ tailWord_224007) baseStart_224007 baseEnd_224007 := by
    simpa [prefixWord, tailWord_224007, baseEnd_224007] using wordTrace_append hprefix tailTrace_224007
  have hstable : (prefixWord ++ tailWord_224007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224007).length < 2 ^ (prefixWord ++ tailWord_224007).sum := by decide
  have hdescent : baseEnd_224007 < baseStart_224007 := by decide
  rcases family_descends (prefixWord ++ tailWord_224007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224067 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 3, 3]
def baseStart_224067 : Nat := 118140960795 + 224067 * 2 ^ 59
def prefixEnd_224067 : Nat := 4983230072969 + 3 ^ 40 * 224067 * 2
def baseEnd_224067 : Nat := 76702713207386713688027

theorem tailTrace_224067 : CollatzResearch.WordTrace tailWord_224067 prefixEnd_224067 76702713207386713688027 := by
  unfold tailWord_224067
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172394879251001442070455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5448263252834000961380303 8172394879251001442070455)
  ·
    refine ⟨12258592318876502163105683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8172394879251001442070455 12258592318876502163105683)
    ·
      refine ⟨18387888478314753244658525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12258592318876502163105683 18387888478314753244658525)
      ·
        refine ⟨6895458179368032466746947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18387888478314753244658525 6895458179368032466746947)
        ·
          refine ⟨10343187269052048700120421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895458179368032466746947 10343187269052048700120421)
          ·
            refine ⟨1939347612947259131272579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10343187269052048700120421 1939347612947259131272579)
            ·
              refine ⟨2909021419420888696908869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939347612947259131272579 2909021419420888696908869)
              ·
                refine ⟨545441516141416630670413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2909021419420888696908869 545441516141416630670413)
                ·
                  refine ⟨204540568553031236501405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545441516141416630670413 204540568553031236501405)
                  ·
                    refine ⟨76702713207386713688027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204540568553031236501405 76702713207386713688027)
                    ·
                      rfl

theorem cell22_224067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 3].length) (baseStart_224067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224067 prefixEnd_224067 := by exact prefixLift 224067
  have htrace : WordTrace (prefixWord ++ tailWord_224067) baseStart_224067 baseEnd_224067 := by
    simpa [prefixWord, tailWord_224067, baseEnd_224067] using wordTrace_append hprefix tailTrace_224067
  have hstable : (prefixWord ++ tailWord_224067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224067).length < 2 ^ (prefixWord ++ tailWord_224067).sum := by decide
  have hdescent : baseEnd_224067 < baseStart_224067 := by decide
  rcases family_descends (prefixWord ++ tailWord_224067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224080 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 7]
def baseStart_224080 : Nat := 118140960795 + 224080 * 2 ^ 59
def prefixEnd_224080 : Nat := 4983230072969 + 3 ^ 40 * 224080 * 2
def baseEnd_224080 : Nat := 25569054457686337704329

theorem tailTrace_224080 : CollatzResearch.WordTrace tailWord_224080 prefixEnd_224080 25569054457686337704329 := by
  unfold tailWord_224080
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086434514101952331146847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5448579352135936441529129 4086434514101952331146847)
  ·
    refine ⟨6129651771152928496720271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4086434514101952331146847 6129651771152928496720271)
    ·
      refine ⟨9194477656729392745080407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6129651771152928496720271 9194477656729392745080407)
      ·
        refine ⟨13791716485094089117620611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9194477656729392745080407 13791716485094089117620611)
        ·
          refine ⟨20687574727641133676430917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13791716485094089117620611 20687574727641133676430917)
          ·
            refine ⟨3878920261432712564330797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20687574727641133676430917 3878920261432712564330797)
            ·
              refine ⟨1454595098037267211624049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3878920261432712564330797 1454595098037267211624049)
              ·
                refine ⟨1090946323527950408718037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454595098037267211624049 1090946323527950408718037)
                ·
                  refine ⟨25569054457686337704329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1090946323527950408718037 25569054457686337704329)
                  ·
                    rfl

theorem cell22_224080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_224080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224080 prefixEnd_224080 := by exact prefixLift 224080
  have htrace : WordTrace (prefixWord ++ tailWord_224080) baseStart_224080 baseEnd_224080 := by
    simpa [prefixWord, tailWord_224080, baseEnd_224080] using wordTrace_append hprefix tailTrace_224080
  have hstable : (prefixWord ++ tailWord_224080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224080).length < 2 ^ (prefixWord ++ tailWord_224080).sum := by decide
  have hdescent : baseEnd_224080 < baseStart_224080 := by decide
  rcases family_descends (prefixWord ++ tailWord_224080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224114 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_224114 : Nat := 118140960795 + 224114 * 2 ^ 59
def prefixEnd_224114 : Nat := 4983230072969 + 3 ^ 40 * 224114 * 2
def baseEnd_224114 : Nat := 25572934089298085920961

theorem tailTrace_224114 : CollatzResearch.WordTrace tailWord_224114 prefixEnd_224114 25572934089298085920961 := by
  unfold tailWord_224114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043527277520182117257849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5449406073387152312687597 2043527277520182117257849)
  ·
    refine ⟨1532645458140136587943387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2043527277520182117257849 1532645458140136587943387)
    ·
      refine ⟨2298968187210204881915081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1532645458140136587943387 2298968187210204881915081)
      ·
        refine ⟨1724226140407653661436311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2298968187210204881915081 1724226140407653661436311)
        ·
          refine ⟨2586339210611480492154467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1724226140407653661436311 2586339210611480492154467)
          ·
            refine ⟨3879508815917220738231701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586339210611480492154467 3879508815917220738231701)
            ·
              refine ⟨181851975746119722104611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3879508815917220738231701 181851975746119722104611)
              ·
                refine ⟨272777963619179583156917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181851975746119722104611 272777963619179583156917)
                ·
                  refine ⟨25572934089298085920961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272777963619179583156917 25572934089298085920961)
                  ·
                    rfl

theorem cell22_224114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_224114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224114 prefixEnd_224114 := by exact prefixLift 224114
  have htrace : WordTrace (prefixWord ++ tailWord_224114) baseStart_224114 baseEnd_224114 := by
    simpa [prefixWord, tailWord_224114, baseEnd_224114] using wordTrace_append hprefix tailTrace_224114
  have hstable : (prefixWord ++ tailWord_224114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224114).length < 2 ^ (prefixWord ++ tailWord_224114).sum := by decide
  have hdescent : baseEnd_224114 < baseStart_224114 := by decide
  rcases family_descends (prefixWord ++ tailWord_224114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224155 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 12]
def baseStart_224155 : Nat := 118140960795 + 224155 * 2 ^ 59
def prefixEnd_224155 : Nat := 4983230072969 + 3 ^ 40 * 224155 * 2
def baseEnd_224155 : Nat := 76732837405783817487757

theorem tailTrace_224155 : CollatzResearch.WordTrace tailWord_224155 prefixEnd_224155 76732837405783817487757 := by
  unfold tailWord_224155
  simp only [CollatzResearch.WordTrace]
  refine ⟨8175604502932192471273919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5450403001954794980849279 8175604502932192471273919)
  ·
    refine ⟨12263406754398288706910879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8175604502932192471273919 12263406754398288706910879)
    ·
      refine ⟨18395110131597433060366319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12263406754398288706910879 18395110131597433060366319)
      ·
        refine ⟨27592665197396149590549479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18395110131597433060366319 27592665197396149590549479)
        ·
          refine ⟨41388997796094224385824219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27592665197396149590549479 41388997796094224385824219)
          ·
            refine ⟨62083496694141336578736329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41388997796094224385824219 62083496694141336578736329)
            ·
              refine ⟨46562622520606002434052247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62083496694141336578736329 46562622520606002434052247)
              ·
                refine ⟨69843933780909003651078371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46562622520606002434052247 69843933780909003651078371)
                ·
                  refine ⟨104765900671363505476617557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69843933780909003651078371 104765900671363505476617557)
                  ·
                    refine ⟨76732837405783817487757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 104765900671363505476617557 76732837405783817487757)
                    ·
                      rfl

theorem cell22_224155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_224155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224155 prefixEnd_224155 := by exact prefixLift 224155
  have htrace : WordTrace (prefixWord ++ tailWord_224155) baseStart_224155 baseEnd_224155 := by
    simpa [prefixWord, tailWord_224155, baseEnd_224155] using wordTrace_append hprefix tailTrace_224155
  have hstable : (prefixWord ++ tailWord_224155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224155).length < 2 ^ (prefixWord ++ tailWord_224155).sum := by decide
  have hdescent : baseEnd_224155 < baseStart_224155 := by decide
  rcases family_descends (prefixWord ++ tailWord_224155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224157 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_224157 : Nat := 118140960795 + 224157 * 2 ^ 59
def prefixEnd_224157 : Nat := 4983230072969 + 3 ^ 40 * 224157 * 2
def baseEnd_224157 : Nat := 76733522046656478937751

theorem tailTrace_224157 : CollatzResearch.WordTrace tailWord_224157 prefixEnd_224157 76733522046656478937751 := by
  unfold tailWord_224157
  simp only [CollatzResearch.WordTrace]
  refine ⟨8175677448924946812846725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5450451632616631208564483 8175677448924946812846725)
  ·
    refine ⟨1532939521673427527408761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8175677448924946812846725 1532939521673427527408761)
    ·
      refine ⟨1149704641255070645556571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1532939521673427527408761 1149704641255070645556571)
      ·
        refine ⟨1724556961882605968334857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149704641255070645556571 1724556961882605968334857)
        ·
          refine ⟨1293417721411954476251143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724556961882605968334857 1293417721411954476251143)
          ·
            refine ⟨1940126582117931714376715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293417721411954476251143 1940126582117931714376715)
            ·
              refine ⟨2910189873176897571565073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940126582117931714376715 2910189873176897571565073)
              ·
                refine ⟨2182642404882673178673805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910189873176897571565073 2182642404882673178673805)
                ·
                  refine ⟨818490901831002442002677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2182642404882673178673805 818490901831002442002677)
                  ·
                    refine ⟨76733522046656478937751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 818490901831002442002677 76733522046656478937751)
                    ·
                      rfl

theorem cell22_224157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_224157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224157 prefixEnd_224157 := by exact prefixLift 224157
  have htrace : WordTrace (prefixWord ++ tailWord_224157) baseStart_224157 baseEnd_224157 := by
    simpa [prefixWord, tailWord_224157, baseEnd_224157] using wordTrace_append hprefix tailTrace_224157
  have hstable : (prefixWord ++ tailWord_224157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224157).length < 2 ^ (prefixWord ++ tailWord_224157).sum := by decide
  have hdescent : baseEnd_224157 < baseStart_224157 := by decide
  rcases family_descends (prefixWord ++ tailWord_224157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224189 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_224189 : Nat := 118140960795 + 224189 * 2 ^ 59
def prefixEnd_224189 : Nat := 4983230072969 + 3 ^ 40 * 224189 * 2
def baseEnd_224189 : Nat := 76744476300619062137653

theorem tailTrace_224189 : CollatzResearch.WordTrace tailWord_224189 prefixEnd_224189 76744476300619062137653 := by
  unfold tailWord_224189
  simp only [CollatzResearch.WordTrace]
  refine ⟨8176844584809016278011621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5451229723206010852007747 8176844584809016278011621)
  ·
    refine ⟨1533158359651690552127179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8176844584809016278011621 1533158359651690552127179)
    ·
      refine ⟨2299737539477535828190769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533158359651690552127179 2299737539477535828190769)
      ·
        refine ⟨1724803154608151871143077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2299737539477535828190769 1724803154608151871143077)
        ·
          refine ⟨323400591489028475839327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1724803154608151871143077 323400591489028475839327)
          ·
            refine ⟨485100887233542713758991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323400591489028475839327 485100887233542713758991)
            ·
              refine ⟨727651330850314070638487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485100887233542713758991 727651330850314070638487)
              ·
                refine ⟨1091476996275471105957731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727651330850314070638487 1091476996275471105957731)
                ·
                  refine ⟨1637215494413206658936597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091476996275471105957731 1637215494413206658936597)
                  ·
                    refine ⟨76744476300619062137653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1637215494413206658936597 76744476300619062137653)
                    ·
                      rfl

theorem cell22_224189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_224189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224189 prefixEnd_224189 := by exact prefixLift 224189
  have htrace : WordTrace (prefixWord ++ tailWord_224189) baseStart_224189 baseEnd_224189 := by
    simpa [prefixWord, tailWord_224189, baseEnd_224189] using wordTrace_append hprefix tailTrace_224189
  have hstable : (prefixWord ++ tailWord_224189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224189).length < 2 ^ (prefixWord ++ tailWord_224189).sum := by decide
  have hdescent : baseEnd_224189 < baseStart_224189 := by decide
  rcases family_descends (prefixWord ++ tailWord_224189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224238 : List Nat := [4, 1, 2, 1, 5, 1, 2, 6]
def baseStart_224238 : Nat := 118140960795 + 224238 * 2 ^ 59
def prefixEnd_224238 : Nat := 4983230072969 + 3 ^ 40 * 224238 * 2
def baseEnd_224238 : Nat := 8529027777999918629167

theorem tailTrace_224238 : CollatzResearch.WordTrace tailWord_224238 prefixEnd_224238 8529027777999918629167 := by
  unfold tailWord_224238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022328970203937205818171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5452421174420998431030245 1022328970203937205818171)
  ·
    refine ⟨1533493455305905808727257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022328970203937205818171 1533493455305905808727257)
    ·
      refine ⟨1150120091479429356545443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1533493455305905808727257 1150120091479429356545443)
      ·
        refine ⟨1725180137219144034818165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150120091479429356545443 1725180137219144034818165)
        ·
          refine ⟨161735637864294753264203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1725180137219144034818165 161735637864294753264203)
          ·
            refine ⟨242603456796442129896305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161735637864294753264203 242603456796442129896305)
            ·
              refine ⟨181952592597331597422229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242603456796442129896305 181952592597331597422229)
              ·
                refine ⟨8529027777999918629167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181952592597331597422229 8529027777999918629167)
                ·
                  rfl

theorem cell22_224238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_224238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224238 prefixEnd_224238 := by exact prefixLift 224238
  have htrace : WordTrace (prefixWord ++ tailWord_224238) baseStart_224238 baseEnd_224238 := by
    simpa [prefixWord, tailWord_224238, baseEnd_224238] using wordTrace_append hprefix tailTrace_224238
  have hstable : (prefixWord ++ tailWord_224238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224238).length < 2 ^ (prefixWord ++ tailWord_224238).sum := by decide
  have hdescent : baseEnd_224238 < baseStart_224238 := by decide
  rcases family_descends (prefixWord ++ tailWord_224238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224244 : List Nat := [2, 6, 2, 1, 1, 2, 1, 3, 4]
def baseStart_224244 : Nat := 118140960795 + 224244 * 2 ^ 59
def prefixEnd_224244 : Nat := 4983230072969 + 3 ^ 40 * 224244 * 2
def baseEnd_224244 : Nat := 25587767974872417337495

theorem tailTrace_224244 : CollatzResearch.WordTrace tailWord_224244 prefixEnd_224244 25587767974872417337495 := by
  unfold tailWord_224244
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089425299804880335631893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5452567066406507114175857 4089425299804880335631893)
  ·
    refine ⟨191691810928353765732745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4089425299804880335631893 191691810928353765732745)
    ·
      refine ⟨143768858196265324299559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191691810928353765732745 143768858196265324299559)
      ·
        refine ⟨215653287294397986449339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143768858196265324299559 215653287294397986449339)
        ·
          refine ⟨323479930941596979674009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215653287294397986449339 323479930941596979674009)
          ·
            refine ⟨242609948206197734755507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323479930941596979674009 242609948206197734755507)
            ·
              refine ⟨363914922309296602133261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242609948206197734755507 363914922309296602133261)
              ·
                refine ⟨136468095865986225799973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363914922309296602133261 136468095865986225799973)
                ·
                  refine ⟨25587767974872417337495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136468095865986225799973 25587767974872417337495)
                  ·
                    rfl

theorem cell22_224244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_224244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224244 prefixEnd_224244 := by exact prefixLift 224244
  have htrace : WordTrace (prefixWord ++ tailWord_224244) baseStart_224244 baseEnd_224244 := by
    simpa [prefixWord, tailWord_224244, baseEnd_224244] using wordTrace_append hprefix tailTrace_224244
  have hstable : (prefixWord ++ tailWord_224244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224244).length < 2 ^ (prefixWord ++ tailWord_224244).sum := by decide
  have hdescent : baseEnd_224244 < baseStart_224244 := by decide
  rcases family_descends (prefixWord ++ tailWord_224244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224270 : List Nat := [4, 1, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_224270 : Nat := 118140960795 + 224270 * 2 ^ 59
def prefixEnd_224270 : Nat := 4983230072969 + 3 ^ 40 * 224270 * 2
def baseEnd_224270 : Nat := 76772204255961850862405

theorem tailTrace_224270 : CollatzResearch.WordTrace tailWord_224270 prefixEnd_224270 76772204255961850862405 := by
  unfold tailWord_224270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022474862189445888963783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5453199265010378074473509 1022474862189445888963783)
  ·
    refine ⟨1533712293284168833445675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022474862189445888963783 1533712293284168833445675)
    ·
      refine ⟨2300568439926253250168513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533712293284168833445675 2300568439926253250168513)
      ·
        refine ⟨1725426329944689937626385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2300568439926253250168513 1725426329944689937626385)
        ·
          refine ⟨1294069747458517453219789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1725426329944689937626385 1294069747458517453219789)
          ·
            refine ⟨485276155296944044957421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1294069747458517453219789 485276155296944044957421)
            ·
              refine ⟨181978558236354016859033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485276155296944044957421 181978558236354016859033)
              ·
                refine ⟨136483918677265512644275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181978558236354016859033 136483918677265512644275)
                ·
                  refine ⟨204725878015898268966413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136483918677265512644275 204725878015898268966413)
                  ·
                    refine ⟨76772204255961850862405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204725878015898268966413 76772204255961850862405)
                    ·
                      rfl

theorem cell22_224270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_224270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224270 prefixEnd_224270 := by exact prefixLift 224270
  have htrace : WordTrace (prefixWord ++ tailWord_224270) baseStart_224270 baseEnd_224270 := by
    simpa [prefixWord, tailWord_224270, baseEnd_224270] using wordTrace_append hprefix tailTrace_224270
  have hstable : (prefixWord ++ tailWord_224270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224270).length < 2 ^ (prefixWord ++ tailWord_224270).sum := by decide
  have hdescent : baseEnd_224270 < baseStart_224270 := by decide
  rcases family_descends (prefixWord ++ tailWord_224270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224313 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 1, 4]
def baseStart_224313 : Nat := 118140960795 + 224313 * 2 ^ 59
def prefixEnd_224313 : Nat := 4983230072969 + 3 ^ 40 * 224313 * 2
def baseEnd_224313 : Nat := 76786924034724072037273

theorem tailTrace_224313 : CollatzResearch.WordTrace tailWord_224313 prefixEnd_224313 76786924034724072037273 := by
  unfold tailWord_224313
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181367236359785455525593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5454244824239856970350395 8181367236359785455525593)
  ·
    refine ⟨6136025427269839091644195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8181367236359785455525593 6136025427269839091644195)
    ·
      refine ⟨9204038140904758637466293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6136025427269839091644195 9204038140904758637466293)
      ·
        refine ⟨862878575709821122262465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9204038140904758637466293 862878575709821122262465)
        ·
          refine ⟨647158931782365841696849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862878575709821122262465 647158931782365841696849)
          ·
            refine ⟨485369198836774381272637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647158931782365841696849 485369198836774381272637)
            ·
              refine ⟨182013449563790392977239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485369198836774381272637 182013449563790392977239)
              ·
                refine ⟨273020174345685589465859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182013449563790392977239 273020174345685589465859)
                ·
                  refine ⟨409530261518528384198789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273020174345685589465859 409530261518528384198789)
                  ·
                    refine ⟨76786924034724072037273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409530261518528384198789 76786924034724072037273)
                    ·
                      rfl

theorem cell22_224313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 4].length) (baseStart_224313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224313 prefixEnd_224313 := by exact prefixLift 224313
  have htrace : WordTrace (prefixWord ++ tailWord_224313) baseStart_224313 baseEnd_224313 := by
    simpa [prefixWord, tailWord_224313, baseEnd_224313] using wordTrace_append hprefix tailTrace_224313
  have hstable : (prefixWord ++ tailWord_224313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224313).length < 2 ^ (prefixWord ++ tailWord_224313).sum := by decide
  have hdescent : baseEnd_224313 < baseStart_224313 := by decide
  rcases family_descends (prefixWord ++ tailWord_224313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224388 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_224388 : Nat := 118140960795 + 224388 * 2 ^ 59
def prefixEnd_224388 : Nat := 4983230072969 + 3 ^ 40 * 224388 * 2
def baseEnd_224388 : Nat := 76812598067448876412043

theorem tailTrace_224388 : CollatzResearch.WordTrace tailWord_224388 prefixEnd_224388 76812598067448876412043 := by
  unfold tailWord_224388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092051355544036632252909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5456068474058715509670545 4092051355544036632252909)
  ·
    refine ⟨1534519258329013737094841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4092051355544036632252909 1534519258329013737094841)
    ·
      refine ⟨1150889443746760302821131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1534519258329013737094841 1150889443746760302821131)
      ·
        refine ⟨1726334165620140454231697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150889443746760302821131 1726334165620140454231697)
        ·
          refine ⟨1294750624215105340673773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1726334165620140454231697 1294750624215105340673773)
          ·
            refine ⟨485531484080664502752665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1294750624215105340673773 485531484080664502752665)
            ·
              refine ⟨364148613060498377064499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485531484080664502752665 364148613060498377064499)
              ·
                refine ⟨546222919590747565596749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364148613060498377064499 546222919590747565596749)
                ·
                  refine ⟨204833594846530337098781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546222919590747565596749 204833594846530337098781)
                  ·
                    refine ⟨76812598067448876412043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204833594846530337098781 76812598067448876412043)
                    ·
                      rfl

theorem cell22_224388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_224388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224388 prefixEnd_224388 := by exact prefixLift 224388
  have htrace : WordTrace (prefixWord ++ tailWord_224388) baseStart_224388 baseEnd_224388 := by
    simpa [prefixWord, tailWord_224388, baseEnd_224388] using wordTrace_append hprefix tailTrace_224388
  have hstable : (prefixWord ++ tailWord_224388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224388).length < 2 ^ (prefixWord ++ tailWord_224388).sum := by decide
  have hdescent : baseEnd_224388 < baseStart_224388 := by decide
  rcases family_descends (prefixWord ++ tailWord_224388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224431 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 1, 4]
def baseStart_224431 : Nat := 118140960795 + 224431 * 2 ^ 59
def prefixEnd_224431 : Nat := 4983230072969 + 3 ^ 40 * 224431 * 2
def baseEnd_224431 : Nat := 76827317846211097586911

theorem tailTrace_224431 : CollatzResearch.WordTrace tailWord_224431 prefixEnd_224431 76827317846211097586911 := by
  unfold tailWord_224431
  simp only [CollatzResearch.WordTrace]
  refine ⟨8185671049932291608321147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5457114033288194405547431 8185671049932291608321147)
  ·
    refine ⟨12278506574898437412481721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8185671049932291608321147 12278506574898437412481721)
    ·
      refine ⟨9208879931173828059361291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12278506574898437412481721 9208879931173828059361291)
      ·
        refine ⟨13813319896760742089041937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9208879931173828059361291 13813319896760742089041937)
        ·
          refine ⟨10359989922570556566781453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13813319896760742089041937 10359989922570556566781453)
          ·
            refine ⟨3884996220963958712543045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10359989922570556566781453 3884996220963958712543045)
            ·
              refine ⟨728436791430742258601821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3884996220963958712543045 728436791430742258601821)
              ·
                refine ⟨273163796786528346975683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 728436791430742258601821 273163796786528346975683)
                ·
                  refine ⟨409745695179792520463525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273163796786528346975683 409745695179792520463525)
                  ·
                    refine ⟨76827317846211097586911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409745695179792520463525 76827317846211097586911)
                    ·
                      rfl

theorem cell22_224431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_224431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224431 prefixEnd_224431 := by exact prefixLift 224431
  have htrace : WordTrace (prefixWord ++ tailWord_224431) baseStart_224431 baseEnd_224431 := by
    simpa [prefixWord, tailWord_224431, baseEnd_224431] using wordTrace_append hprefix tailTrace_224431
  have hstable : (prefixWord ++ tailWord_224431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224431).length < 2 ^ (prefixWord ++ tailWord_224431).sum := by decide
  have hdescent : baseEnd_224431 < baseStart_224431 := by decide
  rcases family_descends (prefixWord ++ tailWord_224431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224452 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 5]
def baseStart_224452 : Nat := 118140960795 + 224452 * 2 ^ 59
def prefixEnd_224452 : Nat := 4983230072969 + 3 ^ 40 * 224452 * 2
def baseEnd_224452 : Nat := 25611502191791347603949

theorem tailTrace_224452 : CollatzResearch.WordTrace tailWord_224452 prefixEnd_224452 25611502191791347603949 := by
  unfold tailWord_224452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093218491428106097417805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5457624655237474796557073 4093218491428106097417805)
  ·
    refine ⟨1534956934285539786531677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4093218491428106097417805 1534956934285539786531677)
    ·
      refine ⟨575608850357077419949379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1534956934285539786531677 575608850357077419949379)
      ·
        refine ⟨863413275535616129924069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575608850357077419949379 863413275535616129924069)
        ·
          refine ⟨161889989162928024360763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 863413275535616129924069 161889989162928024360763)
          ·
            refine ⟨242834983744392036541145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161889989162928024360763 242834983744392036541145)
            ·
              refine ⟨182126237808294027405859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242834983744392036541145 182126237808294027405859)
              ·
                refine ⟨273189356712441041108789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182126237808294027405859 273189356712441041108789)
                ·
                  refine ⟨25611502191791347603949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273189356712441041108789 25611502191791347603949)
                  ·
                    rfl

theorem cell22_224452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_224452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224452 prefixEnd_224452 := by exact prefixLift 224452
  have htrace : WordTrace (prefixWord ++ tailWord_224452) baseStart_224452 baseEnd_224452 := by
    simpa [prefixWord, tailWord_224452, baseEnd_224452] using wordTrace_append hprefix tailTrace_224452
  have hstable : (prefixWord ++ tailWord_224452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224452).length < 2 ^ (prefixWord ++ tailWord_224452).sum := by decide
  have hdescent : baseEnd_224452 < baseStart_224452 := by decide
  rcases family_descends (prefixWord ++ tailWord_224452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224459 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 1, 6]
def baseStart_224459 : Nat := 118140960795 + 224459 * 2 ^ 59
def prefixEnd_224459 : Nat := 4983230072969 + 3 ^ 40 * 224459 * 2
def baseEnd_224459 : Nat := 76836902818428357886825

theorem tailTrace_224459 : CollatzResearch.WordTrace tailWord_224459 prefixEnd_224459 76836902818428357886825 := by
  unfold tailWord_224459
  simp only [CollatzResearch.WordTrace]
  refine ⟨8186692293830852390340431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5457794862553901593560287 8186692293830852390340431)
  ·
    refine ⟨12280038440746278585510647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8186692293830852390340431 12280038440746278585510647)
    ·
      refine ⟨18420057661119417878265971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12280038440746278585510647 18420057661119417878265971)
      ·
        refine ⟨27630086491679126817398957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18420057661119417878265971 27630086491679126817398957)
        ·
          refine ⟨10361282434379672556524609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27630086491679126817398957 10361282434379672556524609)
          ·
            refine ⟨7770961825784754417393457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10361282434379672556524609 7770961825784754417393457)
            ·
              refine ⟨5828221369338565813045093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7770961825784754417393457 5828221369338565813045093)
              ·
                refine ⟨1092791506750981089945955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5828221369338565813045093 1092791506750981089945955)
                ·
                  refine ⟨1639187260126471634918933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092791506750981089945955 1639187260126471634918933)
                  ·
                    refine ⟨76836902818428357886825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1639187260126471634918933 76836902818428357886825)
                    ·
                      rfl

theorem cell22_224459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_224459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224459 prefixEnd_224459 := by exact prefixLift 224459
  have htrace : WordTrace (prefixWord ++ tailWord_224459) baseStart_224459 baseEnd_224459 := by
    simpa [prefixWord, tailWord_224459, baseEnd_224459] using wordTrace_append hprefix tailTrace_224459
  have hstable : (prefixWord ++ tailWord_224459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224459).length < 2 ^ (prefixWord ++ tailWord_224459).sum := by decide
  have hdescent : baseEnd_224459 < baseStart_224459 := by decide
  rcases family_descends (prefixWord ++ tailWord_224459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224493 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_224493 : Nat := 118140960795 + 224493 * 2 ^ 59
def prefixEnd_224493 : Nat := 4983230072969 + 3 ^ 40 * 224493 * 2
def baseEnd_224493 : Nat := 76848541713263602536721

theorem tailTrace_224493 : CollatzResearch.WordTrace tailWord_224493 prefixEnd_224493 76848541713263602536721 := by
  unfold tailWord_224493
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187932375707676197078133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5458621583805117464718755 8187932375707676197078133)
  ·
    refine ⟨767618660222594643476075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8187932375707676197078133 767618660222594643476075)
    ·
      refine ⟨1151427990333891965214113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 767618660222594643476075 1151427990333891965214113)
      ·
        refine ⟨863570992750418973910585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1151427990333891965214113 863570992750418973910585)
        ·
          refine ⟨647678244562814230432939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863570992750418973910585 647678244562814230432939)
          ·
            refine ⟨971517366844221345649409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647678244562814230432939 971517366844221345649409)
            ·
              refine ⟨728638025133166009237057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971517366844221345649409 728638025133166009237057)
              ·
                refine ⟨546478518849874506927793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728638025133166009237057 546478518849874506927793)
                ·
                  refine ⟨409858889137405880195845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546478518849874506927793 409858889137405880195845)
                  ·
                    refine ⟨76848541713263602536721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409858889137405880195845 76848541713263602536721)
                    ·
                      rfl

theorem cell22_224493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_224493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224493 prefixEnd_224493 := by exact prefixLift 224493
  have htrace : WordTrace (prefixWord ++ tailWord_224493) baseStart_224493 baseEnd_224493 := by
    simpa [prefixWord, tailWord_224493, baseEnd_224493] using wordTrace_append hprefix tailTrace_224493
  have hstable : (prefixWord ++ tailWord_224493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224493).length < 2 ^ (prefixWord ++ tailWord_224493).sum := by decide
  have hdescent : baseEnd_224493 < baseStart_224493 := by decide
  rcases family_descends (prefixWord ++ tailWord_224493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224495 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 2, 3]
def baseStart_224495 : Nat := 118140960795 + 224495 * 2 ^ 59
def prefixEnd_224495 : Nat := 4983230072969 + 3 ^ 40 * 224495 * 2
def baseEnd_224495 : Nat := 76849226354136263986715

theorem tailTrace_224495 : CollatzResearch.WordTrace tailWord_224495 prefixEnd_224495 76849226354136263986715 := by
  unfold tailWord_224495
  simp only [CollatzResearch.WordTrace]
  refine ⟨8188005321700430538650939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5458670214466953692433959 8188005321700430538650939)
  ·
    refine ⟨12282007982550645807976409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8188005321700430538650939 12282007982550645807976409)
    ·
      refine ⟨9211505986912984355982307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12282007982550645807976409 9211505986912984355982307)
      ·
        refine ⟨13817258980369476533973461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9211505986912984355982307 13817258980369476533973461)
        ·
          refine ⟨323842007352409606265003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13817258980369476533973461 323842007352409606265003)
          ·
            refine ⟨485763011028614409397505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323842007352409606265003 485763011028614409397505)
            ·
              refine ⟨364322258271460807048129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485763011028614409397505 364322258271460807048129)
              ·
                refine ⟨273241693703595605286097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364322258271460807048129 273241693703595605286097)
                ·
                  refine ⟨204931270277696703964573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273241693703595605286097 204931270277696703964573)
                  ·
                    refine ⟨76849226354136263986715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204931270277696703964573 76849226354136263986715)
                    ·
                      rfl

theorem cell22_224495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_224495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224495 prefixEnd_224495 := by exact prefixLift 224495
  have htrace : WordTrace (prefixWord ++ tailWord_224495) baseStart_224495 baseEnd_224495 := by
    simpa [prefixWord, tailWord_224495, baseEnd_224495] using wordTrace_append hprefix tailTrace_224495
  have hstable : (prefixWord ++ tailWord_224495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224495).length < 2 ^ (prefixWord ++ tailWord_224495).sum := by decide
  have hdescent : baseEnd_224495 < baseStart_224495 := by decide
  rcases family_descends (prefixWord ++ tailWord_224495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224508 : List Nat := [2, 2, 2, 1, 5, 2, 1, 7]
def baseStart_224508 : Nat := 118140960795 + 224508 * 2 ^ 59
def prefixEnd_224508 : Nat := 4983230072969 + 3 ^ 40 * 224508 * 2
def baseEnd_224508 : Nat := 8539297391089840379075

theorem tailTrace_224508 : CollatzResearch.WordTrace tailWord_224508 prefixEnd_224508 8539297391089840379075 := by
  unfold tailWord_224508
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094239735326666879437089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5458986313768889172582785 4094239735326666879437089)
  ·
    refine ⟨3070679801495000159577817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4094239735326666879437089 3070679801495000159577817)
    ·
      refine ⟨2303009851121250119683363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3070679801495000159577817 2303009851121250119683363)
      ·
        refine ⟨3454514776681875179525045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303009851121250119683363 3454514776681875179525045)
        ·
          refine ⟨323860760313925798080473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3454514776681875179525045 323860760313925798080473)
          ·
            refine ⟨242895570235444348560355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323860760313925798080473 242895570235444348560355)
            ·
              refine ⟨364343355353166522840533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242895570235444348560355 364343355353166522840533)
              ·
                refine ⟨8539297391089840379075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 364343355353166522840533 8539297391089840379075)
                ·
                  rfl

theorem cell22_224508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 7].length) (baseStart_224508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224508 prefixEnd_224508 := by exact prefixLift 224508
  have htrace : WordTrace (prefixWord ++ tailWord_224508) baseStart_224508 baseEnd_224508 := by
    simpa [prefixWord, tailWord_224508, baseEnd_224508] using wordTrace_append hprefix tailTrace_224508
  have hstable : (prefixWord ++ tailWord_224508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224508).length < 2 ^ (prefixWord ++ tailWord_224508).sum := by decide
  have hdescent : baseEnd_224508 < baseStart_224508 := by decide
  rcases family_descends (prefixWord ++ tailWord_224508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224523 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 3, 3]
def baseStart_224523 : Nat := 118140960795 + 224523 * 2 ^ 59
def prefixEnd_224523 : Nat := 4983230072969 + 3 ^ 40 * 224523 * 2
def baseEnd_224523 : Nat := 76858811326353524286629

theorem tailTrace_224523 : CollatzResearch.WordTrace tailWord_224523 prefixEnd_224523 76858811326353524286629 := by
  unfold tailWord_224523
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189026565598991320670223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5459351043732660880446815 8189026565598991320670223)
  ·
    refine ⟨12283539848398486981005335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8189026565598991320670223 12283539848398486981005335)
    ·
      refine ⟨18425309772597730471508003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12283539848398486981005335 18425309772597730471508003)
      ·
        refine ⟨27637964658896595707262005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18425309772597730471508003 27637964658896595707262005)
        ·
          refine ⟨2591059186771555847555813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27637964658896595707262005 2591059186771555847555813)
          ·
            refine ⟨485823597519666721416715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2591059186771555847555813 485823597519666721416715)
            ·
              refine ⟨728735396279500082125073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485823597519666721416715 728735396279500082125073)
              ·
                refine ⟨546551547209625061593805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728735396279500082125073 546551547209625061593805)
                ·
                  refine ⟨204956830203609398097677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546551547209625061593805 204956830203609398097677)
                  ·
                    refine ⟨76858811326353524286629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204956830203609398097677 76858811326353524286629)
                    ·
                      rfl

theorem cell22_224523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 3].length) (baseStart_224523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224523 prefixEnd_224523 := by exact prefixLift 224523
  have htrace : WordTrace (prefixWord ++ tailWord_224523) baseStart_224523 baseEnd_224523 := by
    simpa [prefixWord, tailWord_224523, baseEnd_224523] using wordTrace_append hprefix tailTrace_224523
  have hstable : (prefixWord ++ tailWord_224523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224523).length < 2 ^ (prefixWord ++ tailWord_224523).sum := by decide
  have hdescent : baseEnd_224523 < baseStart_224523 := by decide
  rcases family_descends (prefixWord ++ tailWord_224523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224540 : List Nat := [2, 2, 3, 1, 1, 1, 3, 5, 1, 3]
def baseStart_224540 : Nat := 118140960795 + 224540 * 2 ^ 59
def prefixEnd_224540 : Nat := 4983230072969 + 3 ^ 40 * 224540 * 2
def baseEnd_224540 : Nat := 76864630773771146611577

theorem tailTrace_224540 : CollatzResearch.WordTrace tailWord_224540 prefixEnd_224540 76864630773771146611577 := by
  unfold tailWord_224540
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094823303268701612019537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5459764404358268816026049 4094823303268701612019537)
  ·
    refine ⟨3071117477451526209014653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4094823303268701612019537 3071117477451526209014653)
    ·
      refine ⟨1151669054044322328380495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3071117477451526209014653 1151669054044322328380495)
      ·
        refine ⟨1727503581066483492570743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151669054044322328380495 1727503581066483492570743)
        ·
          refine ⟨2591255371599725238856115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727503581066483492570743 2591255371599725238856115)
          ·
            refine ⟨3886883057399587858284173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591255371599725238856115 3886883057399587858284173)
            ·
              refine ⟨1457581146524845446856565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3886883057399587858284173 1457581146524845446856565)
              ·
                refine ⟨136648232486704260642803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1457581146524845446856565 136648232486704260642803)
                ·
                  refine ⟨204972348730056390964205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136648232486704260642803 204972348730056390964205)
                  ·
                    refine ⟨76864630773771146611577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204972348730056390964205 76864630773771146611577)
                    ·
                      rfl

theorem cell22_224540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_224540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224540 prefixEnd_224540 := by exact prefixLift 224540
  have htrace : WordTrace (prefixWord ++ tailWord_224540) baseStart_224540 baseEnd_224540 := by
    simpa [prefixWord, tailWord_224540, baseEnd_224540] using wordTrace_append hprefix tailTrace_224540
  have hstable : (prefixWord ++ tailWord_224540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224540).length < 2 ^ (prefixWord ++ tailWord_224540).sum := by decide
  have hdescent : baseEnd_224540 < baseStart_224540 := by decide
  rcases family_descends (prefixWord ++ tailWord_224540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224557 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_224557 : Nat := 118140960795 + 224557 * 2 ^ 59
def prefixEnd_224557 : Nat := 4983230072969 + 3 ^ 40 * 224557 * 2
def baseEnd_224557 : Nat := 76870450221188768936525

theorem tailTrace_224557 : CollatzResearch.WordTrace tailWord_224557 prefixEnd_224557 76870450221188768936525 := by
  unfold tailWord_224557
  simp only [CollatzResearch.WordTrace]
  refine ⟨8190266647475815127407925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5460177764983876751605283 8190266647475815127407925)
  ·
    refine ⟨767837498200857668194493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8190266647475815127407925 767837498200857668194493)
    ·
      refine ⟨287939061825321625572935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 767837498200857668194493 287939061825321625572935)
      ·
        refine ⟨431908592737982438359403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287939061825321625572935 431908592737982438359403)
        ·
          refine ⟨647862889106973657539105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431908592737982438359403 647862889106973657539105)
          ·
            refine ⟨485897166830230243154329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647862889106973657539105 485897166830230243154329)
            ·
              refine ⟨364422875122672682365747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485897166830230243154329 364422875122672682365747)
              ·
                refine ⟨546634312684009023548621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364422875122672682365747 546634312684009023548621)
                ·
                  refine ⟨204987867256503383830733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546634312684009023548621 204987867256503383830733)
                  ·
                    refine ⟨76870450221188768936525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204987867256503383830733 76870450221188768936525)
                    ·
                      rfl

theorem cell22_224557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_224557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224557 prefixEnd_224557 := by exact prefixLift 224557
  have htrace : WordTrace (prefixWord ++ tailWord_224557) baseStart_224557 baseEnd_224557 := by
    simpa [prefixWord, tailWord_224557, baseEnd_224557] using wordTrace_append hprefix tailTrace_224557
  have hstable : (prefixWord ++ tailWord_224557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224557).length < 2 ^ (prefixWord ++ tailWord_224557).sum := by decide
  have hdescent : baseEnd_224557 < baseStart_224557 := by decide
  rcases family_descends (prefixWord ++ tailWord_224557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224583 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 1, 4]
def baseStart_224583 : Nat := 118140960795 + 224583 * 2 ^ 59
def prefixEnd_224583 : Nat := 4983230072969 + 3 ^ 40 * 224583 * 2
def baseEnd_224583 : Nat := 76879350552533367786445

theorem tailTrace_224583 : CollatzResearch.WordTrace tailWord_224583 prefixEnd_224583 76879350552533367786445 := by
  unfold tailWord_224583
  simp only [CollatzResearch.WordTrace]
  refine ⟨8191214945381621567854403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5460809963587747711902935 8191214945381621567854403)
  ·
    refine ⟨12286822418072432351781605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8191214945381621567854403 12286822418072432351781605)
    ·
      refine ⟨2303779203388581065959051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12286822418072432351781605 2303779203388581065959051)
      ·
        refine ⟨3455668805082871598938577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303779203388581065959051 3455668805082871598938577)
        ·
          refine ⟨2591751603812153699203933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3455668805082871598938577 2591751603812153699203933)
          ·
            refine ⟨971906851429557637201475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2591751603812153699203933 971906851429557637201475)
            ·
              refine ⟨1457860277144336455802213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971906851429557637201475 1457860277144336455802213)
              ·
                refine ⟨273348801964563085462915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1457860277144336455802213 273348801964563085462915)
                ·
                  refine ⟨410023202946844628194373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273348801964563085462915 410023202946844628194373)
                  ·
                    refine ⟨76879350552533367786445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 410023202946844628194373 76879350552533367786445)
                    ·
                      rfl

theorem cell22_224583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_224583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224583 prefixEnd_224583 := by exact prefixLift 224583
  have htrace : WordTrace (prefixWord ++ tailWord_224583) baseStart_224583 baseEnd_224583 := by
    simpa [prefixWord, tailWord_224583, baseEnd_224583] using wordTrace_append hprefix tailTrace_224583
  have hstable : (prefixWord ++ tailWord_224583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224583).length < 2 ^ (prefixWord ++ tailWord_224583).sum := by decide
  have hdescent : baseEnd_224583 < baseStart_224583 := by decide
  rcases family_descends (prefixWord ++ tailWord_224583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224613 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_224613 : Nat := 118140960795 + 224613 * 2 ^ 59
def prefixEnd_224613 : Nat := 4983230072969 + 3 ^ 40 * 224613 * 2
def baseEnd_224613 : Nat := 76889620165623289536353

theorem tailTrace_224613 : CollatzResearch.WordTrace tailWord_224613 prefixEnd_224613 76889620165623289536353 := by
  unfold tailWord_224613
  simp only [CollatzResearch.WordTrace]
  refine ⟨8192309135272936691446493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5461539423515291127630995 8192309135272936691446493)
  ·
    refine ⟨3072115925727351259292435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8192309135272936691446493 3072115925727351259292435)
    ·
      refine ⟨4608173888591026888938653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3072115925727351259292435 4608173888591026888938653)
      ·
        refine ⟨1728065208221635083351995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4608173888591026888938653 1728065208221635083351995)
        ·
          refine ⟨2592097812332452625027993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728065208221635083351995 2592097812332452625027993)
          ·
            refine ⟨1944073359249339468770995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2592097812332452625027993 1944073359249339468770995)
            ·
              refine ⟨2916110038874009203156493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944073359249339468770995 2916110038874009203156493)
              ·
                refine ⟨1093541264577753451183685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2916110038874009203156493 1093541264577753451183685)
                ·
                  refine ⟨205038987108328772096941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093541264577753451183685 205038987108328772096941)
                  ·
                    refine ⟨76889620165623289536353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205038987108328772096941 76889620165623289536353)
                    ·
                      rfl

theorem cell22_224613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_224613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224613 prefixEnd_224613 := by exact prefixLift 224613
  have htrace : WordTrace (prefixWord ++ tailWord_224613) baseStart_224613 baseEnd_224613 := by
    simpa [prefixWord, tailWord_224613, baseEnd_224613] using wordTrace_append hprefix tailTrace_224613
  have hstable : (prefixWord ++ tailWord_224613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224613).length < 2 ^ (prefixWord ++ tailWord_224613).sum := by decide
  have hdescent : baseEnd_224613 < baseStart_224613 := by decide
  rcases family_descends (prefixWord ++ tailWord_224613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224615 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 6]
def baseStart_224615 : Nat := 118140960795 + 224615 * 2 ^ 59
def prefixEnd_224615 : Nat := 4983230072969 + 3 ^ 40 * 224615 * 2
def baseEnd_224615 : Nat := 25630101602165316995449

theorem tailTrace_224615 : CollatzResearch.WordTrace tailWord_224615 prefixEnd_224615 25630101602165316995449 := by
  unfold tailWord_224615
  simp only [CollatzResearch.WordTrace]
  refine ⟨8192382081265691033019299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5461588054177127355346199 8192382081265691033019299)
  ·
    refine ⟨12288573121898536549528949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8192382081265691033019299 12288573121898536549528949)
    ·
      refine ⟨1152053730177987801518339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12288573121898536549528949 1152053730177987801518339)
      ·
        refine ⟨1728080595266981702277509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152053730177987801518339 1728080595266981702277509)
        ·
          refine ⟨324015111612559069177033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1728080595266981702277509 324015111612559069177033)
          ·
            refine ⟨243011333709419301882775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324015111612559069177033 243011333709419301882775)
            ·
              refine ⟨364517000564128952824163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243011333709419301882775 364517000564128952824163)
              ·
                refine ⟨546775500846193429236245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364517000564128952824163 546775500846193429236245)
                ·
                  refine ⟨25630101602165316995449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 546775500846193429236245 25630101602165316995449)
                  ·
                    rfl

theorem cell22_224615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 6].length) (baseStart_224615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224615 prefixEnd_224615 := by exact prefixLift 224615
  have htrace : WordTrace (prefixWord ++ tailWord_224615) baseStart_224615 baseEnd_224615 := by
    simpa [prefixWord, tailWord_224615, baseEnd_224615] using wordTrace_append hprefix tailTrace_224615
  have hstable : (prefixWord ++ tailWord_224615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224615).length < 2 ^ (prefixWord ++ tailWord_224615).sum := by decide
  have hdescent : baseEnd_224615 < baseStart_224615 := by decide
  rcases family_descends (prefixWord ++ tailWord_224615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224748 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_224748 : Nat := 118140960795 + 224748 * 2 ^ 59
def prefixEnd_224748 : Nat := 4983230072969 + 3 ^ 40 * 224748 * 2
def baseEnd_224748 : Nat := 76935833424527937410939

theorem tailTrace_224748 : CollatzResearch.WordTrace tailWord_224748 prefixEnd_224748 76935833424527937410939 := by
  unfold tailWord_224748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098616494891927373805449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5464821993189236498407265 4098616494891927373805449)
  ·
    refine ⟨3073962371168945530354087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4098616494891927373805449 3073962371168945530354087)
    ·
      refine ⟨4610943556753418295531131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3073962371168945530354087 4610943556753418295531131)
      ·
        refine ⟨6916415335130127443296697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610943556753418295531131 6916415335130127443296697)
        ·
          refine ⟨5187311501347595582472523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6916415335130127443296697 5187311501347595582472523)
          ·
            refine ⟨7780967252021393373708785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5187311501347595582472523 7780967252021393373708785)
            ·
              refine ⟨5835725439016045030281589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7780967252021393373708785 5835725439016045030281589)
              ·
                refine ⟨547099259907754221588899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5835725439016045030281589 547099259907754221588899)
                ·
                  refine ⟨820648889861631332383349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547099259907754221588899 820648889861631332383349)
                  ·
                    refine ⟨76935833424527937410939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 820648889861631332383349 76935833424527937410939)
                    ·
                      rfl

theorem cell22_224748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_224748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224748 prefixEnd_224748 := by exact prefixLift 224748
  have htrace : WordTrace (prefixWord ++ tailWord_224748) baseStart_224748 baseEnd_224748 := by
    simpa [prefixWord, tailWord_224748, baseEnd_224748] using wordTrace_append hprefix tailTrace_224748
  have hstable : (prefixWord ++ tailWord_224748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224748).length < 2 ^ (prefixWord ++ tailWord_224748).sum := by decide
  have hdescent : baseEnd_224748 < baseStart_224748 := by decide
  rcases family_descends (prefixWord ++ tailWord_224748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224765 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_224765 : Nat := 118140960795 + 224765 * 2 ^ 59
def prefixEnd_224765 : Nat := 4983230072969 + 3 ^ 40 * 224765 * 2
def baseEnd_224765 : Nat := 76941652871945559735887

theorem tailTrace_224765 : CollatzResearch.WordTrace tailWord_224765 prefixEnd_224765 76941652871945559735887 := by
  unfold tailWord_224765
  simp only [CollatzResearch.WordTrace]
  refine ⟨8197853030722266650979749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5465235353814844433986499 8197853030722266650979749)
  ·
    refine ⟨1537097443260424997058703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8197853030722266650979749 1537097443260424997058703)
    ·
      refine ⟨2305646164890637495588055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537097443260424997058703 2305646164890637495588055)
      ·
        refine ⟨3458469247335956243382083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2305646164890637495588055 3458469247335956243382083)
        ·
          refine ⟨5187703871003934365073125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3458469247335956243382083 5187703871003934365073125)
          ·
            refine ⟨972694475813237693451211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5187703871003934365073125 972694475813237693451211)
            ·
              refine ⟨1459041713719856540176817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972694475813237693451211 1459041713719856540176817)
              ·
                refine ⟨1094281285289892405132613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459041713719856540176817 1094281285289892405132613)
                ·
                  refine ⟨205177740991854825962365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1094281285289892405132613 205177740991854825962365)
                  ·
                    refine ⟨76941652871945559735887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205177740991854825962365 76941652871945559735887)
                    ·
                      rfl

theorem cell22_224765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_224765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224765 prefixEnd_224765 := by exact prefixLift 224765
  have htrace : WordTrace (prefixWord ++ tailWord_224765) baseStart_224765 baseEnd_224765 := by
    simpa [prefixWord, tailWord_224765, baseEnd_224765] using wordTrace_append hprefix tailTrace_224765
  have hstable : (prefixWord ++ tailWord_224765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224765).length < 2 ^ (prefixWord ++ tailWord_224765).sum := by decide
  have hdescent : baseEnd_224765 < baseStart_224765 := by decide
  rcases family_descends (prefixWord ++ tailWord_224765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224778 : List Nat := [3, 1, 2, 2, 2, 2, 10]
def baseStart_224778 : Nat := 118140960795 + 224778 * 2 ^ 59
def prefixEnd_224778 : Nat := 4983230072969 + 3 ^ 40 * 224778 * 2
def baseEnd_224778 : Nat := 2849855668059920709661

theorem tailTrace_224778 : CollatzResearch.WordTrace tailWord_224778 prefixEnd_224778 2849855668059920709661 := by
  unfold tailWord_224778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2049581794918792467800747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5465551453116779914135325 2049581794918792467800747)
  ·
    refine ⟨3074372692378188701701121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2049581794918792467800747 3074372692378188701701121)
    ·
      refine ⟨2305779519283641526275841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3074372692378188701701121 2305779519283641526275841)
      ·
        refine ⟨1729334639462731144706881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2305779519283641526275841 1729334639462731144706881)
        ·
          refine ⟨1297000979597048358530161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1729334639462731144706881 1297000979597048358530161)
          ·
            refine ⟨972750734697786268897621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297000979597048358530161 972750734697786268897621)
            ·
              refine ⟨2849855668059920709661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 972750734697786268897621 2849855668059920709661)
              ·
                rfl

theorem cell22_224778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 10].length) (baseStart_224778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224778 prefixEnd_224778 := by exact prefixLift 224778
  have htrace : WordTrace (prefixWord ++ tailWord_224778) baseStart_224778 baseEnd_224778 := by
    simpa [prefixWord, tailWord_224778, baseEnd_224778] using wordTrace_append hprefix tailTrace_224778
  have hstable : (prefixWord ++ tailWord_224778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224778).length < 2 ^ (prefixWord ++ tailWord_224778).sum := by decide
  have hdescent : baseEnd_224778 < baseStart_224778 := by decide
  rcases family_descends (prefixWord ++ tailWord_224778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224844 : List Nat := [2, 2, 1, 3, 1, 4, 1, 4, 1, 3]
def baseStart_224844 : Nat := 118140960795 + 224844 * 2 ^ 59
def prefixEnd_224844 : Nat := 4983230072969 + 3 ^ 40 * 224844 * 2
def baseEnd_224844 : Nat := 76968696186415687010645

theorem tailTrace_224844 : CollatzResearch.WordTrace tailWord_224844 prefixEnd_224844 76968696186415687010645 := by
  unfold tailWord_224844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100367198718031571552793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5467156264957375428737057 4100367198718031571552793)
  ·
    refine ⟨3075275399038523678664595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4100367198718031571552793 3075275399038523678664595)
    ·
      refine ⟨4612913098557785517996893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3075275399038523678664595 4612913098557785517996893)
      ·
        refine ⟨1729842411959169569248835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4612913098557785517996893 1729842411959169569248835)
        ·
          refine ⟨2594763617938754353873253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729842411959169569248835 2594763617938754353873253)
          ·
            refine ⟨486518178363516441351235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2594763617938754353873253 486518178363516441351235)
            ·
              refine ⟨729777267545274662026853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486518178363516441351235 729777267545274662026853)
              ·
                refine ⟨136833237664738999130035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 729777267545274662026853 136833237664738999130035)
                ·
                  refine ⟨205249856497108498695053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136833237664738999130035 205249856497108498695053)
                  ·
                    refine ⟨76968696186415687010645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205249856497108498695053 76968696186415687010645)
                    ·
                      rfl

theorem cell22_224844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_224844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224844 prefixEnd_224844 := by exact prefixLift 224844
  have htrace : WordTrace (prefixWord ++ tailWord_224844) baseStart_224844 baseEnd_224844 := by
    simpa [prefixWord, tailWord_224844, baseEnd_224844] using wordTrace_append hprefix tailTrace_224844
  have hstable : (prefixWord ++ tailWord_224844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224844).length < 2 ^ (prefixWord ++ tailWord_224844).sum := by decide
  have hdescent : baseEnd_224844 < baseStart_224844 := by decide
  rcases family_descends (prefixWord ++ tailWord_224844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224855 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 2, 5]
def baseStart_224855 : Nat := 118140960795 + 224855 * 2 ^ 59
def prefixEnd_224855 : Nat := 4983230072969 + 3 ^ 40 * 224855 * 2
def baseEnd_224855 : Nat := 76972461711215324985611

theorem tailTrace_224855 : CollatzResearch.WordTrace tailWord_224855 prefixEnd_224855 76972461711215324985611 := by
  unfold tailWord_224855
  simp only [CollatzResearch.WordTrace]
  refine ⟨8201135600396212021756019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5467423733597474681170679 8201135600396212021756019)
  ·
    refine ⟨12301703400594318032634029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8201135600396212021756019 12301703400594318032634029)
    ·
      refine ⟨4613138775222869262237761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12301703400594318032634029 4613138775222869262237761)
      ·
        refine ⟨3459854081417151946678321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4613138775222869262237761 3459854081417151946678321)
        ·
          refine ⟨2594890561062863960008741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3459854081417151946678321 2594890561062863960008741)
          ·
            refine ⟨486541980199286992501639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2594890561062863960008741 486541980199286992501639)
            ·
              refine ⟨729812970298930488752459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486541980199286992501639 729812970298930488752459)
              ·
                refine ⟨1094719455448395733128689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729812970298930488752459 1094719455448395733128689)
                ·
                  refine ⟨821039591586296799846517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1094719455448395733128689 821039591586296799846517)
                  ·
                    refine ⟨76972461711215324985611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 821039591586296799846517 76972461711215324985611)
                    ·
                      rfl

theorem cell22_224855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_224855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224855 prefixEnd_224855 := by exact prefixLift 224855
  have htrace : WordTrace (prefixWord ++ tailWord_224855) baseStart_224855 baseEnd_224855 := by
    simpa [prefixWord, tailWord_224855, baseEnd_224855] using wordTrace_append hprefix tailTrace_224855
  have hstable : (prefixWord ++ tailWord_224855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224855).length < 2 ^ (prefixWord ++ tailWord_224855).sum := by decide
  have hdescent : baseEnd_224855 < baseStart_224855 := by decide
  rcases family_descends (prefixWord ++ tailWord_224855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224861 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_224861 : Nat := 118140960795 + 224861 * 2 ^ 59
def prefixEnd_224861 : Nat := 4983230072969 + 3 ^ 40 * 224861 * 2
def baseEnd_224861 : Nat := 76974515633833309335593

theorem tailTrace_224861 : CollatzResearch.WordTrace tailWord_224861 prefixEnd_224861 76974515633833309335593 := by
  unfold tailWord_224861
  simp only [CollatzResearch.WordTrace]
  refine ⟨8201354438374475046474437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5467569625582983364316291 8201354438374475046474437)
  ·
    refine ⟨1537753957195214071213957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8201354438374475046474437 1537753957195214071213957)
    ·
      refine ⟨288328866974102638352617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1537753957195214071213957 288328866974102638352617)
      ·
        refine ⟨216246650230576978764463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288328866974102638352617 216246650230576978764463)
        ·
          refine ⟨324369975345865468146695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216246650230576978764463 324369975345865468146695)
          ·
            refine ⟨486554963018798202220043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324369975345865468146695 486554963018798202220043)
            ·
              refine ⟨729832444528197303330065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486554963018798202220043 729832444528197303330065)
              ·
                refine ⟨547374333396147977497549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729832444528197303330065 547374333396147977497549)
                ·
                  refine ⟨205265375023555491561581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547374333396147977497549 205265375023555491561581)
                  ·
                    refine ⟨76974515633833309335593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205265375023555491561581 76974515633833309335593)
                    ·
                      rfl

theorem cell22_224861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_224861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224861 prefixEnd_224861 := by exact prefixLift 224861
  have htrace : WordTrace (prefixWord ++ tailWord_224861) baseStart_224861 baseEnd_224861 := by
    simpa [prefixWord, tailWord_224861, baseEnd_224861] using wordTrace_append hprefix tailTrace_224861
  have hstable : (prefixWord ++ tailWord_224861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224861).length < 2 ^ (prefixWord ++ tailWord_224861).sum := by decide
  have hdescent : baseEnd_224861 < baseStart_224861 := by decide
  rcases family_descends (prefixWord ++ tailWord_224861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224883 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 2, 9]
def baseStart_224883 : Nat := 118140960795 + 224883 * 2 ^ 59
def prefixEnd_224883 : Nat := 4983230072969 + 3 ^ 40 * 224883 * 2
def baseEnd_224883 : Nat := 76982046683432585285525

theorem tailTrace_224883 : CollatzResearch.WordTrace tailWord_224883 prefixEnd_224883 76982046683432585285525 := by
  unfold tailWord_224883
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202156844294772803775303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5468104562863181869183535 8202156844294772803775303)
  ·
    refine ⟨12303235266442159205662955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8202156844294772803775303 12303235266442159205662955)
    ·
      refine ⟨18454852899663238808494433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12303235266442159205662955 18454852899663238808494433)
      ·
        refine ⟨13841139674747429106370825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18454852899663238808494433 13841139674747429106370825)
        ·
          refine ⟨10380854756060571829778119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13841139674747429106370825 10380854756060571829778119)
          ·
            refine ⟨15571282134090857744667179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10380854756060571829778119 15571282134090857744667179)
            ·
              refine ⟨23356923201136286617000769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15571282134090857744667179 23356923201136286617000769)
              ·
                refine ⟨17517692400852214962750577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23356923201136286617000769 17517692400852214962750577)
                ·
                  refine ⟨13138269300639161222062933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17517692400852214962750577 13138269300639161222062933)
                  ·
                    refine ⟨76982046683432585285525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 13138269300639161222062933 76982046683432585285525)
                    ·
                      rfl

theorem cell22_224883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_224883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224883 prefixEnd_224883 := by exact prefixLift 224883
  have htrace : WordTrace (prefixWord ++ tailWord_224883) baseStart_224883 baseEnd_224883 := by
    simpa [prefixWord, tailWord_224883, baseEnd_224883] using wordTrace_append hprefix tailTrace_224883
  have hstable : (prefixWord ++ tailWord_224883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224883).length < 2 ^ (prefixWord ++ tailWord_224883).sum := by decide
  have hdescent : baseEnd_224883 < baseStart_224883 := by decide
  rcases family_descends (prefixWord ++ tailWord_224883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224917 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_224917 : Nat := 118140960795 + 224917 * 2 ^ 59
def prefixEnd_224917 : Nat := 4983230072969 + 3 ^ 40 * 224917 * 2
def baseEnd_224917 : Nat := 76993685578267829935421

theorem tailTrace_224917 : CollatzResearch.WordTrace tailWord_224917 prefixEnd_224917 76993685578267829935421 := by
  unfold tailWord_224917
  simp only [CollatzResearch.WordTrace]
  refine ⟨8203396926171596610513005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5468931284114397740342003 8203396926171596610513005)
  ·
    refine ⟨3076273847314348728942377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8203396926171596610513005 3076273847314348728942377)
    ·
      refine ⟨2307205385485761546706783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3076273847314348728942377 2307205385485761546706783)
      ·
        refine ⟨3460808078228642320060175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307205385485761546706783 3460808078228642320060175)
        ·
          refine ⟨5191212117342963480090263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460808078228642320060175 5191212117342963480090263)
          ·
            refine ⟨7786818176014445220135395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191212117342963480090263 7786818176014445220135395)
            ·
              refine ⟨11680227264021667830203093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7786818176014445220135395 11680227264021667830203093)
              ·
                refine ⟨273755326500507839770385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11680227264021667830203093 273755326500507839770385)
                ·
                  refine ⟨205316494875380879827789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273755326500507839770385 205316494875380879827789)
                  ·
                    refine ⟨76993685578267829935421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205316494875380879827789 76993685578267829935421)
                    ·
                      rfl

theorem cell22_224917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_224917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224917 prefixEnd_224917 := by exact prefixLift 224917
  have htrace : WordTrace (prefixWord ++ tailWord_224917) baseStart_224917 baseEnd_224917 := by
    simpa [prefixWord, tailWord_224917, baseEnd_224917] using wordTrace_append hprefix tailTrace_224917
  have hstable : (prefixWord ++ tailWord_224917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224917).length < 2 ^ (prefixWord ++ tailWord_224917).sum := by decide
  have hdescent : baseEnd_224917 < baseStart_224917 := by decide
  rcases family_descends (prefixWord ++ tailWord_224917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224949 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_224949 : Nat := 118140960795 + 224949 * 2 ^ 59
def prefixEnd_224949 : Nat := 4983230072969 + 3 ^ 40 * 224949 * 2
def baseEnd_224949 : Nat := 77004639832230413135323

theorem tailTrace_224949 : CollatzResearch.WordTrace tailWord_224949 prefixEnd_224949 77004639832230413135323 := by
  unfold tailWord_224949
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204564062055666075677901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5469709374703777383785267 8204564062055666075677901)
  ·
    refine ⟨3076711523270874778379213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8204564062055666075677901 3076711523270874778379213)
    ·
      refine ⟨1153766821226578041892205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3076711523270874778379213 1153766821226578041892205)
      ·
        refine ⟨432662557959966765709577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1153766821226578041892205 432662557959966765709577)
        ·
          refine ⟨324496918469975074282183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432662557959966765709577 324496918469975074282183)
          ·
            refine ⟨486745377704962611423275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324496918469975074282183 486745377704962611423275)
            ·
              refine ⟨730118066557443917134913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486745377704962611423275 730118066557443917134913)
              ·
                refine ⟨547588549918082937851185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730118066557443917134913 547588549918082937851185)
                ·
                  refine ⟨410691412438562203388389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547588549918082937851185 410691412438562203388389)
                  ·
                    refine ⟨77004639832230413135323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 410691412438562203388389 77004639832230413135323)
                    ·
                      rfl

theorem cell22_224949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_224949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224949 prefixEnd_224949 := by exact prefixLift 224949
  have htrace : WordTrace (prefixWord ++ tailWord_224949) baseStart_224949 baseEnd_224949 := by
    simpa [prefixWord, tailWord_224949, baseEnd_224949] using wordTrace_append hprefix tailTrace_224949
  have hstable : (prefixWord ++ tailWord_224949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224949).length < 2 ^ (prefixWord ++ tailWord_224949).sum := by decide
  have hdescent : baseEnd_224949 < baseStart_224949 := by decide
  rcases family_descends (prefixWord ++ tailWord_224949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224960 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_224960 : Nat := 118140960795 + 224960 * 2 ^ 59
def prefixEnd_224960 : Nat := 4983230072969 + 3 ^ 40 * 224960 * 2
def baseEnd_224960 : Nat := 77008405357030051110289

theorem tailTrace_224960 : CollatzResearch.WordTrace tailWord_224960 prefixEnd_224960 77008405357030051110289 := by
  unfold tailWord_224960
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102482632507907477164167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5469976843343876636218889 4102482632507907477164167)
  ·
    refine ⟨6153723948761861215746251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4102482632507907477164167 6153723948761861215746251)
    ·
      refine ⟨9230585923142791823619377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6153723948761861215746251 9230585923142791823619377)
      ·
        refine ⟨6922939442357093867714533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9230585923142791823619377 6922939442357093867714533)
        ·
          refine ⟨1298051145441955100196475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6922939442357093867714533 1298051145441955100196475)
          ·
            refine ⟨1947076718162932650294713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298051145441955100196475 1947076718162932650294713)
            ·
              refine ⟨1460307538622199487721035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947076718162932650294713 1460307538622199487721035)
              ·
                refine ⟨2190461307933299231581553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460307538622199487721035 2190461307933299231581553)
                ·
                  refine ⟨1642845980949974423686165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2190461307933299231581553 1642845980949974423686165)
                  ·
                    refine ⟨77008405357030051110289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1642845980949974423686165 77008405357030051110289)
                    ·
                      rfl

theorem cell22_224960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_224960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_224960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_224960 prefixEnd_224960 := by exact prefixLift 224960
  have htrace : WordTrace (prefixWord ++ tailWord_224960) baseStart_224960 baseEnd_224960 := by
    simpa [prefixWord, tailWord_224960, baseEnd_224960] using wordTrace_append hprefix tailTrace_224960
  have hstable : (prefixWord ++ tailWord_224960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224960).length < 2 ^ (prefixWord ++ tailWord_224960).sum := by decide
  have hdescent : baseEnd_224960 < baseStart_224960 := by decide
  rcases family_descends (prefixWord ++ tailWord_224960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225052 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_225052 : Nat := 118140960795 + 225052 * 2 ^ 59
def prefixEnd_225052 : Nat := 4983230072969 + 3 ^ 40 * 225052 * 2
def baseEnd_225052 : Nat := 77039898837172477810007

theorem tailTrace_225052 : CollatzResearch.WordTrace tailWord_225052 prefixEnd_225052 77039898837172477810007 := by
  unfold tailWord_225052
  simp only [CollatzResearch.WordTrace]
  refine ⟨4104160390341257333338705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5472213853788343111118273 4104160390341257333338705)
  ·
    refine ⟨3078120292755943000004029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4104160390341257333338705 3078120292755943000004029)
    ·
      refine ⟨1154295109783478625001511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3078120292755943000004029 1154295109783478625001511)
      ·
        refine ⟨1731442664675217937502267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154295109783478625001511 1731442664675217937502267)
        ·
          refine ⟨2597163997012826906253401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731442664675217937502267 2597163997012826906253401)
          ·
            refine ⟨1947872997759620179690051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2597163997012826906253401 1947872997759620179690051)
            ·
              refine ⟨2921809496639430269535077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947872997759620179690051 2921809496639430269535077)
              ·
                refine ⟨547839280619893175537827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2921809496639430269535077 547839280619893175537827)
                ·
                  refine ⟨821758920929839763306741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547839280619893175537827 821758920929839763306741)
                  ·
                    refine ⟨77039898837172477810007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 821758920929839763306741 77039898837172477810007)
                    ·
                      rfl

theorem cell22_225052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_225052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225052 prefixEnd_225052 := by exact prefixLift 225052
  have htrace : WordTrace (prefixWord ++ tailWord_225052) baseStart_225052 baseEnd_225052 := by
    simpa [prefixWord, tailWord_225052, baseEnd_225052] using wordTrace_append hprefix tailTrace_225052
  have hstable : (prefixWord ++ tailWord_225052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225052).length < 2 ^ (prefixWord ++ tailWord_225052).sum := by decide
  have hdescent : baseEnd_225052 < baseStart_225052 := by decide
  rcases family_descends (prefixWord ++ tailWord_225052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225086 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_225086 : Nat := 118140960795 + 225086 * 2 ^ 59
def prefixEnd_225086 : Nat := 4983230072969 + 3 ^ 40 * 225086 * 2
def baseEnd_225086 : Nat := 77051537732007722459903

theorem tailTrace_225086 : CollatzResearch.WordTrace tailWord_225086 prefixEnd_225086 77051537732007722459903 := by
  unfold tailWord_225086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1026195107819917309176889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5473040575039558982276741 1026195107819917309176889)
  ·
    refine ⟨769646330864937981882667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1026195107819917309176889 769646330864937981882667)
    ·
      refine ⟨1154469496297406972824001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 769646330864937981882667 1154469496297406972824001)
      ·
        refine ⟨865852122223055229618001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1154469496297406972824001 865852122223055229618001)
        ·
          refine ⟨649389091667291422213501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865852122223055229618001 649389091667291422213501)
          ·
            refine ⟨243520909375234283330063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 649389091667291422213501 243520909375234283330063)
            ·
              refine ⟨365281364062851424995095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243520909375234283330063 365281364062851424995095)
              ·
                refine ⟨547922046094277137492643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365281364062851424995095 547922046094277137492643)
                ·
                  refine ⟨821883069141415706238965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547922046094277137492643 821883069141415706238965)
                  ·
                    refine ⟨77051537732007722459903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 821883069141415706238965 77051537732007722459903)
                    ·
                      rfl

theorem cell22_225086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_225086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225086 prefixEnd_225086 := by exact prefixLift 225086
  have htrace : WordTrace (prefixWord ++ tailWord_225086) baseStart_225086 baseEnd_225086 := by
    simpa [prefixWord, tailWord_225086, baseEnd_225086] using wordTrace_append hprefix tailTrace_225086
  have hstable : (prefixWord ++ tailWord_225086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225086).length < 2 ^ (prefixWord ++ tailWord_225086).sum := by decide
  have hdescent : baseEnd_225086 < baseStart_225086 := by decide
  rcases family_descends (prefixWord ++ tailWord_225086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225116 : List Nat := [2, 2, 4, 2, 3, 1, 8]
def baseStart_225116 : Nat := 118140960795 + 225116 * 2 ^ 59
def prefixEnd_225116 : Nat := 4983230072969 + 3 ^ 40 * 225116 * 2
def baseEnd_225116 : Nat := 2854141012781394229993

theorem tailTrace_225116 : CollatzResearch.WordTrace tailWord_225116 prefixEnd_225116 2854141012781394229993 := by
  unfold tailWord_225116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105327526225326798503601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5473770034967102398004801 4105327526225326798503601)
  ·
    refine ⟨3078995644668995098877701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4105327526225326798503601 3078995644668995098877701)
    ·
      refine ⟨577311683375436581039569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3078995644668995098877701 577311683375436581039569)
      ·
        refine ⟨432983762531577435779677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577311683375436581039569 432983762531577435779677)
        ·
          refine ⟨162368910949341538417379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432983762531577435779677 162368910949341538417379)
          ·
            refine ⟨243553366424012307626069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162368910949341538417379 243553366424012307626069)
            ·
              refine ⟨2854141012781394229993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 243553366424012307626069 2854141012781394229993)
              ·
                rfl

theorem cell22_225116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 8].length) (baseStart_225116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225116 prefixEnd_225116 := by exact prefixLift 225116
  have htrace : WordTrace (prefixWord ++ tailWord_225116) baseStart_225116 baseEnd_225116 := by
    simpa [prefixWord, tailWord_225116, baseEnd_225116] using wordTrace_append hprefix tailTrace_225116
  have hstable : (prefixWord ++ tailWord_225116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225116).length < 2 ^ (prefixWord ++ tailWord_225116).sum := by decide
  have hdescent : baseEnd_225116 < baseStart_225116 := by decide
  rcases family_descends (prefixWord ++ tailWord_225116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225127 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 7]
def baseStart_225127 : Nat := 118140960795 + 225127 * 2 ^ 59
def prefixEnd_225127 : Nat := 4983230072969 + 3 ^ 40 * 225127 * 2
def baseEnd_225127 : Nat := 25688524289965760728259

theorem tailTrace_225127 : CollatzResearch.WordTrace tailWord_225127 prefixEnd_225127 25688524289965760728259 := by
  unfold tailWord_225127
  simp only [CollatzResearch.WordTrace]
  refine ⟨8211056255410802475657635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5474037503607201650438423 8211056255410802475657635)
  ·
    refine ⟨12316584383116203713486453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8211056255410802475657635 12316584383116203713486453)
    ·
      refine ⟨1154679785917144098139355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12316584383116203713486453 1154679785917144098139355)
      ·
        refine ⟨1732019678875716147209033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154679785917144098139355 1732019678875716147209033)
        ·
          refine ⟨1299014759156787110406775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1732019678875716147209033 1299014759156787110406775)
          ·
            refine ⟨1948522138735180665610163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299014759156787110406775 1948522138735180665610163)
            ·
              refine ⟨2922783208102770998415245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948522138735180665610163 2922783208102770998415245)
              ·
                refine ⟨1096043703038539124405717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2922783208102770998415245 1096043703038539124405717)
                ·
                  refine ⟨25688524289965760728259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1096043703038539124405717 25688524289965760728259)
                  ·
                    rfl

theorem cell22_225127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 7].length) (baseStart_225127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225127 prefixEnd_225127 := by exact prefixLift 225127
  have htrace : WordTrace (prefixWord ++ tailWord_225127) baseStart_225127 baseEnd_225127 := by
    simpa [prefixWord, tailWord_225127, baseEnd_225127] using wordTrace_append hprefix tailTrace_225127
  have hstable : (prefixWord ++ tailWord_225127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225127).length < 2 ^ (prefixWord ++ tailWord_225127).sum := by decide
  have hdescent : baseEnd_225127 < baseStart_225127 := by decide
  rcases family_descends (prefixWord ++ tailWord_225127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225182 : List Nat := [4, 3, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_225182 : Nat := 118140960795 + 225182 * 2 ^ 59
def prefixEnd_225182 : Nat := 4983230072969 + 3 ^ 40 * 225182 * 2
def baseEnd_225182 : Nat := 77084400493895472059609

theorem tailTrace_225182 : CollatzResearch.WordTrace tailWord_225182 prefixEnd_225182 77084400493895472059609 := by
  unfold tailWord_225182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1026632783776443358613725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5475374846807697912606533 1026632783776443358613725)
  ·
    refine ⟨384987293916166259480147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1026632783776443358613725 384987293916166259480147)
    ·
      refine ⟨577480940874249389220221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384987293916166259480147 577480940874249389220221)
      ·
        refine ⟨216555352827843520957583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577480940874249389220221 216555352827843520957583)
        ·
          refine ⟨324833029241765281436375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216555352827843520957583 324833029241765281436375)
          ·
            refine ⟨487249543862647922154563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324833029241765281436375 487249543862647922154563)
            ·
              refine ⟨730874315793971883231845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487249543862647922154563 730874315793971883231845)
              ·
                refine ⟨137038934211369728105971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730874315793971883231845 137038934211369728105971)
                ·
                  refine ⟨205558401317054592158957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137038934211369728105971 205558401317054592158957)
                  ·
                    refine ⟨77084400493895472059609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205558401317054592158957 77084400493895472059609)
                    ·
                      rfl

theorem cell22_225182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_225182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225182 prefixEnd_225182 := by exact prefixLift 225182
  have htrace : WordTrace (prefixWord ++ tailWord_225182) baseStart_225182 baseEnd_225182 := by
    simpa [prefixWord, tailWord_225182, baseEnd_225182] using wordTrace_append hprefix tailTrace_225182
  have hstable : (prefixWord ++ tailWord_225182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225182).length < 2 ^ (prefixWord ++ tailWord_225182).sum := by decide
  have hdescent : baseEnd_225182 < baseStart_225182 := by decide
  rcases family_descends (prefixWord ++ tailWord_225182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225187 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 5, 5]
def baseStart_225187 : Nat := 118140960795 + 225187 * 2 ^ 59
def prefixEnd_225187 : Nat := 4983230072969 + 3 ^ 40 * 225187 * 2
def baseEnd_225187 : Nat := 77086112096077125684593

theorem tailTrace_225187 : CollatzResearch.WordTrace tailWord_225187 prefixEnd_225187 77086112096077125684593 := by
  unfold tailWord_225187
  simp only [CollatzResearch.WordTrace]
  refine ⟨8213244635193432722841815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5475496423462288481894543 8213244635193432722841815)
  ·
    refine ⟨12319866952790149084262723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8213244635193432722841815 12319866952790149084262723)
    ·
      refine ⟨18479800429185223626394085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12319866952790149084262723 18479800429185223626394085)
      ·
        refine ⟨3464962580472229429948891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18479800429185223626394085 3464962580472229429948891)
        ·
          refine ⟨5197443870708344144923337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464962580472229429948891 5197443870708344144923337)
          ·
            refine ⟨3898082903031258108692503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5197443870708344144923337 3898082903031258108692503)
            ·
              refine ⟨5847124354546887163038755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898082903031258108692503 5847124354546887163038755)
              ·
                refine ⟨8770686531820330744558133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5847124354546887163038755 8770686531820330744558133)
                ·
                  refine ⟨822251862358156007302325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8770686531820330744558133 822251862358156007302325)
                  ·
                    refine ⟨77086112096077125684593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 822251862358156007302325 77086112096077125684593)
                    ·
                      rfl

theorem cell22_225187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_225187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225187 prefixEnd_225187 := by exact prefixLift 225187
  have htrace : WordTrace (prefixWord ++ tailWord_225187) baseStart_225187 baseEnd_225187 := by
    simpa [prefixWord, tailWord_225187, baseEnd_225187] using wordTrace_append hprefix tailTrace_225187
  have hstable : (prefixWord ++ tailWord_225187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225187).length < 2 ^ (prefixWord ++ tailWord_225187).sum := by decide
  have hdescent : baseEnd_225187 < baseStart_225187 := by decide
  rcases family_descends (prefixWord ++ tailWord_225187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225255 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 2, 3]
def baseStart_225255 : Nat := 118140960795 + 225255 * 2 ^ 59
def prefixEnd_225255 : Nat := 4983230072969 + 3 ^ 40 * 225255 * 2
def baseEnd_225255 : Nat := 77109389885747614984385

theorem tailTrace_225255 : CollatzResearch.WordTrace tailWord_225255 prefixEnd_225255 77109389885747614984385 := by
  unfold tailWord_225255
  simp only [CollatzResearch.WordTrace]
  refine ⟨8215724798947080336317219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5477149865964720224211479 8215724798947080336317219)
  ·
    refine ⟨12323587198420620504475829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8215724798947080336317219 12323587198420620504475829)
    ·
      refine ⟨1155336299851933172294609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12323587198420620504475829 1155336299851933172294609)
      ·
        refine ⟨866502224888949879220957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1155336299851933172294609 866502224888949879220957)
        ·
          refine ⟨324938334333356204707859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 866502224888949879220957 324938334333356204707859)
          ·
            refine ⟨487407501500034307061789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324938334333356204707859 487407501500034307061789)
            ·
              refine ⟨182777813062512865148171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 487407501500034307061789 182777813062512865148171)
              ·
                refine ⟨274166719593769297722257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182777813062512865148171 274166719593769297722257)
                ·
                  refine ⟨205625039695326973291693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274166719593769297722257 205625039695326973291693)
                  ·
                    refine ⟨77109389885747614984385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205625039695326973291693 77109389885747614984385)
                    ·
                      rfl

theorem cell22_225255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_225255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225255 prefixEnd_225255 := by exact prefixLift 225255
  have htrace : WordTrace (prefixWord ++ tailWord_225255) baseStart_225255 baseEnd_225255 := by
    simpa [prefixWord, tailWord_225255, baseEnd_225255] using wordTrace_append hprefix tailTrace_225255
  have hstable : (prefixWord ++ tailWord_225255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225255).length < 2 ^ (prefixWord ++ tailWord_225255).sum := by decide
  have hdescent : baseEnd_225255 < baseStart_225255 := by decide
  rcases family_descends (prefixWord ++ tailWord_225255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225339 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 1, 5]
def baseStart_225339 : Nat := 118140960795 + 225339 * 2 ^ 59
def prefixEnd_225339 : Nat := 4983230072969 + 3 ^ 40 * 225339 * 2
def baseEnd_225339 : Nat := 77138144802399395884127

theorem tailTrace_225339 : CollatzResearch.WordTrace tailWord_225339 prefixEnd_225339 77138144802399395884127 := by
  unfold tailWord_225339
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218788530642762682375071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5479192353761841788250047 8218788530642762682375071)
  ·
    refine ⟨12328182795964144023562607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8218788530642762682375071 12328182795964144023562607)
    ·
      refine ⟨18492274193946216035343911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12328182795964144023562607 18492274193946216035343911)
      ·
        refine ⟨27738411290919324053015867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18492274193946216035343911 27738411290919324053015867)
        ·
          refine ⟨41607616936378986079523801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27738411290919324053015867 41607616936378986079523801)
          ·
            refine ⟨31205712702284239559642851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41607616936378986079523801 31205712702284239559642851)
            ·
              refine ⟨46808569053426359339464277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31205712702284239559642851 46808569053426359339464277)
              ·
                refine ⟨548537918594840148509347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46808569053426359339464277 548537918594840148509347)
                ·
                  refine ⟨822806877892260222764021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548537918594840148509347 822806877892260222764021)
                  ·
                    refine ⟨77138144802399395884127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 822806877892260222764021 77138144802399395884127)
                    ·
                      rfl

theorem cell22_225339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 5].length) (baseStart_225339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225339 prefixEnd_225339 := by exact prefixLift 225339
  have htrace : WordTrace (prefixWord ++ tailWord_225339) baseStart_225339 baseEnd_225339 := by
    simpa [prefixWord, tailWord_225339, baseEnd_225339] using wordTrace_append hprefix tailTrace_225339
  have hstable : (prefixWord ++ tailWord_225339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225339).length < 2 ^ (prefixWord ++ tailWord_225339).sum := by decide
  have hdescent : baseEnd_225339 < baseStart_225339 := by decide
  rcases family_descends (prefixWord ++ tailWord_225339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225354 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_225354 : Nat := 118140960795 + 225354 * 2 ^ 59
def prefixEnd_225354 : Nat := 4983230072969 + 3 ^ 40 * 225354 * 2
def baseEnd_225354 : Nat := 77143279608944356759081

theorem tailTrace_225354 : CollatzResearch.WordTrace tailWord_225354 prefixEnd_225354 77143279608944356759081 := by
  unfold tailWord_225354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2054833906397105061042779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5479557083725613496114077 2054833906397105061042779)
  ·
    refine ⟨3082250859595657591564169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2054833906397105061042779 3082250859595657591564169)
    ·
      refine ⟨2311688144696743193673127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3082250859595657591564169 2311688144696743193673127)
      ·
        refine ⟨3467532217045114790509691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311688144696743193673127 3467532217045114790509691)
        ·
          refine ⟨5201298325567672185764537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467532217045114790509691 5201298325567672185764537)
          ·
            refine ⟨3900973744175754139323403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5201298325567672185764537 3900973744175754139323403)
            ·
              refine ⟨5851460616263631208985105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900973744175754139323403 5851460616263631208985105)
              ·
                refine ⟨4388595462197723406738829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5851460616263631208985105 4388595462197723406738829)
                ·
                  refine ⟨1645723298324146277527061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4388595462197723406738829 1645723298324146277527061)
                  ·
                    refine ⟨77143279608944356759081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1645723298324146277527061 77143279608944356759081)
                    ·
                      rfl

theorem cell22_225354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_225354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225354 prefixEnd_225354 := by exact prefixLift 225354
  have htrace : WordTrace (prefixWord ++ tailWord_225354) baseStart_225354 baseEnd_225354 := by
    simpa [prefixWord, tailWord_225354, baseEnd_225354] using wordTrace_append hprefix tailTrace_225354
  have hstable : (prefixWord ++ tailWord_225354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225354).length < 2 ^ (prefixWord ++ tailWord_225354).sum := by decide
  have hdescent : baseEnd_225354 < baseStart_225354 := by decide
  rcases family_descends (prefixWord ++ tailWord_225354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225356 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_225356 : Nat := 118140960795 + 225356 * 2 ^ 59
def prefixEnd_225356 : Nat := 4983230072969 + 3 ^ 40 * 225356 * 2
def baseEnd_225356 : Nat := 77143964249817018209075

theorem tailTrace_225356 : CollatzResearch.WordTrace tailWord_225356 prefixEnd_225356 77143964249817018209075 := by
  unfold tailWord_225356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109704285790587292871961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5479605714387449723829281 4109704285790587292871961)
  ·
    refine ⟨3082278214342940469653971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4109704285790587292871961 3082278214342940469653971)
    ·
      refine ⟨4623417321514410704480957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3082278214342940469653971 4623417321514410704480957)
      ·
        refine ⟨1733781495567904014180359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4623417321514410704480957 1733781495567904014180359)
        ·
          refine ⟨2600672243351856021270539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733781495567904014180359 2600672243351856021270539)
          ·
            refine ⟨3901008365027784031905809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600672243351856021270539 3901008365027784031905809)
            ·
              refine ⟨2925756273770838023929357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901008365027784031905809 2925756273770838023929357)
              ·
                refine ⟨1097158602664064258973509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2925756273770838023929357 1097158602664064258973509)
                ·
                  refine ⟨205717237999512048557533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097158602664064258973509 205717237999512048557533)
                  ·
                    refine ⟨77143964249817018209075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205717237999512048557533 77143964249817018209075)
                    ·
                      rfl

theorem cell22_225356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_225356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225356 prefixEnd_225356 := by exact prefixLift 225356
  have htrace : WordTrace (prefixWord ++ tailWord_225356) baseStart_225356 baseEnd_225356 := by
    simpa [prefixWord, tailWord_225356, baseEnd_225356] using wordTrace_append hprefix tailTrace_225356
  have hstable : (prefixWord ++ tailWord_225356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225356).length < 2 ^ (prefixWord ++ tailWord_225356).sum := by decide
  have hdescent : baseEnd_225356 < baseStart_225356 := by decide
  rcases family_descends (prefixWord ++ tailWord_225356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225358 : List Nat := [4, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_225358 : Nat := 118140960795 + 225358 * 2 ^ 59
def prefixEnd_225358 : Nat := 4983230072969 + 3 ^ 40 * 225358 * 2
def baseEnd_225358 : Nat := 25714882963563226553023

theorem tailTrace_225358 : CollatzResearch.WordTrace tailWord_225358 prefixEnd_225358 25714882963563226553023 := by
  unfold tailWord_225358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027435189696741115914591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5479654345049285951544485 1027435189696741115914591)
  ·
    refine ⟨1541152784545111673871887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1027435189696741115914591 1541152784545111673871887)
    ·
      refine ⟨2311729176817667510807831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541152784545111673871887 2311729176817667510807831)
      ·
        refine ⟨3467593765226501266211747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311729176817667510807831 3467593765226501266211747)
        ·
          refine ⟨5201390647839751899317621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467593765226501266211747 5201390647839751899317621)
          ·
            refine ⟨487630373234976740561027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5201390647839751899317621 487630373234976740561027)
            ·
              refine ⟨731445559852465110841541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487630373234976740561027 731445559852465110841541)
              ·
                refine ⟨137146042472337208282789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 731445559852465110841541 137146042472337208282789)
                ·
                  refine ⟨25714882963563226553023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137146042472337208282789 25714882963563226553023)
                  ·
                    rfl

theorem cell22_225358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_225358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225358 prefixEnd_225358 := by exact prefixLift 225358
  have htrace : WordTrace (prefixWord ++ tailWord_225358) baseStart_225358 baseEnd_225358 := by
    simpa [prefixWord, tailWord_225358, baseEnd_225358] using wordTrace_append hprefix tailTrace_225358
  have hstable : (prefixWord ++ tailWord_225358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225358).length < 2 ^ (prefixWord ++ tailWord_225358).sum := by decide
  have hdescent : baseEnd_225358 < baseStart_225358 := by decide
  rcases family_descends (prefixWord ++ tailWord_225358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225373 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_225373 : Nat := 118140960795 + 225373 * 2 ^ 59
def prefixEnd_225373 : Nat := 4983230072969 + 3 ^ 40 * 225373 * 2
def baseEnd_225373 : Nat := 77149783697234640534023

theorem tailTrace_225373 : CollatzResearch.WordTrace tailWord_225373 prefixEnd_225373 77149783697234640534023 := by
  unfold tailWord_225373
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220028612519586489112773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5480019075013057659408515 8220028612519586489112773)
  ·
    refine ⟨1541255364847422466708645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8220028612519586489112773 1541255364847422466708645)
    ·
      refine ⟨288985380908891712507871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1541255364847422466708645 288985380908891712507871)
      ·
        refine ⟨433478071363337568761807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288985380908891712507871 433478071363337568761807)
        ·
          refine ⟨650217107045006353142711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433478071363337568761807 650217107045006353142711)
          ·
            refine ⟨975325660567509529714067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650217107045006353142711 975325660567509529714067)
            ·
              refine ⟨1462988490851264294571101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975325660567509529714067 1462988490851264294571101)
              ·
                refine ⟨548620684069224110464163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1462988490851264294571101 548620684069224110464163)
                ·
                  refine ⟨822931026103836165696245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548620684069224110464163 822931026103836165696245)
                  ·
                    refine ⟨77149783697234640534023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 822931026103836165696245 77149783697234640534023)
                    ·
                      rfl

theorem cell22_225373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_225373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225373 prefixEnd_225373 := by exact prefixLift 225373
  have htrace : WordTrace (prefixWord ++ tailWord_225373) baseStart_225373 baseEnd_225373 := by
    simpa [prefixWord, tailWord_225373, baseEnd_225373] using wordTrace_append hprefix tailTrace_225373
  have hstable : (prefixWord ++ tailWord_225373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225373).length < 2 ^ (prefixWord ++ tailWord_225373).sum := by decide
  have hdescent : baseEnd_225373 < baseStart_225373 := by decide
  rcases family_descends (prefixWord ++ tailWord_225373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225388 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_225388 : Nat := 118140960795 + 225388 * 2 ^ 59
def prefixEnd_225388 : Nat := 4983230072969 + 3 ^ 40 * 225388 * 2
def baseEnd_225388 : Nat := 77154918503779601408977

theorem tailTrace_225388 : CollatzResearch.WordTrace tailWord_225388 prefixEnd_225388 77154918503779601408977 := by
  unfold tailWord_225388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4110287853732622025454409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5480383804976829367272545 4110287853732622025454409)
  ·
    refine ⟨3082715890299466519090807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4110287853732622025454409 3082715890299466519090807)
    ·
      refine ⟨4624073835449199778636211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3082715890299466519090807 4624073835449199778636211)
      ·
        refine ⟨6936110753173799667954317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4624073835449199778636211 6936110753173799667954317)
        ·
          refine ⟨2601041532440174875482869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6936110753173799667954317 2601041532440174875482869)
          ·
            refine ⟨243847643666266394576519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2601041532440174875482869 243847643666266394576519)
            ·
              refine ⟨365771465499399591864779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243847643666266394576519 365771465499399591864779)
              ·
                refine ⟨548657198249099387797169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365771465499399591864779 548657198249099387797169)
                ·
                  refine ⟨411492898686824540847877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548657198249099387797169 411492898686824540847877)
                  ·
                    refine ⟨77154918503779601408977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 411492898686824540847877 77154918503779601408977)
                    ·
                      rfl

theorem cell22_225388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_225388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225388 prefixEnd_225388 := by exact prefixLift 225388
  have htrace : WordTrace (prefixWord ++ tailWord_225388) baseStart_225388 baseEnd_225388 := by
    simpa [prefixWord, tailWord_225388, baseEnd_225388] using wordTrace_append hprefix tailTrace_225388
  have hstable : (prefixWord ++ tailWord_225388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225388).length < 2 ^ (prefixWord ++ tailWord_225388).sum := by decide
  have hdescent : baseEnd_225388 < baseStart_225388 := by decide
  rcases family_descends (prefixWord ++ tailWord_225388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225418 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_225418 : Nat := 118140960795 + 225418 * 2 ^ 59
def prefixEnd_225418 : Nat := 4983230072969 + 3 ^ 40 * 225418 * 2
def baseEnd_225418 : Nat := 77165188116869523158885

theorem tailTrace_225418 : CollatzResearch.WordTrace tailWord_225418 prefixEnd_225418 77165188116869523158885 := by
  unfold tailWord_225418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055417474339139793625227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5481113264904372783000605 2055417474339139793625227)
  ·
    refine ⟨3083126211508709690437841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2055417474339139793625227 3083126211508709690437841)
    ·
      refine ⟨2312344658631532267828381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3083126211508709690437841 2312344658631532267828381)
      ·
        refine ⟨867129246986824600435643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2312344658631532267828381 867129246986824600435643)
        ·
          refine ⟨1300693870480236900653465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867129246986824600435643 1300693870480236900653465)
          ·
            refine ⟨975520402860177675490099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1300693870480236900653465 975520402860177675490099)
            ·
              refine ⟨1463280604290266513235149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975520402860177675490099 1463280604290266513235149)
              ·
                refine ⟨548730226608849942463181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1463280604290266513235149 548730226608849942463181)
                ·
                  refine ⟨205773834978318728423693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548730226608849942463181 205773834978318728423693)
                  ·
                    refine ⟨77165188116869523158885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205773834978318728423693 77165188116869523158885)
                    ·
                      rfl

theorem cell22_225418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_225418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225418 prefixEnd_225418 := by exact prefixLift 225418
  have htrace : WordTrace (prefixWord ++ tailWord_225418) baseStart_225418 baseEnd_225418 := by
    simpa [prefixWord, tailWord_225418, baseEnd_225418] using wordTrace_append hprefix tailTrace_225418
  have hstable : (prefixWord ++ tailWord_225418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225418).length < 2 ^ (prefixWord ++ tailWord_225418).sum := by decide
  have hdescent : baseEnd_225418 < baseStart_225418 := by decide
  rcases family_descends (prefixWord ++ tailWord_225418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225553 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 5, 3]
def baseStart_225553 : Nat := 118140960795 + 225553 * 2 ^ 59
def prefixEnd_225553 : Nat := 4983230072969 + 3 ^ 40 * 225553 * 2
def baseEnd_225553 : Nat := 77211401375774171033471

theorem tailTrace_225553 : CollatzResearch.WordTrace tailWord_225553 prefixEnd_225553 77211401375774171033471 := by
  unfold tailWord_225553
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226593751867477230665313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5484395834578318153776875 8226593751867477230665313)
  ·
    refine ⟨6169945313900607922998985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8226593751867477230665313 6169945313900607922998985)
    ·
      refine ⟨4627458985425455942249239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6169945313900607922998985 4627458985425455942249239)
      ·
        refine ⟨6941188478138183913373859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627458985425455942249239 6941188478138183913373859)
        ·
          refine ⟨10411782717207275870060789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6941188478138183913373859 10411782717207275870060789)
          ·
            refine ⟨976104629738182112818199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10411782717207275870060789 976104629738182112818199)
            ·
              refine ⟨1464156944607273169227299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976104629738182112818199 1464156944607273169227299)
              ·
                refine ⟨2196235416910909753840949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464156944607273169227299 2196235416910909753840949)
                ·
                  refine ⟨205897070335397789422589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2196235416910909753840949 205897070335397789422589)
                  ·
                    refine ⟨77211401375774171033471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205897070335397789422589 77211401375774171033471)
                    ·
                      rfl

theorem cell22_225553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_225553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225553 prefixEnd_225553 := by exact prefixLift 225553
  have htrace : WordTrace (prefixWord ++ tailWord_225553) baseStart_225553 baseEnd_225553 := by
    simpa [prefixWord, tailWord_225553, baseEnd_225553] using wordTrace_append hprefix tailTrace_225553
  have hstable : (prefixWord ++ tailWord_225553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225553).length < 2 ^ (prefixWord ++ tailWord_225553).sum := by decide
  have hdescent : baseEnd_225553 < baseStart_225553 := by decide
  rcases family_descends (prefixWord ++ tailWord_225553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225583 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 5]
def baseStart_225583 : Nat := 118140960795 + 225583 * 2 ^ 59
def prefixEnd_225583 : Nat := 4983230072969 + 3 ^ 40 * 225583 * 2
def baseEnd_225583 : Nat := 25740556996288030927793

theorem tailTrace_225583 : CollatzResearch.WordTrace tailWord_225583 prefixEnd_225583 25740556996288030927793 := by
  unfold tailWord_225583
  simp only [CollatzResearch.WordTrace]
  refine ⟨8227687941758792354257403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5485125294505861569504935 8227687941758792354257403)
  ·
    refine ⟨12341531912638188531386105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8227687941758792354257403 12341531912638188531386105)
    ·
      refine ⟨9256148934478641398539579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12341531912638188531386105 9256148934478641398539579)
      ·
        refine ⟨13884223401717962097809369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9256148934478641398539579 13884223401717962097809369)
        ·
          refine ⟨10413167551288471573357027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13884223401717962097809369 10413167551288471573357027)
          ·
            refine ⟨15619751326932707360035541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10413167551288471573357027 15619751326932707360035541)
            ·
              refine ⟨366087921724985328750833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15619751326932707360035541 366087921724985328750833)
              ·
                refine ⟨274565941293738996563125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366087921724985328750833 274565941293738996563125)
                ·
                  refine ⟨25740556996288030927793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274565941293738996563125 25740556996288030927793)
                  ·
                    rfl

theorem cell22_225583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 5].length) (baseStart_225583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225583 prefixEnd_225583 := by exact prefixLift 225583
  have htrace : WordTrace (prefixWord ++ tailWord_225583) baseStart_225583 baseEnd_225583 := by
    simpa [prefixWord, tailWord_225583, baseEnd_225583] using wordTrace_append hprefix tailTrace_225583
  have hstable : (prefixWord ++ tailWord_225583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225583).length < 2 ^ (prefixWord ++ tailWord_225583).sum := by decide
  have hdescent : baseEnd_225583 < baseStart_225583 := by decide
  rcases family_descends (prefixWord ++ tailWord_225583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225611 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 8]
def baseStart_225611 : Nat := 118140960795 + 225611 * 2 ^ 59
def prefixEnd_225611 : Nat := 4983230072969 + 3 ^ 40 * 225611 * 2
def baseEnd_225611 : Nat := 25743751987027117694431

theorem tailTrace_225611 : CollatzResearch.WordTrace tailWord_225611 prefixEnd_225611 25743751987027117694431 := by
  unfold tailWord_225611
  simp only [CollatzResearch.WordTrace]
  refine ⟨8228709185657353136276687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5485806123771568757517791 8228709185657353136276687)
  ·
    refine ⟨12343063778486029704415031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8228709185657353136276687 12343063778486029704415031)
    ·
      refine ⟨18514595667729044556622547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12343063778486029704415031 18514595667729044556622547)
      ·
        refine ⟨27771893501593566834933821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18514595667729044556622547 27771893501593566834933821)
        ·
          refine ⟨10414460063097587563100183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27771893501593566834933821 10414460063097587563100183)
          ·
            refine ⟨15621690094646381344650275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10414460063097587563100183 15621690094646381344650275)
            ·
              refine ⟨23432535141969572016975413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15621690094646381344650275 23432535141969572016975413)
              ·
                refine ⟨2196800169559647376591445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23432535141969572016975413 2196800169559647376591445)
                ·
                  refine ⟨25743751987027117694431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2196800169559647376591445 25743751987027117694431)
                  ·
                    rfl

theorem cell22_225611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 8].length) (baseStart_225611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225611 prefixEnd_225611 := by exact prefixLift 225611
  have htrace : WordTrace (prefixWord ++ tailWord_225611) baseStart_225611 baseEnd_225611 := by
    simpa [prefixWord, tailWord_225611, baseEnd_225611] using wordTrace_append hprefix tailTrace_225611
  have hstable : (prefixWord ++ tailWord_225611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225611).length < 2 ^ (prefixWord ++ tailWord_225611).sum := by decide
  have hdescent : baseEnd_225611 < baseStart_225611 := by decide
  rcases family_descends (prefixWord ++ tailWord_225611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225621 : List Nat := [1, 3, 2, 2, 5, 1, 1, 3, 1, 3]
def baseStart_225621 : Nat := 118140960795 + 225621 * 2 ^ 59
def prefixEnd_225621 : Nat := 4983230072969 + 3 ^ 40 * 225621 * 2
def baseEnd_225621 : Nat := 77234679165444660333263

theorem tailTrace_225621 : CollatzResearch.WordTrace tailWord_225621 prefixEnd_225621 77234679165444660333263 := by
  unfold tailWord_225621
  simp only [CollatzResearch.WordTrace]
  refine ⟨8229073915621124844140717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5486049277080749896093811 8229073915621124844140717)
  ·
    refine ⟨3085902718357921816552769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8229073915621124844140717 3085902718357921816552769)
    ·
      refine ⟨2314427038768441362414577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3085902718357921816552769 2314427038768441362414577)
      ·
        refine ⟨1735820279076331021810933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2314427038768441362414577 1735820279076331021810933)
        ·
          refine ⟨162733151163406033294775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1735820279076331021810933 162733151163406033294775)
          ·
            refine ⟨244099726745109049942163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162733151163406033294775 244099726745109049942163)
            ·
              refine ⟨366149590117663574913245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244099726745109049942163 366149590117663574913245)
              ·
                refine ⟨137306096294123840592467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366149590117663574913245 137306096294123840592467)
                ·
                  refine ⟨205959144441185760888701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137306096294123840592467 205959144441185760888701)
                  ·
                    refine ⟨77234679165444660333263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205959144441185760888701 77234679165444660333263)
                    ·
                      rfl

theorem cell22_225621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_225621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225621 prefixEnd_225621 := by exact prefixLift 225621
  have htrace : WordTrace (prefixWord ++ tailWord_225621) baseStart_225621 baseEnd_225621 := by
    simpa [prefixWord, tailWord_225621, baseEnd_225621] using wordTrace_append hprefix tailTrace_225621
  have hstable : (prefixWord ++ tailWord_225621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225621).length < 2 ^ (prefixWord ++ tailWord_225621).sum := by decide
  have hdescent : baseEnd_225621 < baseStart_225621 := by decide
  rcases family_descends (prefixWord ++ tailWord_225621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225673 : List Nat := [1, 2, 1, 1, 6, 1, 2, 8]
def baseStart_225673 : Nat := 118140960795 + 225673 * 2 ^ 59
def prefixEnd_225673 : Nat := 4983230072969 + 3 ^ 40 * 225673 * 2
def baseEnd_225673 : Nat := 8583608869792650892567

theorem tailTrace_225673 : CollatzResearch.WordTrace tailWord_225673 prefixEnd_225673 8583608869792650892567 := by
  unfold tailWord_225673
  simp only [CollatzResearch.WordTrace]
  refine ⟨8230970511432737725033673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5487313674288491816689115 8230970511432737725033673)
  ·
    refine ⟨6173227883574553293775255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8230970511432737725033673 6173227883574553293775255)
    ·
      refine ⟨9259841825361829940662883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6173227883574553293775255 9259841825361829940662883)
      ·
        refine ⟨13889762738042744910994325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9259841825361829940662883 13889762738042744910994325)
        ·
          refine ⟨651082628345753667702859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13889762738042744910994325 651082628345753667702859)
          ·
            refine ⟨976623942518630501554289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651082628345753667702859 976623942518630501554289)
            ·
              refine ⟨732467956888972876165717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976623942518630501554289 732467956888972876165717)
              ·
                refine ⟨8583608869792650892567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 732467956888972876165717 8583608869792650892567)
                ·
                  rfl

theorem cell22_225673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 8].length) (baseStart_225673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225673 prefixEnd_225673 := by exact prefixLift 225673
  have htrace : WordTrace (prefixWord ++ tailWord_225673) baseStart_225673 baseEnd_225673 := by
    simpa [prefixWord, tailWord_225673, baseEnd_225673] using wordTrace_append hprefix tailTrace_225673
  have hstable : (prefixWord ++ tailWord_225673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225673).length < 2 ^ (prefixWord ++ tailWord_225673).sum := by decide
  have hdescent : baseEnd_225673 < baseStart_225673 := by decide
  rcases family_descends (prefixWord ++ tailWord_225673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225675 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 2, 4]
def baseStart_225675 : Nat := 118140960795 + 225675 * 2 ^ 59
def prefixEnd_225675 : Nat := 4983230072969 + 3 ^ 40 * 225675 * 2
def baseEnd_225675 : Nat := 77253164469006519483097

theorem tailTrace_225675 : CollatzResearch.WordTrace tailWord_225675 prefixEnd_225675 77253164469006519483097 := by
  unfold tailWord_225675
  simp only [CollatzResearch.WordTrace]
  refine ⟨8231043457425492066606479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5487362304950328044404319 8231043457425492066606479)
  ·
    refine ⟨12346565186138238099909719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8231043457425492066606479 12346565186138238099909719)
    ·
      refine ⟨18519847779207357149864579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12346565186138238099909719 18519847779207357149864579)
      ·
        refine ⟨27779771668811035724796869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18519847779207357149864579 27779771668811035724796869)
        ·
          refine ⟨5208707187902069198399413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27779771668811035724796869 5208707187902069198399413)
          ·
            refine ⟨488316298865818987349945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5208707187902069198399413 488316298865818987349945)
            ·
              refine ⟨366237224149364240512459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488316298865818987349945 366237224149364240512459)
              ·
                refine ⟨549355836224046360768689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366237224149364240512459 549355836224046360768689)
                ·
                  refine ⟨412016877168034770576517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 549355836224046360768689 412016877168034770576517)
                  ·
                    refine ⟨77253164469006519483097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 412016877168034770576517 77253164469006519483097)
                    ·
                      rfl

theorem cell22_225675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 4].length) (baseStart_225675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225675 prefixEnd_225675 := by exact prefixLift 225675
  have htrace : WordTrace (prefixWord ++ tailWord_225675) baseStart_225675 baseEnd_225675 := by
    simpa [prefixWord, tailWord_225675, baseEnd_225675] using wordTrace_append hprefix tailTrace_225675
  have hstable : (prefixWord ++ tailWord_225675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225675).length < 2 ^ (prefixWord ++ tailWord_225675).sum := by decide
  have hdescent : baseEnd_225675 < baseStart_225675 := by decide
  rcases family_descends (prefixWord ++ tailWord_225675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225694 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_225694 : Nat := 118140960795 + 225694 * 2 ^ 59
def prefixEnd_225694 : Nat := 4983230072969 + 3 ^ 40 * 225694 * 2
def baseEnd_225694 : Nat := 77259668557296803258039

theorem tailTrace_225694 : CollatzResearch.WordTrace tailWord_225694 prefixEnd_225694 77259668557296803258039 := by
  unfold tailWord_225694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028967055544582288943517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5487824296237772207698757 1028967055544582288943517)
  ·
    refine ⟨385862645829218358353819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1028967055544582288943517 385862645829218358353819)
    ·
      refine ⟨578793968743827537530729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385862645829218358353819 578793968743827537530729)
      ·
        refine ⟨434095476557870653148047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578793968743827537530729 434095476557870653148047)
        ·
          refine ⟨651143214836805979722071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434095476557870653148047 651143214836805979722071)
          ·
            refine ⟨976714822255208969583107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651143214836805979722071 976714822255208969583107)
            ·
              refine ⟨1465072233382813454374661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976714822255208969583107 1465072233382813454374661)
              ·
                refine ⟨274701043759277522695249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1465072233382813454374661 274701043759277522695249)
                ·
                  refine ⟨206025782819458142021437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274701043759277522695249 206025782819458142021437)
                  ·
                    refine ⟨77259668557296803258039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206025782819458142021437 77259668557296803258039)
                    ·
                      rfl

theorem cell22_225694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_225694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225694 prefixEnd_225694 := by exact prefixLift 225694
  have htrace : WordTrace (prefixWord ++ tailWord_225694) baseStart_225694 baseEnd_225694 := by
    simpa [prefixWord, tailWord_225694, baseEnd_225694] using wordTrace_append hprefix tailTrace_225694
  have hstable : (prefixWord ++ tailWord_225694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225694).length < 2 ^ (prefixWord ++ tailWord_225694).sum := by decide
  have hdescent : baseEnd_225694 < baseStart_225694 := by decide
  rcases family_descends (prefixWord ++ tailWord_225694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225795 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 6, 3]
def baseStart_225795 : Nat := 118140960795 + 225795 * 2 ^ 59
def prefixEnd_225795 : Nat := 4983230072969 + 3 ^ 40 * 225795 * 2
def baseEnd_225795 : Nat := 77294242921366206482729

theorem tailTrace_225795 : CollatzResearch.WordTrace tailWord_225795 prefixEnd_225795 77294242921366206482729 := by
  unfold tailWord_225795
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235420216990752560974839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5490280144660501707316559 8235420216990752560974839)
  ·
    refine ⟨12353130325486128841462259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8235420216990752560974839 12353130325486128841462259)
    ·
      refine ⟨18529695488229193262193389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12353130325486128841462259 18529695488229193262193389)
      ·
        refine ⟨6948635808085947473322521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18529695488229193262193389 6948635808085947473322521)
        ·
          refine ⟨5211476856064460604991891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6948635808085947473322521 5211476856064460604991891)
          ·
            refine ⟨7817215284096690907487837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5211476856064460604991891 7817215284096690907487837)
            ·
              refine ⟨2931455731536259090307939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7817215284096690907487837 2931455731536259090307939)
              ·
                refine ⟨4397183597304388635461909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931455731536259090307939 4397183597304388635461909)
                ·
                  refine ⟨206117981123643217287277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4397183597304388635461909 206117981123643217287277)
                  ·
                    refine ⟨77294242921366206482729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206117981123643217287277 77294242921366206482729)
                    ·
                      rfl

theorem cell22_225795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 3].length) (baseStart_225795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225795 prefixEnd_225795 := by exact prefixLift 225795
  have htrace : WordTrace (prefixWord ++ tailWord_225795) baseStart_225795 baseEnd_225795 := by
    simpa [prefixWord, tailWord_225795, baseEnd_225795] using wordTrace_append hprefix tailTrace_225795
  have hstable : (prefixWord ++ tailWord_225795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225795).length < 2 ^ (prefixWord ++ tailWord_225795).sum := by decide
  have hdescent : baseEnd_225795 < baseStart_225795 := by decide
  rcases family_descends (prefixWord ++ tailWord_225795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225797 : List Nat := [1, 3, 1, 1, 2, 2, 5, 3, 4]
def baseStart_225797 : Nat := 118140960795 + 225797 * 2 ^ 59
def prefixEnd_225797 : Nat := 4983230072969 + 3 ^ 40 * 225797 * 2
def baseEnd_225797 : Nat := 25764975854079622644241

theorem tailTrace_225797 : CollatzResearch.WordTrace tailWord_225797 prefixEnd_225797 25764975854079622644241 := by
  unfold tailWord_225797
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235493162983506902547645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5490328775322337935031763 8235493162983506902547645)
  ·
    refine ⟨3088309936118815088455367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8235493162983506902547645 3088309936118815088455367)
    ·
      refine ⟨4632464904178222632683051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3088309936118815088455367 4632464904178222632683051)
      ·
        refine ⟨6948697356267333949024577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4632464904178222632683051 6948697356267333949024577)
        ·
          refine ⟨5211523017200500461768433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6948697356267333949024577 5211523017200500461768433)
          ·
            refine ⟨3908642262900375346326325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5211523017200500461768433 3908642262900375346326325)
            ·
              refine ⟨366435212146910188718093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3908642262900375346326325 366435212146910188718093)
              ·
                refine ⟨137413204555091320769285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366435212146910188718093 137413204555091320769285)
                ·
                  refine ⟨25764975854079622644241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137413204555091320769285 25764975854079622644241)
                  ·
                    rfl

theorem cell22_225797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_225797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225797 prefixEnd_225797 := by exact prefixLift 225797
  have htrace : WordTrace (prefixWord ++ tailWord_225797) baseStart_225797 baseEnd_225797 := by
    simpa [prefixWord, tailWord_225797, baseEnd_225797] using wordTrace_append hprefix tailTrace_225797
  have hstable : (prefixWord ++ tailWord_225797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225797).length < 2 ^ (prefixWord ++ tailWord_225797).sum := by decide
  have hdescent : baseEnd_225797 < baseStart_225797 := by decide
  rcases family_descends (prefixWord ++ tailWord_225797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225825 : List Nat := [1, 2, 3, 2, 2, 1, 4, 7]
def baseStart_225825 : Nat := 118140960795 + 225825 * 2 ^ 59
def prefixEnd_225825 : Nat := 4983230072969 + 3 ^ 40 * 225825 * 2
def baseEnd_225825 : Nat := 8589390281606236470293

theorem tailTrace_225825 : CollatzResearch.WordTrace tailWord_225825 prefixEnd_225825 8589390281606236470293 := by
  unfold tailWord_225825
  simp only [CollatzResearch.WordTrace]
  refine ⟨8236514406882067684566929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5491009604588045123044619 8236514406882067684566929)
  ·
    refine ⟨6177385805161550763425197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8236514406882067684566929 6177385805161550763425197)
    ·
      refine ⟨2316519676935581536284449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6177385805161550763425197 2316519676935581536284449)
      ·
        refine ⟨1737389757701686152213337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2316519676935581536284449 1737389757701686152213337)
        ·
          refine ⟨1303042318276264614160003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1737389757701686152213337 1303042318276264614160003)
          ·
            refine ⟨1954563477414396921240005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303042318276264614160003 1954563477414396921240005)
            ·
              refine ⟨366480652015199422732501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1954563477414396921240005 366480652015199422732501)
              ·
                refine ⟨8589390281606236470293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 366480652015199422732501 8589390281606236470293)
                ·
                  rfl

theorem cell22_225825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 7].length) (baseStart_225825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225825 prefixEnd_225825 := by exact prefixLift 225825
  have htrace : WordTrace (prefixWord ++ tailWord_225825) baseStart_225825 baseEnd_225825 := by
    simpa [prefixWord, tailWord_225825, baseEnd_225825] using wordTrace_append hprefix tailTrace_225825
  have hstable : (prefixWord ++ tailWord_225825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225825).length < 2 ^ (prefixWord ++ tailWord_225825).sum := by decide
  have hdescent : baseEnd_225825 < baseStart_225825 := by decide
  rcases family_descends (prefixWord ++ tailWord_225825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225829 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 2, 3]
def baseStart_225829 : Nat := 118140960795 + 225829 * 2 ^ 59
def prefixEnd_225829 : Nat := 4983230072969 + 3 ^ 40 * 225829 * 2
def baseEnd_225829 : Nat := 77305881816201451132625

theorem tailTrace_225829 : CollatzResearch.WordTrace tailWord_225829 prefixEnd_225829 77305881816201451132625 := by
  unfold tailWord_225829
  simp only [CollatzResearch.WordTrace]
  refine ⟨8236660298867576367712541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5491106865911717578475027 8236660298867576367712541)
  ·
    refine ⟨3088747612075341137892203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8236660298867576367712541 3088747612075341137892203)
    ·
      refine ⟨4633121418113011706838305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3088747612075341137892203 4633121418113011706838305)
      ·
        refine ⟨3474841063584758780128729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4633121418113011706838305 3474841063584758780128729)
        ·
          refine ⟨2606130797688569085096547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3474841063584758780128729 2606130797688569085096547)
          ·
            refine ⟨3909196196532853627644821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606130797688569085096547 3909196196532853627644821)
            ·
              refine ⟨183243571712477513795851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3909196196532853627644821 183243571712477513795851)
              ·
                refine ⟨274865357568716270693777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183243571712477513795851 274865357568716270693777)
                ·
                  refine ⟨206149018176537203020333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274865357568716270693777 206149018176537203020333)
                  ·
                    refine ⟨77305881816201451132625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206149018176537203020333 77305881816201451132625)
                    ·
                      rfl

theorem cell22_225829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_225829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225829 prefixEnd_225829 := by exact prefixLift 225829
  have htrace : WordTrace (prefixWord ++ tailWord_225829) baseStart_225829 baseEnd_225829 := by
    simpa [prefixWord, tailWord_225829, baseEnd_225829] using wordTrace_append hprefix tailTrace_225829
  have hstable : (prefixWord ++ tailWord_225829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225829).length < 2 ^ (prefixWord ++ tailWord_225829).sum := by decide
  have hdescent : baseEnd_225829 < baseStart_225829 := by decide
  rcases family_descends (prefixWord ++ tailWord_225829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225870 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_225870 : Nat := 118140960795 + 225870 * 2 ^ 59
def prefixEnd_225870 : Nat := 4983230072969 + 3 ^ 40 * 225870 * 2
def baseEnd_225870 : Nat := 25773305651363670285833

theorem tailTrace_225870 : CollatzResearch.WordTrace tailWord_225870 prefixEnd_225870 25773305651363670285833 := by
  unfold tailWord_225870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1029769461464880046244383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5492103794479360246636709 1029769461464880046244383)
  ·
    refine ⟨1544654192197320069366575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1029769461464880046244383 1544654192197320069366575)
    ·
      refine ⟨2316981288295980104049863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1544654192197320069366575 2316981288295980104049863)
      ·
        refine ⟨3475471932443970156074795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316981288295980104049863 3475471932443970156074795)
        ·
          refine ⟨5213207898665955234112193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475471932443970156074795 5213207898665955234112193)
          ·
            refine ⟨3909905923999466425584145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5213207898665955234112193 3909905923999466425584145)
            ·
              refine ⟨2932429442999599819188109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3909905923999466425584145 2932429442999599819188109)
              ·
                refine ⟨1099661041124849932195541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2932429442999599819188109 1099661041124849932195541)
                ·
                  refine ⟨25773305651363670285833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1099661041124849932195541 25773305651363670285833)
                  ·
                    rfl

theorem cell22_225870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_225870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225870 prefixEnd_225870 := by exact prefixLift 225870
  have htrace : WordTrace (prefixWord ++ tailWord_225870) baseStart_225870 baseEnd_225870 := by
    simpa [prefixWord, tailWord_225870, baseEnd_225870] using wordTrace_append hprefix tailTrace_225870
  have hstable : (prefixWord ++ tailWord_225870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225870).length < 2 ^ (prefixWord ++ tailWord_225870).sum := by decide
  have hdescent : baseEnd_225870 < baseStart_225870 := by decide
  rcases family_descends (prefixWord ++ tailWord_225870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225945 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_225945 : Nat := 118140960795 + 225945 * 2 ^ 59
def prefixEnd_225945 : Nat := 4983230072969 + 3 ^ 40 * 225945 * 2
def baseEnd_225945 : Nat := 77345590986815815232269

theorem tailTrace_225945 : CollatzResearch.WordTrace tailWord_225945 prefixEnd_225945 77345590986815815232269 := by
  unfold tailWord_225945
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240891166447328178935289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5493927444298218785956859 8240891166447328178935289)
  ·
    refine ⟨6180668374835496134201467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8240891166447328178935289 6180668374835496134201467)
    ·
      refine ⟨9271002562253244201302201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6180668374835496134201467 9271002562253244201302201)
      ·
        refine ⟨6953251921689933150976651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9271002562253244201302201 6953251921689933150976651)
        ·
          refine ⟨10429877882534899726464977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6953251921689933150976651 10429877882534899726464977)
          ·
            refine ⟨7822408411901174794848733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10429877882534899726464977 7822408411901174794848733)
            ·
              refine ⟨2933403154462940548068275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7822408411901174794848733 2933403154462940548068275)
              ·
                refine ⟨4400104731694410822102413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933403154462940548068275 4400104731694410822102413)
                ·
                  refine ⟨1650039274385404058288405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4400104731694410822102413 1650039274385404058288405)
                  ·
                    refine ⟨77345590986815815232269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1650039274385404058288405 77345590986815815232269)
                    ·
                      rfl

theorem cell22_225945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_225945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225945 prefixEnd_225945 := by exact prefixLift 225945
  have htrace : WordTrace (prefixWord ++ tailWord_225945) baseStart_225945 baseEnd_225945 := by
    simpa [prefixWord, tailWord_225945, baseEnd_225945] using wordTrace_append hprefix tailTrace_225945
  have hstable : (prefixWord ++ tailWord_225945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225945).length < 2 ^ (prefixWord ++ tailWord_225945).sum := by decide
  have hdescent : baseEnd_225945 < baseStart_225945 := by decide
  rcases family_descends (prefixWord ++ tailWord_225945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225998 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_225998 : Nat := 118140960795 + 225998 * 2 ^ 59
def prefixEnd_225998 : Nat := 4983230072969 + 3 ^ 40 * 225998 * 2
def baseEnd_225998 : Nat := 77363733969941343657107

theorem tailTrace_225998 : CollatzResearch.WordTrace tailWord_225998 prefixEnd_225998 77363733969941343657107 := by
  unfold tailWord_225998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1030353029406914778826831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5495216156836878820409765 1030353029406914778826831)
  ·
    refine ⟨1545529544110372168240247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1030353029406914778826831 1545529544110372168240247)
    ·
      refine ⟨2318294316165558252360371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1545529544110372168240247 2318294316165558252360371)
      ·
        refine ⟨3477441474248337378540557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2318294316165558252360371 3477441474248337378540557)
        ·
          refine ⟨1304040552843126516952709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3477441474248337378540557 1304040552843126516952709)
          ·
            refine ⟨244507603658086221928633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1304040552843126516952709 244507603658086221928633)
            ·
              refine ⟨183380702743564666446475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244507603658086221928633 183380702743564666446475)
              ·
                refine ⟨275071054115346999669713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183380702743564666446475 275071054115346999669713)
                ·
                  refine ⟨206303290586510249752285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275071054115346999669713 206303290586510249752285)
                  ·
                    refine ⟨77363733969941343657107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206303290586510249752285 77363733969941343657107)
                    ·
                      rfl

theorem cell22_225998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_225998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_225998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_225998 prefixEnd_225998 := by exact prefixLift 225998
  have htrace : WordTrace (prefixWord ++ tailWord_225998) baseStart_225998 baseEnd_225998 := by
    simpa [prefixWord, tailWord_225998, baseEnd_225998] using wordTrace_append hprefix tailTrace_225998
  have hstable : (prefixWord ++ tailWord_225998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225998).length < 2 ^ (prefixWord ++ tailWord_225998).sum := by decide
  have hdescent : baseEnd_225998 < baseStart_225998 := by decide
  rcases family_descends (prefixWord ++ tailWord_225998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226026 : List Nat := [3, 1, 3, 1, 1, 1, 1, 7, 1, 3]
def baseStart_226026 : Nat := 118140960795 + 226026 * 2 ^ 59
def prefixEnd_226026 : Nat := 4983230072969 + 3 ^ 40 * 226026 * 2
def baseEnd_226026 : Nat := 77373318942158603957021

theorem tailTrace_226026 : CollatzResearch.WordTrace tailWord_226026 prefixEnd_226026 77373318942158603957021 := by
  unfold tailWord_226026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060961369788469753158483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5495896986102586008422621 2060961369788469753158483)
  ·
    refine ⟨3091442054682704629737725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060961369788469753158483 3091442054682704629737725)
    ·
      refine ⟨1159290770506014236151647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3091442054682704629737725 1159290770506014236151647)
      ·
        refine ⟨1738936155759021354227471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159290770506014236151647 1738936155759021354227471)
        ·
          refine ⟨2608404233638532031341207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738936155759021354227471 2608404233638532031341207)
          ·
            refine ⟨3912606350457798047011811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608404233638532031341207 3912606350457798047011811)
            ·
              refine ⟨5868909525686697070517717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3912606350457798047011811 5868909525686697070517717)
              ·
                refine ⟨137552567008281962590259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5868909525686697070517717 137552567008281962590259)
                ·
                  refine ⟨206328850512422943885389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137552567008281962590259 206328850512422943885389)
                  ·
                    refine ⟨77373318942158603957021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206328850512422943885389 77373318942158603957021)
                    ·
                      rfl

theorem cell22_226026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_226026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226026 prefixEnd_226026 := by exact prefixLift 226026
  have htrace : WordTrace (prefixWord ++ tailWord_226026) baseStart_226026 baseEnd_226026 := by
    simpa [prefixWord, tailWord_226026, baseEnd_226026] using wordTrace_append hprefix tailTrace_226026
  have hstable : (prefixWord ++ tailWord_226026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226026).length < 2 ^ (prefixWord ++ tailWord_226026).sum := by decide
  have hdescent : baseEnd_226026 < baseStart_226026 := by decide
  rcases family_descends (prefixWord ++ tailWord_226026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226067 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 6]
def baseStart_226067 : Nat := 118140960795 + 226067 * 2 ^ 59
def prefixEnd_226067 : Nat := 4983230072969 + 3 ^ 40 * 226067 * 2
def baseEnd_226067 : Nat := 25795784693349387893965

theorem tailTrace_226067 : CollatzResearch.WordTrace tailWord_226067 prefixEnd_226067 25795784693349387893965 := by
  unfold tailWord_226067
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245340872005343014876455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5496893914670228676584303 8245340872005343014876455)
  ·
    refine ⟨12368011308008014522314683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8245340872005343014876455 12368011308008014522314683)
    ·
      refine ⟨18552016962012021783472025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12368011308008014522314683 18552016962012021783472025)
      ·
        refine ⟨13914012721509016337604019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18552016962012021783472025 13914012721509016337604019)
        ·
          refine ⟨20871019082263524506406029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13914012721509016337604019 20871019082263524506406029)
          ·
            refine ⟨7826632155848821689902261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20871019082263524506406029 7826632155848821689902261)
            ·
              refine ⟨733746764610827033428337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7826632155848821689902261 733746764610827033428337)
              ·
                refine ⟨550310073458120275071253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733746764610827033428337 550310073458120275071253)
                ·
                  refine ⟨25795784693349387893965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 550310073458120275071253 25795784693349387893965)
                  ·
                    rfl

theorem cell22_226067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 6].length) (baseStart_226067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226067 prefixEnd_226067 := by exact prefixLift 226067
  have htrace : WordTrace (prefixWord ++ tailWord_226067) baseStart_226067 baseEnd_226067 := by
    simpa [prefixWord, tailWord_226067, baseEnd_226067] using wordTrace_append hprefix tailTrace_226067
  have hstable : (prefixWord ++ tailWord_226067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226067).length < 2 ^ (prefixWord ++ tailWord_226067).sum := by decide
  have hdescent : baseEnd_226067 < baseStart_226067 := by decide
  rcases family_descends (prefixWord ++ tailWord_226067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226069 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_226069 : Nat := 118140960795 + 226069 * 2 ^ 59
def prefixEnd_226069 : Nat := 4983230072969 + 3 ^ 40 * 226069 * 2
def baseEnd_226069 : Nat := 77388038720920825131889

theorem tailTrace_226069 : CollatzResearch.WordTrace tailWord_226069 prefixEnd_226069 77388038720920825131889 := by
  unfold tailWord_226069
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245413817998097356449261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5496942545332064904299507 8245413817998097356449261)
  ·
    refine ⟨3092030181749286508668473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8245413817998097356449261 3092030181749286508668473)
    ·
      refine ⟨2319022636311964881501355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3092030181749286508668473 2319022636311964881501355)
      ·
        refine ⟨3478533954467947322252033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319022636311964881501355 3478533954467947322252033)
        ·
          refine ⟨2608900465850960491689025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478533954467947322252033 2608900465850960491689025)
          ·
            refine ⟨1956675349388220368766769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608900465850960491689025 1956675349388220368766769)
            ·
              refine ⟨1467506512041165276575077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956675349388220368766769 1467506512041165276575077)
              ·
                refine ⟨275157471007718489357827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1467506512041165276575077 275157471007718489357827)
                ·
                  refine ⟨412736206511577734036741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275157471007718489357827 412736206511577734036741)
                  ·
                    refine ⟨77388038720920825131889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 412736206511577734036741 77388038720920825131889)
                    ·
                      rfl

theorem cell22_226069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_226069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226069 prefixEnd_226069 := by exact prefixLift 226069
  have htrace : WordTrace (prefixWord ++ tailWord_226069) baseStart_226069 baseEnd_226069 := by
    simpa [prefixWord, tailWord_226069, baseEnd_226069] using wordTrace_append hprefix tailTrace_226069
  have hstable : (prefixWord ++ tailWord_226069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226069).length < 2 ^ (prefixWord ++ tailWord_226069).sum := by decide
  have hdescent : baseEnd_226069 < baseStart_226069 := by decide
  rcases family_descends (prefixWord ++ tailWord_226069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226090 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_226090 : Nat := 118140960795 + 226090 * 2 ^ 59
def prefixEnd_226090 : Nat := 4983230072969 + 3 ^ 40 * 226090 * 2
def baseEnd_226090 : Nat := 25798409150027923452275

theorem tailTrace_226090 : CollatzResearch.WordTrace tailWord_226090 prefixEnd_226090 25798409150027923452275 := by
  unfold tailWord_226090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061544937730504485740931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5497453167281345295309149 2061544937730504485740931)
  ·
    refine ⟨3092317406595756728611397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2061544937730504485740931 3092317406595756728611397)
    ·
      refine ⟨579809513736704386614637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3092317406595756728611397 579809513736704386614637)
      ·
        refine ⟨217428567651264144980489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 579809513736704386614637 217428567651264144980489)
        ·
          refine ⟨163071425738448108735367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217428567651264144980489 163071425738448108735367)
          ·
            refine ⟨244607138607672163103051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163071425738448108735367 244607138607672163103051)
            ·
              refine ⟨366910707911508244654577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244607138607672163103051 366910707911508244654577)
              ·
                refine ⟨275183030933631183490933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366910707911508244654577 275183030933631183490933)
                ·
                  refine ⟨25798409150027923452275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275183030933631183490933 25798409150027923452275)
                  ·
                    rfl

theorem cell22_226090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_226090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226090 prefixEnd_226090 := by exact prefixLift 226090
  have htrace : WordTrace (prefixWord ++ tailWord_226090) baseStart_226090 baseEnd_226090 := by
    simpa [prefixWord, tailWord_226090, baseEnd_226090] using wordTrace_append hprefix tailTrace_226090
  have hstable : (prefixWord ++ tailWord_226090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226090).length < 2 ^ (prefixWord ++ tailWord_226090).sum := by decide
  have hdescent : baseEnd_226090 < baseStart_226090 := by decide
  rcases family_descends (prefixWord ++ tailWord_226090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226101 : List Nat := [1, 3, 3, 1, 3, 1, 2, 4, 4]
def baseStart_226101 : Nat := 118140960795 + 226101 * 2 ^ 59
def prefixEnd_226101 : Nat := 4983230072969 + 3 ^ 40 * 226101 * 2
def baseEnd_226101 : Nat := 25799664324961136110597

theorem tailTrace_226101 : CollatzResearch.WordTrace tailWord_226101 prefixEnd_226101 25799664324961136110597 := by
  unfold tailWord_226101
  simp only [CollatzResearch.WordTrace]
  refine ⟨8246580953882166821614157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5497720635921444547742771 8246580953882166821614157)
  ·
    refine ⟨3092467857705812558105309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8246580953882166821614157 3092467857705812558105309)
    ·
      refine ⟨1159675446639679709289491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3092467857705812558105309 1159675446639679709289491)
      ·
        refine ⟨1739513169959519563934237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159675446639679709289491 1739513169959519563934237)
        ·
          refine ⟨652317438734819836475339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1739513169959519563934237 652317438734819836475339)
          ·
            refine ⟨978476158102229754713009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652317438734819836475339 978476158102229754713009)
            ·
              refine ⟨733857118576672316034757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978476158102229754713009 733857118576672316034757)
              ·
                refine ⟨137598209733126059256517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 733857118576672316034757 137598209733126059256517)
                ·
                  refine ⟨25799664324961136110597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137598209733126059256517 25799664324961136110597)
                  ·
                    rfl

theorem cell22_226101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_226101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226101 prefixEnd_226101 := by exact prefixLift 226101
  have htrace : WordTrace (prefixWord ++ tailWord_226101) baseStart_226101 baseEnd_226101 := by
    simpa [prefixWord, tailWord_226101, baseEnd_226101] using wordTrace_append hprefix tailTrace_226101
  have hstable : (prefixWord ++ tailWord_226101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226101).length < 2 ^ (prefixWord ++ tailWord_226101).sum := by decide
  have hdescent : baseEnd_226101 < baseStart_226101 := by decide
  rcases family_descends (prefixWord ++ tailWord_226101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226129 : List Nat := [1, 2, 2, 1, 6, 1, 1, 8]
def baseStart_226129 : Nat := 118140960795 + 226129 * 2 ^ 59
def prefixEnd_226129 : Nat := 4983230072969 + 3 ^ 40 * 226129 * 2
def baseEnd_226129 : Nat := 8600953105233407625745

theorem tailTrace_226129 : CollatzResearch.WordTrace tailWord_226129 prefixEnd_226129 8600953105233407625745 := by
  unfold tailWord_226129
  simp only [CollatzResearch.WordTrace]
  refine ⟨8247602197780727603633441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5498401465187151735755627 8247602197780727603633441)
  ·
    refine ⟨6185701648335545702725081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8247602197780727603633441 6185701648335545702725081)
    ·
      refine ⟨4639276236251659277043811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6185701648335545702725081 4639276236251659277043811)
      ·
        refine ⟨6958914354377488915565717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639276236251659277043811 6958914354377488915565717)
        ·
          refine ⟨326199110361444792917143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6958914354377488915565717 326199110361444792917143)
          ·
            refine ⟨489298665542167189375715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326199110361444792917143 489298665542167189375715)
            ·
              refine ⟨733947998313250784063573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489298665542167189375715 733947998313250784063573)
              ·
                refine ⟨8600953105233407625745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 733947998313250784063573 8600953105233407625745)
                ·
                  rfl

theorem cell22_226129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 8].length) (baseStart_226129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226129 prefixEnd_226129 := by exact prefixLift 226129
  have htrace : WordTrace (prefixWord ++ tailWord_226129) baseStart_226129 baseEnd_226129 := by
    simpa [prefixWord, tailWord_226129, baseEnd_226129] using wordTrace_append hprefix tailTrace_226129
  have hstable : (prefixWord ++ tailWord_226129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226129).length < 2 ^ (prefixWord ++ tailWord_226129).sum := by decide
  have hdescent : baseEnd_226129 < baseStart_226129 := by decide
  rcases family_descends (prefixWord ++ tailWord_226129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226146 : List Nat := [3, 3, 2, 1, 3, 2, 8]
def baseStart_226146 : Nat := 118140960795 + 226146 * 2 ^ 59
def prefixEnd_226146 : Nat := 4983230072969 + 3 ^ 40 * 226146 * 2
def baseEnd_226146 : Nat := 2867199903500677442839

theorem tailTrace_226146 : CollatzResearch.WordTrace tailWord_226146 prefixEnd_226146 2867199903500677442839 := by
  unfold tailWord_226146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062055559679784876750573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5498814825812759671334861 2062055559679784876750573)
  ·
    refine ⟨773270834879919328781465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2062055559679784876750573 773270834879919328781465)
    ·
      refine ⟨579953126159939496586099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 773270834879919328781465 579953126159939496586099)
      ·
        refine ⟨869929689239909244879149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579953126159939496586099 869929689239909244879149)
        ·
          refine ⟨326223633464965966829681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 869929689239909244879149 326223633464965966829681)
          ·
            refine ⟨244667725098724475122261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326223633464965966829681 244667725098724475122261)
            ·
              refine ⟨2867199903500677442839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 244667725098724475122261 2867199903500677442839)
              ·
                rfl

theorem cell22_226146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 8].length) (baseStart_226146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226146 prefixEnd_226146 := by exact prefixLift 226146
  have htrace : WordTrace (prefixWord ++ tailWord_226146) baseStart_226146 baseEnd_226146 := by
    simpa [prefixWord, tailWord_226146, baseEnd_226146] using wordTrace_append hprefix tailTrace_226146
  have hstable : (prefixWord ++ tailWord_226146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226146).length < 2 ^ (prefixWord ++ tailWord_226146).sum := by decide
  have hdescent : baseEnd_226146 < baseStart_226146 := by decide
  rcases family_descends (prefixWord ++ tailWord_226146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226161 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 3, 3]
def baseStart_226161 : Nat := 118140960795 + 226161 * 2 ^ 59
def prefixEnd_226161 : Nat := 4983230072969 + 3 ^ 40 * 226161 * 2
def baseEnd_226161 : Nat := 77419532201063251831607

theorem tailTrace_226161 : CollatzResearch.WordTrace tailWord_226161 prefixEnd_226161 77419532201063251831607 := by
  unfold tailWord_226161
  simp only [CollatzResearch.WordTrace]
  refine ⟨8248769333664797068798337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5499179555776531379198891 8248769333664797068798337)
  ·
    refine ⟨6186577000248597801598753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8248769333664797068798337 6186577000248597801598753)
    ·
      refine ⟨4639932750186448351199065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6186577000248597801598753 4639932750186448351199065)
      ·
        refine ⟨3479949562639836263399299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4639932750186448351199065 3479949562639836263399299)
        ·
          refine ⟨5219924343959754395098949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3479949562639836263399299 5219924343959754395098949)
          ·
            refine ⟨978735814492453949081053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5219924343959754395098949 978735814492453949081053)
            ·
              refine ⟨367025930434670230905395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 978735814492453949081053 367025930434670230905395)
              ·
                refine ⟨550538895652005346358093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367025930434670230905395 550538895652005346358093)
                ·
                  refine ⟨206452085869502004884285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550538895652005346358093 206452085869502004884285)
                  ·
                    refine ⟨77419532201063251831607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206452085869502004884285 77419532201063251831607)
                    ·
                      rfl

theorem cell22_226161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_226161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226161 prefixEnd_226161 := by exact prefixLift 226161
  have htrace : WordTrace (prefixWord ++ tailWord_226161) baseStart_226161 baseEnd_226161 := by
    simpa [prefixWord, tailWord_226161, baseEnd_226161] using wordTrace_append hprefix tailTrace_226161
  have hstable : (prefixWord ++ tailWord_226161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226161).length < 2 ^ (prefixWord ++ tailWord_226161).sum := by decide
  have hdescent : baseEnd_226161 < baseStart_226161 := by decide
  rcases family_descends (prefixWord ++ tailWord_226161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226264 : List Nat := [2, 1, 2, 2, 2, 4, 9]
def baseStart_226264 : Nat := 118140960795 + 226264 * 2 ^ 59
def prefixEnd_226264 : Nat := 4983230072969 + 3 ^ 40 * 226264 * 2
def baseEnd_226264 : Nat := 2868695970592789500233

theorem tailTrace_226264 : CollatzResearch.WordTrace tailWord_226264 prefixEnd_226264 2868695970592789500233 := by
  unfold tailWord_226264
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126263026145822829898923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5501684034861097106531897 4126263026145822829898923)
  ·
    refine ⟨6189394539218734244848385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4126263026145822829898923 6189394539218734244848385)
    ·
      refine ⟨4642045904414050683636289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6189394539218734244848385 4642045904414050683636289)
      ·
        refine ⟨3481534428310538012727217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4642045904414050683636289 3481534428310538012727217)
        ·
          refine ⟨2611150821232903509545413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3481534428310538012727217 2611150821232903509545413)
          ·
            refine ⟨489590778981169408039765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2611150821232903509545413 489590778981169408039765)
            ·
              refine ⟨2868695970592789500233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 489590778981169408039765 2868695970592789500233)
              ·
                rfl

theorem cell22_226264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 9].length) (baseStart_226264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226264 prefixEnd_226264 := by exact prefixLift 226264
  have htrace : WordTrace (prefixWord ++ tailWord_226264) baseStart_226264 baseEnd_226264 := by
    simpa [prefixWord, tailWord_226264, baseEnd_226264] using wordTrace_append hprefix tailTrace_226264
  have hstable : (prefixWord ++ tailWord_226264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226264).length < 2 ^ (prefixWord ++ tailWord_226264).sum := by decide
  have hdescent : baseEnd_226264 < baseStart_226264 := by decide
  rcases family_descends (prefixWord ++ tailWord_226264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226309 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 9]
def baseStart_226309 : Nat := 118140960795 + 226309 * 2 ^ 59
def prefixEnd_226309 : Nat := 4983230072969 + 3 ^ 40 * 226309 * 2
def baseEnd_226309 : Nat := 25823398541880066377051

theorem tailTrace_226309 : CollatzResearch.WordTrace tailWord_226309 prefixEnd_226309 25823398541880066377051 := by
  unfold tailWord_226309
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254167337128618345185981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5502778224752412230123987 8254167337128618345185981)
  ·
    refine ⟨3095312751423231879444743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8254167337128618345185981 3095312751423231879444743)
    ·
      refine ⟨4642969127134847819167115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095312751423231879444743 4642969127134847819167115)
      ·
        refine ⟨6964453690702271728750673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642969127134847819167115 6964453690702271728750673)
        ·
          refine ⟨5223340268026703796563005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6964453690702271728750673 5223340268026703796563005)
          ·
            refine ⟨1958752600510013923711127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5223340268026703796563005 1958752600510013923711127)
            ·
              refine ⟨2938128900765020885566691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958752600510013923711127 2938128900765020885566691)
              ·
                refine ⟨4407193351147531328350037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938128900765020885566691 4407193351147531328350037)
                ·
                  refine ⟨25823398541880066377051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4407193351147531328350037 25823398541880066377051)
                  ·
                    rfl

theorem cell22_226309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_226309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226309 prefixEnd_226309 := by exact prefixLift 226309
  have htrace : WordTrace (prefixWord ++ tailWord_226309) baseStart_226309 baseEnd_226309 := by
    simpa [prefixWord, tailWord_226309, baseEnd_226309] using wordTrace_append hprefix tailTrace_226309
  have hstable : (prefixWord ++ tailWord_226309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226309).length < 2 ^ (prefixWord ++ tailWord_226309).sum := by decide
  have hdescent : baseEnd_226309 < baseStart_226309 := by decide
  rcases family_descends (prefixWord ++ tailWord_226309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226401 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_226401 : Nat := 118140960795 + 226401 * 2 ^ 59
def prefixEnd_226401 : Nat := 4983230072969 + 3 ^ 40 * 226401 * 2
def baseEnd_226401 : Nat := 77501689105782625830871

theorem tailTrace_226401 : CollatzResearch.WordTrace tailWord_226401 prefixEnd_226401 77501689105782625830871 := by
  unfold tailWord_226401
  simp only [CollatzResearch.WordTrace]
  refine ⟨8257522852795318057535057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5505015235196878705023371 8257522852795318057535057)
  ·
    refine ⟨6193142139596488543151293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8257522852795318057535057 6193142139596488543151293)
    ·
      refine ⟨2322428302348683203681735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6193142139596488543151293 2322428302348683203681735)
      ·
        refine ⟨3483642453523024805522603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322428302348683203681735 3483642453523024805522603)
        ·
          refine ⟨5225463680284537208283905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483642453523024805522603 5225463680284537208283905)
          ·
            refine ⟨3919097760213402906212929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5225463680284537208283905 3919097760213402906212929)
            ·
              refine ⟨2939323320160052179659697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3919097760213402906212929 2939323320160052179659697)
              ·
                refine ⟨2204492490120039134744773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2939323320160052179659697 2204492490120039134744773)
                ·
                  refine ⟨413342341897507337764645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2204492490120039134744773 413342341897507337764645)
                  ·
                    refine ⟨77501689105782625830871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 413342341897507337764645 77501689105782625830871)
                    ·
                      rfl

theorem cell22_226401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_226401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226401 prefixEnd_226401 := by exact prefixLift 226401
  have htrace : WordTrace (prefixWord ++ tailWord_226401) baseStart_226401 baseEnd_226401 := by
    simpa [prefixWord, tailWord_226401, baseEnd_226401] using wordTrace_append hprefix tailTrace_226401
  have hstable : (prefixWord ++ tailWord_226401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226401).length < 2 ^ (prefixWord ++ tailWord_226401).sum := by decide
  have hdescent : baseEnd_226401 < baseStart_226401 := by decide
  rcases family_descends (prefixWord ++ tailWord_226401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226437 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_226437 : Nat := 118140960795 + 226437 * 2 ^ 59
def prefixEnd_226437 : Nat := 4983230072969 + 3 ^ 40 * 226437 * 2
def baseEnd_226437 : Nat := 77514012641490531930761

theorem tailTrace_226437 : CollatzResearch.WordTrace tailWord_226437 prefixEnd_226437 77514012641490531930761 := by
  unfold tailWord_226437
  simp only [CollatzResearch.WordTrace]
  refine ⟨8258835880664896205845565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5505890587109930803897043 8258835880664896205845565)
  ·
    refine ⟨3097063455249336077192087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8258835880664896205845565 3097063455249336077192087)
    ·
      refine ⟨4645595182874004115788131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3097063455249336077192087 4645595182874004115788131)
      ·
        refine ⟨6968392774311006173682197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645595182874004115788131 6968392774311006173682197)
        ·
          refine ⟨326643411295828414391353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6968392774311006173682197 326643411295828414391353)
          ·
            refine ⟨244982558471871310793515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326643411295828414391353 244982558471871310793515)
            ·
              refine ⟨367473837707806966190273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244982558471871310793515 367473837707806966190273)
              ·
                refine ⟨275605378280855224642705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367473837707806966190273 275605378280855224642705)
                ·
                  refine ⟨206704033710641418482029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275605378280855224642705 206704033710641418482029)
                  ·
                    refine ⟨77514012641490531930761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206704033710641418482029 77514012641490531930761)
                    ·
                      rfl

theorem cell22_226437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_226437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226437 prefixEnd_226437 := by exact prefixLift 226437
  have htrace : WordTrace (prefixWord ++ tailWord_226437) baseStart_226437 baseEnd_226437 := by
    simpa [prefixWord, tailWord_226437, baseEnd_226437] using wordTrace_append hprefix tailTrace_226437
  have hstable : (prefixWord ++ tailWord_226437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226437).length < 2 ^ (prefixWord ++ tailWord_226437).sum := by decide
  have hdescent : baseEnd_226437 < baseStart_226437 := by decide
  rcases family_descends (prefixWord ++ tailWord_226437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226476 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_226476 : Nat := 118140960795 + 226476 * 2 ^ 59
def prefixEnd_226476 : Nat := 4983230072969 + 3 ^ 40 * 226476 * 2
def baseEnd_226476 : Nat := 77527363138507430205641

theorem tailTrace_226476 : CollatzResearch.WordTrace tailWord_226476 prefixEnd_226476 77527363138507430205641 := by
  unfold tailWord_226476
  simp only [CollatzResearch.WordTrace]
  refine ⟨4130129163761802933257641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5506838885015737244343521 4130129163761802933257641)
  ·
    refine ⟨3097596872821352199943231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4130129163761802933257641 3097596872821352199943231)
    ·
      refine ⟨4646395309232028299914847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3097596872821352199943231 4646395309232028299914847)
      ·
        refine ⟨6969592963848042449872271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4646395309232028299914847 6969592963848042449872271)
        ·
          refine ⟨10454389445772063674808407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969592963848042449872271 10454389445772063674808407)
          ·
            refine ⟨15681584168658095512212611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10454389445772063674808407 15681584168658095512212611)
            ·
              refine ⟨23522376252987143268318917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15681584168658095512212611 23522376252987143268318917)
              ·
                refine ⟨4410445547435089362809797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23522376252987143268318917 4410445547435089362809797)
                ·
                  refine ⟨826958540144079255526837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4410445547435089362809797 826958540144079255526837)
                  ·
                    refine ⟨77527363138507430205641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 826958540144079255526837 77527363138507430205641)
                    ·
                      rfl

theorem cell22_226476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_226476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226476 prefixEnd_226476 := by exact prefixLift 226476
  have htrace : WordTrace (prefixWord ++ tailWord_226476) baseStart_226476 baseEnd_226476 := by
    simpa [prefixWord, tailWord_226476, baseEnd_226476] using wordTrace_append hprefix tailTrace_226476
  have hstable : (prefixWord ++ tailWord_226476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226476).length < 2 ^ (prefixWord ++ tailWord_226476).sum := by decide
  have hdescent : baseEnd_226476 < baseStart_226476 := by decide
  rcases family_descends (prefixWord ++ tailWord_226476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226482 : List Nat := [3, 2, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_226482 : Nat := 118140960795 + 226482 * 2 ^ 59
def prefixEnd_226482 : Nat := 4983230072969 + 3 ^ 40 * 226482 * 2
def baseEnd_226482 : Nat := 77529417061125414555623

theorem tailTrace_226482 : CollatzResearch.WordTrace tailWord_226482 prefixEnd_226482 77529417061125414555623 := by
  unfold tailWord_226482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065119291375467222808425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5506984777001245927489133 2065119291375467222808425)
  ·
    refine ⟨1548839468531600417106319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2065119291375467222808425 1548839468531600417106319)
    ·
      refine ⟨2323259202797400625659479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1548839468531600417106319 2323259202797400625659479)
      ·
        refine ⟨3484888804196100938489219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323259202797400625659479 3484888804196100938489219)
        ·
          refine ⟨5227333206294151407733829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3484888804196100938489219 5227333206294151407733829)
          ·
            refine ⟨980124976180153388950093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5227333206294151407733829 980124976180153388950093)
            ·
              refine ⟨367546866067557520856285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 980124976180153388950093 367546866067557520856285)
              ·
                refine ⟨137830074775334070321107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367546866067557520856285 137830074775334070321107)
                ·
                  refine ⟨206745112163001105481661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137830074775334070321107 206745112163001105481661)
                  ·
                    refine ⟨77529417061125414555623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206745112163001105481661 77529417061125414555623)
                    ·
                      rfl

theorem cell22_226482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_226482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226482 prefixEnd_226482 := by exact prefixLift 226482
  have htrace : WordTrace (prefixWord ++ tailWord_226482) baseStart_226482 baseEnd_226482 := by
    simpa [prefixWord, tailWord_226482, baseEnd_226482] using wordTrace_append hprefix tailTrace_226482
  have hstable : (prefixWord ++ tailWord_226482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226482).length < 2 ^ (prefixWord ++ tailWord_226482).sum := by decide
  have hdescent : baseEnd_226482 < baseStart_226482 := by decide
  rcases family_descends (prefixWord ++ tailWord_226482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226538 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_226538 : Nat := 118140960795 + 226538 * 2 ^ 59
def prefixEnd_226538 : Nat := 4983230072969 + 3 ^ 40 * 226538 * 2
def baseEnd_226538 : Nat := 77548587005559935155451

theorem tailTrace_226538 : CollatzResearch.WordTrace tailWord_226538 prefixEnd_226538 77548587005559935155451 := by
  unfold tailWord_226538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065629913324747613818067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5508346435532660303514845 2065629913324747613818067)
  ·
    refine ⟨3098444869987121420727101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2065629913324747613818067 3098444869987121420727101)
    ·
      refine ⟨1161916826245170532772663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3098444869987121420727101 1161916826245170532772663)
      ·
        refine ⟨1742875239367755799158995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161916826245170532772663 1742875239367755799158995)
        ·
          refine ⟨2614312859051633698738493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742875239367755799158995 2614312859051633698738493)
          ·
            refine ⟨980367322144362637026935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2614312859051633698738493 980367322144362637026935)
            ·
              refine ⟨1470550983216543955540403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980367322144362637026935 1470550983216543955540403)
              ·
                refine ⟨2205826474824815933310605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470550983216543955540403 2205826474824815933310605)
                ·
                  refine ⟨827184928059305974991477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2205826474824815933310605 827184928059305974991477)
                  ·
                    refine ⟨77548587005559935155451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 827184928059305974991477 77548587005559935155451)
                    ·
                      rfl

theorem cell22_226538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_226538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226538 prefixEnd_226538 := by exact prefixLift 226538
  have htrace : WordTrace (prefixWord ++ tailWord_226538) baseStart_226538 baseEnd_226538 := by
    simpa [prefixWord, tailWord_226538, baseEnd_226538] using wordTrace_append hprefix tailTrace_226538
  have hstable : (prefixWord ++ tailWord_226538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226538).length < 2 ^ (prefixWord ++ tailWord_226538).sum := by decide
  have hdescent : baseEnd_226538 < baseStart_226538 := by decide
  rcases family_descends (prefixWord ++ tailWord_226538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226553 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_226553 : Nat := 118140960795 + 226553 * 2 ^ 59
def prefixEnd_226553 : Nat := 4983230072969 + 3 ^ 40 * 226553 * 2
def baseEnd_226553 : Nat := 77553721812104896030405

theorem tailTrace_226553 : CollatzResearch.WordTrace tailWord_226553 prefixEnd_226553 77553721812104896030405 := by
  unfold tailWord_226553
  simp only [CollatzResearch.WordTrace]
  refine ⟨8263066748244648017068313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5508711165496432011378875 8263066748244648017068313)
  ·
    refine ⟨6197300061183486012801235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8263066748244648017068313 6197300061183486012801235)
    ·
      refine ⟨9295950091775229019201853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6197300061183486012801235 9295950091775229019201853)
      ·
        refine ⟨3485981284415710882200695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9295950091775229019201853 3485981284415710882200695)
        ·
          refine ⟨5228971926623566323301043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3485981284415710882200695 5228971926623566323301043)
          ·
            refine ⟨7843457889935349484951565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5228971926623566323301043 7843457889935349484951565)
            ·
              refine ⟨2941296708725756056856837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7843457889935349484951565 2941296708725756056856837)
              ·
                refine ⟨551493132886079260660657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2941296708725756056856837 551493132886079260660657)
                ·
                  refine ⟨413619849664559445495493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551493132886079260660657 413619849664559445495493)
                  ·
                    refine ⟨77553721812104896030405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 413619849664559445495493 77553721812104896030405)
                    ·
                      rfl

theorem cell22_226553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_226553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226553 prefixEnd_226553 := by exact prefixLift 226553
  have htrace : WordTrace (prefixWord ++ tailWord_226553) baseStart_226553 baseEnd_226553 := by
    simpa [prefixWord, tailWord_226553, baseEnd_226553] using wordTrace_append hprefix tailTrace_226553
  have hstable : (prefixWord ++ tailWord_226553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226553).length < 2 ^ (prefixWord ++ tailWord_226553).sum := by decide
  have hdescent : baseEnd_226553 < baseStart_226553 := by decide
  rcases family_descends (prefixWord ++ tailWord_226553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226688 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_226688 : Nat := 118140960795 + 226688 * 2 ^ 59
def prefixEnd_226688 : Nat := 4983230072969 + 3 ^ 40 * 226688 * 2
def baseEnd_226688 : Nat := 77599935071009543904991

theorem tailTrace_226688 : CollatzResearch.WordTrace tailWord_226688 prefixEnd_226688 77599935071009543904991 := by
  unfold tailWord_226688
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133995301377783036616359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5511993735170377382155145 4133995301377783036616359)
  ·
    refine ⟨6200992952066674554924539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4133995301377783036616359 6200992952066674554924539)
    ·
      refine ⟨9301489428100011832386809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6200992952066674554924539 9301489428100011832386809)
      ·
        refine ⟨6976117071075008874290107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9301489428100011832386809 6976117071075008874290107)
        ·
          refine ⟨10464175606612513311435161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6976117071075008874290107 10464175606612513311435161)
          ·
            refine ⟨7848131704959384983576371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10464175606612513311435161 7848131704959384983576371)
            ·
              refine ⟨11772197557439077475364557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848131704959384983576371 11772197557439077475364557)
              ·
                refine ⟨4414574084039654053261709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11772197557439077475364557 4414574084039654053261709)
                ·
                  refine ⟨1655465281514870269973141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4414574084039654053261709 1655465281514870269973141)
                  ·
                    refine ⟨77599935071009543904991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1655465281514870269973141 77599935071009543904991)
                    ·
                      rfl

theorem cell22_226688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_226688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226688 prefixEnd_226688 := by exact prefixLift 226688
  have htrace : WordTrace (prefixWord ++ tailWord_226688) baseStart_226688 baseEnd_226688 := by
    simpa [prefixWord, tailWord_226688, baseEnd_226688] using wordTrace_append hprefix tailTrace_226688
  have hstable : (prefixWord ++ tailWord_226688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226688).length < 2 ^ (prefixWord ++ tailWord_226688).sum := by decide
  have hdescent : baseEnd_226688 < baseStart_226688 := by decide
  rcases family_descends (prefixWord ++ tailWord_226688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226722 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_226722 : Nat := 118140960795 + 226722 * 2 ^ 59
def prefixEnd_226722 : Nat := 4983230072969 + 3 ^ 40 * 226722 * 2
def baseEnd_226722 : Nat := 77611573965844788554887

theorem tailTrace_226722 : CollatzResearch.WordTrace tailWord_226722 prefixEnd_226722 77611573965844788554887 := by
  unfold tailWord_226722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067307671158097469992605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5512820456421593253313613 2067307671158097469992605)
  ·
    refine ⟨775240376684286551247227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2067307671158097469992605 775240376684286551247227)
    ·
      refine ⟨1162860565026429826870841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775240376684286551247227 1162860565026429826870841)
      ·
        refine ⟨872145423769822370153131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1162860565026429826870841 872145423769822370153131)
        ·
          refine ⟨1308218135654733555229697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872145423769822370153131 1308218135654733555229697)
          ·
            refine ⟨981163601741050166422273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308218135654733555229697 981163601741050166422273)
            ·
              refine ⟨735872701305787624816705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981163601741050166422273 735872701305787624816705)
              ·
                refine ⟨551904525979340718612529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735872701305787624816705 551904525979340718612529)
                ·
                  refine ⟨413928394484505538959397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551904525979340718612529 413928394484505538959397)
                  ·
                    refine ⟨77611573965844788554887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 413928394484505538959397 77611573965844788554887)
                    ·
                      rfl

theorem cell22_226722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_226722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226722 prefixEnd_226722 := by exact prefixLift 226722
  have htrace : WordTrace (prefixWord ++ tailWord_226722) baseStart_226722 baseEnd_226722 := by
    simpa [prefixWord, tailWord_226722, baseEnd_226722] using wordTrace_append hprefix tailTrace_226722
  have hstable : (prefixWord ++ tailWord_226722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226722).length < 2 ^ (prefixWord ++ tailWord_226722).sum := by decide
  have hdescent : baseEnd_226722 < baseStart_226722 := by decide
  rcases family_descends (prefixWord ++ tailWord_226722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226735 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 7, 3]
def baseStart_226735 : Nat := 118140960795 + 226735 * 2 ^ 59
def prefixEnd_226735 : Nat := 4983230072969 + 3 ^ 40 * 226735 * 2
def baseEnd_226735 : Nat := 77616024131517087979847

theorem tailTrace_226735 : CollatzResearch.WordTrace tailWord_226735 prefixEnd_226735 77616024131517087979847 := by
  unfold tailWord_226735
  simp only [CollatzResearch.WordTrace]
  refine ⟨8269704833585293100193659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5513136555723528733462439 8269704833585293100193659)
  ·
    refine ⟨12404557250377939650290489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8269704833585293100193659 12404557250377939650290489)
    ·
      refine ⟨9303417937783454737717867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12404557250377939650290489 9303417937783454737717867)
      ·
        refine ⟨13955126906675182106576801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9303417937783454737717867 13955126906675182106576801)
        ·
          refine ⟨10466345180006386579932601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13955126906675182106576801 10466345180006386579932601)
          ·
            refine ⟨7849758885004789934949451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10466345180006386579932601 7849758885004789934949451)
            ·
              refine ⟨11774638327507184902424177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849758885004789934949451 11774638327507184902424177)
              ·
                refine ⟨8830978745630388676818133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11774638327507184902424177 8830978745630388676818133)
                ·
                  refine ⟨206976064350712234612925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8830978745630388676818133 206976064350712234612925)
                  ·
                    refine ⟨77616024131517087979847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206976064350712234612925 77616024131517087979847)
                    ·
                      rfl

theorem cell22_226735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_226735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226735 prefixEnd_226735 := by exact prefixLift 226735
  have htrace : WordTrace (prefixWord ++ tailWord_226735) baseStart_226735 baseEnd_226735 := by
    simpa [prefixWord, tailWord_226735, baseEnd_226735] using wordTrace_append hprefix tailTrace_226735
  have hstable : (prefixWord ++ tailWord_226735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226735).length < 2 ^ (prefixWord ++ tailWord_226735).sum := by decide
  have hdescent : baseEnd_226735 < baseStart_226735 := by decide
  rcases family_descends (prefixWord ++ tailWord_226735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226750 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_226750 : Nat := 118140960795 + 226750 * 2 ^ 59
def prefixEnd_226750 : Nat := 4983230072969 + 3 ^ 40 * 226750 * 2
def baseEnd_226750 : Nat := 77621158938062048854801

theorem tailTrace_226750 : CollatzResearch.WordTrace tailWord_226750 prefixEnd_226750 77621158938062048854801 := by
  unfold tailWord_226750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033781491066368832748713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5513501285687300441326469 1033781491066368832748713)
  ·
    refine ⟨775336118299776624561535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1033781491066368832748713 775336118299776624561535)
    ·
      refine ⟨1163004177449664936842303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775336118299776624561535 1163004177449664936842303)
      ·
        refine ⟨1744506266174497405263455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1163004177449664936842303 1744506266174497405263455)
        ·
          refine ⟨2616759399261746107895183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1744506266174497405263455 2616759399261746107895183)
          ·
            refine ⟨3925139098892619161842775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616759399261746107895183 3925139098892619161842775)
            ·
              refine ⟨5887708648338928742764163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925139098892619161842775 5887708648338928742764163)
              ·
                refine ⟨8831562972508393114146245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887708648338928742764163 8831562972508393114146245)
                ·
                  refine ⟨1655918057345323708902421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8831562972508393114146245 1655918057345323708902421)
                  ·
                    refine ⟨77621158938062048854801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1655918057345323708902421 77621158938062048854801)
                    ·
                      rfl

theorem cell22_226750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_226750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226750 prefixEnd_226750 := by exact prefixLift 226750
  have htrace : WordTrace (prefixWord ++ tailWord_226750) baseStart_226750 baseEnd_226750 := by
    simpa [prefixWord, tailWord_226750, baseEnd_226750] using wordTrace_append hprefix tailTrace_226750
  have hstable : (prefixWord ++ tailWord_226750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226750).length < 2 ^ (prefixWord ++ tailWord_226750).sum := by decide
  have hdescent : baseEnd_226750 < baseStart_226750 := by decide
  rcases family_descends (prefixWord ++ tailWord_226750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226795 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 3, 4]
def baseStart_226795 : Nat := 118140960795 + 226795 * 2 ^ 59
def prefixEnd_226795 : Nat := 4983230072969 + 3 ^ 40 * 226795 * 2
def baseEnd_226795 : Nat := 77636563357696931479663

theorem tailTrace_226795 : CollatzResearch.WordTrace tailWord_226795 prefixEnd_226795 77636563357696931479663 := by
  unfold tailWord_226795
  simp only [CollatzResearch.WordTrace]
  refine ⟨8271893213367923347377839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5514595475578615564918559 8271893213367923347377839)
  ·
    refine ⟨12407839820051885021066759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8271893213367923347377839 12407839820051885021066759)
    ·
      refine ⟨18611759730077827531600139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12407839820051885021066759 18611759730077827531600139)
      ·
        refine ⟨27917639595116741297400209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18611759730077827531600139 27917639595116741297400209)
        ·
          refine ⟨20938229696337555973050157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27917639595116741297400209 20938229696337555973050157)
          ·
            refine ⟨7851836136126583489893809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20938229696337555973050157 7851836136126583489893809)
            ·
              refine ⟨5888877102094937617420357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7851836136126583489893809 5888877102094937617420357)
              ·
                refine ⟨1104164456642800803266317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5888877102094937617420357 1104164456642800803266317)
                ·
                  refine ⟨414061671241050301224869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104164456642800803266317 414061671241050301224869)
                  ·
                    refine ⟨77636563357696931479663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414061671241050301224869 77636563357696931479663)
                    ·
                      rfl

theorem cell22_226795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 4].length) (baseStart_226795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226795 prefixEnd_226795 := by exact prefixLift 226795
  have htrace : WordTrace (prefixWord ++ tailWord_226795) baseStart_226795 baseEnd_226795 := by
    simpa [prefixWord, tailWord_226795, baseEnd_226795] using wordTrace_append hprefix tailTrace_226795
  have hstable : (prefixWord ++ tailWord_226795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226795).length < 2 ^ (prefixWord ++ tailWord_226795).sum := by decide
  have hdescent : baseEnd_226795 < baseStart_226795 := by decide
  rcases family_descends (prefixWord ++ tailWord_226795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226810 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_226810 : Nat := 118140960795 + 226810 * 2 ^ 59
def prefixEnd_226810 : Nat := 4983230072969 + 3 ^ 40 * 226810 * 2
def baseEnd_226810 : Nat := 25880566054747297451539

theorem tailTrace_226810 : CollatzResearch.WordTrace tailWord_226810 prefixEnd_226810 25880566054747297451539 := by
  unfold tailWord_226810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2068110077078395227293471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5514960205542387272782589 2068110077078395227293471)
  ·
    refine ⟨3102165115617592840940207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2068110077078395227293471 3102165115617592840940207)
    ·
      refine ⟨4653247673426389261410311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3102165115617592840940207 4653247673426389261410311)
      ·
        refine ⟨6979871510139583892115467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4653247673426389261410311 6979871510139583892115467)
        ·
          refine ⟨10469807265209375838173201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6979871510139583892115467 10469807265209375838173201)
          ·
            refine ⟨7852355448907031878629901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10469807265209375838173201 7852355448907031878629901)
            ·
              refine ⟨2944633293340136954486213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7852355448907031878629901 2944633293340136954486213)
              ·
                refine ⟨552118742501275678966165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2944633293340136954486213 552118742501275678966165)
                ·
                  refine ⟨25880566054747297451539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 552118742501275678966165 25880566054747297451539)
                  ·
                    rfl

theorem cell22_226810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_226810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226810 prefixEnd_226810 := by exact prefixLift 226810
  have htrace : WordTrace (prefixWord ++ tailWord_226810) baseStart_226810 baseEnd_226810 := by
    simpa [prefixWord, tailWord_226810, baseEnd_226810] using wordTrace_append hprefix tailTrace_226810
  have hstable : (prefixWord ++ tailWord_226810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226810).length < 2 ^ (prefixWord ++ tailWord_226810).sum := by decide
  have hdescent : baseEnd_226810 < baseStart_226810 := by decide
  rcases family_descends (prefixWord ++ tailWord_226810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226812 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_226812 : Nat := 118140960795 + 226812 * 2 ^ 59
def prefixEnd_226812 : Nat := 4983230072969 + 3 ^ 40 * 226812 * 2
def baseEnd_226812 : Nat := 77642382805114553804611

theorem tailTrace_226812 : CollatzResearch.WordTrace tailWord_226812 prefixEnd_226812 77642382805114553804611 := by
  unfold tailWord_226812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4136256627153167625373345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5515008836204223500497793 4136256627153167625373345)
  ·
    refine ⟨3102192470364875719030009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4136256627153167625373345 3102192470364875719030009)
    ·
      refine ⟨2326644352773656789272507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3102192470364875719030009 2326644352773656789272507)
      ·
        refine ⟨3489966529160485183908761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2326644352773656789272507 3489966529160485183908761)
        ·
          refine ⟨2617474896870363887931571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3489966529160485183908761 2617474896870363887931571)
          ·
            refine ⟨3926212345305545831897357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617474896870363887931571 3926212345305545831897357)
            ·
              refine ⟨1472329629489579686961509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3926212345305545831897357 1472329629489579686961509)
              ·
                refine ⟨276061805529296191305283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1472329629489579686961509 276061805529296191305283)
                ·
                  refine ⟨414092708293944286957925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276061805529296191305283 414092708293944286957925)
                  ·
                    refine ⟨77642382805114553804611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414092708293944286957925 77642382805114553804611)
                    ·
                      rfl

theorem cell22_226812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_226812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226812 prefixEnd_226812 := by exact prefixLift 226812
  have htrace : WordTrace (prefixWord ++ tailWord_226812) baseStart_226812 baseEnd_226812 := by
    simpa [prefixWord, tailWord_226812, baseEnd_226812] using wordTrace_append hprefix tailTrace_226812
  have hstable : (prefixWord ++ tailWord_226812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226812).length < 2 ^ (prefixWord ++ tailWord_226812).sum := by decide
  have hdescent : baseEnd_226812 < baseStart_226812 := by decide
  rcases family_descends (prefixWord ++ tailWord_226812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226820 : List Nat := [2, 3, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_226820 : Nat := 118140960795 + 226820 * 2 ^ 59
def prefixEnd_226820 : Nat := 4983230072969 + 3 ^ 40 * 226820 * 2
def baseEnd_226820 : Nat := 77645121368605199604587

theorem tailTrace_226820 : CollatzResearch.WordTrace tailWord_226820 prefixEnd_226820 77645121368605199604587 := by
  unfold tailWord_226820
  simp only [CollatzResearch.WordTrace]
  refine ⟨4136402519138676308518957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5515203358851568411358609 4136402519138676308518957)
  ·
    refine ⟨1551150944677003615694609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4136402519138676308518957 1551150944677003615694609)
    ·
      refine ⟨1163363208507752711770957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1551150944677003615694609 1163363208507752711770957)
      ·
        refine ⟨436261203190407266914109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1163363208507752711770957 436261203190407266914109)
        ·
          refine ⟨163597951196402725092791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436261203190407266914109 163597951196402725092791)
          ·
            refine ⟨245396926794604087639187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163597951196402725092791 245396926794604087639187)
            ·
              refine ⟨368095390191906131458781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245396926794604087639187 368095390191906131458781)
              ·
                refine ⟨138035771321964799297043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368095390191906131458781 138035771321964799297043)
                ·
                  refine ⟨207053656982947198945565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138035771321964799297043 207053656982947198945565)
                  ·
                    refine ⟨77645121368605199604587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207053656982947198945565 77645121368605199604587)
                    ·
                      rfl

theorem cell22_226820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_226820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226820 prefixEnd_226820 := by exact prefixLift 226820
  have htrace : WordTrace (prefixWord ++ tailWord_226820) baseStart_226820 baseEnd_226820 := by
    simpa [prefixWord, tailWord_226820, baseEnd_226820] using wordTrace_append hprefix tailTrace_226820
  have hstable : (prefixWord ++ tailWord_226820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226820).length < 2 ^ (prefixWord ++ tailWord_226820).sum := by decide
  have hdescent : baseEnd_226820 < baseStart_226820 := by decide
  rcases family_descends (prefixWord ++ tailWord_226820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226825 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_226825 : Nat := 118140960795 + 226825 * 2 ^ 59
def prefixEnd_226825 : Nat := 4983230072969 + 3 ^ 40 * 226825 * 2
def baseEnd_226825 : Nat := 77646832970786853229571

theorem tailTrace_226825 : CollatzResearch.WordTrace tailWord_226825 prefixEnd_226825 77646832970786853229571 := by
  unfold tailWord_226825
  simp only [CollatzResearch.WordTrace]
  refine ⟨8272987403259238470969929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5515324935506158980646619 8272987403259238470969929)
  ·
    refine ⟨6204740552444428853227447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8272987403259238470969929 6204740552444428853227447)
    ·
      refine ⟨9307110828666643279841171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6204740552444428853227447 9307110828666643279841171)
      ·
        refine ⟨13960666242999964919761757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9307110828666643279841171 13960666242999964919761757)
        ·
          refine ⟨5235249841124986844910659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13960666242999964919761757 5235249841124986844910659)
          ·
            refine ⟨7852874761687480267365989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235249841124986844910659 7852874761687480267365989)
            ·
              refine ⟨1472414017816402550131123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7852874761687480267365989 1472414017816402550131123)
              ·
                refine ⟨2208621026724603825196685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472414017816402550131123 2208621026724603825196685)
                ·
                  refine ⟨828232885021726434448757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2208621026724603825196685 828232885021726434448757)
                  ·
                    refine ⟨77646832970786853229571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 828232885021726434448757 77646832970786853229571)
                    ·
                      rfl

theorem cell22_226825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_226825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226825 prefixEnd_226825 := by exact prefixLift 226825
  have htrace : WordTrace (prefixWord ++ tailWord_226825) baseStart_226825 baseEnd_226825 := by
    simpa [prefixWord, tailWord_226825, baseEnd_226825] using wordTrace_append hprefix tailTrace_226825
  have hstable : (prefixWord ++ tailWord_226825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226825).length < 2 ^ (prefixWord ++ tailWord_226825).sum := by decide
  have hdescent : baseEnd_226825 < baseStart_226825 := by decide
  rcases family_descends (prefixWord ++ tailWord_226825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226893 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_226893 : Nat := 118140960795 + 226893 * 2 ^ 59
def prefixEnd_226893 : Nat := 4983230072969 + 3 ^ 40 * 226893 * 2
def baseEnd_226893 : Nat := 77670110760457342529363

theorem tailTrace_226893 : CollatzResearch.WordTrace tailWord_226893 prefixEnd_226893 77670110760457342529363 := by
  unfold tailWord_226893
  simp only [CollatzResearch.WordTrace]
  refine ⟨8275467567012886084445333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5516978378008590722963555 8275467567012886084445333)
  ·
    refine ⟨387912542203729035208375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8275467567012886084445333 387912542203729035208375)
    ·
      refine ⟨581868813305593552812563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387912542203729035208375 581868813305593552812563)
      ·
        refine ⟨872803219958390329218845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581868813305593552812563 872803219958390329218845)
        ·
          refine ⟨327301207484396373457067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 872803219958390329218845 327301207484396373457067)
          ·
            refine ⟨490951811226594560185601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327301207484396373457067 490951811226594560185601)
            ·
              refine ⟨368213858419945920139201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490951811226594560185601 368213858419945920139201)
              ·
                refine ⟨276160393814959440104401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368213858419945920139201 276160393814959440104401)
                ·
                  refine ⟨207120295361219580078301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276160393814959440104401 207120295361219580078301)
                  ·
                    refine ⟨77670110760457342529363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207120295361219580078301 77670110760457342529363)
                    ·
                      rfl

theorem cell22_226893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_226893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226893 prefixEnd_226893 := by exact prefixLift 226893
  have htrace : WordTrace (prefixWord ++ tailWord_226893) baseStart_226893 baseEnd_226893 := by
    simpa [prefixWord, tailWord_226893, baseEnd_226893] using wordTrace_append hprefix tailTrace_226893
  have hstable : (prefixWord ++ tailWord_226893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226893).length < 2 ^ (prefixWord ++ tailWord_226893).sum := by decide
  have hdescent : baseEnd_226893 < baseStart_226893 := by decide
  rcases family_descends (prefixWord ++ tailWord_226893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226992 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_226992 : Nat := 118140960795 + 226992 * 2 ^ 59
def prefixEnd_226992 : Nat := 4983230072969 + 3 ^ 40 * 226992 * 2
def baseEnd_226992 : Nat := 77704000483654084304059

theorem tailTrace_226992 : CollatzResearch.WordTrace tailWord_226992 prefixEnd_226992 77704000483654084304059 := by
  unfold tailWord_226992
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139539196827112996149615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5519385595769483994866153 4139539196827112996149615)
  ·
    refine ⟨6209308795240669494224423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4139539196827112996149615 6209308795240669494224423)
    ·
      refine ⟨9313963192861004241336635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6209308795240669494224423 9313963192861004241336635)
      ·
        refine ⟨13970944789291506362004953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9313963192861004241336635 13970944789291506362004953)
        ·
          refine ⟨10478208591968629771503715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13970944789291506362004953 10478208591968629771503715)
          ·
            refine ⟨15717312887952944657255573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10478208591968629771503715 15717312887952944657255573)
            ·
              refine ⟨736749041622794280808855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15717312887952944657255573 736749041622794280808855)
              ·
                refine ⟨1105123562434191421213283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736749041622794280808855 1105123562434191421213283)
                ·
                  refine ⟨1657685343651287131819925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105123562434191421213283 1657685343651287131819925)
                  ·
                    refine ⟨77704000483654084304059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1657685343651287131819925 77704000483654084304059)
                    ·
                      rfl

theorem cell22_226992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_226992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226992 prefixEnd_226992 := by exact prefixLift 226992
  have htrace : WordTrace (prefixWord ++ tailWord_226992) baseStart_226992 baseEnd_226992 := by
    simpa [prefixWord, tailWord_226992, baseEnd_226992] using wordTrace_append hprefix tailTrace_226992
  have hstable : (prefixWord ++ tailWord_226992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226992).length < 2 ^ (prefixWord ++ tailWord_226992).sum := by decide
  have hdescent : baseEnd_226992 < baseStart_226992 := by decide
  rcases family_descends (prefixWord ++ tailWord_226992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226994 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_226994 : Nat := 118140960795 + 226994 * 2 ^ 59
def prefixEnd_226994 : Nat := 4983230072969 + 3 ^ 40 * 226994 * 2
def baseEnd_226994 : Nat := 77704685124526745754053

theorem tailTrace_226994 : CollatzResearch.WordTrace tailWord_226994 prefixEnd_226994 77704685124526745754053 := by
  unfold tailWord_226994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069787834911745083468009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5519434226431320222581357 2069787834911745083468009)
  ·
    refine ⟨1552340876183808812601007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2069787834911745083468009 1552340876183808812601007)
    ·
      refine ⟨2328511314275713218901511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1552340876183808812601007 2328511314275713218901511)
      ·
        refine ⟨3492766971413569828352267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328511314275713218901511 3492766971413569828352267)
        ·
          refine ⟨5239150457120354742528401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492766971413569828352267 5239150457120354742528401)
          ·
            refine ⟨3929362842840266056896301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5239150457120354742528401 3929362842840266056896301)
            ·
              refine ⟨1473511066065099771336113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3929362842840266056896301 1473511066065099771336113)
              ·
                refine ⟨1105133299548824828502085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473511066065099771336113 1105133299548824828502085)
                ·
                  refine ⟨207212493665404655344141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1105133299548824828502085 207212493665404655344141)
                  ·
                    refine ⟨77704685124526745754053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207212493665404655344141 77704685124526745754053)
                    ·
                      rfl

theorem cell22_226994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_226994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226994 prefixEnd_226994 := by exact prefixLift 226994
  have htrace : WordTrace (prefixWord ++ tailWord_226994) baseStart_226994 baseEnd_226994 := by
    simpa [prefixWord, tailWord_226994, baseEnd_226994] using wordTrace_append hprefix tailTrace_226994
  have hstable : (prefixWord ++ tailWord_226994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226994).length < 2 ^ (prefixWord ++ tailWord_226994).sum := by decide
  have hdescent : baseEnd_226994 < baseStart_226994 := by decide
  rcases family_descends (prefixWord ++ tailWord_226994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226998 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_226998 : Nat := 118140960795 + 226998 * 2 ^ 59
def prefixEnd_226998 : Nat := 4983230072969 + 3 ^ 40 * 226998 * 2
def baseEnd_226998 : Nat := 77706054406272068654041

theorem tailTrace_226998 : CollatzResearch.WordTrace tailWord_226998 prefixEnd_226998 77706054406272068654041 := by
  unfold tailWord_226998
  simp only [CollatzResearch.WordTrace]
  refine ⟨517456076977030563563603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5519531487754992678011765 517456076977030563563603)
  ·
    refine ⟨776184115465545845345405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 517456076977030563563603 776184115465545845345405)
    ·
      refine ⟨291069043299579692004527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 776184115465545845345405 291069043299579692004527)
      ·
        refine ⟨436603564949369538006791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291069043299579692004527 436603564949369538006791)
        ·
          refine ⟨654905347424054307010187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436603564949369538006791 654905347424054307010187)
          ·
            refine ⟨982358021136081460515281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654905347424054307010187 982358021136081460515281)
            ·
              refine ⟨736768515852061095386461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982358021136081460515281 736768515852061095386461)
              ·
                refine ⟨276288193444522910769923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736768515852061095386461 276288193444522910769923)
                ·
                  refine ⟨414432290166784366154885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276288193444522910769923 414432290166784366154885)
                  ·
                    refine ⟨77706054406272068654041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414432290166784366154885 77706054406272068654041)
                    ·
                      rfl

theorem cell22_226998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_226998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_226998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_226998 prefixEnd_226998 := by exact prefixLift 226998
  have htrace : WordTrace (prefixWord ++ tailWord_226998) baseStart_226998 baseEnd_226998 := by
    simpa [prefixWord, tailWord_226998, baseEnd_226998] using wordTrace_append hprefix tailTrace_226998
  have hstable : (prefixWord ++ tailWord_226998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226998).length < 2 ^ (prefixWord ++ tailWord_226998).sum := by decide
  have hdescent : baseEnd_226998 < baseStart_226998 := by decide
  rcases family_descends (prefixWord ++ tailWord_226998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227028 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_227028 : Nat := 118140960795 + 227028 * 2 ^ 59
def prefixEnd_227028 : Nat := 4983230072969 + 3 ^ 40 * 227028 * 2
def baseEnd_227028 : Nat := 77716324019361990403949

theorem tailTrace_227028 : CollatzResearch.WordTrace tailWord_227028 prefixEnd_227028 77716324019361990403949 := by
  unfold tailWord_227028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140195710761902070304869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5520260947682536093739825 4140195710761902070304869)
  ·
    refine ⟨776286695767856638182163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4140195710761902070304869 776286695767856638182163)
    ·
      refine ⟨1164430043651784957273245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776286695767856638182163 1164430043651784957273245)
      ·
        refine ⟨436661266369419358977467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1164430043651784957273245 436661266369419358977467)
        ·
          refine ⟨654991899554129038466201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436661266369419358977467 654991899554129038466201)
          ·
            refine ⟨491243924665596778849651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654991899554129038466201 491243924665596778849651)
            ·
              refine ⟨736865886998395168274477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491243924665596778849651 736865886998395168274477)
              ·
                refine ⟨276324707624398188102929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736865886998395168274477 276324707624398188102929)
                ·
                  refine ⟨207243530718298641077197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276324707624398188102929 207243530718298641077197)
                  ·
                    refine ⟨77716324019361990403949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207243530718298641077197 77716324019361990403949)
                    ·
                      rfl

theorem cell22_227028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_227028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227028 prefixEnd_227028 := by exact prefixLift 227028
  have htrace : WordTrace (prefixWord ++ tailWord_227028) baseStart_227028 baseEnd_227028 := by
    simpa [prefixWord, tailWord_227028, baseEnd_227028] using wordTrace_append hprefix tailTrace_227028
  have hstable : (prefixWord ++ tailWord_227028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227028).length < 2 ^ (prefixWord ++ tailWord_227028).sum := by decide
  have hdescent : baseEnd_227028 < baseStart_227028 := by decide
  rcases family_descends (prefixWord ++ tailWord_227028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227039 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 5, 3]
def baseStart_227039 : Nat := 118140960795 + 227039 * 2 ^ 59
def prefixEnd_227039 : Nat := 4983230072969 + 3 ^ 40 * 227039 * 2
def baseEnd_227039 : Nat := 77720089544161628378915

theorem tailTrace_227039 : CollatzResearch.WordTrace tailWord_227039 prefixEnd_227039 77720089544161628378915 := by
  unfold tailWord_227039
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280792624483953019260171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5520528416322635346173447 8280792624483953019260171)
  ·
    refine ⟨12421188936725929528890257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8280792624483953019260171 12421188936725929528890257)
    ·
      refine ⟨9315891702544447146667693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12421188936725929528890257 9315891702544447146667693)
      ·
        refine ⟨3493459388454167680000385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9315891702544447146667693 3493459388454167680000385)
        ·
          refine ⟨2620094541340625760000289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3493459388454167680000385 2620094541340625760000289)
          ·
            refine ⟨1965070906005469320000217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620094541340625760000289 1965070906005469320000217)
            ·
              refine ⟨1473803179504101990000163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965070906005469320000217 1473803179504101990000163)
              ·
                refine ⟨2210704769256152985000245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473803179504101990000163 2210704769256152985000245)
                ·
                  refine ⟨207253572117764342343773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2210704769256152985000245 207253572117764342343773)
                  ·
                    refine ⟨77720089544161628378915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207253572117764342343773 77720089544161628378915)
                    ·
                      rfl

theorem cell22_227039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_227039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227039 prefixEnd_227039 := by exact prefixLift 227039
  have htrace : WordTrace (prefixWord ++ tailWord_227039) baseStart_227039 baseEnd_227039 := by
    simpa [prefixWord, tailWord_227039, baseEnd_227039] using wordTrace_append hprefix tailTrace_227039
  have hstable : (prefixWord ++ tailWord_227039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227039).length < 2 ^ (prefixWord ++ tailWord_227039).sum := by decide
  have hdescent : baseEnd_227039 < baseStart_227039 := by decide
  rcases family_descends (prefixWord ++ tailWord_227039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227052 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 9]
def baseStart_227052 : Nat := 118140960795 + 227052 * 2 ^ 59
def prefixEnd_227052 : Nat := 4983230072969 + 3 ^ 40 * 227052 * 2
def baseEnd_227052 : Nat := 25908179903277975934625

theorem tailTrace_227052 : CollatzResearch.WordTrace tailWord_227052 prefixEnd_227052 25908179903277975934625 := by
  unfold tailWord_227052
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140633386718428119741705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5520844515624570826322273 4140633386718428119741705)
  ·
    refine ⟨3105475040038821089806279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4140633386718428119741705 3105475040038821089806279)
    ·
      refine ⟨4658212560058231634709419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105475040038821089806279 4658212560058231634709419)
      ·
        refine ⟨6987318840087347452064129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658212560058231634709419 6987318840087347452064129)
        ·
          refine ⟨5240489130065510589048097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6987318840087347452064129 5240489130065510589048097)
          ·
            refine ⟨3930366847549132941786073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5240489130065510589048097 3930366847549132941786073)
            ·
              refine ⟨2947775135661849706339555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3930366847549132941786073 2947775135661849706339555)
              ·
                refine ⟨4421662703492774559509333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947775135661849706339555 4421662703492774559509333)
                ·
                  refine ⟨25908179903277975934625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4421662703492774559509333 25908179903277975934625)
                  ·
                    rfl

theorem cell22_227052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_227052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227052 prefixEnd_227052 := by exact prefixLift 227052
  have htrace : WordTrace (prefixWord ++ tailWord_227052) baseStart_227052 baseEnd_227052 := by
    simpa [prefixWord, tailWord_227052, baseEnd_227052] using wordTrace_append hprefix tailTrace_227052
  have hstable : (prefixWord ++ tailWord_227052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227052).length < 2 ^ (prefixWord ++ tailWord_227052).sum := by decide
  have hdescent : baseEnd_227052 < baseStart_227052 := by decide
  rcases family_descends (prefixWord ++ tailWord_227052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227116 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_227116 : Nat := 118140960795 + 227116 * 2 ^ 59
def prefixEnd_227116 : Nat := 4983230072969 + 3 ^ 40 * 227116 * 2
def baseEnd_227116 : Nat := 77746448217759094203679

theorem tailTrace_227116 : CollatzResearch.WordTrace tailWord_227116 prefixEnd_227116 77746448217759094203679 := by
  unfold tailWord_227116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4141800522602497584906601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5522400696803330113208801 4141800522602497584906601)
  ·
    refine ⟨3106350391951873188679951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4141800522602497584906601 3106350391951873188679951)
    ·
      refine ⟨4659525587927809783019927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3106350391951873188679951 4659525587927809783019927)
      ·
        refine ⟨6989288381891714674529891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4659525587927809783019927 6989288381891714674529891)
        ·
          refine ⟨10483932572837572011794837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989288381891714674529891 10483932572837572011794837)
          ·
            refine ⟨491434339351761188052883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10483932572837572011794837 491434339351761188052883)
            ·
              refine ⟨737151509027641782079325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491434339351761188052883 737151509027641782079325)
              ·
                refine ⟨276431815885365668279747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737151509027641782079325 276431815885365668279747)
                ·
                  refine ⟨414647723828048502419621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276431815885365668279747 414647723828048502419621)
                  ·
                    refine ⟨77746448217759094203679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414647723828048502419621 77746448217759094203679)
                    ·
                      rfl

theorem cell22_227116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_227116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227116 prefixEnd_227116 := by exact prefixLift 227116
  have htrace : WordTrace (prefixWord ++ tailWord_227116) baseStart_227116 baseEnd_227116 := by
    simpa [prefixWord, tailWord_227116, baseEnd_227116] using wordTrace_append hprefix tailTrace_227116
  have hstable : (prefixWord ++ tailWord_227116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227116).length < 2 ^ (prefixWord ++ tailWord_227116).sum := by decide
  have hdescent : baseEnd_227116 < baseStart_227116 := by decide
  rcases family_descends (prefixWord ++ tailWord_227116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227144 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_227144 : Nat := 118140960795 + 227144 * 2 ^ 59
def prefixEnd_227144 : Nat := 4983230072969 + 3 ^ 40 * 227144 * 2
def baseEnd_227144 : Nat := 77756033189976354503593

theorem tailTrace_227144 : CollatzResearch.WordTrace tailWord_227144 prefixEnd_227144 77756033189976354503593 := by
  unfold tailWord_227144
  simp only [CollatzResearch.WordTrace]
  refine ⟨4142311144551777975916243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5523081526069037301221657 4142311144551777975916243)
  ·
    refine ⟨6213466716827666963874365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4142311144551777975916243 6213466716827666963874365)
    ·
      refine ⟨2330050018810375111452887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6213466716827666963874365 2330050018810375111452887)
      ·
        refine ⟨3495075028215562667179331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330050018810375111452887 3495075028215562667179331)
        ·
          refine ⟨5242612542323344000768997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3495075028215562667179331 5242612542323344000768997)
          ·
            refine ⟨982989851685627000144187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5242612542323344000768997 982989851685627000144187)
            ·
              refine ⟨1474484777528440500216281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982989851685627000144187 1474484777528440500216281)
              ·
                refine ⟨1105863583146330375162211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474484777528440500216281 1105863583146330375162211)
                ·
                  refine ⟨1658795374719495562743317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105863583146330375162211 1658795374719495562743317)
                  ·
                    refine ⟨77756033189976354503593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1658795374719495562743317 77756033189976354503593)
                    ·
                      rfl

theorem cell22_227144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_227144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227144 prefixEnd_227144 := by exact prefixLift 227144
  have htrace : WordTrace (prefixWord ++ tailWord_227144) baseStart_227144 baseEnd_227144 := by
    simpa [prefixWord, tailWord_227144, baseEnd_227144] using wordTrace_append hprefix tailTrace_227144
  have hstable : (prefixWord ++ tailWord_227144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227144).length < 2 ^ (prefixWord ++ tailWord_227144).sum := by decide
  have hdescent : baseEnd_227144 < baseStart_227144 := by decide
  rcases family_descends (prefixWord ++ tailWord_227144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227285 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 1, 4]
def baseStart_227285 : Nat := 118140960795 + 227285 * 2 ^ 59
def prefixEnd_227285 : Nat := 4983230072969 + 3 ^ 40 * 227285 * 2
def baseEnd_227285 : Nat := 77804300371498986728161

theorem tailTrace_227285 : CollatzResearch.WordTrace tailWord_227285 prefixEnd_227285 77804300371498986728161 := by
  unfold tailWord_227285
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289764981592737032715309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5526509987728491355143539 8289764981592737032715309)
  ·
    refine ⟨3108661868097276387268241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8289764981592737032715309 3108661868097276387268241)
    ·
      refine ⟨2331496401072957290451181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3108661868097276387268241 2331496401072957290451181)
      ·
        refine ⟨874311150402358983919193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2331496401072957290451181 874311150402358983919193)
        ·
          refine ⟨655733362801769237939395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874311150402358983919193 655733362801769237939395)
          ·
            refine ⟨983600044202653856909093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655733362801769237939395 983600044202653856909093)
            ·
              refine ⟨184425008287997598170455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 983600044202653856909093 184425008287997598170455)
              ·
                refine ⟨276637512431996397255683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184425008287997598170455 276637512431996397255683)
                ·
                  refine ⟨414956268647994595883525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276637512431996397255683 414956268647994595883525)
                  ·
                    refine ⟨77804300371498986728161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414956268647994595883525 77804300371498986728161)
                    ·
                      rfl

theorem cell22_227285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_227285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227285 prefixEnd_227285 := by exact prefixLift 227285
  have htrace : WordTrace (prefixWord ++ tailWord_227285) baseStart_227285 baseEnd_227285 := by
    simpa [prefixWord, tailWord_227285, baseEnd_227285] using wordTrace_append hprefix tailTrace_227285
  have hstable : (prefixWord ++ tailWord_227285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227285).length < 2 ^ (prefixWord ++ tailWord_227285).sum := by decide
  have hdescent : baseEnd_227285 < baseStart_227285 := by decide
  rcases family_descends (prefixWord ++ tailWord_227285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227296 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_227296 : Nat := 118140960795 + 227296 * 2 ^ 59
def prefixEnd_227296 : Nat := 4983230072969 + 3 ^ 40 * 227296 * 2
def baseEnd_227296 : Nat := 77808065896298624703127

theorem tailTrace_227296 : CollatzResearch.WordTrace tailWord_227296 prefixEnd_227296 77808065896298624703127 := by
  unfold tailWord_227296
  simp only [CollatzResearch.WordTrace]
  refine ⟨4145083092276442955682871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5526777456368590607577161 4145083092276442955682871)
  ·
    refine ⟨6217624638414664433524307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4145083092276442955682871 6217624638414664433524307)
    ·
      refine ⟨9326436957621996650286461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6217624638414664433524307 9326436957621996650286461)
      ·
        refine ⟨3497413859108248743857423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9326436957621996650286461 3497413859108248743857423)
        ·
          refine ⟨5246120788662373115786135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497413859108248743857423 5246120788662373115786135)
          ·
            refine ⟨7869181182993559673679203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5246120788662373115786135 7869181182993559673679203)
            ·
              refine ⟨11803771774490339510518805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869181182993559673679203 11803771774490339510518805)
              ·
                refine ⟨553301801929234664555569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11803771774490339510518805 553301801929234664555569)
                ·
                  refine ⟨414976351446925998416677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553301801929234664555569 414976351446925998416677)
                  ·
                    refine ⟨77808065896298624703127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414976351446925998416677 77808065896298624703127)
                    ·
                      rfl

theorem cell22_227296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_227296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227296 prefixEnd_227296 := by exact prefixLift 227296
  have htrace : WordTrace (prefixWord ++ tailWord_227296) baseStart_227296 baseEnd_227296 := by
    simpa [prefixWord, tailWord_227296, baseEnd_227296] using wordTrace_append hprefix tailTrace_227296
  have hstable : (prefixWord ++ tailWord_227296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227296).length < 2 ^ (prefixWord ++ tailWord_227296).sum := by decide
  have hdescent : baseEnd_227296 < baseStart_227296 := by decide
  rcases family_descends (prefixWord ++ tailWord_227296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227433 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_227433 : Nat := 118140960795 + 227433 * 2 ^ 59
def prefixEnd_227433 : Nat := 4983230072969 + 3 ^ 40 * 227433 * 2
def baseEnd_227433 : Nat := 77854963796075934027707

theorem tailTrace_227433 : CollatzResearch.WordTrace tailWord_227433 prefixEnd_227433 77854963796075934027707 := by
  unfold tailWord_227433
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295162985056558309102953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5530108656704372206068635 8295162985056558309102953)
  ·
    refine ⟨6221372238792418731827215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8295162985056558309102953 6221372238792418731827215)
    ·
      refine ⟨9332058358188628097740823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6221372238792418731827215 9332058358188628097740823)
      ·
        refine ⟨13998087537282942146611235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9332058358188628097740823 13998087537282942146611235)
        ·
          refine ⟨20997131305924413219916853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13998087537282942146611235 20997131305924413219916853)
          ·
            refine ⟨1968481059930413739367205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20997131305924413219916853 1968481059930413739367205)
            ·
              refine ⟨369090198736952576131351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1968481059930413739367205 369090198736952576131351)
              ·
                refine ⟨553635298105428864197027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369090198736952576131351 553635298105428864197027)
                ·
                  refine ⟨830452947158143296295541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553635298105428864197027 830452947158143296295541)
                  ·
                    refine ⟨77854963796075934027707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 830452947158143296295541 77854963796075934027707)
                    ·
                      rfl

theorem cell22_227433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_227433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227433 prefixEnd_227433 := by exact prefixLift 227433
  have htrace : WordTrace (prefixWord ++ tailWord_227433) baseStart_227433 baseEnd_227433 := by
    simpa [prefixWord, tailWord_227433, baseEnd_227433] using wordTrace_append hprefix tailTrace_227433
  have hstable : (prefixWord ++ tailWord_227433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227433).length < 2 ^ (prefixWord ++ tailWord_227433).sum := by decide
  have hdescent : baseEnd_227433 < baseStart_227433 := by decide
  rcases family_descends (prefixWord ++ tailWord_227433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227553 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 8]
def baseStart_227553 : Nat := 118140960795 + 227553 * 2 ^ 59
def prefixEnd_227553 : Nat := 4983230072969 + 3 ^ 40 * 227553 * 2
def baseEnd_227553 : Nat := 25965347416145207009113

theorem tailTrace_227553 : CollatzResearch.WordTrace tailWord_227553 prefixEnd_227553 25965347416145207009113 := by
  unfold tailWord_227553
  simp only [CollatzResearch.WordTrace]
  refine ⟨8299539744621818803471313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5533026496414545868980875 8299539744621818803471313)
  ·
    refine ⟨6224654808466364102603485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8299539744621818803471313 6224654808466364102603485)
    ·
      refine ⟨2334245553174886538476307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6224654808466364102603485 2334245553174886538476307)
      ·
        refine ⟨3501368329762329807714461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2334245553174886538476307 3501368329762329807714461)
        ·
          refine ⟨1313013123660873677892923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3501368329762329807714461 1313013123660873677892923)
          ·
            refine ⟨1969519685491310516839385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313013123660873677892923 1969519685491310516839385)
            ·
              refine ⟨1477139764118482887629539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1969519685491310516839385 1477139764118482887629539)
              ·
                refine ⟨2215709646177724331444309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477139764118482887629539 2215709646177724331444309)
                ·
                  refine ⟨25965347416145207009113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2215709646177724331444309 25965347416145207009113)
                  ·
                    rfl

theorem cell22_227553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_227553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227553 prefixEnd_227553 := by exact prefixLift 227553
  have htrace : WordTrace (prefixWord ++ tailWord_227553) baseStart_227553 baseEnd_227553 := by
    simpa [prefixWord, tailWord_227553, baseEnd_227553] using wordTrace_append hprefix tailTrace_227553
  have hstable : (prefixWord ++ tailWord_227553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227553).length < 2 ^ (prefixWord ++ tailWord_227553).sum := by decide
  have hdescent : baseEnd_227553 < baseStart_227553 := by decide
  rcases family_descends (prefixWord ++ tailWord_227553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227636 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_227636 : Nat := 118140960795 + 227636 * 2 ^ 59
def prefixEnd_227636 : Nat := 4983230072969 + 3 ^ 40 * 227636 * 2
def baseEnd_227636 : Nat := 77924454844651071202085

theorem tailTrace_227636 : CollatzResearch.WordTrace tailWord_227636 prefixEnd_227636 77924454844651071202085 := by
  unfold tailWord_227636
  simp only [CollatzResearch.WordTrace]
  refine ⟨4151283501660561989371381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5535044668880749319161841 4151283501660561989371381)
  ·
    refine ⟨389182828280677686503567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4151283501660561989371381 389182828280677686503567)
    ·
      refine ⟨583774242421016529755351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389182828280677686503567 583774242421016529755351)
      ·
        refine ⟨875661363631524794633027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583774242421016529755351 875661363631524794633027)
        ·
          refine ⟨1313492045447287191949541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875661363631524794633027 1313492045447287191949541)
          ·
            refine ⟨246279758521366348490539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1313492045447287191949541 246279758521366348490539)
            ·
              refine ⟨369419637782049522735809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246279758521366348490539 369419637782049522735809)
              ·
                refine ⟨277064728336537142051857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369419637782049522735809 277064728336537142051857)
                ·
                  refine ⟨207798546252402856538893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277064728336537142051857 207798546252402856538893)
                  ·
                    refine ⟨77924454844651071202085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207798546252402856538893 77924454844651071202085)
                    ·
                      rfl

theorem cell22_227636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_227636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227636 prefixEnd_227636 := by exact prefixLift 227636
  have htrace : WordTrace (prefixWord ++ tailWord_227636) baseStart_227636 baseEnd_227636 := by
    simpa [prefixWord, tailWord_227636, baseEnd_227636] using wordTrace_append hprefix tailTrace_227636
  have hstable : (prefixWord ++ tailWord_227636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227636).length < 2 ^ (prefixWord ++ tailWord_227636).sum := by decide
  have hdescent : baseEnd_227636 < baseStart_227636 := by decide
  rcases family_descends (prefixWord ++ tailWord_227636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227647 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 3, 3]
def baseStart_227647 : Nat := 118140960795 + 227647 * 2 ^ 59
def prefixEnd_227647 : Nat := 4983230072969 + 3 ^ 40 * 227647 * 2
def baseEnd_227647 : Nat := 77928220369450709177051

theorem tailTrace_227647 : CollatzResearch.WordTrace tailWord_227647 prefixEnd_227647 77928220369450709177051 := by
  unfold tailWord_227647
  simp only [CollatzResearch.WordTrace]
  refine ⟨8302968206281272857393195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5535312137520848571595463 8302968206281272857393195)
  ·
    refine ⟨12454452309421909286089793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8302968206281272857393195 12454452309421909286089793)
    ·
      refine ⟨9340839232066431964567345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12454452309421909286089793 9340839232066431964567345)
      ·
        refine ⟨7005629424049823973425509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9340839232066431964567345 7005629424049823973425509)
        ·
          refine ⟨1313555517009341995017283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7005629424049823973425509 1313555517009341995017283)
          ·
            refine ⟨1970333275514012992525925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313555517009341995017283 1970333275514012992525925)
            ·
              refine ⟨369437489158877436098611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1970333275514012992525925 369437489158877436098611)
              ·
                refine ⟨554156233738316154147917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369437489158877436098611 554156233738316154147917)
                ·
                  refine ⟨207808587651868557805469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554156233738316154147917 207808587651868557805469)
                  ·
                    refine ⟨77928220369450709177051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207808587651868557805469 77928220369450709177051)
                    ·
                      rfl

theorem cell22_227647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_227647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227647 prefixEnd_227647 := by exact prefixLift 227647
  have htrace : WordTrace (prefixWord ++ tailWord_227647) baseStart_227647 baseEnd_227647 := by
    simpa [prefixWord, tailWord_227647, baseEnd_227647] using wordTrace_append hprefix tailTrace_227647
  have hstable : (prefixWord ++ tailWord_227647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227647).length < 2 ^ (prefixWord ++ tailWord_227647).sum := by decide
  have hdescent : baseEnd_227647 < baseStart_227647 := by decide
  rcases family_descends (prefixWord ++ tailWord_227647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227724 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_227724 : Nat := 118140960795 + 227724 * 2 ^ 59
def prefixEnd_227724 : Nat := 4983230072969 + 3 ^ 40 * 227724 * 2
def baseEnd_227724 : Nat := 77954579043048175001815

theorem tailTrace_227724 : CollatzResearch.WordTrace tailWord_227724 prefixEnd_227724 77954579043048175001815 := by
  unfold tailWord_227724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4152888313501157503973113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5537184418001543338630817 4152888313501157503973113)
  ·
    refine ⟨3114666235125868127979835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4152888313501157503973113 3114666235125868127979835)
    ·
      refine ⟨4671999352688802191969753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3114666235125868127979835 4671999352688802191969753)
      ·
        refine ⟨3503999514516601643977315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4671999352688802191969753 3503999514516601643977315)
        ·
          refine ⟨5255999271774902465965973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3503999514516601643977315 5255999271774902465965973)
          ·
            refine ⟨246374965864448553092155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5255999271774902465965973 246374965864448553092155)
            ·
              refine ⟨369562448796672829638233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246374965864448553092155 369562448796672829638233)
              ·
                refine ⟨277171836597504622228675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369562448796672829638233 277171836597504622228675)
                ·
                  refine ⟨415757754896256933343013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277171836597504622228675 415757754896256933343013)
                  ·
                    refine ⟨77954579043048175001815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415757754896256933343013 77954579043048175001815)
                    ·
                      rfl

theorem cell22_227724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_227724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227724 prefixEnd_227724 := by exact prefixLift 227724
  have htrace : WordTrace (prefixWord ++ tailWord_227724) baseStart_227724 baseEnd_227724 := by
    simpa [prefixWord, tailWord_227724, baseEnd_227724] using wordTrace_append hprefix tailTrace_227724
  have hstable : (prefixWord ++ tailWord_227724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227724).length < 2 ^ (prefixWord ++ tailWord_227724).sum := by decide
  have hdescent : baseEnd_227724 < baseStart_227724 := by decide
  rcases family_descends (prefixWord ++ tailWord_227724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227735 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 1, 6]
def baseStart_227735 : Nat := 118140960795 + 227735 * 2 ^ 59
def prefixEnd_227735 : Nat := 4983230072969 + 3 ^ 40 * 227735 * 2
def baseEnd_227735 : Nat := 77958344567847812976781

theorem tailTrace_227735 : CollatzResearch.WordTrace tailWord_227735 prefixEnd_227735 77958344567847812976781 := by
  unfold tailWord_227735
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306177829962463886596659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5537451886641642591064439 8306177829962463886596659)
  ·
    refine ⟨12459266744943695829894989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8306177829962463886596659 12459266744943695829894989)
    ·
      refine ⟨4672225029353885936210621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12459266744943695829894989 4672225029353885936210621)
      ·
        refine ⟨1752084386007707226078983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4672225029353885936210621 1752084386007707226078983)
        ·
          refine ⟨2628126579011560839118475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752084386007707226078983 2628126579011560839118475)
          ·
            refine ⟨3942189868517341258677713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628126579011560839118475 3942189868517341258677713)
            ·
              refine ⟨2956642401388005944008285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3942189868517341258677713 2956642401388005944008285)
              ·
                refine ⟨1108740900520502229003107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2956642401388005944008285 1108740900520502229003107)
                ·
                  refine ⟨1663111350780753343504661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108740900520502229003107 1663111350780753343504661)
                  ·
                    refine ⟨77958344567847812976781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1663111350780753343504661 77958344567847812976781)
                    ·
                      rfl

theorem cell22_227735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_227735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227735 prefixEnd_227735 := by exact prefixLift 227735
  have htrace : WordTrace (prefixWord ++ tailWord_227735) baseStart_227735 baseEnd_227735 := by
    simpa [prefixWord, tailWord_227735, baseEnd_227735] using wordTrace_append hprefix tailTrace_227735
  have hstable : (prefixWord ++ tailWord_227735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227735).length < 2 ^ (prefixWord ++ tailWord_227735).sum := by decide
  have hdescent : baseEnd_227735 < baseStart_227735 := by decide
  rcases family_descends (prefixWord ++ tailWord_227735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227741 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_227741 : Nat := 118140960795 + 227741 * 2 ^ 59
def prefixEnd_227741 : Nat := 4983230072969 + 3 ^ 40 * 227741 * 2
def baseEnd_227741 : Nat := 77960398490465797326763

theorem tailTrace_227741 : CollatzResearch.WordTrace tailWord_227741 prefixEnd_227741 77960398490465797326763 := by
  unfold tailWord_227741
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306396667940726911315077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5537597778627151274210051 8306396667940726911315077)
  ·
    refine ⟨1557449375238886295871577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8306396667940726911315077 1557449375238886295871577)
    ·
      refine ⟨1168087031429164721903683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1557449375238886295871577 1168087031429164721903683)
      ·
        refine ⟨1752130547143747082855525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168087031429164721903683 1752130547143747082855525)
        ·
          refine ⟨328524477589452578035411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1752130547143747082855525 328524477589452578035411)
          ·
            refine ⟨492786716384178867053117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328524477589452578035411 492786716384178867053117)
            ·
              refine ⟨184795018644067075144919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492786716384178867053117 184795018644067075144919)
              ·
                refine ⟨277192527966100612717379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184795018644067075144919 277192527966100612717379)
                ·
                  refine ⟨415788791949150919076069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277192527966100612717379 415788791949150919076069)
                  ·
                    refine ⟨77960398490465797326763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415788791949150919076069 77960398490465797326763)
                    ·
                      rfl

theorem cell22_227741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_227741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227741 prefixEnd_227741 := by exact prefixLift 227741
  have htrace : WordTrace (prefixWord ++ tailWord_227741) baseStart_227741 baseEnd_227741 := by
    simpa [prefixWord, tailWord_227741, baseEnd_227741] using wordTrace_append hprefix tailTrace_227741
  have hstable : (prefixWord ++ tailWord_227741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227741).length < 2 ^ (prefixWord ++ tailWord_227741).sum := by decide
  have hdescent : baseEnd_227741 < baseStart_227741 := by decide
  rcases family_descends (prefixWord ++ tailWord_227741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227767 : List Nat := [1, 1, 3, 1, 3, 5, 1, 7]
def baseStart_227767 : Nat := 118140960795 + 227767 * 2 ^ 59
def prefixEnd_227767 : Nat := 4983230072969 + 3 ^ 40 * 227767 * 2
def baseEnd_227767 : Nat := 8663255424645599575187

theorem tailTrace_227767 : CollatzResearch.WordTrace tailWord_227767 prefixEnd_227767 8663255424645599575187 := by
  unfold tailWord_227767
  simp only [CollatzResearch.WordTrace]
  refine ⟨8307344965846533351761555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5538229977231022234507703 8307344965846533351761555)
  ·
    refine ⟨12461017448769800027642333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8307344965846533351761555 12461017448769800027642333)
    ·
      refine ⟨4672881543288675010365875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12461017448769800027642333 4672881543288675010365875)
      ·
        refine ⟨7009322314933012515548813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672881543288675010365875 7009322314933012515548813)
        ·
          refine ⟨2628495868099879693330805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7009322314933012515548813 2628495868099879693330805)
          ·
            refine ⟨246421487634363721249763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2628495868099879693330805 246421487634363721249763)
            ·
              refine ⟨369632231451545581874645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246421487634363721249763 369632231451545581874645)
              ·
                refine ⟨8663255424645599575187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 369632231451545581874645 8663255424645599575187)
                ·
                  rfl

theorem cell22_227767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 7].length) (baseStart_227767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227767 prefixEnd_227767 := by exact prefixLift 227767
  have htrace : WordTrace (prefixWord ++ tailWord_227767) baseStart_227767 baseEnd_227767 := by
    simpa [prefixWord, tailWord_227767, baseEnd_227767] using wordTrace_append hprefix tailTrace_227767
  have hstable : (prefixWord ++ tailWord_227767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227767).length < 2 ^ (prefixWord ++ tailWord_227767).sum := by decide
  have hdescent : baseEnd_227767 < baseStart_227767 := by decide
  rcases family_descends (prefixWord ++ tailWord_227767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227816 : List Nat := [2, 1, 4, 1, 1, 3, 2, 4, 1, 3]
def baseStart_227816 : Nat := 118140960795 + 227816 * 2 ^ 59
def prefixEnd_227816 : Nat := 4983230072969 + 3 ^ 40 * 227816 * 2
def baseEnd_227816 : Nat := 77986072523190601701533

theorem tailTrace_227816 : CollatzResearch.WordTrace tailWord_227816 prefixEnd_227816 77986072523190601701533 := by
  unfold tailWord_227816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4154566071334507360147651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5539421428446009813530201 4154566071334507360147651)
  ·
    refine ⟨6231849107001761040221477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4154566071334507360147651 6231849107001761040221477)
    ·
      refine ⟨1168471707562830195041527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6231849107001761040221477 1168471707562830195041527)
      ·
        refine ⟨1752707561344245292562291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168471707562830195041527 1752707561344245292562291)
        ·
          refine ⟨2629061342016367938843437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752707561344245292562291 2629061342016367938843437)
          ·
            refine ⟨985898003256137977066289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2629061342016367938843437 985898003256137977066289)
            ·
              refine ⟨739423502442103482799717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985898003256137977066289 739423502442103482799717)
              ·
                refine ⟨138641906707894403024947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 739423502442103482799717 138641906707894403024947)
                ·
                  refine ⟨207962860061841604537421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138641906707894403024947 207962860061841604537421)
                  ·
                    refine ⟨77986072523190601701533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207962860061841604537421 77986072523190601701533)
                    ·
                      rfl

theorem cell22_227816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_227816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227816 prefixEnd_227816 := by exact prefixLift 227816
  have htrace : WordTrace (prefixWord ++ tailWord_227816) baseStart_227816 baseEnd_227816 := by
    simpa [prefixWord, tailWord_227816, baseEnd_227816] using wordTrace_append hprefix tailTrace_227816
  have hstable : (prefixWord ++ tailWord_227816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227816).length < 2 ^ (prefixWord ++ tailWord_227816).sum := by decide
  have hdescent : baseEnd_227816 < baseStart_227816 := by decide
  rcases family_descends (prefixWord ++ tailWord_227816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227910 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_227910 : Nat := 118140960795 + 227910 * 2 ^ 59
def prefixEnd_227910 : Nat := 4983230072969 + 3 ^ 40 * 227910 * 2
def baseEnd_227910 : Nat := 78018250644205689851245

theorem tailTrace_227910 : CollatzResearch.WordTrace tailWord_227910 prefixEnd_227910 78018250644205689851245 := by
  unfold tailWord_227910
  simp only [CollatzResearch.WordTrace]
  refine ⟨259767518885264649194287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5541707069552312516144789 259767518885264649194287)
  ·
    refine ⟨389651278327896973791431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259767518885264649194287 389651278327896973791431)
    ·
      refine ⟨584476917491845460687147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389651278327896973791431 584476917491845460687147)
      ·
        refine ⟨876715376237768191030721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584476917491845460687147 876715376237768191030721)
        ·
          refine ⟨657536532178326143273041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876715376237768191030721 657536532178326143273041)
          ·
            refine ⟨493152399133744607454781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657536532178326143273041 493152399133744607454781)
            ·
              refine ⟨184932149675154227795543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493152399133744607454781 184932149675154227795543)
              ·
                refine ⟨277398224512731341693315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184932149675154227795543 277398224512731341693315)
                ·
                  refine ⟨416097336769097012539973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277398224512731341693315 416097336769097012539973)
                  ·
                    refine ⟨78018250644205689851245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416097336769097012539973 78018250644205689851245)
                    ·
                      rfl

theorem cell22_227910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_227910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227910 prefixEnd_227910 := by exact prefixLift 227910
  have htrace : WordTrace (prefixWord ++ tailWord_227910) baseStart_227910 baseEnd_227910 := by
    simpa [prefixWord, tailWord_227910, baseEnd_227910] using wordTrace_append hprefix tailTrace_227910
  have hstable : (prefixWord ++ tailWord_227910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227910).length < 2 ^ (prefixWord ++ tailWord_227910).sum := by decide
  have hdescent : baseEnd_227910 < baseStart_227910 := by decide
  rcases family_descends (prefixWord ++ tailWord_227910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227968 : List Nat := [2, 1, 1, 2, 1, 6, 2, 3, 1, 3]
def baseStart_227968 : Nat := 118140960795 + 227968 * 2 ^ 59
def prefixEnd_227968 : Nat := 4983230072969 + 3 ^ 40 * 227968 * 2
def baseEnd_227968 : Nat := 78038105229512871901067

theorem tailTrace_227968 : CollatzResearch.WordTrace tailWord_227968 prefixEnd_227968 78038105229512871901067 := by
  unfold tailWord_227968
  simp only [CollatzResearch.WordTrace]
  refine ⟨4157338019059172339914279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5543117358745563119885705 4157338019059172339914279)
  ·
    refine ⟨6236007028588758509871419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4157338019059172339914279 6236007028588758509871419)
    ·
      refine ⟨9354010542883137764807129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6236007028588758509871419 9354010542883137764807129)
      ·
        refine ⟨7015507907162353323605347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9354010542883137764807129 7015507907162353323605347)
        ·
          refine ⟨10523261860743529985408021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7015507907162353323605347 10523261860743529985408021)
          ·
            refine ⟨493277899722352968066001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10523261860743529985408021 493277899722352968066001)
            ·
              refine ⟨369958424791764726049501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493277899722352968066001 369958424791764726049501)
              ·
                refine ⟨138734409296911772268563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369958424791764726049501 138734409296911772268563)
                ·
                  refine ⟨208101613945367658402845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138734409296911772268563 208101613945367658402845)
                  ·
                    refine ⟨78038105229512871901067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 208101613945367658402845 78038105229512871901067)
                    ·
                      rfl

theorem cell22_227968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 3].length) (baseStart_227968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227968 prefixEnd_227968 := by exact prefixLift 227968
  have htrace : WordTrace (prefixWord ++ tailWord_227968) baseStart_227968 baseEnd_227968 := by
    simpa [prefixWord, tailWord_227968, baseEnd_227968] using wordTrace_append hprefix tailTrace_227968
  have hstable : (prefixWord ++ tailWord_227968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227968).length < 2 ^ (prefixWord ++ tailWord_227968).sum := by decide
  have hdescent : baseEnd_227968 < baseStart_227968 := by decide
  rcases family_descends (prefixWord ++ tailWord_227968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227998 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_227998 : Nat := 118140960795 + 227998 * 2 ^ 59
def prefixEnd_227998 : Nat := 4983230072969 + 3 ^ 40 * 227998 * 2
def baseEnd_227998 : Nat := 26016124947534264550325

theorem tailTrace_227998 : CollatzResearch.WordTrace tailWord_227998 prefixEnd_227998 26016124947534264550325 := by
  unfold tailWord_227998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039471278501207475427581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5543846818673106535613765 1039471278501207475427581)
  ·
    refine ⟨389801729437952803285343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1039471278501207475427581 389801729437952803285343)
    ·
      refine ⟨584702594156929204928015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389801729437952803285343 584702594156929204928015)
      ·
        refine ⟨877053891235393807392023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584702594156929204928015 877053891235393807392023)
        ·
          refine ⟨1315580836853090711088035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877053891235393807392023 1315580836853090711088035)
          ·
            refine ⟨1973371255279636066632053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315580836853090711088035 1973371255279636066632053)
            ·
              refine ⟨185003555182465881246755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1973371255279636066632053 185003555182465881246755)
              ·
                refine ⟨277505332773698821870133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185003555182465881246755 277505332773698821870133)
                ·
                  refine ⟨26016124947534264550325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277505332773698821870133 26016124947534264550325)
                  ·
                    rfl

theorem cell22_227998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_227998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_227998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_227998 prefixEnd_227998 := by exact prefixLift 227998
  have htrace : WordTrace (prefixWord ++ tailWord_227998) baseStart_227998 baseEnd_227998 := by
    simpa [prefixWord, tailWord_227998, baseEnd_227998] using wordTrace_append hprefix tailTrace_227998
  have hstable : (prefixWord ++ tailWord_227998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227998).length < 2 ^ (prefixWord ++ tailWord_227998).sum := by decide
  have hdescent : baseEnd_227998 < baseStart_227998 := by decide
  rcases family_descends (prefixWord ++ tailWord_227998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228176 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_228176 : Nat := 118140960795 + 228176 * 2 ^ 59
def prefixEnd_228176 : Nat := 4983230072969 + 3 ^ 40 * 228176 * 2
def baseEnd_228176 : Nat := 78109307880269662700429

theorem tailTrace_228176 : CollatzResearch.WordTrace tailWord_228176 prefixEnd_228176 78109307880269662700429 := by
  unfold tailWord_228176
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161131210682398101700191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5548174947576530802266921 4161131210682398101700191)
  ·
    refine ⟨6241696816023597152550287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4161131210682398101700191 6241696816023597152550287)
    ·
      refine ⟨9362545224035395728825431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6241696816023597152550287 9362545224035395728825431)
      ·
        refine ⟨14043817836053093593238147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9362545224035395728825431 14043817836053093593238147)
        ·
          refine ⟨21065726754079640389857221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14043817836053093593238147 21065726754079640389857221)
          ·
            refine ⟨3949823766389932573098229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21065726754079640389857221 3949823766389932573098229)
            ·
              refine ⟨370295978099056178727959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3949823766389932573098229 370295978099056178727959)
              ·
                refine ⟨555443967148584268091939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370295978099056178727959 555443967148584268091939)
                ·
                  refine ⟨833165950722876402137909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555443967148584268091939 833165950722876402137909)
                  ·
                    refine ⟨78109307880269662700429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 833165950722876402137909 78109307880269662700429)
                    ·
                      rfl

theorem cell22_228176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_228176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228176 prefixEnd_228176 := by exact prefixLift 228176
  have htrace : WordTrace (prefixWord ++ tailWord_228176) baseStart_228176 baseEnd_228176 := by
    simpa [prefixWord, tailWord_228176, baseEnd_228176] using wordTrace_append hprefix tailTrace_228176
  have hstable : (prefixWord ++ tailWord_228176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228176).length < 2 ^ (prefixWord ++ tailWord_228176).sum := by decide
  have hdescent : baseEnd_228176 < baseStart_228176 := by decide
  rcases family_descends (prefixWord ++ tailWord_228176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228180 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_228180 : Nat := 118140960795 + 228180 * 2 ^ 59
def prefixEnd_228180 : Nat := 4983230072969 + 3 ^ 40 * 228180 * 2
def baseEnd_228180 : Nat := 78110677162014985600417

theorem tailTrace_228180 : CollatzResearch.WordTrace tailWord_228180 prefixEnd_228180 78110677162014985600417 := by
  unfold tailWord_228180
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161204156675152443272997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5548272208900203257697329 4161204156675152443272997)
  ·
    refine ⟨780225779376591083113687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4161204156675152443272997 780225779376591083113687)
    ·
      refine ⟨1170338669064886624670531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780225779376591083113687 1170338669064886624670531)
      ·
        refine ⟨1755508003597329937005797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170338669064886624670531 1755508003597329937005797)
        ·
          refine ⟨329157750674499363188587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1755508003597329937005797 329157750674499363188587)
          ·
            refine ⟨493736626011749044782881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329157750674499363188587 493736626011749044782881)
            ·
              refine ⟨370302469508811783587161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493736626011749044782881 370302469508811783587161)
              ·
                refine ⟨277726852131608837690371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370302469508811783587161 277726852131608837690371)
                ·
                  refine ⟨416590278197413256535557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277726852131608837690371 416590278197413256535557)
                  ·
                    refine ⟨78110677162014985600417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416590278197413256535557 78110677162014985600417)
                    ·
                      rfl

theorem cell22_228180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_228180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228180 prefixEnd_228180 := by exact prefixLift 228180
  have htrace : WordTrace (prefixWord ++ tailWord_228180) baseStart_228180 baseEnd_228180 := by
    simpa [prefixWord, tailWord_228180, baseEnd_228180] using wordTrace_append hprefix tailTrace_228180
  have hstable : (prefixWord ++ tailWord_228180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228180).length < 2 ^ (prefixWord ++ tailWord_228180).sum := by decide
  have hdescent : baseEnd_228180 < baseStart_228180 := by decide
  rcases family_descends (prefixWord ++ tailWord_228180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228191 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 2, 4]
def baseStart_228191 : Nat := 118140960795 + 228191 * 2 ^ 59
def prefixEnd_228191 : Nat := 4983230072969 + 3 ^ 40 * 228191 * 2
def baseEnd_228191 : Nat := 78114442686814623575383

theorem tailTrace_228191 : CollatzResearch.WordTrace tailWord_228191 prefixEnd_228191 78114442686814623575383 := by
  unfold tailWord_228191
  simp only [CollatzResearch.WordTrace]
  refine ⟨8322809516310453765196427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5548539677540302510130951 8322809516310453765196427)
  ·
    refine ⟨12484214274465680647794641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8322809516310453765196427 12484214274465680647794641)
    ·
      refine ⟨9363160705849260485845981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12484214274465680647794641 9363160705849260485845981)
      ·
        refine ⟨3511185264693472682192243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9363160705849260485845981 3511185264693472682192243)
        ·
          refine ⟨5266777897040209023288365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511185264693472682192243 5266777897040209023288365)
          ·
            refine ⟨1975041711390078383733137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5266777897040209023288365 1975041711390078383733137)
            ·
              refine ⟨1481281283542558787799853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975041711390078383733137 1481281283542558787799853)
              ·
                refine ⟨555480481328459545424945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1481281283542558787799853 555480481328459545424945)
                ·
                  refine ⟨416610360996344659068709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555480481328459545424945 416610360996344659068709)
                  ·
                    refine ⟨78114442686814623575383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416610360996344659068709 78114442686814623575383)
                    ·
                      rfl

theorem cell22_228191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_228191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228191 prefixEnd_228191 := by exact prefixLift 228191
  have htrace : WordTrace (prefixWord ++ tailWord_228191) baseStart_228191 baseEnd_228191 := by
    simpa [prefixWord, tailWord_228191, baseEnd_228191] using wordTrace_append hprefix tailTrace_228191
  have hstable : (prefixWord ++ tailWord_228191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228191).length < 2 ^ (prefixWord ++ tailWord_228191).sum := by decide
  have hdescent : baseEnd_228191 < baseStart_228191 := by decide
  rcases family_descends (prefixWord ++ tailWord_228191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228195 : List Nat := [1, 1, 1, 5, 3, 3, 1, 3, 4]
def baseStart_228195 : Nat := 118140960795 + 228195 * 2 ^ 59
def prefixEnd_228195 : Nat := 4983230072969 + 3 ^ 40 * 228195 * 2
def baseEnd_228195 : Nat := 26038603989519982158457

theorem tailTrace_228195 : CollatzResearch.WordTrace tailWord_228195 prefixEnd_228195 26038603989519982158457 := by
  unfold tailWord_228195
  simp only [CollatzResearch.WordTrace]
  refine ⟨8322955408295962448342039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5548636938863974965561359 8322955408295962448342039)
  ·
    refine ⟨12484433112443943672513059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8322955408295962448342039 12484433112443943672513059)
    ·
      refine ⟨18726649668665915508769589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12484433112443943672513059 18726649668665915508769589)
      ·
        refine ⟨1755623406437429578947149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18726649668665915508769589 1755623406437429578947149)
        ·
          refine ⟨658358777414036092105181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1755623406437429578947149 658358777414036092105181)
          ·
            refine ⟨246884541530263534539443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658358777414036092105181 246884541530263534539443)
            ·
              refine ⟨370326812295395301809165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246884541530263534539443 370326812295395301809165)
              ·
                refine ⟨138872554610773238178437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370326812295395301809165 138872554610773238178437)
                ·
                  refine ⟨26038603989519982158457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138872554610773238178437 26038603989519982158457)
                  ·
                    rfl

theorem cell22_228195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 4].length) (baseStart_228195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228195 prefixEnd_228195 := by exact prefixLift 228195
  have htrace : WordTrace (prefixWord ++ tailWord_228195) baseStart_228195 baseEnd_228195 := by
    simpa [prefixWord, tailWord_228195, baseEnd_228195] using wordTrace_append hprefix tailTrace_228195
  have hstable : (prefixWord ++ tailWord_228195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228195).length < 2 ^ (prefixWord ++ tailWord_228195).sum := by decide
  have hdescent : baseEnd_228195 < baseStart_228195 := by decide
  rcases family_descends (prefixWord ++ tailWord_228195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228298 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_228298 : Nat := 118140960795 + 228298 * 2 ^ 59
def prefixEnd_228298 : Nat := 4983230072969 + 3 ^ 40 * 228298 * 2
def baseEnd_228298 : Nat := 78151070973502011150055

theorem tailTrace_228298 : CollatzResearch.WordTrace tailWord_228298 prefixEnd_228298 78151070973502011150055 := by
  unfold tailWord_228298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081678031730702759835387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5551141417948540692894365 2081678031730702759835387)
  ·
    refine ⟨3122517047596054139753081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081678031730702759835387 3122517047596054139753081)
    ·
      refine ⟨2341887785697040604814811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3122517047596054139753081 2341887785697040604814811)
      ·
        refine ⟨3512831678545560907222217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341887785697040604814811 3512831678545560907222217)
        ·
          refine ⟨2634623758909170680416663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3512831678545560907222217 2634623758909170680416663)
          ·
            refine ⟨3951935638363756020624995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634623758909170680416663 3951935638363756020624995)
            ·
              refine ⟨5927903457545634030937493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951935638363756020624995 5927903457545634030937493)
              ·
                refine ⟨277870474572451595200195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5927903457545634030937493 277870474572451595200195)
                ·
                  refine ⟨416805711858677392800293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277870474572451595200195 416805711858677392800293)
                  ·
                    refine ⟨78151070973502011150055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 416805711858677392800293 78151070973502011150055)
                    ·
                      rfl

theorem cell22_228298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_228298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228298 prefixEnd_228298 := by exact prefixLift 228298
  have htrace : WordTrace (prefixWord ++ tailWord_228298) baseStart_228298 baseEnd_228298 := by
    simpa [prefixWord, tailWord_228298, baseEnd_228298] using wordTrace_append hprefix tailTrace_228298
  have hstable : (prefixWord ++ tailWord_228298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228298).length < 2 ^ (prefixWord ++ tailWord_228298).sum := by decide
  have hdescent : baseEnd_228298 < baseStart_228298 := by decide
  rcases family_descends (prefixWord ++ tailWord_228298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228311 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 3, 5]
def baseStart_228311 : Nat := 118140960795 + 228311 * 2 ^ 59
def prefixEnd_228311 : Nat := 4983230072969 + 3 ^ 40 * 228311 * 2
def baseEnd_228311 : Nat := 78155521139174310575015

theorem tailTrace_228311 : CollatzResearch.WordTrace tailWord_228311 prefixEnd_228311 78155521139174310575015 := by
  unfold tailWord_228311
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327186275875714259564787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5551457517250476173043191 8327186275875714259564787)
  ·
    refine ⟨12490779413813571389347181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8327186275875714259564787 12490779413813571389347181)
    ·
      refine ⟨4684042280180089271005193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12490779413813571389347181 4684042280180089271005193)
      ·
        refine ⟨3513031710135066953253895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4684042280180089271005193 3513031710135066953253895)
        ·
          refine ⟨5269547565202600429880843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513031710135066953253895 5269547565202600429880843)
          ·
            refine ⟨7904321347803900644821265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269547565202600429880843 7904321347803900644821265)
            ·
              refine ⟨5928241010852925483615949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7904321347803900644821265 5928241010852925483615949)
              ·
                refine ⟨2223090379069847056355981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5928241010852925483615949 2223090379069847056355981)
                ·
                  refine ⟨833658892151192646133493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2223090379069847056355981 833658892151192646133493)
                  ·
                    refine ⟨78155521139174310575015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 833658892151192646133493 78155521139174310575015)
                    ·
                      rfl

theorem cell22_228311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_228311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228311 prefixEnd_228311 := by exact prefixLift 228311
  have htrace : WordTrace (prefixWord ++ tailWord_228311) baseStart_228311 baseEnd_228311 := by
    simpa [prefixWord, tailWord_228311, baseEnd_228311] using wordTrace_append hprefix tailTrace_228311
  have hstable : (prefixWord ++ tailWord_228311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228311).length < 2 ^ (prefixWord ++ tailWord_228311).sum := by decide
  have hdescent : baseEnd_228311 < baseStart_228311 := by decide
  rcases family_descends (prefixWord ++ tailWord_228311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228330 : List Nat := [3, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_228330 : Nat := 118140960795 + 228330 * 2 ^ 59
def prefixEnd_228330 : Nat := 4983230072969 + 3 ^ 40 * 228330 * 2
def baseEnd_228330 : Nat := 26054008409154864783319

theorem tailTrace_228330 : CollatzResearch.WordTrace tailWord_228330 prefixEnd_228330 26054008409154864783319 := by
  unfold tailWord_228330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081969815701720126126611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5551919508537920336337629 2081969815701720126126611)
  ·
    refine ⟨3122954723552580189189917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081969815701720126126611 3122954723552580189189917)
    ·
      refine ⟨1171108021332217570946219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3122954723552580189189917 1171108021332217570946219)
      ·
        refine ⟨1756662031998326356419329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171108021332217570946219 1756662031998326356419329)
        ·
          refine ⟨1317496523998744767314497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756662031998326356419329 1317496523998744767314497)
          ·
            refine ⟨988122392999058575485873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1317496523998744767314497 988122392999058575485873)
            ·
              refine ⟨741091794749293931614405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988122392999058575485873 741091794749293931614405)
              ·
                refine ⟨138954711515492612177701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741091794749293931614405 138954711515492612177701)
                ·
                  refine ⟨26054008409154864783319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138954711515492612177701 26054008409154864783319)
                  ·
                    rfl

theorem cell22_228330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_228330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228330 prefixEnd_228330 := by exact prefixLift 228330
  have htrace : WordTrace (prefixWord ++ tailWord_228330) baseStart_228330 baseEnd_228330 := by
    simpa [prefixWord, tailWord_228330, baseEnd_228330] using wordTrace_append hprefix tailTrace_228330
  have hstable : (prefixWord ++ tailWord_228330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228330).length < 2 ^ (prefixWord ++ tailWord_228330).sum := by decide
  have hdescent : baseEnd_228330 < baseStart_228330 := by decide
  rcases family_descends (prefixWord ++ tailWord_228330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228371 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 1, 8]
def baseStart_228371 : Nat := 118140960795 + 228371 * 2 ^ 59
def prefixEnd_228371 : Nat := 4983230072969 + 3 ^ 40 * 228371 * 2
def baseEnd_228371 : Nat := 78176060365354154074831

theorem tailTrace_228371 : CollatzResearch.WordTrace tailWord_228371 prefixEnd_228371 78176060365354154074831 := by
  unfold tailWord_228371
  simp only [CollatzResearch.WordTrace]
  refine ⟨8329374655658344506748967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5552916437105563004499311 8329374655658344506748967)
  ·
    refine ⟨12494061983487516760123451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8329374655658344506748967 12494061983487516760123451)
    ·
      refine ⟨18741092975231275140185177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12494061983487516760123451 18741092975231275140185177)
      ·
        refine ⟨14055819731423456355138883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18741092975231275140185177 14055819731423456355138883)
        ·
          refine ⟨21083729597135184532708325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14055819731423456355138883 21083729597135184532708325)
          ·
            refine ⟨3953199299462847099882811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21083729597135184532708325 3953199299462847099882811)
            ·
              refine ⟨5929798949194270649824217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3953199299462847099882811 5929798949194270649824217)
              ·
                refine ⟨4447349211895702987368163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5929798949194270649824217 4447349211895702987368163)
                ·
                  refine ⟨6671023817843554481052245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447349211895702987368163 6671023817843554481052245)
                  ·
                    refine ⟨78176060365354154074831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6671023817843554481052245 78176060365354154074831)
                    ·
                      rfl

theorem cell22_228371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_228371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228371 prefixEnd_228371 := by exact prefixLift 228371
  have htrace : WordTrace (prefixWord ++ tailWord_228371) baseStart_228371 baseEnd_228371 := by
    simpa [prefixWord, tailWord_228371, baseEnd_228371] using wordTrace_append hprefix tailTrace_228371
  have hstable : (prefixWord ++ tailWord_228371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228371).length < 2 ^ (prefixWord ++ tailWord_228371).sum := by decide
  have hdescent : baseEnd_228371 < baseStart_228371 := by decide
  rcases family_descends (prefixWord ++ tailWord_228371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228448 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 6]
def baseStart_228448 : Nat := 118140960795 + 228448 * 2 ^ 59
def prefixEnd_228448 : Nat := 4983230072969 + 3 ^ 40 * 228448 * 2
def baseEnd_228448 : Nat := 26067473012983873299865

theorem tailTrace_228448 : CollatzResearch.WordTrace tailWord_228448 prefixEnd_228448 26067473012983873299865 := by
  unfold tailWord_228448
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166091538189693328650999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5554788717586257771534665 4166091538189693328650999)
  ·
    refine ⟨6249137307284539992976499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4166091538189693328650999 6249137307284539992976499)
    ·
      refine ⟨9373705960926809989464749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6249137307284539992976499 9373705960926809989464749)
      ·
        refine ⟨3515139735347553746049281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9373705960926809989464749 3515139735347553746049281)
        ·
          refine ⟨2636354801510665309536961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3515139735347553746049281 2636354801510665309536961)
          ·
            refine ⟨1977266101132998982152721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2636354801510665309536961 1977266101132998982152721)
            ·
              refine ⟨1482949575849749236614541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977266101132998982152721 1482949575849749236614541)
              ·
                refine ⟨556106090943655963730453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1482949575849749236614541 556106090943655963730453)
                ·
                  refine ⟨26067473012983873299865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 556106090943655963730453 26067473012983873299865)
                  ·
                    rfl

theorem cell22_228448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_228448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228448 prefixEnd_228448 := by exact prefixLift 228448
  have htrace : WordTrace (prefixWord ++ tailWord_228448) baseStart_228448 baseEnd_228448 := by
    simpa [prefixWord, tailWord_228448, baseEnd_228448] using wordTrace_append hprefix tailTrace_228448
  have hstable : (prefixWord ++ tailWord_228448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228448).length < 2 ^ (prefixWord ++ tailWord_228448).sum := by decide
  have hdescent : baseEnd_228448 < baseStart_228448 := by decide
  rcases family_descends (prefixWord ++ tailWord_228448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228484 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_228484 : Nat := 118140960795 + 228484 * 2 ^ 59
def prefixEnd_228484 : Nat := 4983230072969 + 3 ^ 40 * 228484 * 2
def baseEnd_228484 : Nat := 78214742574659525999485

theorem tailTrace_228484 : CollatzResearch.WordTrace tailWord_228484 prefixEnd_228484 78214742574659525999485 := by
  unfold tailWord_228484
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166748052124482402806253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5555664069499309870408337 4166748052124482402806253)
  ·
    refine ⟨1562530519546680901052345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4166748052124482402806253 1562530519546680901052345)
    ·
      refine ⟨1171897889660010675789259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1562530519546680901052345 1171897889660010675789259)
      ·
        refine ⟨1757846834490016013683889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171897889660010675789259 1757846834490016013683889)
        ·
          refine ⟨1318385125867512010262917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1757846834490016013683889 1318385125867512010262917)
          ·
            refine ⟨247197211100158501924297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1318385125867512010262917 247197211100158501924297)
            ·
              refine ⟨185397908325118876443223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247197211100158501924297 185397908325118876443223)
              ·
                refine ⟨278096862487678314664835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185397908325118876443223 278096862487678314664835)
                ·
                  refine ⟨417145293731517471997253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278096862487678314664835 417145293731517471997253)
                  ·
                    refine ⟨78214742574659525999485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 417145293731517471997253 78214742574659525999485)
                    ·
                      rfl

theorem cell22_228484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_228484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228484 prefixEnd_228484 := by exact prefixLift 228484
  have htrace : WordTrace (prefixWord ++ tailWord_228484) baseStart_228484 baseEnd_228484 := by
    simpa [prefixWord, tailWord_228484, baseEnd_228484] using wordTrace_append hprefix tailTrace_228484
  have hstable : (prefixWord ++ tailWord_228484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228484).length < 2 ^ (prefixWord ++ tailWord_228484).sum := by decide
  have hdescent : baseEnd_228484 < baseStart_228484 := by decide
  rcases family_descends (prefixWord ++ tailWord_228484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228514 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_228514 : Nat := 118140960795 + 228514 * 2 ^ 59
def prefixEnd_228514 : Nat := 4983230072969 + 3 ^ 40 * 228514 * 2
def baseEnd_228514 : Nat := 78225012187749447749393

theorem tailTrace_228514 : CollatzResearch.WordTrace tailWord_228514 prefixEnd_228514 78225012187749447749393 := by
  unfold tailWord_228514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083647573535069982301149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5556393529426853286136397 2083647573535069982301149)
  ·
    refine ⟨781367840075651243362931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2083647573535069982301149 781367840075651243362931)
    ·
      refine ⟨1172051760113476865044397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781367840075651243362931 1172051760113476865044397)
      ·
        refine ⟨439519410042553824391649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1172051760113476865044397 439519410042553824391649)
        ·
          refine ⟨329639557531915368293737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439519410042553824391649 329639557531915368293737)
          ·
            refine ⟨247229668148936526220303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329639557531915368293737 247229668148936526220303)
            ·
              refine ⟨370844502223404789330455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247229668148936526220303 370844502223404789330455)
              ·
                refine ⟨556266753335107183995683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370844502223404789330455 556266753335107183995683)
                ·
                  refine ⟨834400130002660775993525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556266753335107183995683 834400130002660775993525)
                  ·
                    refine ⟨78225012187749447749393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 834400130002660775993525 78225012187749447749393)
                    ·
                      rfl

theorem cell22_228514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_228514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228514 prefixEnd_228514 := by exact prefixLift 228514
  have htrace : WordTrace (prefixWord ++ tailWord_228514) baseStart_228514 baseEnd_228514 := by
    simpa [prefixWord, tailWord_228514, baseEnd_228514] using wordTrace_append hprefix tailTrace_228514
  have hstable : (prefixWord ++ tailWord_228514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228514).length < 2 ^ (prefixWord ++ tailWord_228514).sum := by decide
  have hdescent : baseEnd_228514 < baseStart_228514 := by decide
  rcases family_descends (prefixWord ++ tailWord_228514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228546 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_228546 : Nat := 118140960795 + 228546 * 2 ^ 59
def prefixEnd_228546 : Nat := 4983230072969 + 3 ^ 40 * 228546 * 2
def baseEnd_228546 : Nat := 78235966441712030949295

theorem tailTrace_228546 : CollatzResearch.WordTrace tailWord_228546 prefixEnd_228546 78235966441712030949295 := by
  unfold tailWord_228546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083939357506087348592373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5557171620016232929579661 2083939357506087348592373)
  ·
    refine ⟨195369314766195688930535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2083939357506087348592373 195369314766195688930535)
    ·
      refine ⟨293053972149293533395803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195369314766195688930535 293053972149293533395803)
      ·
        refine ⟨439580958223940300093705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293053972149293533395803 439580958223940300093705)
        ·
          refine ⟨329685718667955225070279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439580958223940300093705 329685718667955225070279)
          ·
            refine ⟨494528578001932837605419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329685718667955225070279 494528578001932837605419)
            ·
              refine ⟨741792867002899256408129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494528578001932837605419 741792867002899256408129)
              ·
                refine ⟨556344650252174442306097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741792867002899256408129 556344650252174442306097)
                ·
                  refine ⟨417258487689130831729573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556344650252174442306097 417258487689130831729573)
                  ·
                    refine ⟨78235966441712030949295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 417258487689130831729573 78235966441712030949295)
                    ·
                      rfl

theorem cell22_228546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_228546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228546 prefixEnd_228546 := by exact prefixLift 228546
  have htrace : WordTrace (prefixWord ++ tailWord_228546) baseStart_228546 baseEnd_228546 := by
    simpa [prefixWord, tailWord_228546, baseEnd_228546] using wordTrace_append hprefix tailTrace_228546
  have hstable : (prefixWord ++ tailWord_228546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228546).length < 2 ^ (prefixWord ++ tailWord_228546).sum := by decide
  have hdescent : baseEnd_228546 < baseStart_228546 := by decide
  rcases family_descends (prefixWord ++ tailWord_228546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228550 : List Nat := [6, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_228550 : Nat := 118140960795 + 228550 * 2 ^ 59
def prefixEnd_228550 : Nat := 4983230072969 + 3 ^ 40 * 228550 * 2
def baseEnd_228550 : Nat := 26079111907819117949761

theorem tailTrace_228550 : CollatzResearch.WordTrace tailWord_228550 prefixEnd_228550 26079111907819117949761 := by
  unfold tailWord_228550
  simp only [CollatzResearch.WordTrace]
  refine ⟨260496978812808064922347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5557268881339905385010069 260496978812808064922347)
  ·
    refine ⟨390745468219212097383521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260496978812808064922347 390745468219212097383521)
    ·
      refine ⟨293059101164409073037641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390745468219212097383521 293059101164409073037641)
      ·
        refine ⟨219794325873306804778231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293059101164409073037641 219794325873306804778231)
        ·
          refine ⟨329691488809960207167347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219794325873306804778231 329691488809960207167347)
          ·
            refine ⟨494537233214940310751021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329691488809960207167347 494537233214940310751021)
            ·
              refine ⟨185451462455602616531633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494537233214940310751021 185451462455602616531633)
              ·
                refine ⟨139088596841701962398725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185451462455602616531633 139088596841701962398725)
                ·
                  refine ⟨26079111907819117949761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139088596841701962398725 26079111907819117949761)
                  ·
                    rfl

theorem cell22_228550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_228550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228550 prefixEnd_228550 := by exact prefixLift 228550
  have htrace : WordTrace (prefixWord ++ tailWord_228550) baseStart_228550 baseEnd_228550 := by
    simpa [prefixWord, tailWord_228550, baseEnd_228550] using wordTrace_append hprefix tailTrace_228550
  have hstable : (prefixWord ++ tailWord_228550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228550).length < 2 ^ (prefixWord ++ tailWord_228550).sum := by decide
  have hdescent : baseEnd_228550 < baseStart_228550 := by decide
  rcases family_descends (prefixWord ++ tailWord_228550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228610 : List Nat := [3, 4, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_228610 : Nat := 118140960795 + 228610 * 2 ^ 59
def prefixEnd_228610 : Nat := 4983230072969 + 3 ^ 40 * 228610 * 2
def baseEnd_228610 : Nat := 78257874949637197349099

theorem tailTrace_228610 : CollatzResearch.WordTrace tailWord_228610 prefixEnd_228610 78257874949637197349099 := by
  unfold tailWord_228610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084522925448122081174821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5558727801194992216466189 2084522925448122081174821)
  ·
    refine ⟨390848048521522890220279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2084522925448122081174821 390848048521522890220279)
    ·
      refine ⟨586272072782284335330419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390848048521522890220279 586272072782284335330419)
      ·
        refine ⟨879408109173426502995629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586272072782284335330419 879408109173426502995629)
        ·
          refine ⟨329778040940034938623361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 879408109173426502995629 329778040940034938623361)
          ·
            refine ⟨247333530705026203967521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329778040940034938623361 247333530705026203967521)
            ·
              refine ⟨185500148028769652975641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247333530705026203967521 185500148028769652975641)
              ·
                refine ⟨139125111021577239731731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185500148028769652975641 139125111021577239731731)
                ·
                  refine ⟨208687666532365859597597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139125111021577239731731 208687666532365859597597)
                  ·
                    refine ⟨78257874949637197349099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 208687666532365859597597 78257874949637197349099)
                    ·
                      rfl

theorem cell22_228610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_228610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228610 prefixEnd_228610 := by exact prefixLift 228610
  have htrace : WordTrace (prefixWord ++ tailWord_228610) baseStart_228610 baseEnd_228610 := by
    simpa [prefixWord, tailWord_228610, baseEnd_228610] using wordTrace_append hprefix tailTrace_228610
  have hstable : (prefixWord ++ tailWord_228610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228610).length < 2 ^ (prefixWord ++ tailWord_228610).sum := by decide
  have hdescent : baseEnd_228610 < baseStart_228610 := by decide
  rcases family_descends (prefixWord ++ tailWord_228610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228617 : List Nat := [1, 2, 1, 1, 3, 3, 3, 4, 4]
def baseStart_228617 : Nat := 118140960795 + 228617 * 2 ^ 59
def prefixEnd_228617 : Nat := 4983230072969 + 3 ^ 40 * 228617 * 2
def baseEnd_228617 : Nat := 26086757064230504141359

theorem tailTrace_228617 : CollatzResearch.WordTrace tailWord_228617 prefixEnd_228617 26086757064230504141359 := by
  unfold tailWord_228617
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338347012767128520204105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5558898008511419013469403 8338347012767128520204105)
  ·
    refine ⟨6253760259575346390153079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8338347012767128520204105 6253760259575346390153079)
    ·
      refine ⟨9380640389363019585229619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6253760259575346390153079 9380640389363019585229619)
      ·
        refine ⟨14070960584044529377844429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9380640389363019585229619 14070960584044529377844429)
        ·
          refine ⟨5276610219016698516691661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14070960584044529377844429 5276610219016698516691661)
          ·
            refine ⟨1978728832131261943759373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5276610219016698516691661 1978728832131261943759373)
            ·
              refine ⟨742023312049223228909765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1978728832131261943759373 742023312049223228909765)
              ·
                refine ⟨139129371009229355420581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742023312049223228909765 139129371009229355420581)
                ·
                  refine ⟨26086757064230504141359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139129371009229355420581 26086757064230504141359)
                  ·
                    rfl

theorem cell22_228617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 4].length) (baseStart_228617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228617 prefixEnd_228617 := by exact prefixLift 228617
  have htrace : WordTrace (prefixWord ++ tailWord_228617) baseStart_228617 baseEnd_228617 := by
    simpa [prefixWord, tailWord_228617, baseEnd_228617] using wordTrace_append hprefix tailTrace_228617
  have hstable : (prefixWord ++ tailWord_228617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228617).length < 2 ^ (prefixWord ++ tailWord_228617).sum := by decide
  have hdescent : baseEnd_228617 < baseStart_228617 := by decide
  rcases family_descends (prefixWord ++ tailWord_228617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228632 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_228632 : Nat := 118140960795 + 228632 * 2 ^ 59
def prefixEnd_228632 : Nat := 4983230072969 + 3 ^ 40 * 228632 * 2
def baseEnd_228632 : Nat := 78265405999236473299031

theorem tailTrace_228632 : CollatzResearch.WordTrace tailWord_228632 prefixEnd_228632 78265405999236473299031 := by
  unfold tailWord_228632
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169447053856393041000075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5559262738475190721333433 4169447053856393041000075)
  ·
    refine ⟨6254170580784589561500113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4169447053856393041000075 6254170580784589561500113)
    ·
      refine ⟨4690627935588442171125085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6254170580784589561500113 4690627935588442171125085)
      ·
        refine ⟨1758985475845665814171907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4690627935588442171125085 1758985475845665814171907)
        ·
          refine ⟨2638478213768498721257861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758985475845665814171907 2638478213768498721257861)
          ·
            refine ⟨494714665081593510235849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2638478213768498721257861 494714665081593510235849)
            ·
              refine ⟨371035998811195132676887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494714665081593510235849 371035998811195132676887)
              ·
                refine ⟨556553998216792699015331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371035998811195132676887 556553998216792699015331)
                ·
                  refine ⟨834830997325189048522997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556553998216792699015331 834830997325189048522997)
                  ·
                    refine ⟨78265405999236473299031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 834830997325189048522997 78265405999236473299031)
                    ·
                      rfl

theorem cell22_228632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_228632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228632 prefixEnd_228632 := by exact prefixLift 228632
  have htrace : WordTrace (prefixWord ++ tailWord_228632) baseStart_228632 baseEnd_228632 := by
    simpa [prefixWord, tailWord_228632, baseEnd_228632] using wordTrace_append hprefix tailTrace_228632
  have hstable : (prefixWord ++ tailWord_228632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228632).length < 2 ^ (prefixWord ++ tailWord_228632).sum := by decide
  have hdescent : baseEnd_228632 < baseStart_228632 := by decide
  rcases family_descends (prefixWord ++ tailWord_228632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228653 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_228653 : Nat := 118140960795 + 228653 * 2 ^ 59
def prefixEnd_228653 : Nat := 4983230072969 + 3 ^ 40 * 228653 * 2
def baseEnd_228653 : Nat := 78272594728399418523967

theorem tailTrace_228653 : CollatzResearch.WordTrace tailWord_228653 prefixEnd_228653 78272594728399418523967 := by
  unfold tailWord_228653
  simp only [CollatzResearch.WordTrace]
  refine ⟨8339660040636706668514613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5559773360424471112343075 8339660040636706668514613)
  ·
    refine ⟨781843128809691250173245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8339660040636706668514613 781843128809691250173245)
    ·
      refine ⟨293191173303634218814967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 781843128809691250173245 293191173303634218814967)
      ·
        refine ⟨439786759955451328222451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293191173303634218814967 439786759955451328222451)
        ·
          refine ⟨659680139933176992333677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439786759955451328222451 659680139933176992333677)
          ·
            refine ⟨247380052474941372125129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 659680139933176992333677 247380052474941372125129)
            ·
              refine ⟨185535039356206029093847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247380052474941372125129 185535039356206029093847)
              ·
                refine ⟨278302559034309043640771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185535039356206029093847 278302559034309043640771)
                ·
                  refine ⟨417453838551463565461157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278302559034309043640771 417453838551463565461157)
                  ·
                    refine ⟨78272594728399418523967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 417453838551463565461157 78272594728399418523967)
                    ·
                      rfl

theorem cell22_228653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_228653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228653 prefixEnd_228653 := by exact prefixLift 228653
  have htrace : WordTrace (prefixWord ++ tailWord_228653) baseStart_228653 baseEnd_228653 := by
    simpa [prefixWord, tailWord_228653, baseEnd_228653] using wordTrace_append hprefix tailTrace_228653
  have hstable : (prefixWord ++ tailWord_228653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228653).length < 2 ^ (prefixWord ++ tailWord_228653).sum := by decide
  have hdescent : baseEnd_228653 < baseStart_228653 := by decide
  rcases family_descends (prefixWord ++ tailWord_228653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228705 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_228705 : Nat := 118140960795 + 228705 * 2 ^ 59
def prefixEnd_228705 : Nat := 4983230072969 + 3 ^ 40 * 228705 * 2
def baseEnd_228705 : Nat := 78290395391088616223807

theorem tailTrace_228705 : CollatzResearch.WordTrace tailWord_228705 prefixEnd_228705 78290395391088616223807 := by
  unfold tailWord_228705
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341556636448319549407569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5561037757632213032938379 8341556636448319549407569)
  ·
    refine ⟨6256167477336239662055677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8341556636448319549407569 6256167477336239662055677)
    ·
      refine ⟨2346062804001089873270879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6256167477336239662055677 2346062804001089873270879)
      ·
        refine ⟨3519094206001634809906319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2346062804001089873270879 3519094206001634809906319)
        ·
          refine ⟨5278641309002452214859479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519094206001634809906319 5278641309002452214859479)
          ·
            refine ⟨7917961963503678322289219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278641309002452214859479 7917961963503678322289219)
            ·
              refine ⟨11876942945255517483433829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7917961963503678322289219 11876942945255517483433829)
              ·
                refine ⟨2226926802235409528143843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11876942945255517483433829 2226926802235409528143843)
                ·
                  refine ⟨3340390203353114292215765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226926802235409528143843 3340390203353114292215765)
                  ·
                    refine ⟨78290395391088616223807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3340390203353114292215765 78290395391088616223807)
                    ·
                      rfl

theorem cell22_228705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_228705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228705 prefixEnd_228705 := by exact prefixLift 228705
  have htrace : WordTrace (prefixWord ++ tailWord_228705) baseStart_228705 baseEnd_228705 := by
    simpa [prefixWord, tailWord_228705, baseEnd_228705] using wordTrace_append hprefix tailTrace_228705
  have hstable : (prefixWord ++ tailWord_228705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228705).length < 2 ^ (prefixWord ++ tailWord_228705).sum := by decide
  have hdescent : baseEnd_228705 < baseStart_228705 := by decide
  rcases family_descends (prefixWord ++ tailWord_228705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228767 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 3, 5]
def baseStart_228767 : Nat := 118140960795 + 228767 * 2 ^ 59
def prefixEnd_228767 : Nat := 4983230072969 + 3 ^ 40 * 228767 * 2
def baseEnd_228767 : Nat := 78311619258141121173617

theorem tailTrace_228767 : CollatzResearch.WordTrace tailWord_228767 prefixEnd_228767 78311619258141121173617 := by
  unfold tailWord_228767
  simp only [CollatzResearch.WordTrace]
  refine ⟨8343817962223704138164555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5562545308149136092109703 8343817962223704138164555)
  ·
    refine ⟨12515726943335556207246833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8343817962223704138164555 12515726943335556207246833)
    ·
      refine ⟨9386795207501667155435125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12515726943335556207246833 9386795207501667155435125)
      ·
        refine ⟨880012050703281295822043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9386795207501667155435125 880012050703281295822043)
        ·
          refine ⟨1320018076054921943733065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880012050703281295822043 1320018076054921943733065)
          ·
            refine ⟨990013557041191457799799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320018076054921943733065 990013557041191457799799)
            ·
              refine ⟨1485020335561787186699699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990013557041191457799799 1485020335561787186699699)
              ·
                refine ⟨2227530503342680780049549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485020335561787186699699 2227530503342680780049549)
                ·
                  refine ⟨835323938753505292518581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2227530503342680780049549 835323938753505292518581)
                  ·
                    refine ⟨78311619258141121173617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 835323938753505292518581 78311619258141121173617)
                    ·
                      rfl

theorem cell22_228767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_228767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228767 prefixEnd_228767 := by exact prefixLift 228767
  have htrace : WordTrace (prefixWord ++ tailWord_228767) baseStart_228767 baseEnd_228767 := by
    simpa [prefixWord, tailWord_228767, baseEnd_228767] using wordTrace_append hprefix tailTrace_228767
  have hstable : (prefixWord ++ tailWord_228767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228767).length < 2 ^ (prefixWord ++ tailWord_228767).sum := by decide
  have hdescent : baseEnd_228767 < baseStart_228767 := by decide
  rcases family_descends (prefixWord ++ tailWord_228767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228846 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_228846 : Nat := 118140960795 + 228846 * 2 ^ 59
def prefixEnd_228846 : Nat := 4983230072969 + 3 ^ 40 * 228846 * 2
def baseEnd_228846 : Nat := 78338662572611248448375

theorem tailTrace_228846 : CollatzResearch.WordTrace tailWord_228846 prefixEnd_228846 78338662572611248448375 := by
  unfold tailWord_228846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043337416117187578786299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5564466219291667086860261 1043337416117187578786299)
  ·
    refine ⟨1565006124175781368179449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1043337416117187578786299 1565006124175781368179449)
    ·
      refine ⟨1173754593131836026134587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1565006124175781368179449 1173754593131836026134587)
      ·
        refine ⟨1760631889697754039201881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173754593131836026134587 1760631889697754039201881)
        ·
          refine ⟨1320473917273315529401411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1760631889697754039201881 1320473917273315529401411)
          ·
            refine ⟨1980710875909973294102117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320473917273315529401411 1980710875909973294102117)
            ·
              refine ⟨371383289233119992644147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1980710875909973294102117 371383289233119992644147)
              ·
                refine ⟨557074933849679988966221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371383289233119992644147 557074933849679988966221)
                ·
                  refine ⟨208903100193629995862333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 557074933849679988966221 208903100193629995862333)
                  ·
                    refine ⟨78338662572611248448375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 208903100193629995862333 78338662572611248448375)
                    ·
                      rfl

theorem cell22_228846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_228846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228846 prefixEnd_228846 := by exact prefixLift 228846
  have htrace : WordTrace (prefixWord ++ tailWord_228846) baseStart_228846 baseEnd_228846 := by
    simpa [prefixWord, tailWord_228846, baseEnd_228846] using wordTrace_append hprefix tailTrace_228846
  have hstable : (prefixWord ++ tailWord_228846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228846).length < 2 ^ (prefixWord ++ tailWord_228846).sum := by decide
  have hdescent : baseEnd_228846 < baseStart_228846 := by decide
  rcases family_descends (prefixWord ++ tailWord_228846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228947 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 3, 9]
def baseStart_228947 : Nat := 118140960795 + 228947 * 2 ^ 59
def prefixEnd_228947 : Nat := 4983230072969 + 3 ^ 40 * 228947 * 2
def baseEnd_228947 : Nat := 78373236936680651673065

theorem tailTrace_228947 : CollatzResearch.WordTrace tailWord_228947 prefixEnd_228947 78373236936680651673065 := by
  unfold tailWord_228947
  simp only [CollatzResearch.WordTrace]
  refine ⟨8350383101571594879717095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5566922067714396586478063 8350383101571594879717095)
  ·
    refine ⟨12525574652357392319575643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8350383101571594879717095 12525574652357392319575643)
    ·
      refine ⟨18788361978536088479363465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12525574652357392319575643 18788361978536088479363465)
      ·
        refine ⟨14091271483902066359522599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18788361978536088479363465 14091271483902066359522599)
        ·
          refine ⟨21136907225853099539283899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14091271483902066359522599 21136907225853099539283899)
          ·
            refine ⟨31705360838779649308925849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21136907225853099539283899 31705360838779649308925849)
            ·
              refine ⟨23779020629084736981694387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31705360838779649308925849 23779020629084736981694387)
              ·
                refine ⟨35668530943627105472541581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23779020629084736981694387 35668530943627105472541581)
                ·
                  refine ⟨13375699103860164552203093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35668530943627105472541581 13375699103860164552203093)
                  ·
                    refine ⟨78373236936680651673065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 13375699103860164552203093 78373236936680651673065)
                    ·
                      rfl

theorem cell22_228947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_228947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_228947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_228947 prefixEnd_228947 := by exact prefixLift 228947
  have htrace : WordTrace (prefixWord ++ tailWord_228947) baseStart_228947 baseEnd_228947 := by
    simpa [prefixWord, tailWord_228947, baseEnd_228947] using wordTrace_append hprefix tailTrace_228947
  have hstable : (prefixWord ++ tailWord_228947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228947).length < 2 ^ (prefixWord ++ tailWord_228947).sum := by decide
  have hdescent : baseEnd_228947 < baseStart_228947 := by decide
  rcases family_descends (prefixWord ++ tailWord_228947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229028 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 5]
def baseStart_229028 : Nat := 118140960795 + 229028 * 2 ^ 59
def prefixEnd_229028 : Nat := 4983230072969 + 3 ^ 40 * 229028 * 2
def baseEnd_229028 : Nat := 26133654964007813465939

theorem tailTrace_229028 : CollatzResearch.WordTrace tailWord_229028 prefixEnd_229028 26133654964007813465939 := by
  unfold tailWord_229028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176668707139072856707869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5568891609518763808943825 4176668707139072856707869)
  ·
    refine ⟨1566250765177152321265451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4176668707139072856707869 1566250765177152321265451)
    ·
      refine ⟨2349376147765728481898177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1566250765177152321265451 2349376147765728481898177)
      ·
        refine ⟨1762032110824296361423633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2349376147765728481898177 1762032110824296361423633)
        ·
          refine ⟨1321524083118222271067725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1762032110824296361423633 1321524083118222271067725)
          ·
            refine ⟨495571531169333351650397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1321524083118222271067725 495571531169333351650397)
            ·
              refine ⟨185839324188500006868899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 495571531169333351650397 185839324188500006868899)
              ·
                refine ⟨278758986282750010303349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185839324188500006868899 278758986282750010303349)
                ·
                  refine ⟨26133654964007813465939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278758986282750010303349 26133654964007813465939)
                  ·
                    rfl

theorem cell22_229028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_229028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229028 prefixEnd_229028 := by exact prefixLift 229028
  have htrace : WordTrace (prefixWord ++ tailWord_229028) baseStart_229028 baseEnd_229028 := by
    simpa [prefixWord, tailWord_229028, baseEnd_229028] using wordTrace_append hprefix tailTrace_229028
  have hstable : (prefixWord ++ tailWord_229028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229028).length < 2 ^ (prefixWord ++ tailWord_229028).sum := by decide
  have hdescent : baseEnd_229028 < baseStart_229028 := by decide
  rcases family_descends (prefixWord ++ tailWord_229028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229039 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 6]
def baseStart_229039 : Nat := 118140960795 + 229039 * 2 ^ 59
def prefixEnd_229039 : Nat := 4983230072969 + 3 ^ 40 * 229039 * 2
def baseEnd_229039 : Nat := 26134910138941026124261

theorem tailTrace_229039 : CollatzResearch.WordTrace tailWord_229039 prefixEnd_229039 26134910138941026124261 := by
  unfold tailWord_229039
  simp only [CollatzResearch.WordTrace]
  refine ⟨8353738617238294592066171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5569159078158863061377447 8353738617238294592066171)
  ·
    refine ⟨12530607925857441888099257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8353738617238294592066171 12530607925857441888099257)
    ·
      refine ⟨9397955944393081416074443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12530607925857441888099257 9397955944393081416074443)
      ·
        refine ⟨14096933916589622124111665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9397955944393081416074443 14096933916589622124111665)
        ·
          refine ⟨10572700437442216593083749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14096933916589622124111665 10572700437442216593083749)
          ·
            refine ⟨1982381332020415611203203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10572700437442216593083749 1982381332020415611203203)
            ·
              refine ⟨2973571998030623416804805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982381332020415611203203 2973571998030623416804805)
              ·
                refine ⟨557544749630741890650901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2973571998030623416804805 557544749630741890650901)
                ·
                  refine ⟨26134910138941026124261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 557544749630741890650901 26134910138941026124261)
                  ·
                    rfl

theorem cell22_229039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 6].length) (baseStart_229039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229039 prefixEnd_229039 := by exact prefixLift 229039
  have htrace : WordTrace (prefixWord ++ tailWord_229039) baseStart_229039 baseEnd_229039 := by
    simpa [prefixWord, tailWord_229039, baseEnd_229039] using wordTrace_append hprefix tailTrace_229039
  have hstable : (prefixWord ++ tailWord_229039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229039).length < 2 ^ (prefixWord ++ tailWord_229039).sum := by decide
  have hdescent : baseEnd_229039 < baseStart_229039 := by decide
  rcases family_descends (prefixWord ++ tailWord_229039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229099 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 2, 7]
def baseStart_229099 : Nat := 118140960795 + 229099 * 2 ^ 59
def prefixEnd_229099 : Nat := 4983230072969 + 3 ^ 40 * 229099 * 2
def baseEnd_229099 : Nat := 78425269643002921872599

theorem tailTrace_229099 : CollatzResearch.WordTrace tailWord_229099 prefixEnd_229099 78425269643002921872599 := by
  unfold tailWord_229099
  simp only [CollatzResearch.WordTrace]
  refine ⟨8355926997020924839250351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5570617998013949892833567 8355926997020924839250351)
  ·
    refine ⟨12533890495531387258875527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8355926997020924839250351 12533890495531387258875527)
    ·
      refine ⟨18800835743297080888313291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12533890495531387258875527 18800835743297080888313291)
      ·
        refine ⟨28201253614945621332469937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18800835743297080888313291 28201253614945621332469937)
        ·
          refine ⟨21150940211209215999352453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28201253614945621332469937 21150940211209215999352453)
          ·
            refine ⟨3965801289601727999878585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21150940211209215999352453 3965801289601727999878585)
            ·
              refine ⟨2974350967201295999908939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3965801289601727999878585 2974350967201295999908939)
              ·
                refine ⟨4461526450801943999863409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974350967201295999908939 4461526450801943999863409)
                ·
                  refine ⟨3346144838101457999897557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461526450801943999863409 3346144838101457999897557)
                  ·
                    refine ⟨78425269643002921872599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3346144838101457999897557 78425269643002921872599)
                    ·
                      rfl

theorem cell22_229099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_229099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229099 prefixEnd_229099 := by exact prefixLift 229099
  have htrace : WordTrace (prefixWord ++ tailWord_229099) baseStart_229099 baseEnd_229099 := by
    simpa [prefixWord, tailWord_229099, baseEnd_229099] using wordTrace_append hprefix tailTrace_229099
  have hstable : (prefixWord ++ tailWord_229099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229099).length < 2 ^ (prefixWord ++ tailWord_229099).sum := by decide
  have hdescent : baseEnd_229099 < baseStart_229099 := by decide
  rcases family_descends (prefixWord ++ tailWord_229099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229101 : List Nat := [1, 5, 1, 2, 1, 2, 2, 8]
def baseStart_229101 : Nat := 118140960795 + 229101 * 2 ^ 59
def prefixEnd_229101 : Nat := 4983230072969 + 3 ^ 40 * 229101 * 2
def baseEnd_229101 : Nat := 8713994920430620369177

theorem tailTrace_229101 : CollatzResearch.WordTrace tailWord_229101 prefixEnd_229101 8713994920430620369177 := by
  unfold tailWord_229101
  simp only [CollatzResearch.WordTrace]
  refine ⟨8355999943013679180823157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5570666628675786120548771 8355999943013679180823157)
  ·
    refine ⟨783374994657532423202171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8355999943013679180823157 783374994657532423202171)
    ·
      refine ⟨1175062491986298634803257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783374994657532423202171 1175062491986298634803257)
      ·
        refine ⟨881296868989723976102443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1175062491986298634803257 881296868989723976102443)
        ·
          refine ⟨1321945303484585964153665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881296868989723976102443 1321945303484585964153665)
          ·
            refine ⟨991458977613439473115249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321945303484585964153665 991458977613439473115249)
            ·
              refine ⟨743594233210079604836437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991458977613439473115249 743594233210079604836437)
              ·
                refine ⟨8713994920430620369177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 743594233210079604836437 8713994920430620369177)
                ·
                  rfl

theorem cell22_229101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 8].length) (baseStart_229101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229101 prefixEnd_229101 := by exact prefixLift 229101
  have htrace : WordTrace (prefixWord ++ tailWord_229101) baseStart_229101 baseEnd_229101 := by
    simpa [prefixWord, tailWord_229101, baseEnd_229101] using wordTrace_append hprefix tailTrace_229101
  have hstable : (prefixWord ++ tailWord_229101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229101).length < 2 ^ (prefixWord ++ tailWord_229101).sum := by decide
  have hdescent : baseEnd_229101 < baseStart_229101 := by decide
  rcases family_descends (prefixWord ++ tailWord_229101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229118 : List Nat := [4, 2, 2, 1, 4, 9]
def baseStart_229118 : Nat := 118140960795 + 229118 * 2 ^ 59
def prefixEnd_229118 : Nat := 4983230072969 + 3 ^ 40 * 229118 * 2
def baseEnd_229118 : Nat := 968293502855471674661

theorem tailTrace_229118 : CollatzResearch.WordTrace tailWord_229118 prefixEnd_229118 968293502855471674661 := by
  unfold tailWord_229118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044577497994011385524001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5571079989301394056128005 1044577497994011385524001)
  ·
    refine ⟨783433123495508539143001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1044577497994011385524001 783433123495508539143001)
    ·
      refine ⟨587574842621631404357251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 783433123495508539143001 587574842621631404357251)
      ·
        refine ⟨881362263932447106535877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587574842621631404357251 881362263932447106535877)
        ·
          refine ⟨165255424487333832475477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 881362263932447106535877 165255424487333832475477)
          ·
            refine ⟨968293502855471674661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 165255424487333832475477 968293502855471674661)
            ·
              rfl

theorem cell22_229118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 9].length) (baseStart_229118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229118 prefixEnd_229118 := by exact prefixLift 229118
  have htrace : WordTrace (prefixWord ++ tailWord_229118) baseStart_229118 baseEnd_229118 := by
    simpa [prefixWord, tailWord_229118, baseEnd_229118] using wordTrace_append hprefix tailTrace_229118
  have hstable : (prefixWord ++ tailWord_229118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229118).length < 2 ^ (prefixWord ++ tailWord_229118).sum := by decide
  have hdescent : baseEnd_229118 < baseStart_229118 := by decide
  rcases family_descends (prefixWord ++ tailWord_229118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229191 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 6]
def baseStart_229191 : Nat := 118140960795 + 229191 * 2 ^ 59
def prefixEnd_229191 : Nat := 4983230072969 + 3 ^ 40 * 229191 * 2
def baseEnd_229191 : Nat := 26152254374381782857439

theorem tailTrace_229191 : CollatzResearch.WordTrace tailWord_229191 prefixEnd_229191 26152254374381782857439 := by
  unfold tailWord_229191
  simp only [CollatzResearch.WordTrace]
  refine ⟨8359282512687624551599427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5572855008458416367732951 8359282512687624551599427)
  ·
    refine ⟨12538923769031436827399141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8359282512687624551599427 12538923769031436827399141)
    ·
      refine ⟨2351048206693394405137339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12538923769031436827399141 2351048206693394405137339)
      ·
        refine ⟨3526572310040091607706009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351048206693394405137339 3526572310040091607706009)
        ·
          refine ⟨2644929232530068705779507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3526572310040091607706009 2644929232530068705779507)
          ·
            refine ⟨3967393848795103058669261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644929232530068705779507 3967393848795103058669261)
            ·
              refine ⟨1487772693298163647000973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3967393848795103058669261 1487772693298163647000973)
              ·
                refine ⟨557914759986811367625365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1487772693298163647000973 557914759986811367625365)
                ·
                  refine ⟨26152254374381782857439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 557914759986811367625365 26152254374381782857439)
                  ·
                    rfl

theorem cell22_229191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 6].length) (baseStart_229191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229191 prefixEnd_229191 := by exact prefixLift 229191
  have htrace : WordTrace (prefixWord ++ tailWord_229191) baseStart_229191 baseEnd_229191 := by
    simpa [prefixWord, tailWord_229191, baseEnd_229191] using wordTrace_append hprefix tailTrace_229191
  have hstable : (prefixWord ++ tailWord_229191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229191).length < 2 ^ (prefixWord ++ tailWord_229191).sum := by decide
  have hdescent : baseEnd_229191 < baseStart_229191 := by decide
  rcases family_descends (prefixWord ++ tailWord_229191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229197 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 5]
def baseStart_229197 : Nat := 118140960795 + 229197 * 2 ^ 59
def prefixEnd_229197 : Nat := 4983230072969 + 3 ^ 40 * 229197 * 2
def baseEnd_229197 : Nat := 26152939015254444307433

theorem tailTrace_229197 : CollatzResearch.WordTrace tailWord_229197 prefixEnd_229197 26152939015254444307433 := by
  unfold tailWord_229197
  simp only [CollatzResearch.WordTrace]
  refine ⟨8359501350665887576317845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5573000900443925050878563 8359501350665887576317845)
  ·
    refine ⟨391851625812463480139899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8359501350665887576317845 391851625812463480139899)
    ·
      refine ⟨587777438718695220209849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391851625812463480139899 587777438718695220209849)
      ·
        refine ⟨440833079039021415157387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587777438718695220209849 440833079039021415157387)
        ·
          refine ⟨661249618558532122736081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440833079039021415157387 661249618558532122736081)
          ·
            refine ⟨495937213918899092052061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661249618558532122736081 495937213918899092052061)
            ·
              refine ⟨185976455219587159519523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 495937213918899092052061 185976455219587159519523)
              ·
                refine ⟨278964682829380739279285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185976455219587159519523 278964682829380739279285)
                ·
                  refine ⟨26152939015254444307433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278964682829380739279285 26152939015254444307433)
                  ·
                    rfl

theorem cell22_229197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_229197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229197 prefixEnd_229197 := by exact prefixLift 229197
  have htrace : WordTrace (prefixWord ++ tailWord_229197) baseStart_229197 baseEnd_229197 := by
    simpa [prefixWord, tailWord_229197, baseEnd_229197] using wordTrace_append hprefix tailTrace_229197
  have hstable : (prefixWord ++ tailWord_229197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229197).length < 2 ^ (prefixWord ++ tailWord_229197).sum := by decide
  have hdescent : baseEnd_229197 < baseStart_229197 := by decide
  rcases family_descends (prefixWord ++ tailWord_229197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229223 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 6, 3]
def baseStart_229223 : Nat := 118140960795 + 229223 * 2 ^ 59
def prefixEnd_229223 : Nat := 4983230072969 + 3 ^ 40 * 229223 * 2
def baseEnd_229223 : Nat := 78467717377107931772219

theorem tailTrace_229223 : CollatzResearch.WordTrace tailWord_229223 prefixEnd_229223 78467717377107931772219 := by
  unfold tailWord_229223
  simp only [CollatzResearch.WordTrace]
  refine ⟨8360449648571694016764323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5573633099047796011176215 8360449648571694016764323)
  ·
    refine ⟨12540674472857541025146485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8360449648571694016764323 12540674472857541025146485)
    ·
      refine ⟨1175688231830394471107483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12540674472857541025146485 1175688231830394471107483)
      ·
        refine ⟨1763532347745591706661225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1175688231830394471107483 1763532347745591706661225)
        ·
          refine ⟨1322649260809193779995919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1763532347745591706661225 1322649260809193779995919)
          ·
            refine ⟨1983973891213790669993879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322649260809193779995919 1983973891213790669993879)
            ·
              refine ⟨2975960836820686004990819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983973891213790669993879 2975960836820686004990819)
              ·
                refine ⟨4463941255231029007486229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975960836820686004990819 4463941255231029007486229)
                ·
                  refine ⟨209247246338954484725917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4463941255231029007486229 209247246338954484725917)
                  ·
                    refine ⟨78467717377107931772219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209247246338954484725917 78467717377107931772219)
                    ·
                      rfl

theorem cell22_229223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_229223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229223 prefixEnd_229223 := by exact prefixLift 229223
  have htrace : WordTrace (prefixWord ++ tailWord_229223) baseStart_229223 baseEnd_229223 := by
    simpa [prefixWord, tailWord_229223, baseEnd_229223] using wordTrace_append hprefix tailTrace_229223
  have hstable : (prefixWord ++ tailWord_229223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229223).length < 2 ^ (prefixWord ++ tailWord_229223).sum := by decide
  have hdescent : baseEnd_229223 < baseStart_229223 := by decide
  rcases family_descends (prefixWord ++ tailWord_229223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229272 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 2, 4]
def baseStart_229272 : Nat := 118140960795 + 229272 * 2 ^ 59
def prefixEnd_229272 : Nat := 4983230072969 + 3 ^ 40 * 229272 * 2
def baseEnd_229272 : Nat := 78484491078488137297069

theorem tailTrace_229272 : CollatzResearch.WordTrace tailWord_229272 prefixEnd_229272 78484491078488137297069 := by
  unfold tailWord_229272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181118412697087692649035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5574824550262783590198713 4181118412697087692649035)
  ·
    refine ⟨6271677619045631538973553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4181118412697087692649035 6271677619045631538973553)
    ·
      refine ⟨4703758214284223654230165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6271677619045631538973553 4703758214284223654230165)
      ·
        refine ⟨220488666294572983792039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4703758214284223654230165 220488666294572983792039)
        ·
          refine ⟨330732999441859475688059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220488666294572983792039 330732999441859475688059)
          ·
            refine ⟨496099499162789213532089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330732999441859475688059 496099499162789213532089)
            ·
              refine ⟨372074624372091910149067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496099499162789213532089 372074624372091910149067)
              ·
                refine ⟨558111936558137865223601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372074624372091910149067 558111936558137865223601)
                ·
                  refine ⟨418583952418603398917701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558111936558137865223601 418583952418603398917701)
                  ·
                    refine ⟨78484491078488137297069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 418583952418603398917701 78484491078488137297069)
                    ·
                      rfl

theorem cell22_229272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_229272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229272 prefixEnd_229272 := by exact prefixLift 229272
  have htrace : WordTrace (prefixWord ++ tailWord_229272) baseStart_229272 baseEnd_229272 := by
    simpa [prefixWord, tailWord_229272, baseEnd_229272] using wordTrace_append hprefix tailTrace_229272
  have hstable : (prefixWord ++ tailWord_229272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229272).length < 2 ^ (prefixWord ++ tailWord_229272).sum := by decide
  have hdescent : baseEnd_229272 < baseStart_229272 := by decide
  rcases family_descends (prefixWord ++ tailWord_229272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229296 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_229296 : Nat := 118140960795 + 229296 * 2 ^ 59
def prefixEnd_229296 : Nat := 4983230072969 + 3 ^ 40 * 229296 * 2
def baseEnd_229296 : Nat := 78492706768960074696995

theorem tailTrace_229296 : CollatzResearch.WordTrace tailWord_229296 prefixEnd_229296 78492706768960074696995 := by
  unfold tailWord_229296
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181556088653613742085871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5575408118204818322781161 4181556088653613742085871)
  ·
    refine ⟨6272334132980420613128807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4181556088653613742085871 6272334132980420613128807)
    ·
      refine ⟨9408501199470630919693211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6272334132980420613128807 9408501199470630919693211)
      ·
        refine ⟨14112751799205946379539817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9408501199470630919693211 14112751799205946379539817)
        ·
          refine ⟨10584563849404459784654863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14112751799205946379539817 10584563849404459784654863)
          ·
            refine ⟨15876845774106689676982295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584563849404459784654863 15876845774106689676982295)
            ·
              refine ⟨23815268661160034515473443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15876845774106689676982295 23815268661160034515473443)
              ·
                refine ⟨35722902991740051773210165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23815268661160034515473443 35722902991740051773210165)
                ·
                  refine ⟨3349022155475629853738453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35722902991740051773210165 3349022155475629853738453)
                  ·
                    refine ⟨78492706768960074696995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3349022155475629853738453 78492706768960074696995)
                    ·
                      rfl

theorem cell22_229296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_229296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229296 prefixEnd_229296 := by exact prefixLift 229296
  have htrace : WordTrace (prefixWord ++ tailWord_229296) baseStart_229296 baseEnd_229296 := by
    simpa [prefixWord, tailWord_229296, baseEnd_229296] using wordTrace_append hprefix tailTrace_229296
  have hstable : (prefixWord ++ tailWord_229296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229296).length < 2 ^ (prefixWord ++ tailWord_229296).sum := by decide
  have hdescent : baseEnd_229296 < baseStart_229296 := by decide
  rcases family_descends (prefixWord ++ tailWord_229296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229328 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_229328 : Nat := 118140960795 + 229328 * 2 ^ 59
def prefixEnd_229328 : Nat := 4983230072969 + 3 ^ 40 * 229328 * 2
def baseEnd_229328 : Nat := 78503661022922657896897

theorem tailTrace_229328 : CollatzResearch.WordTrace tailWord_229328 prefixEnd_229328 78503661022922657896897 := by
  unfold tailWord_229328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182139656595648474668319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5576186208794197966224425 4182139656595648474668319)
  ·
    refine ⟨6273209484893472712002479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4182139656595648474668319 6273209484893472712002479)
    ·
      refine ⟨9409814227340209068003719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6273209484893472712002479 9409814227340209068003719)
      ·
        refine ⟨14114721341010313602005579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9409814227340209068003719 14114721341010313602005579)
        ·
          refine ⟨21172082011515470403008369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14114721341010313602005579 21172082011515470403008369)
          ·
            refine ⟨15879061508636602802256277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21172082011515470403008369 15879061508636602802256277)
            ·
              refine ⟨744331008217340756355763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15879061508636602802256277 744331008217340756355763)
              ·
                refine ⟨1116496512326011134533645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744331008217340756355763 1116496512326011134533645)
                ·
                  refine ⟨418686192122254175450117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116496512326011134533645 418686192122254175450117)
                  ·
                    refine ⟨78503661022922657896897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 418686192122254175450117 78503661022922657896897)
                    ·
                      rfl

theorem cell22_229328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_229328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229328 prefixEnd_229328 := by exact prefixLift 229328
  have htrace : WordTrace (prefixWord ++ tailWord_229328) baseStart_229328 baseEnd_229328 := by
    simpa [prefixWord, tailWord_229328, baseEnd_229328] using wordTrace_append hprefix tailTrace_229328
  have hstable : (prefixWord ++ tailWord_229328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229328).length < 2 ^ (prefixWord ++ tailWord_229328).sum := by decide
  have hdescent : baseEnd_229328 < baseStart_229328 := by decide
  rcases family_descends (prefixWord ++ tailWord_229328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229360 : List Nat := [2, 1, 1, 1, 3, 2, 4, 4, 4]
def baseStart_229360 : Nat := 118140960795 + 229360 * 2 ^ 59
def prefixEnd_229360 : Nat := 4983230072969 + 3 ^ 40 * 229360 * 2
def baseEnd_229360 : Nat := 26171538425628413698933

theorem tailTrace_229360 : CollatzResearch.WordTrace tailWord_229360 prefixEnd_229360 26171538425628413698933 := by
  unfold tailWord_229360
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182723224537683207250767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5576964299383577609667689 4182723224537683207250767)
  ·
    refine ⟨6274084836806524810876151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4182723224537683207250767 6274084836806524810876151)
    ·
      refine ⟨9411127255209787216314227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6274084836806524810876151 9411127255209787216314227)
      ·
        refine ⟨14116690882814680824471341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9411127255209787216314227 14116690882814680824471341)
        ·
          refine ⟨5293759081055505309176753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14116690882814680824471341 5293759081055505309176753)
          ·
            refine ⟨3970319310791628981882565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5293759081055505309176753 3970319310791628981882565)
            ·
              refine ⟨744434870773430434102981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3970319310791628981882565 744434870773430434102981)
              ·
                refine ⟨139581538270018206394309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744434870773430434102981 139581538270018206394309)
                ·
                  refine ⟨26171538425628413698933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139581538270018206394309 26171538425628413698933)
                  ·
                    rfl

theorem cell22_229360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 4].length) (baseStart_229360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229360 prefixEnd_229360 := by exact prefixLift 229360
  have htrace : WordTrace (prefixWord ++ tailWord_229360) baseStart_229360 baseEnd_229360 := by
    simpa [prefixWord, tailWord_229360, baseEnd_229360] using wordTrace_append hprefix tailTrace_229360
  have hstable : (prefixWord ++ tailWord_229360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229360).length < 2 ^ (prefixWord ++ tailWord_229360).sum := by decide
  have hdescent : baseEnd_229360 < baseStart_229360 := by decide
  rcases family_descends (prefixWord ++ tailWord_229360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229373 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_229373 : Nat := 118140960795 + 229373 * 2 ^ 59
def prefixEnd_229373 : Nat := 4983230072969 + 3 ^ 40 * 229373 * 2
def baseEnd_229373 : Nat := 78519065442557540521759

theorem tailTrace_229373 : CollatzResearch.WordTrace tailWord_229373 prefixEnd_229373 78519065442557540521759 := by
  unfold tailWord_229373
  simp only [CollatzResearch.WordTrace]
  refine ⟨8365920598028269634724773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5577280398685513089816515 8365920598028269634724773)
  ·
    refine ⟨1568610112130300556510895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8365920598028269634724773 1568610112130300556510895)
    ·
      refine ⟨2352915168195450834766343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568610112130300556510895 2352915168195450834766343)
      ·
        refine ⟨3529372752293176252149515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352915168195450834766343 3529372752293176252149515)
        ·
          refine ⟨5294059128439764378224273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3529372752293176252149515 5294059128439764378224273)
          ·
            refine ⟨3970544346329823283668205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5294059128439764378224273 3970544346329823283668205)
            ·
              refine ⟨1488954129873683731375577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3970544346329823283668205 1488954129873683731375577)
              ·
                refine ⟨1116715597405262798531683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488954129873683731375577 1116715597405262798531683)
                ·
                  refine ⟨1675073396107894197797525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116715597405262798531683 1675073396107894197797525)
                  ·
                    refine ⟨78519065442557540521759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1675073396107894197797525 78519065442557540521759)
                    ·
                      rfl

theorem cell22_229373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_229373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229373 prefixEnd_229373 := by exact prefixLift 229373
  have htrace : WordTrace (prefixWord ++ tailWord_229373) baseStart_229373 baseEnd_229373 := by
    simpa [prefixWord, tailWord_229373, baseEnd_229373] using wordTrace_append hprefix tailTrace_229373
  have hstable : (prefixWord ++ tailWord_229373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229373).length < 2 ^ (prefixWord ++ tailWord_229373).sum := by decide
  have hdescent : baseEnd_229373 < baseStart_229373 := by decide
  rcases family_descends (prefixWord ++ tailWord_229373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229375 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 2, 3]
def baseStart_229375 : Nat := 118140960795 + 229375 * 2 ^ 59
def prefixEnd_229375 : Nat := 4983230072969 + 3 ^ 40 * 229375 * 2
def baseEnd_229375 : Nat := 78519750083430201971753

theorem tailTrace_229375 : CollatzResearch.WordTrace tailWord_229375 prefixEnd_229375 78519750083430201971753 := by
  unfold tailWord_229375
  simp only [CollatzResearch.WordTrace]
  refine ⟨8365993544021023976297579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5577329029347349317531719 8365993544021023976297579)
  ·
    refine ⟨12548990316031535964446369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8365993544021023976297579 12548990316031535964446369)
    ·
      refine ⟨9411742737023651973334777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12548990316031535964446369 9411742737023651973334777)
      ·
        refine ⟨7058807052767738980001083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9411742737023651973334777 7058807052767738980001083)
        ·
          refine ⟨10588210579151608470001625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7058807052767738980001083 10588210579151608470001625)
          ·
            refine ⟨7941157934363706352501219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10588210579151608470001625 7941157934363706352501219)
            ·
              refine ⟨11911736901545559528751829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7941157934363706352501219 11911736901545559528751829)
              ·
                refine ⟨279181333629974051455121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11911736901545559528751829 279181333629974051455121)
                ·
                  refine ⟨209386000222480538591341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279181333629974051455121 209386000222480538591341)
                  ·
                    refine ⟨78519750083430201971753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209386000222480538591341 78519750083430201971753)
                    ·
                      rfl

theorem cell22_229375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_229375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229375 prefixEnd_229375 := by exact prefixLift 229375
  have htrace : WordTrace (prefixWord ++ tailWord_229375) baseStart_229375 baseEnd_229375 := by
    simpa [prefixWord, tailWord_229375, baseEnd_229375] using wordTrace_append hprefix tailTrace_229375
  have hstable : (prefixWord ++ tailWord_229375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229375).length < 2 ^ (prefixWord ++ tailWord_229375).sum := by decide
  have hdescent : baseEnd_229375 < baseStart_229375 := by decide
  rcases family_descends (prefixWord ++ tailWord_229375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229388 : List Nat := [2, 2, 1, 2, 3, 1, 3, 8]
def baseStart_229388 : Nat := 118140960795 + 229388 * 2 ^ 59
def prefixEnd_229388 : Nat := 4983230072969 + 3 ^ 40 * 229388 * 2
def baseEnd_229388 : Nat := 8724911138789166821857

theorem tailTrace_229388 : CollatzResearch.WordTrace tailWord_229388 prefixEnd_229388 8724911138789166821857 := by
  unfold tailWord_229388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183233846486963598260409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5577645128649284797680545 4183233846486963598260409)
  ·
    refine ⟨3137425384865222698695307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4183233846486963598260409 3137425384865222698695307)
    ·
      refine ⟨4706138077297834048042961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3137425384865222698695307 4706138077297834048042961)
      ·
        refine ⟨3529603557973375536032221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4706138077297834048042961 3529603557973375536032221)
        ·
          refine ⟨1323601334240015826012083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3529603557973375536032221 1323601334240015826012083)
          ·
            refine ⟨1985402001360023739018125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323601334240015826012083 1985402001360023739018125)
            ·
              refine ⟨744525750510008902131797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1985402001360023739018125 744525750510008902131797)
              ·
                refine ⟨8724911138789166821857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 744525750510008902131797 8724911138789166821857)
                ·
                  rfl

theorem cell22_229388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 8].length) (baseStart_229388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229388 prefixEnd_229388 := by exact prefixLift 229388
  have htrace : WordTrace (prefixWord ++ tailWord_229388) baseStart_229388 baseEnd_229388 := by
    simpa [prefixWord, tailWord_229388, baseEnd_229388] using wordTrace_append hprefix tailTrace_229388
  have hstable : (prefixWord ++ tailWord_229388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229388).length < 2 ^ (prefixWord ++ tailWord_229388).sum := by decide
  have hdescent : baseEnd_229388 < baseStart_229388 := by decide
  rcases family_descends (prefixWord ++ tailWord_229388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229390 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_229390 : Nat := 118140960795 + 229390 * 2 ^ 59
def prefixEnd_229390 : Nat := 4983230072969 + 3 ^ 40 * 229390 * 2
def baseEnd_229390 : Nat := 78524884889975162846707

theorem tailTrace_229390 : CollatzResearch.WordTrace tailWord_229390 prefixEnd_229390 78524884889975162846707 := by
  unfold tailWord_229390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045817579870835192261703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5577693759311121025395749 1045817579870835192261703)
  ·
    refine ⟨1568726369806252788392555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1045817579870835192261703 1568726369806252788392555)
    ·
      refine ⟨2353089554709379182588833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568726369806252788392555 2353089554709379182588833)
      ·
        refine ⟨1764817166032034386941625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2353089554709379182588833 1764817166032034386941625)
        ·
          refine ⟨1323612874524025790206219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1764817166032034386941625 1323612874524025790206219)
          ·
            refine ⟨1985419311786038685309329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323612874524025790206219 1985419311786038685309329)
            ·
              refine ⟨1489064483839529013981997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985419311786038685309329 1489064483839529013981997)
              ·
                refine ⟨558399181439823380243249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1489064483839529013981997 558399181439823380243249)
                ·
                  refine ⟨418799386079867535182437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 558399181439823380243249 418799386079867535182437)
                  ·
                    refine ⟨78524884889975162846707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 418799386079867535182437 78524884889975162846707)
                    ·
                      rfl

theorem cell22_229390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_229390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229390 prefixEnd_229390 := by exact prefixLift 229390
  have htrace : WordTrace (prefixWord ++ tailWord_229390) baseStart_229390 baseEnd_229390 := by
    simpa [prefixWord, tailWord_229390, baseEnd_229390] using wordTrace_append hprefix tailTrace_229390
  have hstable : (prefixWord ++ tailWord_229390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229390).length < 2 ^ (prefixWord ++ tailWord_229390).sum := by decide
  have hdescent : baseEnd_229390 < baseStart_229390 := by decide
  rcases family_descends (prefixWord ++ tailWord_229390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229405 : List Nat := [1, 4, 2, 2, 2, 3, 8]
def baseStart_229405 : Nat := 118140960795 + 229405 * 2 ^ 59
def prefixEnd_229405 : Nat := 4983230072969 + 3 ^ 40 * 229405 * 2
def baseEnd_229405 : Nat := 2908519248019263841543

theorem tailTrace_229405 : CollatzResearch.WordTrace tailWord_229405 prefixEnd_229405 2908519248019263841543 := by
  unfold tailWord_229405
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367087733912339099889669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5578058489274892733259779 8367087733912339099889669)
  ·
    refine ⟨1568828950108563581229313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8367087733912339099889669 1568828950108563581229313)
    ·
      refine ⟨1176621712581422685921985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1568828950108563581229313 1176621712581422685921985)
      ·
        refine ⟨882466284436067014441489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1176621712581422685921985 882466284436067014441489)
        ·
          refine ⟨661849713327050260831117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882466284436067014441489 661849713327050260831117)
          ·
            refine ⟨248193642497643847811669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661849713327050260831117 248193642497643847811669)
            ·
              refine ⟨2908519248019263841543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 248193642497643847811669 2908519248019263841543)
              ·
                rfl

theorem cell22_229405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 8].length) (baseStart_229405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229405 prefixEnd_229405 := by exact prefixLift 229405
  have htrace : WordTrace (prefixWord ++ tailWord_229405) baseStart_229405 baseEnd_229405 := by
    simpa [prefixWord, tailWord_229405, baseEnd_229405] using wordTrace_append hprefix tailTrace_229405
  have hstable : (prefixWord ++ tailWord_229405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229405).length < 2 ^ (prefixWord ++ tailWord_229405).sum := by decide
  have hdescent : baseEnd_229405 < baseStart_229405 := by decide
  rcases family_descends (prefixWord ++ tailWord_229405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229420 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_229420 : Nat := 118140960795 + 229420 * 2 ^ 59
def prefixEnd_229420 : Nat := 4983230072969 + 3 ^ 40 * 229420 * 2
def baseEnd_229420 : Nat := 78535154503065084596615

theorem tailTrace_229420 : CollatzResearch.WordTrace tailWord_229420 prefixEnd_229420 78535154503065084596615 := by
  unfold tailWord_229420
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183817414428998330842857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5578423219238664441123809 4183817414428998330842857)
  ·
    refine ⟨3137863060821748748132143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4183817414428998330842857 3137863060821748748132143)
    ·
      refine ⟨4706794591232623122198215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3137863060821748748132143 4706794591232623122198215)
      ·
        refine ⟨7060191886848934683297323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4706794591232623122198215 7060191886848934683297323)
        ·
          refine ⟨10590287830273402024945985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060191886848934683297323 10590287830273402024945985)
          ·
            refine ⟨7942715872705051518709489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10590287830273402024945985 7942715872705051518709489)
            ·
              refine ⟨5957036904528788639032117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7942715872705051518709489 5957036904528788639032117)
              ·
                refine ⟨558472209799573934909261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5957036904528788639032117 558472209799573934909261)
                ·
                  refine ⟨209427078674840225590973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 558472209799573934909261 209427078674840225590973)
                  ·
                    refine ⟨78535154503065084596615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209427078674840225590973 78535154503065084596615)
                    ·
                      rfl

theorem cell22_229420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_229420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229420 prefixEnd_229420 := by exact prefixLift 229420
  have htrace : WordTrace (prefixWord ++ tailWord_229420) baseStart_229420 baseEnd_229420 := by
    simpa [prefixWord, tailWord_229420, baseEnd_229420] using wordTrace_append hprefix tailTrace_229420
  have hstable : (prefixWord ++ tailWord_229420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229420).length < 2 ^ (prefixWord ++ tailWord_229420).sum := by decide
  have hdescent : baseEnd_229420 < baseStart_229420 := by decide
  rcases family_descends (prefixWord ++ tailWord_229420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229448 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_229448 : Nat := 118140960795 + 229448 * 2 ^ 59
def prefixEnd_229448 : Nat := 4983230072969 + 3 ^ 40 * 229448 * 2
def baseEnd_229448 : Nat := 78544739475282344896529

theorem tailTrace_229448 : CollatzResearch.WordTrace tailWord_229448 prefixEnd_229448 78544739475282344896529 := by
  unfold tailWord_229448
  simp only [CollatzResearch.WordTrace]
  refine ⟨4184328036378278721852499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5579104048504371629136665 4184328036378278721852499)
  ·
    refine ⟨6276492054567418082778749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4184328036378278721852499 6276492054567418082778749)
    ·
      refine ⟨2353684520462781781042031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6276492054567418082778749 2353684520462781781042031)
      ·
        refine ⟨3530526780694172671563047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353684520462781781042031 3530526780694172671563047)
        ·
          refine ⟨5295790171041259007344571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3530526780694172671563047 5295790171041259007344571)
          ·
            refine ⟨7943685256561888511016857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295790171041259007344571 7943685256561888511016857)
            ·
              refine ⟨5957763942421416383262643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7943685256561888511016857 5957763942421416383262643)
              ·
                refine ⟨8936645913632124574893965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957763942421416383262643 8936645913632124574893965)
                ·
                  refine ⟨3351242217612046715585237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8936645913632124574893965 3351242217612046715585237)
                  ·
                    refine ⟨78544739475282344896529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3351242217612046715585237 78544739475282344896529)
                    ·
                      rfl

theorem cell22_229448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_229448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229448 prefixEnd_229448 := by exact prefixLift 229448
  have htrace : WordTrace (prefixWord ++ tailWord_229448) baseStart_229448 baseEnd_229448 := by
    simpa [prefixWord, tailWord_229448, baseEnd_229448] using wordTrace_append hprefix tailTrace_229448
  have hstable : (prefixWord ++ tailWord_229448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229448).length < 2 ^ (prefixWord ++ tailWord_229448).sum := by decide
  have hdescent : baseEnd_229448 < baseStart_229448 := by decide
  rcases family_descends (prefixWord ++ tailWord_229448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229482 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_229482 : Nat := 118140960795 + 229482 * 2 ^ 59
def prefixEnd_229482 : Nat := 4983230072969 + 3 ^ 40 * 229482 * 2
def baseEnd_229482 : Nat := 78556378370117589546425

theorem tailTrace_229482 : CollatzResearch.WordTrace tailWord_229482 prefixEnd_229482 78556378370117589546425 := by
  unfold tailWord_229482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092474038658345312610675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5579930769755587500295133 2092474038658345312610675)
  ·
    refine ⟨3138711057987517968916013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2092474038658345312610675 3138711057987517968916013)
    ·
      refine ⟨1177016646745319238343505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3138711057987517968916013 1177016646745319238343505)
      ·
        refine ⟨882762485058989428757629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177016646745319238343505 882762485058989428757629)
        ·
          refine ⟨331035931897121035784111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 882762485058989428757629 331035931897121035784111)
          ·
            refine ⟨496553897845681553676167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331035931897121035784111 496553897845681553676167)
            ·
              refine ⟨744830846768522330514251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496553897845681553676167 744830846768522330514251)
              ·
                refine ⟨1117246270152783495771377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744830846768522330514251 1117246270152783495771377)
                ·
                  refine ⟨837934702614587621828533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117246270152783495771377 837934702614587621828533)
                  ·
                    refine ⟨78556378370117589546425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 837934702614587621828533 78556378370117589546425)
                    ·
                      rfl

theorem cell22_229482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_229482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229482 prefixEnd_229482 := by exact prefixLift 229482
  have htrace : WordTrace (prefixWord ++ tailWord_229482) baseStart_229482 baseEnd_229482 := by
    simpa [prefixWord, tailWord_229482, baseEnd_229482] using wordTrace_append hprefix tailTrace_229482
  have hstable : (prefixWord ++ tailWord_229482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229482).length < 2 ^ (prefixWord ++ tailWord_229482).sum := by decide
  have hdescent : baseEnd_229482 < baseStart_229482 := by decide
  rcases family_descends (prefixWord ++ tailWord_229482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229495 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 6]
def baseStart_229495 : Nat := 118140960795 + 229495 * 2 ^ 59
def prefixEnd_229495 : Nat := 4983230072969 + 3 ^ 40 * 229495 * 2
def baseEnd_229495 : Nat := 26186942845263296323795

theorem tailTrace_229495 : CollatzResearch.WordTrace tailWord_229495 prefixEnd_229495 26186942845263296323795 := by
  unfold tailWord_229495
  simp only [CollatzResearch.WordTrace]
  refine ⟨8370370303586284470665939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5580246869057522980443959 8370370303586284470665939)
  ·
    refine ⟨12555555455379426705998909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8370370303586284470665939 12555555455379426705998909)
    ·
      refine ⟨4708333295767285014749591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12555555455379426705998909 4708333295767285014749591)
      ·
        refine ⟨7062499943650927522124387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4708333295767285014749591 7062499943650927522124387)
        ·
          refine ⟨10593749915476391283186581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7062499943650927522124387 10593749915476391283186581)
          ·
            refine ⟨496582027287955841399371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10593749915476391283186581 496582027287955841399371)
            ·
              refine ⟨744873040931933762099057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496582027287955841399371 744873040931933762099057)
              ·
                refine ⟨558654780698950321574293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744873040931933762099057 558654780698950321574293)
                ·
                  refine ⟨26186942845263296323795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 558654780698950321574293 26186942845263296323795)
                  ·
                    rfl

theorem cell22_229495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 6].length) (baseStart_229495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229495 prefixEnd_229495 := by exact prefixLift 229495
  have htrace : WordTrace (prefixWord ++ tailWord_229495) baseStart_229495 baseEnd_229495 := by
    simpa [prefixWord, tailWord_229495, baseEnd_229495] using wordTrace_append hprefix tailTrace_229495
  have hstable : (prefixWord ++ tailWord_229495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229495).length < 2 ^ (prefixWord ++ tailWord_229495).sum := by decide
  have hdescent : baseEnd_229495 < baseStart_229495 := by decide
  rcases family_descends (prefixWord ++ tailWord_229495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229514 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 1, 4]
def baseStart_229514 : Nat := 118140960795 + 229514 * 2 ^ 59
def prefixEnd_229514 : Nat := 4983230072969 + 3 ^ 40 * 229514 * 2
def baseEnd_229514 : Nat := 78567332624080172746327

theorem tailTrace_229514 : CollatzResearch.WordTrace tailWord_229514 prefixEnd_229514 78567332624080172746327 := by
  unfold tailWord_229514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092765822629362678901899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5580708860344967143738397 2092765822629362678901899)
  ·
    refine ⟨3139148733944044018352849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2092765822629362678901899 3139148733944044018352849)
    ·
      refine ⟨2354361550458033013764637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3139148733944044018352849 2354361550458033013764637)
      ·
        refine ⟨882885581421762380161739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2354361550458033013764637 882885581421762380161739)
        ·
          refine ⟨1324328372132643570242609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882885581421762380161739 1324328372132643570242609)
          ·
            refine ⟨993246279099482677681957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1324328372132643570242609 993246279099482677681957)
            ·
              refine ⟨186233677331153002065367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 993246279099482677681957 186233677331153002065367)
              ·
                refine ⟨279350515996729503098051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186233677331153002065367 279350515996729503098051)
                ·
                  refine ⟨419025773995094254647077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279350515996729503098051 419025773995094254647077)
                  ·
                    refine ⟨78567332624080172746327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419025773995094254647077 78567332624080172746327)
                    ·
                      rfl

theorem cell22_229514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_229514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229514 prefixEnd_229514 := by exact prefixLift 229514
  have htrace : WordTrace (prefixWord ++ tailWord_229514) baseStart_229514 baseEnd_229514 := by
    simpa [prefixWord, tailWord_229514, baseEnd_229514] using wordTrace_append hprefix tailTrace_229514
  have hstable : (prefixWord ++ tailWord_229514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229514).length < 2 ^ (prefixWord ++ tailWord_229514).sum := by decide
  have hdescent : baseEnd_229514 < baseStart_229514 := by decide
  rcases family_descends (prefixWord ++ tailWord_229514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229525 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_229525 : Nat := 118140960795 + 229525 * 2 ^ 59
def prefixEnd_229525 : Nat := 4983230072969 + 3 ^ 40 * 229525 * 2
def baseEnd_229525 : Nat := 78571098148879810721293

theorem tailTrace_229525 : CollatzResearch.WordTrace tailWord_229525 prefixEnd_229525 78571098148879810721293 := by
  unfold tailWord_229525
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371464493477599594258029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5580976328985066396172019 8371464493477599594258029)
  ·
    refine ⟨3139299185054099847846761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8371464493477599594258029 3139299185054099847846761)
    ·
      refine ⟨2354474388790574885885071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3139299185054099847846761 2354474388790574885885071)
      ·
        refine ⟨3531711583185862328827607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354474388790574885885071 3531711583185862328827607)
        ·
          refine ⟨5297567374778793493241411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531711583185862328827607 5297567374778793493241411)
          ·
            refine ⟨7946351062168190239862117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297567374778793493241411 7946351062168190239862117)
            ·
              refine ⟨1489940824156535669974147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7946351062168190239862117 1489940824156535669974147)
              ·
                refine ⟨2234911236234803504961221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489940824156535669974147 2234911236234803504961221)
                ·
                  refine ⟨419045856794025657180229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2234911236234803504961221 419045856794025657180229)
                  ·
                    refine ⟨78571098148879810721293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419045856794025657180229 78571098148879810721293)
                    ·
                      rfl

theorem cell22_229525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_229525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229525 prefixEnd_229525 := by exact prefixLift 229525
  have htrace : WordTrace (prefixWord ++ tailWord_229525) baseStart_229525 baseEnd_229525 := by
    simpa [prefixWord, tailWord_229525, baseEnd_229525] using wordTrace_append hprefix tailTrace_229525
  have hstable : (prefixWord ++ tailWord_229525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229525).length < 2 ^ (prefixWord ++ tailWord_229525).sum := by decide
  have hdescent : baseEnd_229525 < baseStart_229525 := by decide
  rcases family_descends (prefixWord ++ tailWord_229525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229585 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 7]
def baseStart_229585 : Nat := 118140960795 + 229585 * 2 ^ 59
def prefixEnd_229585 : Nat := 4983230072969 + 3 ^ 40 * 229585 * 2
def baseEnd_229585 : Nat := 26197212458353218073703

theorem tailTrace_229585 : CollatzResearch.WordTrace tailWord_229585 prefixEnd_229585 26197212458353218073703 := by
  unfold tailWord_229585
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373652873260229841442209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5582435248840153227628139 8373652873260229841442209)
  ·
    refine ⟨6280239654945172381081657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8373652873260229841442209 6280239654945172381081657)
    ·
      refine ⟨4710179741208879285811243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6280239654945172381081657 4710179741208879285811243)
      ·
        refine ⟨7065269611813318928716865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710179741208879285811243 7065269611813318928716865)
        ·
          refine ⟨5298952208859989196537649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7065269611813318928716865 5298952208859989196537649)
          ·
            refine ⟨3974214156644991897403237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5298952208859989196537649 3974214156644991897403237)
            ·
              refine ⟨745165154370935980763107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3974214156644991897403237 745165154370935980763107)
              ·
                refine ⟨1117747731556403971144661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745165154370935980763107 1117747731556403971144661)
                ·
                  refine ⟨26197212458353218073703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1117747731556403971144661 26197212458353218073703)
                  ·
                    rfl

theorem cell22_229585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_229585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229585 prefixEnd_229585 := by exact prefixLift 229585
  have htrace : WordTrace (prefixWord ++ tailWord_229585) baseStart_229585 baseEnd_229585 := by
    simpa [prefixWord, tailWord_229585, baseEnd_229585] using wordTrace_append hprefix tailTrace_229585
  have hstable : (prefixWord ++ tailWord_229585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229585).length < 2 ^ (prefixWord ++ tailWord_229585).sum := by decide
  have hdescent : baseEnd_229585 < baseStart_229585 := by decide
  rcases family_descends (prefixWord ++ tailWord_229585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229600 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_229600 : Nat := 118140960795 + 229600 * 2 ^ 59
def prefixEnd_229600 : Nat := 4983230072969 + 3 ^ 40 * 229600 * 2
def baseEnd_229600 : Nat := 78596772181604615096063

theorem tailTrace_229600 : CollatzResearch.WordTrace tailWord_229600 prefixEnd_229600 78596772181604615096063 := by
  unfold tailWord_229600
  simp only [CollatzResearch.WordTrace]
  refine ⟨4187099984102943701619127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5582799978803924935492169 4187099984102943701619127)
  ·
    refine ⟨6280649976154415552428691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4187099984102943701619127 6280649976154415552428691)
    ·
      refine ⟨9420974964231623328643037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6280649976154415552428691 9420974964231623328643037)
      ·
        refine ⟨3532865611586858748241139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9420974964231623328643037 3532865611586858748241139)
        ·
          refine ⟨5299298417380288122361709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3532865611586858748241139 5299298417380288122361709)
          ·
            refine ⟨1987236906517608045885641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5299298417380288122361709 1987236906517608045885641)
            ·
              refine ⟨1490427679888206034414231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1987236906517608045885641 1490427679888206034414231)
              ·
                refine ⟨2235641519832309051621347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490427679888206034414231 2235641519832309051621347)
                ·
                  refine ⟨3353462279748463577432021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235641519832309051621347 3353462279748463577432021)
                  ·
                    refine ⟨78596772181604615096063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3353462279748463577432021 78596772181604615096063)
                    ·
                      rfl

theorem cell22_229600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_229600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229600 prefixEnd_229600 := by exact prefixLift 229600
  have htrace : WordTrace (prefixWord ++ tailWord_229600) baseStart_229600 baseEnd_229600 := by
    simpa [prefixWord, tailWord_229600, baseEnd_229600] using wordTrace_append hprefix tailTrace_229600
  have hstable : (prefixWord ++ tailWord_229600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229600).length < 2 ^ (prefixWord ++ tailWord_229600).sum := by decide
  have hdescent : baseEnd_229600 < baseStart_229600 := by decide
  rcases family_descends (prefixWord ++ tailWord_229600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229632 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_229632 : Nat := 118140960795 + 229632 * 2 ^ 59
def prefixEnd_229632 : Nat := 4983230072969 + 3 ^ 40 * 229632 * 2
def baseEnd_229632 : Nat := 78607726435567198295965

theorem tailTrace_229632 : CollatzResearch.WordTrace tailWord_229632 prefixEnd_229632 78607726435567198295965 := by
  unfold tailWord_229632
  simp only [CollatzResearch.WordTrace]
  refine ⟨4187683552044978434201575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5583578069393304578935433 4187683552044978434201575)
  ·
    refine ⟨6281525328067467651302363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4187683552044978434201575 6281525328067467651302363)
    ·
      refine ⟨9422287992101201476953545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6281525328067467651302363 9422287992101201476953545)
      ·
        refine ⟨7066715994075901107715159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9422287992101201476953545 7066715994075901107715159)
        ·
          refine ⟨10600073991113851661572739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7066715994075901107715159 10600073991113851661572739)
          ·
            refine ⟨15900110986670777492359109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10600073991113851661572739 15900110986670777492359109)
            ·
              refine ⟨2981270810000770779817333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15900110986670777492359109 2981270810000770779817333)
              ·
                refine ⟨279494138437572260607875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2981270810000770779817333 279494138437572260607875)
                ·
                  refine ⟨419241207656358390911813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279494138437572260607875 419241207656358390911813)
                  ·
                    refine ⟨78607726435567198295965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419241207656358390911813 78607726435567198295965)
                    ·
                      rfl

theorem cell22_229632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_229632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229632 prefixEnd_229632 := by exact prefixLift 229632
  have htrace : WordTrace (prefixWord ++ tailWord_229632) baseStart_229632 baseEnd_229632 := by
    simpa [prefixWord, tailWord_229632, baseEnd_229632] using wordTrace_append hprefix tailTrace_229632
  have hstable : (prefixWord ++ tailWord_229632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229632).length < 2 ^ (prefixWord ++ tailWord_229632).sum := by decide
  have hdescent : baseEnd_229632 < baseStart_229632 := by decide
  rcases family_descends (prefixWord ++ tailWord_229632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229681 : List Nat := [1, 2, 2, 3, 4, 1, 2, 3, 4]
def baseStart_229681 : Nat := 118140960795 + 229681 * 2 ^ 59
def prefixEnd_229681 : Nat := 4983230072969 + 3 ^ 40 * 229681 * 2
def baseEnd_229681 : Nat := 26208166712315801273605

theorem tailTrace_229681 : CollatzResearch.WordTrace tailWord_229681 prefixEnd_229681 26208166712315801273605 := by
  unfold tailWord_229681
  simp only [CollatzResearch.WordTrace]
  refine ⟨8377154280912438236936897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5584769520608292157957931 8377154280912438236936897)
  ·
    refine ⟨6282865710684328677702673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8377154280912438236936897 6282865710684328677702673)
    ·
      refine ⟨4712149283013246508277005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6282865710684328677702673 4712149283013246508277005)
      ·
        refine ⟨1767055981129967440603877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4712149283013246508277005 1767055981129967440603877)
        ·
          refine ⟨331322996461868895113227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1767055981129967440603877 331322996461868895113227)
          ·
            refine ⟨496984494692803342669841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331322996461868895113227 496984494692803342669841)
            ·
              refine ⟨372738371019602507002381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496984494692803342669841 372738371019602507002381)
              ·
                refine ⟨139776889132350940125893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372738371019602507002381 139776889132350940125893)
                ·
                  refine ⟨26208166712315801273605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139776889132350940125893 26208166712315801273605)
                  ·
                    rfl

theorem cell22_229681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 4].length) (baseStart_229681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229681 prefixEnd_229681 := by exact prefixLift 229681
  have htrace : WordTrace (prefixWord ++ tailWord_229681) baseStart_229681 baseEnd_229681 := by
    simpa [prefixWord, tailWord_229681, baseEnd_229681] using wordTrace_append hprefix tailTrace_229681
  have hstable : (prefixWord ++ tailWord_229681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229681).length < 2 ^ (prefixWord ++ tailWord_229681).sum := by decide
  have hdescent : baseEnd_229681 < baseStart_229681 := by decide
  rcases family_descends (prefixWord ++ tailWord_229681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229771 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 5]
def baseStart_229771 : Nat := 118140960795 + 229771 * 2 ^ 59
def prefixEnd_229771 : Nat := 4983230072969 + 3 ^ 40 * 229771 * 2
def baseEnd_229771 : Nat := 26218436325405723023513

theorem tailTrace_229771 : CollatzResearch.WordTrace tailWord_229771 prefixEnd_229771 26218436325405723023513 := by
  unfold tailWord_229771
  simp only [CollatzResearch.WordTrace]
  refine ⟨8380436850586383607713167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5586957900390922405142111 8380436850586383607713167)
  ·
    refine ⟨12570655275879575411569751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8380436850586383607713167 12570655275879575411569751)
    ·
      refine ⟨18855982913819363117354627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12570655275879575411569751 18855982913819363117354627)
      ·
        refine ⟨28283974370729044676031941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18855982913819363117354627 28283974370729044676031941)
        ·
          refine ⟨5303245194511695876755989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28283974370729044676031941 5303245194511695876755989)
          ·
            refine ⟨248589618492735744222937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5303245194511695876755989 248589618492735744222937)
            ·
              refine ⟨186442213869551808167203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248589618492735744222937 186442213869551808167203)
              ·
                refine ⟨279663320804327712250805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186442213869551808167203 279663320804327712250805)
                ·
                  refine ⟨26218436325405723023513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 279663320804327712250805 26218436325405723023513)
                  ·
                    rfl

theorem cell22_229771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 5].length) (baseStart_229771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229771 prefixEnd_229771 := by exact prefixLift 229771
  have htrace : WordTrace (prefixWord ++ tailWord_229771) baseStart_229771 baseEnd_229771 := by
    simpa [prefixWord, tailWord_229771, baseEnd_229771] using wordTrace_append hprefix tailTrace_229771
  have hstable : (prefixWord ++ tailWord_229771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229771).length < 2 ^ (prefixWord ++ tailWord_229771).sum := by decide
  have hdescent : baseEnd_229771 < baseStart_229771 := by decide
  rcases family_descends (prefixWord ++ tailWord_229771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229831 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 2, 3]
def baseStart_229831 : Nat := 118140960795 + 229831 * 2 ^ 59
def prefixEnd_229831 : Nat := 4983230072969 + 3 ^ 40 * 229831 * 2
def baseEnd_229831 : Nat := 78675848202397012570355

theorem tailTrace_229831 : CollatzResearch.WordTrace tailWord_229831 prefixEnd_229831 78675848202397012570355 := by
  unfold tailWord_229831
  simp only [CollatzResearch.WordTrace]
  refine ⟨8382625230369013854897347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5588416820246009236598231 8382625230369013854897347)
  ·
    refine ⟨12573937845553520782346021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8382625230369013854897347 12573937845553520782346021)
    ·
      refine ⟨2357613346041285146689879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12573937845553520782346021 2357613346041285146689879)
      ·
        refine ⟨3536420019061927720034819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357613346041285146689879 3536420019061927720034819)
        ·
          refine ⟨5304630028592891580052229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536420019061927720034819 5304630028592891580052229)
          ·
            refine ⟨994618130361167171259793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5304630028592891580052229 994618130361167171259793)
            ·
              refine ⟨745963597770875378444845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994618130361167171259793 745963597770875378444845)
              ·
                refine ⟨279736349164078266916817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 745963597770875378444845 279736349164078266916817)
                ·
                  refine ⟨209802261873058700187613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279736349164078266916817 209802261873058700187613)
                  ·
                    refine ⟨78675848202397012570355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209802261873058700187613 78675848202397012570355)
                    ·
                      rfl

theorem cell22_229831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_229831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229831 prefixEnd_229831 := by exact prefixLift 229831
  have htrace : WordTrace (prefixWord ++ tailWord_229831) baseStart_229831 baseEnd_229831 := by
    simpa [prefixWord, tailWord_229831, baseEnd_229831] using wordTrace_append hprefix tailTrace_229831
  have hstable : (prefixWord ++ tailWord_229831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229831).length < 2 ^ (prefixWord ++ tailWord_229831).sum := by decide
  have hdescent : baseEnd_229831 < baseStart_229831 := by decide
  rcases family_descends (prefixWord ++ tailWord_229831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229846 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_229846 : Nat := 118140960795 + 229846 * 2 ^ 59
def prefixEnd_229846 : Nat := 4983230072969 + 3 ^ 40 * 229846 * 2
def baseEnd_229846 : Nat := 78680983008941973445309

theorem tailTrace_229846 : CollatzResearch.WordTrace tailWord_229846 prefixEnd_229846 78680983008941973445309 := by
  unfold tailWord_229846
  simp only [CollatzResearch.WordTrace]
  refine ⟨523948270332166963543337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5588781550209780944462261 523948270332166963543337)
  ·
    refine ⟨392961202749125222657503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 523948270332166963543337 392961202749125222657503)
    ·
      refine ⟨589441804123687833986255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392961202749125222657503 589441804123687833986255)
      ·
        refine ⟨884162706185531750979383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589441804123687833986255 884162706185531750979383)
        ·
          refine ⟨1326244059278297626469075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884162706185531750979383 1326244059278297626469075)
          ·
            refine ⟨1989366088917446439703613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326244059278297626469075 1989366088917446439703613)
            ·
              refine ⟨746012283344042414888855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1989366088917446439703613 746012283344042414888855)
              ·
                refine ⟨1119018425016063622333283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746012283344042414888855 1119018425016063622333283)
                ·
                  refine ⟨1678527637524095433499925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119018425016063622333283 1678527637524095433499925)
                  ·
                    refine ⟨78680983008941973445309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1678527637524095433499925 78680983008941973445309)
                    ·
                      rfl

theorem cell22_229846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_229846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229846 prefixEnd_229846 := by exact prefixLift 229846
  have htrace : WordTrace (prefixWord ++ tailWord_229846) baseStart_229846 baseEnd_229846 := by
    simpa [prefixWord, tailWord_229846, baseEnd_229846] using wordTrace_append hprefix tailTrace_229846
  have hstable : (prefixWord ++ tailWord_229846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229846).length < 2 ^ (prefixWord ++ tailWord_229846).sum := by decide
  have hdescent : baseEnd_229846 < baseStart_229846 := by decide
  rcases family_descends (prefixWord ++ tailWord_229846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229919 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 5, 4]
def baseStart_229919 : Nat := 118140960795 + 229919 * 2 ^ 59
def prefixEnd_229919 : Nat := 4983230072969 + 3 ^ 40 * 229919 * 2
def baseEnd_229919 : Nat := 78705972400794116370085

theorem tailTrace_229919 : CollatzResearch.WordTrace tailWord_229919 prefixEnd_229919 78705972400794116370085 := by
  unfold tailWord_229919
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385834854050204884100811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5590556569366803256067207 8385834854050204884100811)
  ·
    refine ⟨12578752281075307326151217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8385834854050204884100811 12578752281075307326151217)
    ·
      refine ⟨9434064210806480494613413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12578752281075307326151217 9434064210806480494613413)
      ·
        refine ⟨1768887039526215092740015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9434064210806480494613413 1768887039526215092740015)
        ·
          refine ⟨2653330559289322639110023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768887039526215092740015 2653330559289322639110023)
          ·
            refine ⟨3979995838933983958665035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653330559289322639110023 3979995838933983958665035)
            ·
              refine ⟨5969993758400975937997553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979995838933983958665035 5969993758400975937997553)
              ·
                refine ⟨4477495318800731953498165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969993758400975937997553 4477495318800731953498165)
                ·
                  refine ⟨419765186137568620640453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4477495318800731953498165 419765186137568620640453)
                  ·
                    refine ⟨78705972400794116370085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419765186137568620640453 78705972400794116370085)
                    ·
                      rfl

theorem cell22_229919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_229919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229919 prefixEnd_229919 := by exact prefixLift 229919
  have htrace : WordTrace (prefixWord ++ tailWord_229919) baseStart_229919 baseEnd_229919 := by
    simpa [prefixWord, tailWord_229919, baseEnd_229919] using wordTrace_append hprefix tailTrace_229919
  have hstable : (prefixWord ++ tailWord_229919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229919).length < 2 ^ (prefixWord ++ tailWord_229919).sum := by decide
  have hdescent : baseEnd_229919 < baseStart_229919 := by decide
  rcases family_descends (prefixWord ++ tailWord_229919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229927 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 3, 3]
def baseStart_229927 : Nat := 118140960795 + 229927 * 2 ^ 59
def prefixEnd_229927 : Nat := 4983230072969 + 3 ^ 40 * 229927 * 2
def baseEnd_229927 : Nat := 78708710964284762170061

theorem tailTrace_229927 : CollatzResearch.WordTrace tailWord_229927 prefixEnd_229927 78708710964284762170061 := by
  unfold tailWord_229927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386126638021222250392035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5590751092014148166928023 8386126638021222250392035)
  ·
    refine ⟨12579189957031833375588053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8386126638021222250392035 12579189957031833375588053)
    ·
      refine ⟨294824764617933594740345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12579189957031833375588053 294824764617933594740345)
      ·
        refine ⟨221118573463450196055259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294824764617933594740345 221118573463450196055259)
        ·
          refine ⟨331677860195175294082889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221118573463450196055259 331677860195175294082889)
          ·
            refine ⟨248758395146381470562167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331677860195175294082889 248758395146381470562167)
            ·
              refine ⟨373137592719572205843251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248758395146381470562167 373137592719572205843251)
              ·
                refine ⟨559706389079358308764877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373137592719572205843251 559706389079358308764877)
                ·
                  refine ⟨209889895904759365786829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559706389079358308764877 209889895904759365786829)
                  ·
                    refine ⟨78708710964284762170061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209889895904759365786829 78708710964284762170061)
                    ·
                      rfl

theorem cell22_229927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_229927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229927 prefixEnd_229927 := by exact prefixLift 229927
  have htrace : WordTrace (prefixWord ++ tailWord_229927) baseStart_229927 baseEnd_229927 := by
    simpa [prefixWord, tailWord_229927, baseEnd_229927] using wordTrace_append hprefix tailTrace_229927
  have hstable : (prefixWord ++ tailWord_229927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229927).length < 2 ^ (prefixWord ++ tailWord_229927).sum := by decide
  have hdescent : baseEnd_229927 < baseStart_229927 := by decide
  rcases family_descends (prefixWord ++ tailWord_229927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229940 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 5]
def baseStart_229940 : Nat := 118140960795 + 229940 * 2 ^ 59
def prefixEnd_229940 : Nat := 4983230072969 + 3 ^ 40 * 229940 * 2
def baseEnd_229940 : Nat := 26237720376652353865007

theorem tailTrace_229940 : CollatzResearch.WordTrace tailWord_229940 prefixEnd_229940 26237720376652353865007 := by
  unfold tailWord_229940
  simp only [CollatzResearch.WordTrace]
  refine ⟨4193300393487062735307637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5591067191316083647076849 4193300393487062735307637)
  ·
    refine ⟨393121911889412131435091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4193300393487062735307637 393121911889412131435091)
    ·
      refine ⟨589682867834118197152637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393121911889412131435091 589682867834118197152637)
      ·
        refine ⟨221131075437794323932239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589682867834118197152637 221131075437794323932239)
        ·
          refine ⟨331696613156691485898359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221131075437794323932239 331696613156691485898359)
          ·
            refine ⟨497544919735037228847539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331696613156691485898359 497544919735037228847539)
            ·
              refine ⟨746317379602555843271309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497544919735037228847539 746317379602555843271309)
              ·
                refine ⟨279869017350958441226741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746317379602555843271309 279869017350958441226741)
                ·
                  refine ⟨26237720376652353865007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 279869017350958441226741 26237720376652353865007)
                  ·
                    rfl

theorem cell22_229940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_229940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229940 prefixEnd_229940 := by exact prefixLift 229940
  have htrace : WordTrace (prefixWord ++ tailWord_229940) baseStart_229940 baseEnd_229940 := by
    simpa [prefixWord, tailWord_229940, baseEnd_229940] using wordTrace_append hprefix tailTrace_229940
  have hstable : (prefixWord ++ tailWord_229940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229940).length < 2 ^ (prefixWord ++ tailWord_229940).sum := by decide
  have hdescent : baseEnd_229940 < baseStart_229940 := by decide
  rcases family_descends (prefixWord ++ tailWord_229940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229953 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_229953 : Nat := 118140960795 + 229953 * 2 ^ 59
def prefixEnd_229953 : Nat := 4983230072969 + 3 ^ 40 * 229953 * 2
def baseEnd_229953 : Nat := 78717611295629361019981

theorem tailTrace_229953 : CollatzResearch.WordTrace tailWord_229953 prefixEnd_229953 78717611295629361019981 := by
  unfold tailWord_229953
  simp only [CollatzResearch.WordTrace]
  refine ⟨8387074935927028690838513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5591383290618019127225675 8387074935927028690838513)
  ·
    refine ⟨6290306201945271518128885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8387074935927028690838513 6290306201945271518128885)
    ·
      refine ⟨589716206432369204824583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6290306201945271518128885 589716206432369204824583)
      ·
        refine ⟨884574309648553807236875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589716206432369204824583 884574309648553807236875)
        ·
          refine ⟨1326861464472830710855313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884574309648553807236875 1326861464472830710855313)
          ·
            refine ⟨995146098354623033141485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326861464472830710855313 995146098354623033141485)
            ·
              refine ⟨373179786882983637428057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 995146098354623033141485 373179786882983637428057)
              ·
                refine ⟨279884840162237728071043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373179786882983637428057 279884840162237728071043)
                ·
                  refine ⟨419827260243356592106565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279884840162237728071043 419827260243356592106565)
                  ·
                    refine ⟨78717611295629361019981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419827260243356592106565 78717611295629361019981)
                    ·
                      rfl

theorem cell22_229953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_229953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229953 prefixEnd_229953 := by exact prefixLift 229953
  have htrace : WordTrace (prefixWord ++ tailWord_229953) baseStart_229953 baseEnd_229953 := by
    simpa [prefixWord, tailWord_229953, baseEnd_229953] using wordTrace_append hprefix tailTrace_229953
  have hstable : (prefixWord ++ tailWord_229953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229953).length < 2 ^ (prefixWord ++ tailWord_229953).sum := by decide
  have hdescent : baseEnd_229953 < baseStart_229953 := by decide
  rcases family_descends (prefixWord ++ tailWord_229953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229966 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_229966 : Nat := 118140960795 + 229966 * 2 ^ 59
def prefixEnd_229966 : Nat := 4983230072969 + 3 ^ 40 * 229966 * 2
def baseEnd_229966 : Nat := 78722061461301660444941

theorem tailTrace_229966 : CollatzResearch.WordTrace tailWord_229966 prefixEnd_229966 78722061461301660444941 := by
  unfold tailWord_229966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1048443635609991488882719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5591699389919954607374501 1048443635609991488882719)
  ·
    refine ⟨1572665453414987233324079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1048443635609991488882719 1572665453414987233324079)
    ·
      refine ⟨2358998180122480849986119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1572665453414987233324079 2358998180122480849986119)
      ·
        refine ⟨3538497270183721274979179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358998180122480849986119 3538497270183721274979179)
        ·
          refine ⟨5307745905275581912468769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538497270183721274979179 5307745905275581912468769)
          ·
            refine ⟨3980809428956686434351577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5307745905275581912468769 3980809428956686434351577)
            ·
              refine ⟨2985607071717514825763683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3980809428956686434351577 2985607071717514825763683)
              ·
                refine ⟨4478410607576272238645525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985607071717514825763683 4478410607576272238645525)
                ·
                  refine ⟨209925497230137761186509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4478410607576272238645525 209925497230137761186509)
                  ·
                    refine ⟨78722061461301660444941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209925497230137761186509 78722061461301660444941)
                    ·
                      rfl

theorem cell22_229966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_229966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229966 prefixEnd_229966 := by exact prefixLift 229966
  have htrace : WordTrace (prefixWord ++ tailWord_229966) baseStart_229966 baseEnd_229966 := by
    simpa [prefixWord, tailWord_229966, baseEnd_229966] using wordTrace_append hprefix tailTrace_229966
  have hstable : (prefixWord ++ tailWord_229966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229966).length < 2 ^ (prefixWord ++ tailWord_229966).sum := by decide
  have hdescent : baseEnd_229966 < baseStart_229966 := by decide
  rcases family_descends (prefixWord ++ tailWord_229966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229985 : List Nat := [1, 2, 3, 1, 1, 6, 2, 2, 4]
def baseStart_229985 : Nat := 118140960795 + 229985 * 2 ^ 59
def prefixEnd_229985 : Nat := 4983230072969 + 3 ^ 40 * 229985 * 2
def baseEnd_229985 : Nat := 26242855183197314739961

theorem tailTrace_229985 : CollatzResearch.WordTrace tailWord_229985 prefixEnd_229985 26242855183197314739961 := by
  unfold tailWord_229985
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388242071811098156003409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5592161381207398770668939 8388242071811098156003409)
  ·
    refine ⟨6291181553858323617002557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8388242071811098156003409 6291181553858323617002557)
    ·
      refine ⟨2359193082696871356375959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6291181553858323617002557 2359193082696871356375959)
      ·
        refine ⟨3538789624045307034563939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2359193082696871356375959 3538789624045307034563939)
        ·
          refine ⟨5308184436067960551845909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538789624045307034563939 5308184436067960551845909)
          ·
            refine ⟨248821145440685650867777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5308184436067960551845909 248821145440685650867777)
            ·
              refine ⟨186615859080514238150833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248821145440685650867777 186615859080514238150833)
              ·
                refine ⟨139961894310385678613125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186615859080514238150833 139961894310385678613125)
                ·
                  refine ⟨26242855183197314739961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139961894310385678613125 26242855183197314739961)
                  ·
                    rfl

theorem cell22_229985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 4].length) (baseStart_229985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_229985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_229985 prefixEnd_229985 := by exact prefixLift 229985
  have htrace : WordTrace (prefixWord ++ tailWord_229985) baseStart_229985 baseEnd_229985 := by
    simpa [prefixWord, tailWord_229985, baseEnd_229985] using wordTrace_append hprefix tailTrace_229985
  have hstable : (prefixWord ++ tailWord_229985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229985).length < 2 ^ (prefixWord ++ tailWord_229985).sum := by decide
  have hdescent : baseEnd_229985 < baseStart_229985 := by decide
  rcases family_descends (prefixWord ++ tailWord_229985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230013 : List Nat := [1, 4, 1, 1, 5, 1, 3, 6]
def baseStart_230013 : Nat := 118140960795 + 230013 * 2 ^ 59
def prefixEnd_230013 : Nat := 4983230072969 + 3 ^ 40 * 230013 * 2
def baseEnd_230013 : Nat := 8748683391312133835533

theorem tailTrace_230013 : CollatzResearch.WordTrace tailWord_230013 prefixEnd_230013 8748683391312133835533 := by
  unfold tailWord_230013
  simp only [CollatzResearch.WordTrace]
  refine ⟨8389263315709658938022693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5592842210473105958681795 8389263315709658938022693)
  ·
    refine ⟨1572986871695561050879255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8389263315709658938022693 1572986871695561050879255)
    ·
      refine ⟨2359480307543341576318883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1572986871695561050879255 2359480307543341576318883)
      ·
        refine ⟨3539220461315012364478325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2359480307543341576318883 3539220461315012364478325)
        ·
          refine ⟨331801918248282409169843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3539220461315012364478325 331801918248282409169843)
          ·
            refine ⟨497702877372423613754765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331801918248282409169843 497702877372423613754765)
            ·
              refine ⟨186638579014658855158037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497702877372423613754765 186638579014658855158037)
              ·
                refine ⟨8748683391312133835533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186638579014658855158037 8748683391312133835533)
                ·
                  rfl

theorem cell22_230013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 6].length) (baseStart_230013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230013 prefixEnd_230013 := by exact prefixLift 230013
  have htrace : WordTrace (prefixWord ++ tailWord_230013) baseStart_230013 baseEnd_230013 := by
    simpa [prefixWord, tailWord_230013, baseEnd_230013] using wordTrace_append hprefix tailTrace_230013
  have hstable : (prefixWord ++ tailWord_230013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230013).length < 2 ^ (prefixWord ++ tailWord_230013).sum := by decide
  have hdescent : baseEnd_230013 < baseStart_230013 := by decide
  rcases family_descends (prefixWord ++ tailWord_230013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230045 : List Nat := [1, 4, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_230045 : Nat := 118140960795 + 230045 * 2 ^ 59
def prefixEnd_230045 : Nat := 4983230072969 + 3 ^ 40 * 230045 * 2
def baseEnd_230045 : Nat := 78749104775771787719699

theorem tailTrace_230045 : CollatzResearch.WordTrace tailWord_230045 prefixEnd_230045 78749104775771787719699 := by
  unfold tailWord_230045
  simp only [CollatzResearch.WordTrace]
  refine ⟨8390430451593728403187589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5593620301062485602125059 8390430451593728403187589)
  ·
    refine ⟨1573205709673824075597673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8390430451593728403187589 1573205709673824075597673)
    ·
      refine ⟨1179904282255368056698255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1573205709673824075597673 1179904282255368056698255)
      ·
        refine ⟨1769856423383052085047383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179904282255368056698255 1769856423383052085047383)
        ·
          refine ⟨2654784635074578127571075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769856423383052085047383 2654784635074578127571075)
          ·
            refine ⟨3982176952611867191356613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654784635074578127571075 3982176952611867191356613)
            ·
              refine ⟨746658178614725098379365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3982176952611867191356613 746658178614725098379365)
              ·
                refine ⟨139998408490260955946131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746658178614725098379365 139998408490260955946131)
                ·
                  refine ⟨209997612735391433919197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139998408490260955946131 209997612735391433919197)
                  ·
                    refine ⟨78749104775771787719699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209997612735391433919197 78749104775771787719699)
                    ·
                      rfl

theorem cell22_230045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_230045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230045 prefixEnd_230045 := by exact prefixLift 230045
  have htrace : WordTrace (prefixWord ++ tailWord_230045) baseStart_230045 baseEnd_230045 := by
    simpa [prefixWord, tailWord_230045, baseEnd_230045] using wordTrace_append hprefix tailTrace_230045
  have hstable : (prefixWord ++ tailWord_230045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230045).length < 2 ^ (prefixWord ++ tailWord_230045).sum := by decide
  have hdescent : baseEnd_230045 < baseStart_230045 := by decide
  rcases family_descends (prefixWord ++ tailWord_230045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230088 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_230088 : Nat := 118140960795 + 230088 * 2 ^ 59
def prefixEnd_230088 : Nat := 4983230072969 + 3 ^ 40 * 230088 * 2
def baseEnd_230088 : Nat := 78763824554534008894567

theorem tailTrace_230088 : CollatzResearch.WordTrace tailWord_230088 prefixEnd_230088 78763824554534008894567 := by
  unfold tailWord_230088
  simp only [CollatzResearch.WordTrace]
  refine ⟨4195999395218973373501459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5594665860291964498001945 4195999395218973373501459)
  ·
    refine ⟨6293999092828460060252189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4195999395218973373501459 6293999092828460060252189)
    ·
      refine ⟨2360249659810672522594571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6293999092828460060252189 2360249659810672522594571)
      ·
        refine ⟨3540374489716008783891857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360249659810672522594571 3540374489716008783891857)
        ·
          refine ⟨2655280867287006587918893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3540374489716008783891857 2655280867287006587918893)
          ·
            refine ⟨995730325232627470469585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2655280867287006587918893 995730325232627470469585)
            ·
              refine ⟨746797743924470602852189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995730325232627470469585 746797743924470602852189)
              ·
                refine ⟨280049153971676476069571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746797743924470602852189 280049153971676476069571)
                ·
                  refine ⟨420073730957514714104357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280049153971676476069571 420073730957514714104357)
                  ·
                    refine ⟨78763824554534008894567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 420073730957514714104357 78763824554534008894567)
                    ·
                      rfl

theorem cell22_230088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_230088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230088 prefixEnd_230088 := by exact prefixLift 230088
  have htrace : WordTrace (prefixWord ++ tailWord_230088) baseStart_230088 baseEnd_230088 := by
    simpa [prefixWord, tailWord_230088, baseEnd_230088] using wordTrace_append hprefix tailTrace_230088
  have hstable : (prefixWord ++ tailWord_230088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230088).length < 2 ^ (prefixWord ++ tailWord_230088).sum := by decide
  have hdescent : baseEnd_230088 < baseStart_230088 := by decide
  rcases family_descends (prefixWord ++ tailWord_230088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230103 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 6]
def baseStart_230103 : Nat := 118140960795 + 230103 * 2 ^ 59
def prefixEnd_230103 : Nat := 4983230072969 + 3 ^ 40 * 230103 * 2
def baseEnd_230103 : Nat := 26256319787026323256507

theorem tailTrace_230103 : CollatzResearch.WordTrace tailWord_230103 prefixEnd_230103 26256319787026323256507 := by
  unfold tailWord_230103
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392545885383604308798963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5595030590255736205865975 8392545885383604308798963)
  ·
    refine ⟨12588818828075406463198445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8392545885383604308798963 12588818828075406463198445)
    ·
      refine ⟨4720807060528277423699417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12588818828075406463198445 4720807060528277423699417)
      ·
        refine ⟨3540605295396208067774563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4720807060528277423699417 3540605295396208067774563)
        ·
          refine ⟨5310907943094312101661845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540605295396208067774563 5310907943094312101661845)
          ·
            refine ⟨248948809832545879765399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5310907943094312101661845 248948809832545879765399)
            ·
              refine ⟨373423214748818819648099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248948809832545879765399 373423214748818819648099)
              ·
                refine ⟨560134822123228229472149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373423214748818819648099 560134822123228229472149)
                ·
                  refine ⟨26256319787026323256507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 560134822123228229472149 26256319787026323256507)
                  ·
                    rfl

theorem cell22_230103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 6].length) (baseStart_230103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230103 prefixEnd_230103 := by exact prefixLift 230103
  have htrace : WordTrace (prefixWord ++ tailWord_230103) baseStart_230103 baseEnd_230103 := by
    simpa [prefixWord, tailWord_230103, baseEnd_230103] using wordTrace_append hprefix tailTrace_230103
  have hstable : (prefixWord ++ tailWord_230103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230103).length < 2 ^ (prefixWord ++ tailWord_230103).sum := by decide
  have hdescent : baseEnd_230103 < baseStart_230103 := by decide
  rcases family_descends (prefixWord ++ tailWord_230103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230161 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_230161 : Nat := 118140960795 + 230161 * 2 ^ 59
def prefixEnd_230161 : Nat := 4983230072969 + 3 ^ 40 * 230161 * 2
def baseEnd_230161 : Nat := 78788813946386151819343

theorem tailTrace_230161 : CollatzResearch.WordTrace tailWord_230161 prefixEnd_230161 78788813946386151819343 := by
  unfold tailWord_230161
  simp only [CollatzResearch.WordTrace]
  refine ⟨8394661319173480214410337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5596440879448986809606891 8394661319173480214410337)
  ·
    refine ⟨6295995989380110160807753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8394661319173480214410337 6295995989380110160807753)
    ·
      refine ⟨4721996992035082620605815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6295995989380110160807753 4721996992035082620605815)
      ·
        refine ⟨7082995488052623930908723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4721996992035082620605815 7082995488052623930908723)
        ·
          refine ⟨10624493232078935896363085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7082995488052623930908723 10624493232078935896363085)
          ·
            refine ⟨3984184962029600961136157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10624493232078935896363085 3984184962029600961136157)
            ·
              refine ⟨1494069360761100360426059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3984184962029600961136157 1494069360761100360426059)
              ·
                refine ⟨2241104041141650540639089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494069360761100360426059 2241104041141650540639089)
                ·
                  refine ⟨1680828030856237905479317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2241104041141650540639089 1680828030856237905479317)
                  ·
                    refine ⟨78788813946386151819343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1680828030856237905479317 78788813946386151819343)
                    ·
                      rfl

theorem cell22_230161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_230161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230161 prefixEnd_230161 := by exact prefixLift 230161
  have htrace : WordTrace (prefixWord ++ tailWord_230161) baseStart_230161 baseEnd_230161 := by
    simpa [prefixWord, tailWord_230161, baseEnd_230161] using wordTrace_append hprefix tailTrace_230161
  have hstable : (prefixWord ++ tailWord_230161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230161).length < 2 ^ (prefixWord ++ tailWord_230161).sum := by decide
  have hdescent : baseEnd_230161 < baseStart_230161 := by decide
  rcases family_descends (prefixWord ++ tailWord_230161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230163 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 3, 3]
def baseStart_230163 : Nat := 118140960795 + 230163 * 2 ^ 59
def prefixEnd_230163 : Nat := 4983230072969 + 3 ^ 40 * 230163 * 2
def baseEnd_230163 : Nat := 78789498587258813269337

theorem tailTrace_230163 : CollatzResearch.WordTrace tailWord_230163 prefixEnd_230163 78789498587258813269337 := by
  unfold tailWord_230163
  simp only [CollatzResearch.WordTrace]
  refine ⟨8394734265166234555983143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5596489510110823037322095 8394734265166234555983143)
  ·
    refine ⟨12592101397749351833974715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8394734265166234555983143 12592101397749351833974715)
    ·
      refine ⟨18888152096624027750962073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12592101397749351833974715 18888152096624027750962073)
      ·
        refine ⟨14166114072468020813221555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18888152096624027750962073 14166114072468020813221555)
        ·
          refine ⟨21249171108702031219832333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14166114072468020813221555 21249171108702031219832333)
          ·
            refine ⟨7968439165763261707437125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21249171108702031219832333 7968439165763261707437125)
            ·
              refine ⟨1494082343580611570144461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7968439165763261707437125 1494082343580611570144461)
              ·
                refine ⟨560280878842729338804173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1494082343580611570144461 560280878842729338804173)
                ·
                  refine ⟨210105329566023502051565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560280878842729338804173 210105329566023502051565)
                  ·
                    refine ⟨78789498587258813269337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210105329566023502051565 78789498587258813269337)
                    ·
                      rfl

theorem cell22_230163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 3].length) (baseStart_230163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230163 prefixEnd_230163 := by exact prefixLift 230163
  have htrace : WordTrace (prefixWord ++ tailWord_230163) baseStart_230163 baseEnd_230163 := by
    simpa [prefixWord, tailWord_230163, baseEnd_230163] using wordTrace_append hprefix tailTrace_230163
  have hstable : (prefixWord ++ tailWord_230163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230163).length < 2 ^ (prefixWord ++ tailWord_230163).sum := by decide
  have hdescent : baseEnd_230163 < baseStart_230163 := by decide
  rcases family_descends (prefixWord ++ tailWord_230163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230191 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 6, 5]
def baseStart_230191 : Nat := 118140960795 + 230191 * 2 ^ 59
def prefixEnd_230191 : Nat := 4983230072969 + 3 ^ 40 * 230191 * 2
def baseEnd_230191 : Nat := 78799083559476073569251

theorem tailTrace_230191 : CollatzResearch.WordTrace tailWord_230191 prefixEnd_230191 78799083559476073569251 := by
  unfold tailWord_230191
  simp only [CollatzResearch.WordTrace]
  refine ⟨8395755509064795338002427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5597170339376530225334951 8395755509064795338002427)
  ·
    refine ⟨12593633263597193007003641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8395755509064795338002427 12593633263597193007003641)
    ·
      refine ⟨9445224947697894755252731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12593633263597193007003641 9445224947697894755252731)
      ·
        refine ⟨14167837421546842132879097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9445224947697894755252731 14167837421546842132879097)
        ·
          refine ⟨10625878066160131599659323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14167837421546842132879097 10625878066160131599659323)
          ·
            refine ⟨15938817099240197399488985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10625878066160131599659323 15938817099240197399488985)
            ·
              refine ⟨11954112824430148049616739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15938817099240197399488985 11954112824430148049616739)
              ·
                refine ⟨17931169236645222074425109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11954112824430148049616739 17931169236645222074425109)
                ·
                  refine ⟨840523557967744784738677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17931169236645222074425109 840523557967744784738677)
                  ·
                    refine ⟨78799083559476073569251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 840523557967744784738677 78799083559476073569251)
                    ·
                      rfl

theorem cell22_230191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_230191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230191 prefixEnd_230191 := by exact prefixLift 230191
  have htrace : WordTrace (prefixWord ++ tailWord_230191) baseStart_230191 baseEnd_230191 := by
    simpa [prefixWord, tailWord_230191, baseEnd_230191] using wordTrace_append hprefix tailTrace_230191
  have hstable : (prefixWord ++ tailWord_230191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230191).length < 2 ^ (prefixWord ++ tailWord_230191).sum := by decide
  have hdescent : baseEnd_230191 < baseStart_230191 := by decide
  rcases family_descends (prefixWord ++ tailWord_230191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230197 : List Nat := [1, 3, 3, 1, 3, 1, 1, 5, 1, 3]
def baseStart_230197 : Nat := 118140960795 + 230197 * 2 ^ 59
def prefixEnd_230197 : Nat := 4983230072969 + 3 ^ 40 * 230197 * 2
def baseEnd_230197 : Nat := 78801137482094057919233

theorem tailTrace_230197 : CollatzResearch.WordTrace tailWord_230197 prefixEnd_230197 78801137482094057919233 := by
  unfold tailWord_230197
  simp only [CollatzResearch.WordTrace]
  refine ⟨8395974347043058362720845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5597316231362038908480563 8395974347043058362720845)
  ·
    refine ⟨3148490380141146886020317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8395974347043058362720845 3148490380141146886020317)
    ·
      refine ⟨1180683892552930082257619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3148490380141146886020317 1180683892552930082257619)
      ·
        refine ⟨1771025838829395123386429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180683892552930082257619 1771025838829395123386429)
        ·
          refine ⟨664134689561023171269911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1771025838829395123386429 664134689561023171269911)
          ·
            refine ⟨996202034341534756904867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664134689561023171269911 996202034341534756904867)
            ·
              refine ⟨1494303051512302135357301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996202034341534756904867 1494303051512302135357301)
              ·
                refine ⟨140090911079278325189747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1494303051512302135357301 140090911079278325189747)
                ·
                  refine ⟨210136366618917487784621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140090911079278325189747 210136366618917487784621)
                  ·
                    refine ⟨78801137482094057919233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210136366618917487784621 78801137482094057919233)
                    ·
                      rfl

theorem cell22_230197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_230197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230197 prefixEnd_230197 := by exact prefixLift 230197
  have htrace : WordTrace (prefixWord ++ tailWord_230197) baseStart_230197 baseEnd_230197 := by
    simpa [prefixWord, tailWord_230197, baseEnd_230197] using wordTrace_append hprefix tailTrace_230197
  have hstable : (prefixWord ++ tailWord_230197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230197).length < 2 ^ (prefixWord ++ tailWord_230197).sum := by decide
  have hdescent : baseEnd_230197 < baseStart_230197 := by decide
  rcases family_descends (prefixWord ++ tailWord_230197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230240 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_230240 : Nat := 118140960795 + 230240 * 2 ^ 59
def prefixEnd_230240 : Nat := 4983230072969 + 3 ^ 40 * 230240 * 2
def baseEnd_230240 : Nat := 78815857260856279094101

theorem tailTrace_230240 : CollatzResearch.WordTrace tailWord_230240 prefixEnd_230240 78815857260856279094101 := by
  unfold tailWord_230240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198771342943638353268087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5598361790591517804357449 4198771342943638353268087)
  ·
    refine ⟨6298157014415457529902131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4198771342943638353268087 6298157014415457529902131)
    ·
      refine ⟨9447235521623186294853197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6298157014415457529902131 9447235521623186294853197)
      ·
        refine ⟨3542713320608694860569949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9447235521623186294853197 3542713320608694860569949)
        ·
          refine ⟨1328517495228260572713731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3542713320608694860569949 1328517495228260572713731)
          ·
            refine ⟨1992776242842390859070597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328517495228260572713731 1992776242842390859070597)
            ·
              refine ⟨373645545532948286075737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1992776242842390859070597 373645545532948286075737)
              ·
                refine ⟨280234159149711214556803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373645545532948286075737 280234159149711214556803)
                ·
                  refine ⟨420351238724566821835205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280234159149711214556803 420351238724566821835205)
                  ·
                    refine ⟨78815857260856279094101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 420351238724566821835205 78815857260856279094101)
                    ·
                      rfl

theorem cell22_230240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_230240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230240 prefixEnd_230240 := by exact prefixLift 230240
  have htrace : WordTrace (prefixWord ++ tailWord_230240) baseStart_230240 baseEnd_230240 := by
    simpa [prefixWord, tailWord_230240, baseEnd_230240] using wordTrace_append hprefix tailTrace_230240
  have hstable : (prefixWord ++ tailWord_230240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230240).length < 2 ^ (prefixWord ++ tailWord_230240).sum := by decide
  have hdescent : baseEnd_230240 < baseStart_230240 := by decide
  rcases family_descends (prefixWord ++ tailWord_230240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230253 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_230253 : Nat := 118140960795 + 230253 * 2 ^ 59
def prefixEnd_230253 : Nat := 4983230072969 + 3 ^ 40 * 230253 * 2
def baseEnd_230253 : Nat := 78820307426528578519061

theorem tailTrace_230253 : CollatzResearch.WordTrace tailWord_230253 prefixEnd_230253 78820307426528578519061 := by
  unfold tailWord_230253
  simp only [CollatzResearch.WordTrace]
  refine ⟨8398016834840179926759413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5598677889893453284506275 8398016834840179926759413)
  ·
    refine ⟨787314078266266868133695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8398016834840179926759413 787314078266266868133695)
    ·
      refine ⟨1180971117399400302200543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787314078266266868133695 1180971117399400302200543)
      ·
        refine ⟨1771456676099100453300815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180971117399400302200543 1771456676099100453300815)
        ·
          refine ⟨2657185014148650679951223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771456676099100453300815 2657185014148650679951223)
          ·
            refine ⟨3985777521222976019926835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657185014148650679951223 3985777521222976019926835)
            ·
              refine ⟨5978666281834464029890253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985777521222976019926835 5978666281834464029890253)
              ·
                refine ⟨2241999855687924011208845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5978666281834464029890253 2241999855687924011208845)
                ·
                  refine ⟨840749945882971504203317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2241999855687924011208845 840749945882971504203317)
                  ·
                    refine ⟨78820307426528578519061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 840749945882971504203317 78820307426528578519061)
                    ·
                      rfl

theorem cell22_230253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_230253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230253 prefixEnd_230253 := by exact prefixLift 230253
  have htrace : WordTrace (prefixWord ++ tailWord_230253) baseStart_230253 baseEnd_230253 := by
    simpa [prefixWord, tailWord_230253, baseEnd_230253] using wordTrace_append hprefix tailTrace_230253
  have hstable : (prefixWord ++ tailWord_230253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230253).length < 2 ^ (prefixWord ++ tailWord_230253).sum := by decide
  have hdescent : baseEnd_230253 < baseStart_230253 := by decide
  rcases family_descends (prefixWord ++ tailWord_230253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230317 : List Nat := [1, 5, 2, 3, 2, 9]
def baseStart_230317 : Nat := 118140960795 + 230317 * 2 ^ 59
def prefixEnd_230317 : Nat := 4983230072969 + 3 ^ 40 * 230317 * 2
def baseEnd_230317 : Nat := 973360690548811665665

theorem tailTrace_230317 : CollatzResearch.WordTrace tailWord_230317 prefixEnd_230317 973360690548811665665 := by
  unfold tailWord_230317
  simp only [CollatzResearch.WordTrace]
  refine ⟨8400351106608318857089205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5600234071072212571392803 8400351106608318857089205)
  ·
    refine ⟨787532916244529892852113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8400351106608318857089205 787532916244529892852113)
    ·
      refine ⟨590649687183397419639085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787532916244529892852113 590649687183397419639085)
      ·
        refine ⟨221493632693774032364657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 590649687183397419639085 221493632693774032364657)
        ·
          refine ⟨166120224520330524273493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221493632693774032364657 166120224520330524273493)
          ·
            refine ⟨973360690548811665665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 166120224520330524273493 973360690548811665665)
            ·
              rfl

theorem cell22_230317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 9].length) (baseStart_230317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230317 prefixEnd_230317 := by exact prefixLift 230317
  have htrace : WordTrace (prefixWord ++ tailWord_230317) baseStart_230317 baseEnd_230317 := by
    simpa [prefixWord, tailWord_230317, baseEnd_230317] using wordTrace_append hprefix tailTrace_230317
  have hstable : (prefixWord ++ tailWord_230317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230317).length < 2 ^ (prefixWord ++ tailWord_230317).sum := by decide
  have hdescent : baseEnd_230317 < baseStart_230317 := by decide
  rcases family_descends (prefixWord ++ tailWord_230317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230343 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 1, 7]
def baseStart_230343 : Nat := 118140960795 + 230343 * 2 ^ 59
def prefixEnd_230343 : Nat := 4983230072969 + 3 ^ 40 * 230343 * 2
def baseEnd_230343 : Nat := 78851116265798343768785

theorem tailTrace_230343 : CollatzResearch.WordTrace tailWord_230343 prefixEnd_230343 78851116265798343768785 := by
  unfold tailWord_230343
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401299404514125297535683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5600866269676083531690455 8401299404514125297535683)
  ·
    refine ⟨12601949106771187946303525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8401299404514125297535683 12601949106771187946303525)
    ·
      refine ⟨2362865457519597739931911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12601949106771187946303525 2362865457519597739931911)
      ·
        refine ⟨3544298186279396609897867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2362865457519597739931911 3544298186279396609897867)
        ·
          refine ⟨5316447279419094914846801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544298186279396609897867 5316447279419094914846801)
          ·
            refine ⟨3987335459564321186135101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5316447279419094914846801 3987335459564321186135101)
            ·
              refine ⟨1495250797336620444800663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3987335459564321186135101 1495250797336620444800663)
              ·
                refine ⟨2242876196004930667200995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495250797336620444800663 2242876196004930667200995)
                ·
                  refine ⟨3364314294007396000801493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242876196004930667200995 3364314294007396000801493)
                  ·
                    refine ⟨78851116265798343768785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3364314294007396000801493 78851116265798343768785)
                    ·
                      rfl

theorem cell22_230343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_230343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230343 prefixEnd_230343 := by exact prefixLift 230343
  have htrace : WordTrace (prefixWord ++ tailWord_230343) baseStart_230343 baseEnd_230343 := by
    simpa [prefixWord, tailWord_230343, baseEnd_230343] using wordTrace_append hprefix tailTrace_230343
  have hstable : (prefixWord ++ tailWord_230343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230343).length < 2 ^ (prefixWord ++ tailWord_230343).sum := by decide
  have hdescent : baseEnd_230343 < baseStart_230343 := by decide
  rcases family_descends (prefixWord ++ tailWord_230343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230424 : List Nat := [2, 1, 2, 3, 2, 4, 1, 3, 4]
def baseStart_230424 : Nat := 118140960795 + 230424 * 2 ^ 59
def prefixEnd_230424 : Nat := 4983230072969 + 3 ^ 40 * 230424 * 2
def baseEnd_230424 : Nat := 26292948073713710831179

theorem tailTrace_230424 : CollatzResearch.WordTrace tailWord_230424 prefixEnd_230424 26292948073713710831179 := by
  unfold tailWord_230424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202126858610338065617163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5602835811480450754156217 4202126858610338065617163)
  ·
    refine ⟨6303190287915507098425745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4202126858610338065617163 6303190287915507098425745)
    ·
      refine ⟨4727392715936630323819309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6303190287915507098425745 4727392715936630323819309)
      ·
        refine ⟨1772772268476236371432241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4727392715936630323819309 1772772268476236371432241)
        ·
          refine ⟨1329579201357177278574181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772772268476236371432241 1329579201357177278574181)
          ·
            refine ⟨249296100254470739732659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1329579201357177278574181 249296100254470739732659)
            ·
              refine ⟨373944150381706109598989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249296100254470739732659 373944150381706109598989)
              ·
                refine ⟨140229056393139791099621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373944150381706109598989 140229056393139791099621)
                ·
                  refine ⟨26292948073713710831179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140229056393139791099621 26292948073713710831179)
                  ·
                    rfl

theorem cell22_230424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 4].length) (baseStart_230424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230424 prefixEnd_230424 := by exact prefixLift 230424
  have htrace : WordTrace (prefixWord ++ tailWord_230424) baseStart_230424 baseEnd_230424 := by
    simpa [prefixWord, tailWord_230424, baseEnd_230424] using wordTrace_append hprefix tailTrace_230424
  have hstable : (prefixWord ++ tailWord_230424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230424).length < 2 ^ (prefixWord ++ tailWord_230424).sum := by decide
  have hdescent : baseEnd_230424 < baseStart_230424 := by decide
  rcases family_descends (prefixWord ++ tailWord_230424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230435 : List Nat := [1, 1, 1, 4, 3, 4, 8]
def baseStart_230435 : Nat := 118140960795 + 230435 * 2 ^ 59
def prefixEnd_230435 : Nat := 4983230072969 + 3 ^ 40 * 230435 * 2
def baseEnd_230435 : Nat := 2921578138738547054389

theorem tailTrace_230435 : CollatzResearch.WordTrace tailWord_230435 prefixEnd_230435 2921578138738547054389 := by
  unfold tailWord_230435
  simp only [CollatzResearch.WordTrace]
  refine ⟨8404654920180825009884759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5603103280120550006589839 8404654920180825009884759)
  ·
    refine ⟨12606982380271237514827139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8404654920180825009884759 12606982380271237514827139)
    ·
      refine ⟨18910473570406856272240709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12606982380271237514827139 18910473570406856272240709)
      ·
        refine ⟨3545713794451285551045133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18910473570406856272240709 3545713794451285551045133)
        ·
          refine ⟨1329642672919232081641925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3545713794451285551045133 1329642672919232081641925)
          ·
            refine ⟨249308001172356015307861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1329642672919232081641925 249308001172356015307861)
            ·
              refine ⟨2921578138738547054389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 249308001172356015307861 2921578138738547054389)
              ·
                rfl

theorem cell22_230435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 8].length) (baseStart_230435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230435 prefixEnd_230435 := by exact prefixLift 230435
  have htrace : WordTrace (prefixWord ++ tailWord_230435) baseStart_230435 baseEnd_230435 := by
    simpa [prefixWord, tailWord_230435, baseEnd_230435] using wordTrace_append hprefix tailTrace_230435
  have hstable : (prefixWord ++ tailWord_230435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230435).length < 2 ^ (prefixWord ++ tailWord_230435).sum := by decide
  have hdescent : baseEnd_230435 < baseStart_230435 := by decide
  rcases family_descends (prefixWord ++ tailWord_230435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230439 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 4, 3]
def baseStart_230439 : Nat := 118140960795 + 230439 * 2 ^ 59
def prefixEnd_230439 : Nat := 4983230072969 + 3 ^ 40 * 230439 * 2
def baseEnd_230439 : Nat := 78883979027686093368491

theorem tailTrace_230439 : CollatzResearch.WordTrace tailWord_230439 prefixEnd_230439 78883979027686093368491 := by
  unfold tailWord_230439
  simp only [CollatzResearch.WordTrace]
  refine ⟨8404800812166333693030371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5603200541444222462020247 8404800812166333693030371)
  ·
    refine ⟨12607201218249500539545557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8404800812166333693030371 12607201218249500539545557)
    ·
      refine ⟨295481278552722668895599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12607201218249500539545557 295481278552722668895599)
      ·
        refine ⟨443221917829084003343399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295481278552722668895599 443221917829084003343399)
        ·
          refine ⟨664832876743626005015099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443221917829084003343399 664832876743626005015099)
          ·
            refine ⟨997249315115439007522649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664832876743626005015099 997249315115439007522649)
            ·
              refine ⟨747936986336579255641987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997249315115439007522649 747936986336579255641987)
              ·
                refine ⟨1121905479504868883462981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747936986336579255641987 1121905479504868883462981)
                ·
                  refine ⟨210357277407162915649309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121905479504868883462981 210357277407162915649309)
                  ·
                    refine ⟨78883979027686093368491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210357277407162915649309 78883979027686093368491)
                    ·
                      rfl

theorem cell22_230439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_230439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230439 prefixEnd_230439 := by exact prefixLift 230439
  have htrace : WordTrace (prefixWord ++ tailWord_230439) baseStart_230439 baseEnd_230439 := by
    simpa [prefixWord, tailWord_230439, baseEnd_230439] using wordTrace_append hprefix tailTrace_230439
  have hstable : (prefixWord ++ tailWord_230439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230439).length < 2 ^ (prefixWord ++ tailWord_230439).sum := by decide
  have hdescent : baseEnd_230439 < baseStart_230439 := by decide
  rcases family_descends (prefixWord ++ tailWord_230439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230452 : List Nat := [2, 5, 1, 2, 1, 1, 1, 9]
def baseStart_230452 : Nat := 118140960795 + 230452 * 2 ^ 59
def prefixEnd_230452 : Nat := 4983230072969 + 3 ^ 40 * 230452 * 2
def baseEnd_230452 : Nat := 8765381021484265865939

theorem tailTrace_230452 : CollatzResearch.WordTrace tailWord_230452 prefixEnd_230452 8765381021484265865939 := by
  unfold tailWord_230452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202637480559618456626805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5603516640746157942169073 4202637480559618456626805)
  ·
    refine ⟨393997263802464230308763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4202637480559618456626805 393997263802464230308763)
    ·
      refine ⟨590995895703696345463145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393997263802464230308763 590995895703696345463145)
      ·
        refine ⟨443246921777772259097359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590995895703696345463145 443246921777772259097359)
        ·
          refine ⟨664870382666658388646039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443246921777772259097359 664870382666658388646039)
          ·
            refine ⟨997305573999987582969059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664870382666658388646039 997305573999987582969059)
            ·
              refine ⟨1495958360999981374453589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997305573999987582969059 1495958360999981374453589)
              ·
                refine ⟨8765381021484265865939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1495958360999981374453589 8765381021484265865939)
                ·
                  rfl

theorem cell22_230452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 9].length) (baseStart_230452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230452 prefixEnd_230452 := by exact prefixLift 230452
  have htrace : WordTrace (prefixWord ++ tailWord_230452) baseStart_230452 baseEnd_230452 := by
    simpa [prefixWord, tailWord_230452, baseEnd_230452] using wordTrace_append hprefix tailTrace_230452
  have hstable : (prefixWord ++ tailWord_230452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230452).length < 2 ^ (prefixWord ++ tailWord_230452).sum := by decide
  have hdescent : baseEnd_230452 < baseStart_230452 := by decide
  rcases family_descends (prefixWord ++ tailWord_230452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230456 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 2, 3]
def baseStart_230456 : Nat := 118140960795 + 230456 * 2 ^ 59
def prefixEnd_230456 : Nat := 4983230072969 + 3 ^ 40 * 230456 * 2
def baseEnd_230456 : Nat := 78889798475103715693439

theorem tailTrace_230456 : CollatzResearch.WordTrace tailWord_230456 prefixEnd_230456 78889798475103715693439 := by
  unfold tailWord_230456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202710426552372798199611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5603613902069830397599481 4202710426552372798199611)
  ·
    refine ⟨6304065639828559197299417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4202710426552372798199611 6304065639828559197299417)
    ·
      refine ⟨4728049229871419397974563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6304065639828559197299417 4728049229871419397974563)
      ·
        refine ⟨7092073844807129096961845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728049229871419397974563 7092073844807129096961845)
        ·
          refine ⟨664881922950668352840173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7092073844807129096961845 664881922950668352840173)
          ·
            refine ⟨249330721106500632315065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 664881922950668352840173 249330721106500632315065)
            ·
              refine ⟨186998040829875474236299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249330721106500632315065 186998040829875474236299)
              ·
                refine ⟨280497061244813211354449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186998040829875474236299 280497061244813211354449)
                ·
                  refine ⟨210372795933609908515837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280497061244813211354449 210372795933609908515837)
                  ·
                    refine ⟨78889798475103715693439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210372795933609908515837 78889798475103715693439)
                    ·
                      rfl

theorem cell22_230456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_230456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230456 prefixEnd_230456 := by exact prefixLift 230456
  have htrace : WordTrace (prefixWord ++ tailWord_230456) baseStart_230456 baseEnd_230456 := by
    simpa [prefixWord, tailWord_230456, baseEnd_230456] using wordTrace_append hprefix tailTrace_230456
  have hstable : (prefixWord ++ tailWord_230456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230456).length < 2 ^ (prefixWord ++ tailWord_230456).sum := by decide
  have hdescent : baseEnd_230456 < baseStart_230456 := by decide
  rcases family_descends (prefixWord ++ tailWord_230456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230495 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 2, 5]
def baseStart_230495 : Nat := 118140960795 + 230495 * 2 ^ 59
def prefixEnd_230495 : Nat := 4983230072969 + 3 ^ 40 * 230495 * 2
def baseEnd_230495 : Nat := 78903148972120613968319

theorem tailTrace_230495 : CollatzResearch.WordTrace tailWord_230495 prefixEnd_230495 78903148972120613968319 := by
  unfold tailWord_230495
  simp only [CollatzResearch.WordTrace]
  refine ⟨8406843299963455257068939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5604562199975636838045959 8406843299963455257068939)
  ·
    refine ⟨12610264949945182885603409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8406843299963455257068939 12610264949945182885603409)
    ·
      refine ⟨9457698712458887164202557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12610264949945182885603409 9457698712458887164202557)
      ·
        refine ⟨3546637017172082686575959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9457698712458887164202557 3546637017172082686575959)
        ·
          refine ⟨5319955525758124029863939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546637017172082686575959 5319955525758124029863939)
          ·
            refine ⟨7979933288637186044795909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319955525758124029863939 7979933288637186044795909)
            ·
              refine ⟨1496237491619472383399233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7979933288637186044795909 1496237491619472383399233)
              ·
                refine ⟨1122178118714604287549425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496237491619472383399233 1122178118714604287549425)
                ·
                  refine ⟨841633589035953215662069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122178118714604287549425 841633589035953215662069)
                  ·
                    refine ⟨78903148972120613968319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 841633589035953215662069 78903148972120613968319)
                    ·
                      rfl

theorem cell22_230495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_230495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230495 prefixEnd_230495 := by exact prefixLift 230495
  have htrace : WordTrace (prefixWord ++ tailWord_230495) baseStart_230495 baseEnd_230495 := by
    simpa [prefixWord, tailWord_230495, baseEnd_230495] using wordTrace_append hprefix tailTrace_230495
  have hstable : (prefixWord ++ tailWord_230495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230495).length < 2 ^ (prefixWord ++ tailWord_230495).sum := by decide
  have hdescent : baseEnd_230495 < baseStart_230495 := by decide
  rcases family_descends (prefixWord ++ tailWord_230495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230559 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 6]
def baseStart_230559 : Nat := 118140960795 + 230559 * 2 ^ 59
def prefixEnd_230559 : Nat := 4983230072969 + 3 ^ 40 * 230559 * 2
def baseEnd_230559 : Nat := 26308352493348593456041

theorem tailTrace_230559 : CollatzResearch.WordTrace tailWord_230559 prefixEnd_230559 26308352493348593456041 := by
  unfold tailWord_230559
  simp only [CollatzResearch.WordTrace]
  refine ⟨8409177571731594187398731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5606118381154396124932487 8409177571731594187398731)
  ·
    refine ⟨12613766357597391281098097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8409177571731594187398731 12613766357597391281098097)
    ·
      refine ⟨9460324768198043460823573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12613766357597391281098097 9460324768198043460823573)
      ·
        refine ⟨443452723509283287226105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9460324768198043460823573 443452723509283287226105)
        ·
          refine ⟨332589542631962465419579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443452723509283287226105 332589542631962465419579)
          ·
            refine ⟨498884313947943698129369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332589542631962465419579 498884313947943698129369)
            ·
              refine ⟨374163235460957773597027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498884313947943698129369 374163235460957773597027)
              ·
                refine ⟨561244853191436660395541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374163235460957773597027 561244853191436660395541)
                ·
                  refine ⟨26308352493348593456041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 561244853191436660395541 26308352493348593456041)
                  ·
                    rfl

theorem cell22_230559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 6].length) (baseStart_230559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230559 prefixEnd_230559 := by exact prefixLift 230559
  have htrace : WordTrace (prefixWord ++ tailWord_230559) baseStart_230559 baseEnd_230559 := by
    simpa [prefixWord, tailWord_230559, baseEnd_230559] using wordTrace_append hprefix tailTrace_230559
  have hstable : (prefixWord ++ tailWord_230559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230559).length < 2 ^ (prefixWord ++ tailWord_230559).sum := by decide
  have hdescent : baseEnd_230559 < baseStart_230559 := by decide
  rcases family_descends (prefixWord ++ tailWord_230559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230593 : List Nat := [1, 2, 6, 1, 1, 3, 1, 3, 4]
def baseStart_230593 : Nat := 118140960795 + 230593 * 2 ^ 59
def prefixEnd_230593 : Nat := 4983230072969 + 3 ^ 40 * 230593 * 2
def baseEnd_230593 : Nat := 26312232124960341672673

theorem tailTrace_230593 : CollatzResearch.WordTrace tailWord_230593 prefixEnd_230593 26312232124960341672673 := by
  unfold tailWord_230593
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410417653608417994136433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5606945102405611996090955 8410417653608417994136433)
  ·
    refine ⟨6307813240206313495602325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8410417653608417994136433 6307813240206313495602325)
    ·
      refine ⟨295678745634670945106359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6307813240206313495602325 295678745634670945106359)
      ·
        refine ⟨443518118452006417659539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295678745634670945106359 443518118452006417659539)
        ·
          refine ⟨665277177678009626489309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443518118452006417659539 665277177678009626489309)
          ·
            refine ⟨249478941629253609933491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665277177678009626489309 249478941629253609933491)
            ·
              refine ⟨374218412443880414900237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249478941629253609933491 374218412443880414900237)
              ·
                refine ⟨140331904666455155587589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374218412443880414900237 140331904666455155587589)
                ·
                  refine ⟨26312232124960341672673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140331904666455155587589 26312232124960341672673)
                  ·
                    rfl

theorem cell22_230593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 4].length) (baseStart_230593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230593 prefixEnd_230593 := by exact prefixLift 230593
  have htrace : WordTrace (prefixWord ++ tailWord_230593) baseStart_230593 baseEnd_230593 := by
    simpa [prefixWord, tailWord_230593, baseEnd_230593] using wordTrace_append hprefix tailTrace_230593
  have hstable : (prefixWord ++ tailWord_230593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230593).length < 2 ^ (prefixWord ++ tailWord_230593).sum := by decide
  have hdescent : baseEnd_230593 < baseStart_230593 := by decide
  rcases family_descends (prefixWord ++ tailWord_230593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230670 : List Nat := [4, 1, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_230670 : Nat := 118140960795 + 230670 * 2 ^ 59
def prefixEnd_230670 : Nat := 4983230072969 + 3 ^ 40 * 230670 * 2
def baseEnd_230670 : Nat := 78963055048478490842783

theorem tailTrace_230670 : CollatzResearch.WordTrace tailWord_230670 prefixEnd_230670 78963055048478490842783 := by
  unfold tailWord_230670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051653259291182518086183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5608817382886306763126309 1051653259291182518086183)
  ·
    refine ⟨1577479888936773777129275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1051653259291182518086183 1577479888936773777129275)
    ·
      refine ⟨2366219833405160665693913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1577479888936773777129275 2366219833405160665693913)
      ·
        refine ⟨1774664875053870499270435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2366219833405160665693913 1774664875053870499270435)
        ·
          refine ⟨2661997312580805748905653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774664875053870499270435 2661997312580805748905653)
          ·
            refine ⟨249562248054450538959905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2661997312580805748905653 249562248054450538959905)
            ·
              refine ⟨187171686040837904219929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249562248054450538959905 187171686040837904219929)
              ·
                refine ⟨140378764530628428164947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187171686040837904219929 140378764530628428164947)
                ·
                  refine ⟨210568146795942642247421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140378764530628428164947 210568146795942642247421)
                  ·
                    refine ⟨78963055048478490842783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210568146795942642247421 78963055048478490842783)
                    ·
                      rfl

theorem cell22_230670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_230670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230670 prefixEnd_230670 := by exact prefixLift 230670
  have htrace : WordTrace (prefixWord ++ tailWord_230670) baseStart_230670 baseEnd_230670 := by
    simpa [prefixWord, tailWord_230670, baseEnd_230670] using wordTrace_append hprefix tailTrace_230670
  have hstable : (prefixWord ++ tailWord_230670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230670).length < 2 ^ (prefixWord ++ tailWord_230670).sum := by decide
  have hdescent : baseEnd_230670 < baseStart_230670 := by decide
  rcases family_descends (prefixWord ++ tailWord_230670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230677 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 6]
def baseStart_230677 : Nat := 118140960795 + 230677 * 2 ^ 59
def prefixEnd_230677 : Nat := 4983230072969 + 3 ^ 40 * 230677 * 2
def baseEnd_230677 : Nat := 26321817097177601972587

theorem tailTrace_230677 : CollatzResearch.WordTrace tailWord_230677 prefixEnd_230677 26321817097177601972587 := by
  unfold tailWord_230677
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413481385304100340194285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5608987590202733560129523 8413481385304100340194285)
  ·
    refine ⟨3155055519489037627572857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8413481385304100340194285 3155055519489037627572857)
    ·
      refine ⟨2366291639616778220679643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3155055519489037627572857 2366291639616778220679643)
      ·
        refine ⟨3549437459425167331019465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366291639616778220679643 3549437459425167331019465)
        ·
          refine ⟨2662078094568875498264599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3549437459425167331019465 2662078094568875498264599)
          ·
            refine ⟨3993117141853313247396899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662078094568875498264599 3993117141853313247396899)
            ·
              refine ⟨5989675712779969871095349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993117141853313247396899 5989675712779969871095349)
              ·
                refine ⟨561532098073122175415189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5989675712779969871095349 561532098073122175415189)
                ·
                  refine ⟨26321817097177601972587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 561532098073122175415189 26321817097177601972587)
                  ·
                    rfl

theorem cell22_230677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_230677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230677 prefixEnd_230677 := by exact prefixLift 230677
  have htrace : WordTrace (prefixWord ++ tailWord_230677) baseStart_230677 baseEnd_230677 := by
    simpa [prefixWord, tailWord_230677, baseEnd_230677] using wordTrace_append hprefix tailTrace_230677
  have hstable : (prefixWord ++ tailWord_230677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230677).length < 2 ^ (prefixWord ++ tailWord_230677).sum := by decide
  have hdescent : baseEnd_230677 < baseStart_230677 := by decide
  rcases family_descends (prefixWord ++ tailWord_230677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230709 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_230709 : Nat := 118140960795 + 230709 * 2 ^ 59
def prefixEnd_230709 : Nat := 4983230072969 + 3 ^ 40 * 230709 * 2
def baseEnd_230709 : Nat := 78976405545495389117663

theorem tailTrace_230709 : CollatzResearch.WordTrace tailWord_230709 prefixEnd_230709 78976405545495389117663 := by
  unfold tailWord_230709
  simp only [CollatzResearch.WordTrace]
  refine ⟨8414648521188169805359181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5609765680792113203572787 8414648521188169805359181)
  ·
    refine ⟨3155493195445563677009693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8414648521188169805359181 3155493195445563677009693)
    ·
      refine ⟨1183309948292086378878635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3155493195445563677009693 1183309948292086378878635)
      ·
        refine ⟨1774964922438129568317953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183309948292086378878635 1774964922438129568317953)
        ·
          refine ⟨1331223691828597176238465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1774964922438129568317953 1331223691828597176238465)
          ·
            refine ⟨998417768871447882178849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1331223691828597176238465 998417768871447882178849)
            ·
              refine ⟨748813326653585911634137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998417768871447882178849 748813326653585911634137)
              ·
                refine ⟨561609994990189433725603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748813326653585911634137 561609994990189433725603)
                ·
                  refine ⟨842414992485284150588405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561609994990189433725603 842414992485284150588405)
                  ·
                    refine ⟨78976405545495389117663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 842414992485284150588405 78976405545495389117663)
                    ·
                      rfl

theorem cell22_230709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_230709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230709 prefixEnd_230709 := by exact prefixLift 230709
  have htrace : WordTrace (prefixWord ++ tailWord_230709) baseStart_230709 baseEnd_230709 := by
    simpa [prefixWord, tailWord_230709, baseEnd_230709] using wordTrace_append hprefix tailTrace_230709
  have hstable : (prefixWord ++ tailWord_230709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230709).length < 2 ^ (prefixWord ++ tailWord_230709).sum := by decide
  have hdescent : baseEnd_230709 < baseStart_230709 := by decide
  rcases family_descends (prefixWord ++ tailWord_230709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230743 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 2, 3]
def baseStart_230743 : Nat := 118140960795 + 230743 * 2 ^ 59
def prefixEnd_230743 : Nat := 4983230072969 + 3 ^ 40 * 230743 * 2
def baseEnd_230743 : Nat := 78988044440330633767559

theorem tailTrace_230743 : CollatzResearch.WordTrace tailWord_230743 prefixEnd_230743 78988044440330633767559 := by
  unfold tailWord_230743
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415888603064993612096883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5610592402043329074731255 8415888603064993612096883)
  ·
    refine ⟨12623832904597490418145325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8415888603064993612096883 12623832904597490418145325)
    ·
      refine ⟨4733937339224058906804497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12623832904597490418145325 4733937339224058906804497)
      ·
        refine ⟨3550453004418044180103373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4733937339224058906804497 3550453004418044180103373)
        ·
          refine ⟨1331419876656766567538765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3550453004418044180103373 1331419876656766567538765)
          ·
            refine ⟨499282453746287462827037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1331419876656766567538765 499282453746287462827037)
            ·
              refine ⟨187230920154857798560139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499282453746287462827037 187230920154857798560139)
              ·
                refine ⟨280846380232286697840209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187230920154857798560139 280846380232286697840209)
                ·
                  refine ⟨210634785174215023380157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280846380232286697840209 210634785174215023380157)
                  ·
                    refine ⟨78988044440330633767559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210634785174215023380157 78988044440330633767559)
                    ·
                      rfl

theorem cell22_230743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_230743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230743 prefixEnd_230743 := by exact prefixLift 230743
  have htrace : WordTrace (prefixWord ++ tailWord_230743) baseStart_230743 baseEnd_230743 := by
    simpa [prefixWord, tailWord_230743, baseEnd_230743] using wordTrace_append hprefix tailTrace_230743
  have hstable : (prefixWord ++ tailWord_230743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230743).length < 2 ^ (prefixWord ++ tailWord_230743).sum := by decide
  have hdescent : baseEnd_230743 < baseStart_230743 := by decide
  rcases family_descends (prefixWord ++ tailWord_230743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230754 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_230754 : Nat := 118140960795 + 230754 * 2 ^ 59
def prefixEnd_230754 : Nat := 4983230072969 + 3 ^ 40 * 230754 * 2
def baseEnd_230754 : Nat := 78991809965130271742525

theorem tailTrace_230754 : CollatzResearch.WordTrace tailWord_230754 prefixEnd_230754 78991809965130271742525 := by
  unfold tailWord_230754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104072451506285622686829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5610859870683428327164877 2104072451506285622686829)
  ·
    refine ⟨789027169314857108507561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2104072451506285622686829 789027169314857108507561)
    ·
      refine ⟨591770376986142831380671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 789027169314857108507561 591770376986142831380671)
      ·
        refine ⟨887655565479214247071007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591770376986142831380671 887655565479214247071007)
        ·
          refine ⟨1331483348218821370606511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887655565479214247071007 1331483348218821370606511)
          ·
            refine ⟨1997225022328232055909767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331483348218821370606511 1997225022328232055909767)
            ·
              refine ⟨2995837533492348083864651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997225022328232055909767 2995837533492348083864651)
              ·
                refine ⟨4493756300238522125796977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995837533492348083864651 4493756300238522125796977)
                ·
                  refine ⟨3370317225178891594347733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4493756300238522125796977 3370317225178891594347733)
                  ·
                    refine ⟨78991809965130271742525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3370317225178891594347733 78991809965130271742525)
                    ·
                      rfl

theorem cell22_230754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_230754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230754 prefixEnd_230754 := by exact prefixLift 230754
  have htrace : WordTrace (prefixWord ++ tailWord_230754) baseStart_230754 baseEnd_230754 := by
    simpa [prefixWord, tailWord_230754, baseEnd_230754] using wordTrace_append hprefix tailTrace_230754
  have hstable : (prefixWord ++ tailWord_230754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230754).length < 2 ^ (prefixWord ++ tailWord_230754).sum := by decide
  have hdescent : baseEnd_230754 < baseStart_230754 := by decide
  rcases family_descends (prefixWord ++ tailWord_230754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230756 : List Nat := [2, 3, 1, 1, 3, 4, 2, 6]
def baseStart_230756 : Nat := 118140960795 + 230756 * 2 ^ 59
def prefixEnd_230756 : Nat := 4983230072969 + 3 ^ 40 * 230756 * 2
def baseEnd_230756 : Nat := 8776943845111437021391

theorem tailTrace_230756 : CollatzResearch.WordTrace tailWord_230756 prefixEnd_230756 8776943845111437021391 := by
  unfold tailWord_230756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208181376008948416160061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5610908501345264554880081 4208181376008948416160061)
  ·
    refine ⟨1578068016003355656060023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4208181376008948416160061 1578068016003355656060023)
    ·
      refine ⟨2367102024005033484090035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578068016003355656060023 2367102024005033484090035)
      ·
        refine ⟨3550653036007550226135053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367102024005033484090035 3550653036007550226135053)
        ·
          refine ⟨1331494888502831334800645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3550653036007550226135053 1331494888502831334800645)
          ·
            refine ⟨249655291594280875275121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1331494888502831334800645 249655291594280875275121)
            ·
              refine ⟨187241468695710656456341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249655291594280875275121 187241468695710656456341)
              ·
                refine ⟨8776943845111437021391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187241468695710656456341 8776943845111437021391)
                ·
                  rfl

theorem cell22_230756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 6].length) (baseStart_230756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230756 prefixEnd_230756 := by exact prefixLift 230756
  have htrace : WordTrace (prefixWord ++ tailWord_230756) baseStart_230756 baseEnd_230756 := by
    simpa [prefixWord, tailWord_230756, baseEnd_230756] using wordTrace_append hprefix tailTrace_230756
  have hstable : (prefixWord ++ tailWord_230756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230756).length < 2 ^ (prefixWord ++ tailWord_230756).sum := by decide
  have hdescent : baseEnd_230756 < baseStart_230756 := by decide
  rcases family_descends (prefixWord ++ tailWord_230756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230767 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 9]
def baseStart_230767 : Nat := 118140960795 + 230767 * 2 ^ 59
def prefixEnd_230767 : Nat := 4983230072969 + 3 ^ 40 * 230767 * 2
def baseEnd_230767 : Nat := 26332086710267523722495

theorem tailTrace_230767 : CollatzResearch.WordTrace tailWord_230767 prefixEnd_230767 26332086710267523722495 := by
  unfold tailWord_230767
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416763954978045710970555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5611175969985363807313703 8416763954978045710970555)
  ·
    refine ⟨12625145932467068566455833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8416763954978045710970555 12625145932467068566455833)
    ·
      refine ⟨9468859449350301424841875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12625145932467068566455833 9468859449350301424841875)
      ·
        refine ⟨14203289174025452137262813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9468859449350301424841875 14203289174025452137262813)
        ·
          refine ⟨5326233440259544551473555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14203289174025452137262813 5326233440259544551473555)
          ·
            refine ⟨7989350160389316827210333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326233440259544551473555 7989350160389316827210333)
            ·
              refine ⟨2996006310145993810203875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7989350160389316827210333 2996006310145993810203875)
              ·
                refine ⟨4494009465218990715305813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2996006310145993810203875 4494009465218990715305813)
                ·
                  refine ⟨26332086710267523722495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4494009465218990715305813 26332086710267523722495)
                  ·
                    rfl

theorem cell22_230767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 9].length) (baseStart_230767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230767 prefixEnd_230767 := by exact prefixLift 230767
  have htrace : WordTrace (prefixWord ++ tailWord_230767) baseStart_230767 baseEnd_230767 := by
    simpa [prefixWord, tailWord_230767, baseEnd_230767] using wordTrace_append hprefix tailTrace_230767
  have hstable : (prefixWord ++ tailWord_230767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230767).length < 2 ^ (prefixWord ++ tailWord_230767).sum := by decide
  have hdescent : baseEnd_230767 < baseStart_230767 := by decide
  rcases family_descends (prefixWord ++ tailWord_230767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230788 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_230788 : Nat := 118140960795 + 230788 * 2 ^ 59
def prefixEnd_230788 : Nat := 4983230072969 + 3 ^ 40 * 230788 * 2
def baseEnd_230788 : Nat := 79003448859965516392421

theorem tailTrace_230788 : CollatzResearch.WordTrace tailWord_230788 prefixEnd_230788 79003448859965516392421 := by
  unfold tailWord_230788
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208764943950983148742509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5611686591934644198323345 4208764943950983148742509)
  ·
    refine ⟨1578286853981618680778441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4208764943950983148742509 1578286853981618680778441)
    ·
      refine ⟨1183715140486214010583831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1578286853981618680778441 1183715140486214010583831)
      ·
        refine ⟨1775572710729321015875747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183715140486214010583831 1775572710729321015875747)
        ·
          refine ⟨2663359066093981523813621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775572710729321015875747 2663359066093981523813621)
          ·
            refine ⟨249689912446310767857527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2663359066093981523813621 249689912446310767857527)
            ·
              refine ⟨374534868669466151786291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249689912446310767857527 374534868669466151786291)
              ·
                refine ⟨561802303004199227679437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374534868669466151786291 561802303004199227679437)
                ·
                  refine ⟨210675863626574710379789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561802303004199227679437 210675863626574710379789)
                  ·
                    refine ⟨79003448859965516392421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210675863626574710379789 79003448859965516392421)
                    ·
                      rfl

theorem cell22_230788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_230788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230788 prefixEnd_230788 := by exact prefixLift 230788
  have htrace : WordTrace (prefixWord ++ tailWord_230788) baseStart_230788 baseEnd_230788 := by
    simpa [prefixWord, tailWord_230788, baseEnd_230788] using wordTrace_append hprefix tailTrace_230788
  have hstable : (prefixWord ++ tailWord_230788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230788).length < 2 ^ (prefixWord ++ tailWord_230788).sum := by decide
  have hdescent : baseEnd_230788 < baseStart_230788 := by decide
  rcases family_descends (prefixWord ++ tailWord_230788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230859 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 4, 4]
def baseStart_230859 : Nat := 118140960795 + 230859 * 2 ^ 59
def prefixEnd_230859 : Nat := 4983230072969 + 3 ^ 40 * 230859 * 2
def baseEnd_230859 : Nat := 79027753610944997867203

theorem tailTrace_230859 : CollatzResearch.WordTrace tailWord_230859 prefixEnd_230859 79027753610944997867203 := by
  unfold tailWord_230859
  simp only [CollatzResearch.WordTrace]
  refine ⟨8420119470644745423319631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5613412980429830282213087 8420119470644745423319631)
  ·
    refine ⟨12630179205967118134979447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8420119470644745423319631 12630179205967118134979447)
    ·
      refine ⟨18945268808950677202469171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12630179205967118134979447 18945268808950677202469171)
      ·
        refine ⟨28417903213426015803703757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18945268808950677202469171 28417903213426015803703757)
        ·
          refine ⟨10656713705034755926388909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28417903213426015803703757 10656713705034755926388909)
          ·
            refine ⟨3996267639388033472395841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10656713705034755926388909 3996267639388033472395841)
            ·
              refine ⟨2997200729541025104296881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996267639388033472395841 2997200729541025104296881)
              ·
                refine ⟨2247900547155768828222661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2997200729541025104296881 2247900547155768828222661)
                ·
                  refine ⟨421481352591706655291749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247900547155768828222661 421481352591706655291749)
                  ·
                    refine ⟨79027753610944997867203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 421481352591706655291749 79027753610944997867203)
                    ·
                      rfl

theorem cell22_230859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 4].length) (baseStart_230859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230859 prefixEnd_230859 := by exact prefixLift 230859
  have htrace : WordTrace (prefixWord ++ tailWord_230859) baseStart_230859 baseEnd_230859 := by
    simpa [prefixWord, tailWord_230859, baseEnd_230859] using wordTrace_append hprefix tailTrace_230859
  have hstable : (prefixWord ++ tailWord_230859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230859).length < 2 ^ (prefixWord ++ tailWord_230859).sum := by decide
  have hdescent : baseEnd_230859 < baseStart_230859 := by decide
  rcases family_descends (prefixWord ++ tailWord_230859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230925 : List Nat := [1, 7, 1, 1, 2, 1, 1, 8]
def baseStart_230925 : Nat := 118140960795 + 230925 * 2 ^ 59
def prefixEnd_230925 : Nat := 4983230072969 + 3 ^ 40 * 230925 * 2
def baseEnd_230925 : Nat := 8783371862193647301889

theorem tailTrace_230925 : CollatzResearch.WordTrace tailWord_230925 prefixEnd_230925 8783371862193647301889 := by
  unfold tailWord_230925
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422526688405638695222229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5615017792270425796814819 8422526688405638695222229)
  ·
    refine ⟨197402969259507156919271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8422526688405638695222229 197402969259507156919271)
    ·
      refine ⟨296104453889260735378907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197402969259507156919271 296104453889260735378907)
      ·
        refine ⟨444156680833891103068361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296104453889260735378907 444156680833891103068361)
        ·
          refine ⟨333117510625418327301271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444156680833891103068361 333117510625418327301271)
          ·
            refine ⟨499676265938127490951907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333117510625418327301271 499676265938127490951907)
            ·
              refine ⟨749514398907191236427861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499676265938127490951907 749514398907191236427861)
              ·
                refine ⟨8783371862193647301889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 749514398907191236427861 8783371862193647301889)
                ·
                  rfl

theorem cell22_230925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 8].length) (baseStart_230925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230925 prefixEnd_230925 := by exact prefixLift 230925
  have htrace : WordTrace (prefixWord ++ tailWord_230925) baseStart_230925 baseEnd_230925 := by
    simpa [prefixWord, tailWord_230925, baseEnd_230925] using wordTrace_append hprefix tailTrace_230925
  have hstable : (prefixWord ++ tailWord_230925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230925).length < 2 ^ (prefixWord ++ tailWord_230925).sum := by decide
  have hdescent : baseEnd_230925 < baseStart_230925 := by decide
  rcases family_descends (prefixWord ++ tailWord_230925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230942 : List Nat := [4, 3, 3, 1, 1, 2, 8]
def baseStart_230942 : Nat := 118140960795 + 230942 * 2 ^ 59
def prefixEnd_230942 : Nat := 4983230072969 + 3 ^ 40 * 230942 * 2
def baseEnd_230942 : Nat := 2928006155820757334887

theorem tailTrace_230942 : CollatzResearch.WordTrace tailWord_230942 prefixEnd_230942 2928006155820757334887 := by
  unfold tailWord_230942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052893341168006324823885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5615431152896033732394053 1052893341168006324823885)
  ·
    refine ⟨394835002938002371808957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1052893341168006324823885 394835002938002371808957)
    ·
      refine ⟨148063126101750889428359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394835002938002371808957 148063126101750889428359)
      ·
        refine ⟨222094689152626334142539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148063126101750889428359 222094689152626334142539)
        ·
          refine ⟨333142033728939501213809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222094689152626334142539 333142033728939501213809)
          ·
            refine ⟨249856525296704625910357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333142033728939501213809 249856525296704625910357)
            ·
              refine ⟨2928006155820757334887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 249856525296704625910357 2928006155820757334887)
              ·
                rfl

theorem cell22_230942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 8].length) (baseStart_230942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230942 prefixEnd_230942 := by exact prefixLift 230942
  have htrace : WordTrace (prefixWord ++ tailWord_230942) baseStart_230942 baseEnd_230942 := by
    simpa [prefixWord, tailWord_230942, baseEnd_230942] using wordTrace_append hprefix tailTrace_230942
  have hstable : (prefixWord ++ tailWord_230942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230942).length < 2 ^ (prefixWord ++ tailWord_230942).sum := by decide
  have hdescent : baseEnd_230942 < baseStart_230942 := by decide
  rcases family_descends (prefixWord ++ tailWord_230942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230983 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 3, 4]
def baseStart_230983 : Nat := 118140960795 + 230983 * 2 ^ 59
def prefixEnd_230983 : Nat := 4983230072969 + 3 ^ 40 * 230983 * 2
def baseEnd_230983 : Nat := 79070201345050007766823

theorem tailTrace_230983 : CollatzResearch.WordTrace tailWord_230983 prefixEnd_230983 79070201345050007766823 := by
  unfold tailWord_230983
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424642122195514600833603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5616428081463676400555735 8424642122195514600833603)
  ·
    refine ⟨12636963183293271901250405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8424642122195514600833603 12636963183293271901250405)
    ·
      refine ⟨2369430596867488481484451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12636963183293271901250405 2369430596867488481484451)
      ·
        refine ⟨3554145895301232722226677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369430596867488481484451 3554145895301232722226677)
        ·
          refine ⟨333201177684490567708751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3554145895301232722226677 333201177684490567708751)
          ·
            refine ⟨499801766526735851563127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333201177684490567708751 499801766526735851563127)
            ·
              refine ⟨749702649790103777344691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499801766526735851563127 749702649790103777344691)
              ·
                refine ⟨1124553974685155666017037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749702649790103777344691 1124553974685155666017037)
                ·
                  refine ⟨421707740506933374756389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124553974685155666017037 421707740506933374756389)
                  ·
                    refine ⟨79070201345050007766823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 421707740506933374756389 79070201345050007766823)
                    ·
                      rfl

theorem cell22_230983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_230983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_230983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_230983 prefixEnd_230983 := by exact prefixLift 230983
  have htrace : WordTrace (prefixWord ++ tailWord_230983) baseStart_230983 baseEnd_230983 := by
    simpa [prefixWord, tailWord_230983, baseEnd_230983] using wordTrace_append hprefix tailTrace_230983
  have hstable : (prefixWord ++ tailWord_230983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230983).length < 2 ^ (prefixWord ++ tailWord_230983).sum := by decide
  have hdescent : baseEnd_230983 < baseStart_230983 := by decide
  rcases family_descends (prefixWord ++ tailWord_230983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231015 : List Nat := [1, 1, 5, 1, 1, 1, 6, 2, 4]
def baseStart_231015 : Nat := 118140960795 + 231015 * 2 ^ 59
def prefixEnd_231015 : Nat := 4983230072969 + 3 ^ 40 * 231015 * 2
def baseEnd_231015 : Nat := 26360385199670863655575

theorem tailTrace_231015 : CollatzResearch.WordTrace tailWord_231015 prefixEnd_231015 26360385199670863655575 := by
  unfold tailWord_231015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8425809258079584065998499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5617206172053056043998999 8425809258079584065998499)
  ·
    refine ⟨12638713887119376098997749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8425809258079584065998499 12638713887119376098997749)
    ·
      refine ⟨1184879426917441509281039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12638713887119376098997749 1184879426917441509281039)
      ·
        refine ⟨1777319140376162263921559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184879426917441509281039 1777319140376162263921559)
        ·
          refine ⟨2665978710564243395882339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777319140376162263921559 2665978710564243395882339)
          ·
            refine ⟨3998968065846365093823509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665978710564243395882339 3998968065846365093823509)
            ·
              refine ⟨187451628086548363772977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3998968065846365093823509 187451628086548363772977)
              ·
                refine ⟨140588721064911272829733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187451628086548363772977 140588721064911272829733)
                ·
                  refine ⟨26360385199670863655575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140588721064911272829733 26360385199670863655575)
                  ·
                    rfl

theorem cell22_231015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 4].length) (baseStart_231015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231015 prefixEnd_231015 := by exact prefixLift 231015
  have htrace : WordTrace (prefixWord ++ tailWord_231015) baseStart_231015 baseEnd_231015 := by
    simpa [prefixWord, tailWord_231015, baseEnd_231015] using wordTrace_append hprefix tailTrace_231015
  have hstable : (prefixWord ++ tailWord_231015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231015).length < 2 ^ (prefixWord ++ tailWord_231015).sum := by decide
  have hdescent : baseEnd_231015 < baseStart_231015 := by decide
  rcases family_descends (prefixWord ++ tailWord_231015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231030 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_231030 : Nat := 118140960795 + 231030 * 2 ^ 59
def prefixEnd_231030 : Nat := 4983230072969 + 3 ^ 40 * 231030 * 2
def baseEnd_231030 : Nat := 79086290405557551841679

theorem tailTrace_231030 : CollatzResearch.WordTrace tailWord_231030 prefixEnd_231030 79086290405557551841679 := by
  unfold tailWord_231030
  simp only [CollatzResearch.WordTrace]
  refine ⟨526647272064077601737159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5617570902016827751863029 526647272064077601737159)
  ·
    refine ⟨789970908096116402605739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 526647272064077601737159 789970908096116402605739)
    ·
      refine ⟨1184956362144174603908609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789970908096116402605739 1184956362144174603908609)
      ·
        refine ⟨888717271608130952931457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1184956362144174603908609 888717271608130952931457)
        ·
          refine ⟨666537953706098214698593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888717271608130952931457 666537953706098214698593)
          ·
            refine ⟨499903465279573661023945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666537953706098214698593 499903465279573661023945)
            ·
              refine ⟨374927598959680245767959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499903465279573661023945 374927598959680245767959)
              ·
                refine ⟨562391398439520368651939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374927598959680245767959 562391398439520368651939)
                ·
                  refine ⟨843587097659280552977909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562391398439520368651939 843587097659280552977909)
                  ·
                    refine ⟨79086290405557551841679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 843587097659280552977909 79086290405557551841679)
                    ·
                      rfl

theorem cell22_231030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_231030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231030 prefixEnd_231030 := by exact prefixLift 231030
  have htrace : WordTrace (prefixWord ++ tailWord_231030) baseStart_231030 baseEnd_231030 := by
    simpa [prefixWord, tailWord_231030, baseEnd_231030] using wordTrace_append hprefix tailTrace_231030
  have hstable : (prefixWord ++ tailWord_231030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231030).length < 2 ^ (prefixWord ++ tailWord_231030).sum := by decide
  have hdescent : baseEnd_231030 < baseStart_231030 := by decide
  rcases family_descends (prefixWord ++ tailWord_231030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231075 : List Nat := [1, 1, 1, 4, 1, 1, 3, 6, 1, 3]
def baseStart_231075 : Nat := 118140960795 + 231075 * 2 ^ 59
def prefixEnd_231075 : Nat := 4983230072969 + 3 ^ 40 * 231075 * 2
def baseEnd_231075 : Nat := 79101694825192434466541

theorem tailTrace_231075 : CollatzResearch.WordTrace tailWord_231075 prefixEnd_231075 79101694825192434466541 := by
  unfold tailWord_231075
  simp only [CollatzResearch.WordTrace]
  refine ⟨8427997637862214313182679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5618665091908142875455119 8427997637862214313182679)
  ·
    refine ⟨12641996456793321469774019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8427997637862214313182679 12641996456793321469774019)
    ·
      refine ⟨18962994685189982204661029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12641996456793321469774019 18962994685189982204661029)
      ·
        refine ⟨3555561503473121663373943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18962994685189982204661029 3555561503473121663373943)
        ·
          refine ⟨5333342255209682495060915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555561503473121663373943 5333342255209682495060915)
          ·
            refine ⟨8000013382814523742591373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333342255209682495060915 8000013382814523742591373)
            ·
              refine ⟨3000005018555446403471765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8000013382814523742591373 3000005018555446403471765)
              ·
                refine ⟨140625235244786550162739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3000005018555446403471765 140625235244786550162739)
                ·
                  refine ⟨210937852867179825244109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140625235244786550162739 210937852867179825244109)
                  ·
                    refine ⟨79101694825192434466541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210937852867179825244109 79101694825192434466541)
                    ·
                      rfl

theorem cell22_231075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 3].length) (baseStart_231075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231075 prefixEnd_231075 := by exact prefixLift 231075
  have htrace : WordTrace (prefixWord ++ tailWord_231075) baseStart_231075 baseEnd_231075 := by
    simpa [prefixWord, tailWord_231075, baseEnd_231075] using wordTrace_append hprefix tailTrace_231075
  have hstable : (prefixWord ++ tailWord_231075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231075).length < 2 ^ (prefixWord ++ tailWord_231075).sum := by decide
  have hdescent : baseEnd_231075 < baseStart_231075 := by decide
  rcases family_descends (prefixWord ++ tailWord_231075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231126 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_231126 : Nat := 118140960795 + 231126 * 2 ^ 59
def prefixEnd_231126 : Nat := 4983230072969 + 3 ^ 40 * 231126 * 2
def baseEnd_231126 : Nat := 79119153167445301441385

theorem tailTrace_231126 : CollatzResearch.WordTrace tailWord_231126 prefixEnd_231126 79119153167445301441385 := by
  unfold tailWord_231126
  simp only [CollatzResearch.WordTrace]
  refine ⟨526866110042340626455577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5619905173784966682192821 526866110042340626455577)
  ·
    refine ⟨395149582531755469841683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 526866110042340626455577 395149582531755469841683)
    ·
      refine ⟨592724373797633204762525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395149582531755469841683 592724373797633204762525)
      ·
        refine ⟨222271640174112451785947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592724373797633204762525 222271640174112451785947)
        ·
          refine ⟨333407460261168677678921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222271640174112451785947 333407460261168677678921)
          ·
            refine ⟨250055595195876508259191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333407460261168677678921 250055595195876508259191)
            ·
              refine ⟨375083392793814762388787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250055595195876508259191 375083392793814762388787)
              ·
                refine ⟨562625089190722143583181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375083392793814762388787 562625089190722143583181)
                ·
                  refine ⟨210984408446520803843693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562625089190722143583181 210984408446520803843693)
                  ·
                    refine ⟨79119153167445301441385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210984408446520803843693 79119153167445301441385)
                    ·
                      rfl

theorem cell22_231126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_231126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231126 prefixEnd_231126 := by exact prefixLift 231126
  have htrace : WordTrace (prefixWord ++ tailWord_231126) baseStart_231126 baseEnd_231126 := by
    simpa [prefixWord, tailWord_231126, baseEnd_231126] using wordTrace_append hprefix tailTrace_231126
  have hstable : (prefixWord ++ tailWord_231126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231126).length < 2 ^ (prefixWord ++ tailWord_231126).sum := by decide
  have hdescent : baseEnd_231126 < baseStart_231126 := by decide
  rcases family_descends (prefixWord ++ tailWord_231126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231139 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 5]
def baseStart_231139 : Nat := 118140960795 + 231139 * 2 ^ 59
def prefixEnd_231139 : Nat := 4983230072969 + 3 ^ 40 * 231139 * 2
def baseEnd_231139 : Nat := 26374534444372533622115

theorem tailTrace_231139 : CollatzResearch.WordTrace tailWord_231139 prefixEnd_231139 26374534444372533622115 := by
  unfold tailWord_231139
  simp only [CollatzResearch.WordTrace]
  refine ⟨8430331909630353243512471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5620221273086902162341647 8430331909630353243512471)
  ·
    refine ⟨12645497864445529865268707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8430331909630353243512471 12645497864445529865268707)
    ·
      refine ⟨18968246796668294797903061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12645497864445529865268707 18968246796668294797903061)
      ·
        refine ⟨444568284296913159325853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18968246796668294797903061 444568284296913159325853)
        ·
          refine ⟨166713106611342434747195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444568284296913159325853 166713106611342434747195)
          ·
            refine ⟨250069659917013652120793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166713106611342434747195 250069659917013652120793)
            ·
              refine ⟨187552244937760239090595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250069659917013652120793 187552244937760239090595)
              ·
                refine ⟨281328367406640358635893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187552244937760239090595 281328367406640358635893)
                ·
                  refine ⟨26374534444372533622115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281328367406640358635893 26374534444372533622115)
                  ·
                    rfl

theorem cell22_231139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 5].length) (baseStart_231139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231139 prefixEnd_231139 := by exact prefixLift 231139
  have htrace : WordTrace (prefixWord ++ tailWord_231139) baseStart_231139 baseEnd_231139 := by
    simpa [prefixWord, tailWord_231139, baseEnd_231139] using wordTrace_append hprefix tailTrace_231139
  have hstable : (prefixWord ++ tailWord_231139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231139).length < 2 ^ (prefixWord ++ tailWord_231139).sum := by decide
  have hdescent : baseEnd_231139 < baseStart_231139 := by decide
  rcases family_descends (prefixWord ++ tailWord_231139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231214 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_231214 : Nat := 118140960795 + 231214 * 2 ^ 59
def prefixEnd_231214 : Nat := 4983230072969 + 3 ^ 40 * 231214 * 2
def baseEnd_231214 : Nat := 79149277365842405241115

theorem tailTrace_231214 : CollatzResearch.WordTrace tailWord_231214 prefixEnd_231214 79149277365842405241115 := by
  unfold tailWord_231214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054133423044830131561587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5622044922905760701661797 1054133423044830131561587)
  ·
    refine ⟨1581200134567245197342381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054133423044830131561587 1581200134567245197342381)
    ·
      refine ⟨592950050462716949003393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1581200134567245197342381 592950050462716949003393)
      ·
        refine ⟨444712537847037711752545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592950050462716949003393 444712537847037711752545)
        ·
          refine ⟨333534403385278283814409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444712537847037711752545 333534403385278283814409)
          ·
            refine ⟨250150802538958712860807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333534403385278283814409 250150802538958712860807)
            ·
              refine ⟨375226203808438069291211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250150802538958712860807 375226203808438069291211)
              ·
                refine ⟨562839305712657103936817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375226203808438069291211 562839305712657103936817)
                ·
                  refine ⟨422129479284492827952613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562839305712657103936817 422129479284492827952613)
                  ·
                    refine ⟨79149277365842405241115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422129479284492827952613 79149277365842405241115)
                    ·
                      rfl

theorem cell22_231214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_231214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231214 prefixEnd_231214 := by exact prefixLift 231214
  have htrace : WordTrace (prefixWord ++ tailWord_231214) baseStart_231214 baseEnd_231214 := by
    simpa [prefixWord, tailWord_231214, baseEnd_231214] using wordTrace_append hprefix tailTrace_231214
  have hstable : (prefixWord ++ tailWord_231214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231214).length < 2 ^ (prefixWord ++ tailWord_231214).sum := by decide
  have hdescent : baseEnd_231214 < baseStart_231214 := by decide
  rcases family_descends (prefixWord ++ tailWord_231214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231240 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 5]
def baseStart_231240 : Nat := 118140960795 + 231240 * 2 ^ 59
def prefixEnd_231240 : Nat := 4983230072969 + 3 ^ 40 * 231240 * 2
def baseEnd_231240 : Nat := 26386059232395668030345

theorem tailTrace_231240 : CollatzResearch.WordTrace tailWord_231240 prefixEnd_231240 26386059232395668030345 := by
  unfold tailWord_231240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4217007841132223746469587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5622677121509631661959449 4217007841132223746469587)
  ·
    refine ⟨6325511761698335619704381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4217007841132223746469587 6325511761698335619704381)
    ·
      refine ⟨2372066910636875857389143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6325511761698335619704381 2372066910636875857389143)
      ·
        refine ⟨3558100365955313786083715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372066910636875857389143 3558100365955313786083715)
        ·
          refine ⟨5337150548932970679125573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3558100365955313786083715 5337150548932970679125573)
          ·
            refine ⟨1000715727924932002336045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5337150548932970679125573 1000715727924932002336045)
            ·
              refine ⟨375268397971849500876017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1000715727924932002336045 375268397971849500876017)
              ·
                refine ⟨281451298478887125657013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375268397971849500876017 281451298478887125657013)
                ·
                  refine ⟨26386059232395668030345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281451298478887125657013 26386059232395668030345)
                  ·
                    rfl

theorem cell22_231240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_231240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231240 prefixEnd_231240 := by exact prefixLift 231240
  have htrace : WordTrace (prefixWord ++ tailWord_231240) baseStart_231240 baseEnd_231240 := by
    simpa [prefixWord, tailWord_231240, baseEnd_231240] using wordTrace_append hprefix tailTrace_231240
  have hstable : (prefixWord ++ tailWord_231240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231240).length < 2 ^ (prefixWord ++ tailWord_231240).sum := by decide
  have hdescent : baseEnd_231240 < baseStart_231240 := by decide
  rcases family_descends (prefixWord ++ tailWord_231240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231283 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 3, 5]
def baseStart_231283 : Nat := 118140960795 + 231283 * 2 ^ 59
def prefixEnd_231283 : Nat := 4983230072969 + 3 ^ 40 * 231283 * 2
def baseEnd_231283 : Nat := 79172897475949225265903

theorem tailTrace_231283 : CollatzResearch.WordTrace tailWord_231283 prefixEnd_231283 79172897475949225265903 := by
  unfold tailWord_231283
  simp only [CollatzResearch.WordTrace]
  refine ⟨8435584021108665836754503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5623722680739110557836335 8435584021108665836754503)
  ·
    refine ⟨12653376031662998755131755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8435584021108665836754503 12653376031662998755131755)
    ·
      refine ⟨18980064047494498132697633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12653376031662998755131755 18980064047494498132697633)
      ·
        refine ⟨14235048035620873599523225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18980064047494498132697633 14235048035620873599523225)
        ·
          refine ⟨10676286026715655199642419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14235048035620873599523225 10676286026715655199642419)
          ·
            refine ⟨16014429040073482799463629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676286026715655199642419 16014429040073482799463629)
            ·
              refine ⟨6005410890027556049798861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16014429040073482799463629 6005410890027556049798861)
              ·
                refine ⟨2252029083760333518674573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6005410890027556049798861 2252029083760333518674573)
                ·
                  refine ⟨844510906410125069502965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2252029083760333518674573 844510906410125069502965)
                  ·
                    refine ⟨79172897475949225265903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 844510906410125069502965 79172897475949225265903)
                    ·
                      rfl

theorem cell22_231283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_231283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231283 prefixEnd_231283 := by exact prefixLift 231283
  have htrace : WordTrace (prefixWord ++ tailWord_231283) baseStart_231283 baseEnd_231283 := by
    simpa [prefixWord, tailWord_231283, baseEnd_231283] using wordTrace_append hprefix tailTrace_231283
  have hstable : (prefixWord ++ tailWord_231283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231283).length < 2 ^ (prefixWord ++ tailWord_231283).sum := by decide
  have hdescent : baseEnd_231283 < baseStart_231283 := by decide
  rcases family_descends (prefixWord ++ tailWord_231283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231313 : List Nat := [1, 2, 2, 1, 1, 1, 5, 9]
def baseStart_231313 : Nat := 118140960795 + 231313 * 2 ^ 59
def prefixEnd_231313 : Nat := 4983230072969 + 3 ^ 40 * 231313 * 2
def baseEnd_231313 : Nat := 8798129676559905223979

theorem tailTrace_231313 : CollatzResearch.WordTrace tailWord_231313 prefixEnd_231313 8798129676559905223979 := by
  unfold tailWord_231313
  simp only [CollatzResearch.WordTrace]
  refine ⟨8436678210999980960346593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5624452140666653973564395 8436678210999980960346593)
  ·
    refine ⟨6327508658249985720259945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8436678210999980960346593 6327508658249985720259945)
    ·
      refine ⟨4745631493687489290194959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6327508658249985720259945 4745631493687489290194959)
      ·
        refine ⟨7118447240531233935292439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745631493687489290194959 7118447240531233935292439)
        ·
          refine ⟨10677670860796850902938659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7118447240531233935292439 10677670860796850902938659)
          ·
            refine ⟨16016506291195276354407989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10677670860796850902938659 16016506291195276354407989)
            ·
              refine ⟨1501547464799557158225749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16016506291195276354407989 1501547464799557158225749)
              ·
                refine ⟨8798129676559905223979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1501547464799557158225749 8798129676559905223979)
                ·
                  rfl

theorem cell22_231313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 9].length) (baseStart_231313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231313 prefixEnd_231313 := by exact prefixLift 231313
  have htrace : WordTrace (prefixWord ++ tailWord_231313) baseStart_231313 baseEnd_231313 := by
    simpa [prefixWord, tailWord_231313, baseEnd_231313] using wordTrace_append hprefix tailTrace_231313
  have hstable : (prefixWord ++ tailWord_231313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231313).length < 2 ^ (prefixWord ++ tailWord_231313).sum := by decide
  have hdescent : baseEnd_231313 < baseStart_231313 := by decide
  rcases family_descends (prefixWord ++ tailWord_231313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231317 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_231317 : Nat := 118140960795 + 231317 * 2 ^ 59
def prefixEnd_231317 : Nat := 4983230072969 + 3 ^ 40 * 231317 * 2
def baseEnd_231317 : Nat := 79184536370784469915799

theorem tailTrace_231317 : CollatzResearch.WordTrace tailWord_231317 prefixEnd_231317 79184536370784469915799 := by
  unfold tailWord_231317
  simp only [CollatzResearch.WordTrace]
  refine ⟨8436824102985489643492205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5624549401990326428994803 8436824102985489643492205)
  ·
    refine ⟨3163809038619558616309577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8436824102985489643492205 3163809038619558616309577)
    ·
      refine ⟨2372856778964668962232183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3163809038619558616309577 2372856778964668962232183)
      ·
        refine ⟨3559285168447003443348275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372856778964668962232183 3559285168447003443348275)
        ·
          refine ⟨5338927752670505165022413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559285168447003443348275 5338927752670505165022413)
          ·
            refine ⟨2002097907251439436883405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5338927752670505165022413 2002097907251439436883405)
            ·
              refine ⟨750786715219289788831277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2002097907251439436883405 750786715219289788831277)
              ·
                refine ⟨281545018207233670811729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 750786715219289788831277 281545018207233670811729)
                ·
                  refine ⟨211158763655425253108797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281545018207233670811729 211158763655425253108797)
                  ·
                    refine ⟨79184536370784469915799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211158763655425253108797 79184536370784469915799)
                    ·
                      rfl

theorem cell22_231317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_231317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231317 prefixEnd_231317 := by exact prefixLift 231317
  have htrace : WordTrace (prefixWord ++ tailWord_231317) baseStart_231317 baseEnd_231317 := by
    simpa [prefixWord, tailWord_231317, baseEnd_231317] using wordTrace_append hprefix tailTrace_231317
  have hstable : (prefixWord ++ tailWord_231317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231317).length < 2 ^ (prefixWord ++ tailWord_231317).sum := by decide
  have hdescent : baseEnd_231317 < baseStart_231317 := by decide
  rcases family_descends (prefixWord ++ tailWord_231317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231332 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_231332 : Nat := 118140960795 + 231332 * 2 ^ 59
def prefixEnd_231332 : Nat := 4983230072969 + 3 ^ 40 * 231332 * 2
def baseEnd_231332 : Nat := 79189671177329430790753

theorem tailTrace_231332 : CollatzResearch.WordTrace tailWord_231332 prefixEnd_231332 79189671177329430790753 := by
  unfold tailWord_231332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218685598965573602644125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5624914131954098136858833 4218685598965573602644125)
  ·
    refine ⟨1582007099612090100991547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4218685598965573602644125 1582007099612090100991547)
    ·
      refine ⟨2373010649418135151487321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582007099612090100991547 2373010649418135151487321)
      ·
        refine ⟨1779757987063601363615491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373010649418135151487321 1779757987063601363615491)
        ·
          refine ⟨2669636980595402045423237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779757987063601363615491 2669636980595402045423237)
          ·
            refine ⟨500556933861637883516857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2669636980595402045423237 500556933861637883516857)
            ·
              refine ⟨375417700396228412637643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500556933861637883516857 375417700396228412637643)
              ·
                refine ⟨563126550594342618956465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375417700396228412637643 563126550594342618956465)
                ·
                  refine ⟨422344912945756964217349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563126550594342618956465 422344912945756964217349)
                  ·
                    refine ⟨79189671177329430790753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422344912945756964217349 79189671177329430790753)
                    ·
                      rfl

theorem cell22_231332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_231332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231332 prefixEnd_231332 := by exact prefixLift 231332
  have htrace : WordTrace (prefixWord ++ tailWord_231332) baseStart_231332 baseEnd_231332 := by
    simpa [prefixWord, tailWord_231332, baseEnd_231332] using wordTrace_append hprefix tailTrace_231332
  have hstable : (prefixWord ++ tailWord_231332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231332).length < 2 ^ (prefixWord ++ tailWord_231332).sum := by decide
  have hdescent : baseEnd_231332 < baseStart_231332 := by decide
  rcases family_descends (prefixWord ++ tailWord_231332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231375 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 5]
def baseStart_231375 : Nat := 118140960795 + 231375 * 2 ^ 59
def prefixEnd_231375 : Nat := 4983230072969 + 3 ^ 40 * 231375 * 2
def baseEnd_231375 : Nat := 26401463652030550655207

theorem tailTrace_231375 : CollatzResearch.WordTrace tailWord_231375 prefixEnd_231375 26401463652030550655207 := by
  unfold tailWord_231375
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438939536775365549103579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5625959691183577032735719 8438939536775365549103579)
  ·
    refine ⟨12658409305163048323655369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8438939536775365549103579 12658409305163048323655369)
    ·
      refine ⟨9493806978872286242741527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12658409305163048323655369 9493806978872286242741527)
      ·
        refine ⟨14240710468308429364112291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9493806978872286242741527 14240710468308429364112291)
        ·
          refine ⟨21361065702462644046168437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14240710468308429364112291 21361065702462644046168437)
          ·
            refine ⟨2002599909605872879328291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21361065702462644046168437 2002599909605872879328291)
            ·
              refine ⟨3003899864408809318992437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002599909605872879328291 3003899864408809318992437)
              ·
                refine ⟨281615612288325873655541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3003899864408809318992437 281615612288325873655541)
                ·
                  refine ⟨26401463652030550655207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281615612288325873655541 26401463652030550655207)
                  ·
                    rfl

theorem cell22_231375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 5].length) (baseStart_231375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231375 prefixEnd_231375 := by exact prefixLift 231375
  have htrace : WordTrace (prefixWord ++ tailWord_231375) baseStart_231375 baseEnd_231375 := by
    simpa [prefixWord, tailWord_231375, baseEnd_231375] using wordTrace_append hprefix tailTrace_231375
  have hstable : (prefixWord ++ tailWord_231375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231375).length < 2 ^ (prefixWord ++ tailWord_231375).sum := by decide
  have hdescent : baseEnd_231375 < baseStart_231375 := by decide
  rcases family_descends (prefixWord ++ tailWord_231375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231409 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 5]
def baseStart_231409 : Nat := 118140960795 + 231409 * 2 ^ 59
def prefixEnd_231409 : Nat := 4983230072969 + 3 ^ 40 * 231409 * 2
def baseEnd_231409 : Nat := 26405343283642298871839

theorem tailTrace_231409 : CollatzResearch.WordTrace tailWord_231409 prefixEnd_231409 26405343283642298871839 := by
  unfold tailWord_231409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8440179618652189355841281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5626786412434792903894187 8440179618652189355841281)
  ·
    refine ⟨6330134713989142016880961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8440179618652189355841281 6330134713989142016880961)
    ·
      refine ⟨4747601035491856512660721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6330134713989142016880961 4747601035491856512660721)
      ·
        refine ⟨3560700776618892384495541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4747601035491856512660721 3560700776618892384495541)
        ·
          refine ⟨333815697808021161046457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3560700776618892384495541 333815697808021161046457)
          ·
            refine ⟨250361773356015870784843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333815697808021161046457 250361773356015870784843)
            ·
              refine ⟨375542660034023806177265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250361773356015870784843 375542660034023806177265)
              ·
                refine ⟨281656995025517854632949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375542660034023806177265 281656995025517854632949)
                ·
                  refine ⟨26405343283642298871839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281656995025517854632949 26405343283642298871839)
                  ·
                    rfl

theorem cell22_231409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_231409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231409 prefixEnd_231409 := by exact prefixLift 231409
  have htrace : WordTrace (prefixWord ++ tailWord_231409) baseStart_231409 baseEnd_231409 := by
    simpa [prefixWord, tailWord_231409, baseEnd_231409] using wordTrace_append hprefix tailTrace_231409
  have hstable : (prefixWord ++ tailWord_231409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231409).length < 2 ^ (prefixWord ++ tailWord_231409).sum := by decide
  have hdescent : baseEnd_231409 < baseStart_231409 := by decide
  rcases family_descends (prefixWord ++ tailWord_231409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231497 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 5, 3]
def baseStart_231497 : Nat := 118140960795 + 231497 * 2 ^ 59
def prefixEnd_231497 : Nat := 4983230072969 + 3 ^ 40 * 231497 * 2
def baseEnd_231497 : Nat := 79246154049324000415247

theorem tailTrace_231497 : CollatzResearch.WordTrace tailWord_231497 prefixEnd_231497 79246154049324000415247 := by
  unfold tailWord_231497
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443389242333380385044745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5628926161555586923363163 8443389242333380385044745)
  ·
    refine ⟨6332541931750035288783559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8443389242333380385044745 6332541931750035288783559)
    ·
      refine ⟨9498812897625052933175339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6332541931750035288783559 9498812897625052933175339)
      ·
        refine ⟨14248219346437579399763009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9498812897625052933175339 14248219346437579399763009)
        ·
          refine ⟨10686164509828184549822257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14248219346437579399763009 10686164509828184549822257)
          ·
            refine ⟨8014623382371138412366693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10686164509828184549822257 8014623382371138412366693)
            ·
              refine ⟨1502741884194588452318755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8014623382371138412366693 1502741884194588452318755)
              ·
                refine ⟨2254112826291882678478133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502741884194588452318755 2254112826291882678478133)
                ·
                  refine ⟨211323077464864001107325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2254112826291882678478133 211323077464864001107325)
                  ·
                    refine ⟨79246154049324000415247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211323077464864001107325 79246154049324000415247)
                    ·
                      rfl

theorem cell22_231497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_231497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231497 prefixEnd_231497 := by exact prefixLift 231497
  have htrace : WordTrace (prefixWord ++ tailWord_231497) baseStart_231497 baseEnd_231497 := by
    simpa [prefixWord, tailWord_231497, baseEnd_231497] using wordTrace_append hprefix tailTrace_231497
  have hstable : (prefixWord ++ tailWord_231497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231497).length < 2 ^ (prefixWord ++ tailWord_231497).sum := by decide
  have hdescent : baseEnd_231497 < baseStart_231497 := by decide
  rcases family_descends (prefixWord ++ tailWord_231497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
