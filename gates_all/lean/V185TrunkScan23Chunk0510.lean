import V185TrunkScan23Chunk0509

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3016593 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 7]
def baseStart_3016593 : Nat := 118140960795 + 3016593 * 2 ^ 59
def prefixEnd_3016593 : Nat := 4983230072969 + 3 ^ 40 * 3016593 * 2
def baseEnd_3016593 : Nat := 172106905332046811079383

theorem tailTrace_3016593 : CollatzResearch.WordTrace tailWord_3016593 prefixEnd_3016593 172106905332046811079383 := by
  unfold tailWord_3016593
  simp only [CollatzResearch.WordTrace]
  refine ⟨110024185560406228912894433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73349457040270819275262955 110024185560406228912894433)
  ·
    refine ⟨82518139170304671684670825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110024185560406228912894433 82518139170304671684670825)
    ·
      refine ⟨61888604377728503763503119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82518139170304671684670825 61888604377728503763503119)
      ·
        refine ⟨92832906566592755645254679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61888604377728503763503119 92832906566592755645254679)
        ·
          refine ⟨139249359849889133467882019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92832906566592755645254679 139249359849889133467882019)
          ·
            refine ⟨208874039774833700201823029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139249359849889133467882019 208874039774833700201823029)
            ·
              refine ⟨19581941228890659393920909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208874039774833700201823029 19581941228890659393920909)
              ·
                refine ⟨7343227960833997272720341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19581941228890659393920909 7343227960833997272720341)
                ·
                  refine ⟨172106905332046811079383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7343227960833997272720341 172106905332046811079383)
                  ·
                    rfl

theorem cell23_3016593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 7].length) (baseStart_3016593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016593 prefixEnd_3016593 := by exact prefixLift 3016593
  have htrace : WordTrace (prefixWord ++ tailWord_3016593) baseStart_3016593 baseEnd_3016593 := by
    simpa [prefixWord, tailWord_3016593, baseEnd_3016593] using wordTrace_append hprefix tailTrace_3016593
  have hstable : (prefixWord ++ tailWord_3016593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016593).length < 2 ^ (prefixWord ++ tailWord_3016593).sum := by decide
  have hdescent : baseEnd_3016593 < baseStart_3016593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016598 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3016598 : Nat := 118140960795 + 3016598 * 2 ^ 59
def prefixEnd_3016598 : Nat := 4983230072969 + 3 ^ 40 * 3016598 * 2
def baseEnd_3016598 : Nat := 1548964715391693780151925

theorem tailTrace_3016598 : CollatzResearch.WordTrace tailWord_3016598 prefixEnd_3016598 1548964715391693780151925 := by
  unfold tailWord_3016598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6876522995336757172926653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73349578616925409844550965 6876522995336757172926653)
  ·
    refine ⟨2578696123251283939847495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6876522995336757172926653 2578696123251283939847495)
    ·
      refine ⟨3868044184876925909771243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2578696123251283939847495 3868044184876925909771243)
      ·
        refine ⟨5802066277315388864656865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868044184876925909771243 5802066277315388864656865)
        ·
          refine ⟨4351549707986541648492649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5802066277315388864656865 4351549707986541648492649)
          ·
            refine ⟨3263662280989906236369487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4351549707986541648492649 3263662280989906236369487)
            ·
              refine ⟨4895493421484859354554231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263662280989906236369487 4895493421484859354554231)
              ·
                refine ⟨7343240132227289031831347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895493421484859354554231 7343240132227289031831347)
                ·
                  refine ⟨11014860198340933547747021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7343240132227289031831347 11014860198340933547747021)
                  ·
                    refine ⟨4130572574377850080405133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11014860198340933547747021 4130572574377850080405133)
                    ·
                      refine ⟨1548964715391693780151925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4130572574377850080405133 1548964715391693780151925)
                      ·
                        rfl

theorem cell23_3016598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3016598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016598 prefixEnd_3016598 := by exact prefixLift 3016598
  have htrace : WordTrace (prefixWord ++ tailWord_3016598) baseStart_3016598 baseEnd_3016598 := by
    simpa [prefixWord, tailWord_3016598, baseEnd_3016598] using wordTrace_append hprefix tailTrace_3016598
  have hstable : (prefixWord ++ tailWord_3016598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016598).length < 2 ^ (prefixWord ++ tailWord_3016598).sum := by decide
  have hdescent : baseEnd_3016598 < baseStart_3016598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016604 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_3016604 : Nat := 118140960795 + 3016604 * 2 ^ 59
def prefixEnd_3016604 : Nat := 4983230072969 + 3 ^ 40 * 3016604 * 2
def baseEnd_3016604 : Nat := 1548967796275620756676897

theorem tailTrace_3016604 : CollatzResearch.WordTrace tailWord_3016604 prefixEnd_3016604 1548967796275620756676897 := by
  unfold tailWord_3016604
  simp only [CollatzResearch.WordTrace]
  refine ⟨55012293381683188895772433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73349724508910918527696577 55012293381683188895772433)
  ·
    refine ⟨41259220036262391671829325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55012293381683188895772433 41259220036262391671829325)
    ·
      refine ⟨15472207513598396876935997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41259220036262391671829325 15472207513598396876935997)
      ·
        refine ⟨5802077817599398828850999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15472207513598396876935997 5802077817599398828850999)
        ·
          refine ⟨8703116726399098243276499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5802077817599398828850999 8703116726399098243276499)
          ·
            refine ⟨13054675089598647364914749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8703116726399098243276499 13054675089598647364914749)
            ·
              refine ⟨4895503158599492761843031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13054675089598647364914749 4895503158599492761843031)
              ·
                refine ⟨7343254737899239142764547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895503158599492761843031 7343254737899239142764547)
                ·
                  refine ⟨11014882106848858714146821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7343254737899239142764547 11014882106848858714146821)
                  ·
                    refine ⟨2065290395034161008902529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11014882106848858714146821 2065290395034161008902529)
                    ·
                      refine ⟨1548967796275620756676897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065290395034161008902529 1548967796275620756676897)
                      ·
                        rfl

theorem cell23_3016604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_3016604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016604 prefixEnd_3016604 := by exact prefixLift 3016604
  have htrace : WordTrace (prefixWord ++ tailWord_3016604) baseStart_3016604 baseEnd_3016604 := by
    simpa [prefixWord, tailWord_3016604, baseEnd_3016604] using wordTrace_append hprefix tailTrace_3016604
  have hstable : (prefixWord ++ tailWord_3016604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016604).length < 2 ^ (prefixWord ++ tailWord_3016604).sum := by decide
  have hdescent : baseEnd_3016604 < baseStart_3016604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016623 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 1, 7]
def baseStart_3016623 : Nat := 118140960795 + 3016623 * 2 ^ 59
def prefixEnd_3016623 : Nat := 4983230072969 + 3 ^ 40 * 3016623 * 2
def baseEnd_3016623 : Nat := 516325850802685394113103

theorem tailTrace_3016623 : CollatzResearch.WordTrace tailWord_3016623 prefixEnd_3016623 516325850802685394113103 := by
  unfold tailWord_3016623
  simp only [CollatzResearch.WordTrace]
  refine ⟨110025279750297544036486523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73350186500198362690991015 110025279750297544036486523)
  ·
    refine ⟨165037919625446316054729785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110025279750297544036486523 165037919625446316054729785)
    ·
      refine ⟨123778439719084737041047339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165037919625446316054729785 123778439719084737041047339)
      ·
        refine ⟨185667659578627105561571009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123778439719084737041047339 185667659578627105561571009)
        ·
          refine ⟨139250744683970329171178257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185667659578627105561571009 139250744683970329171178257)
          ·
            refine ⟨104438058512977746878383693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139250744683970329171178257 104438058512977746878383693)
            ·
              refine ⟨39164271942366655079393885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104438058512977746878383693 39164271942366655079393885)
              ·
                refine ⟨14686601978387495654772707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39164271942366655079393885 14686601978387495654772707)
                ·
                  refine ⟨22029902967581243482159061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14686601978387495654772707 22029902967581243482159061)
                  ·
                    refine ⟨516325850802685394113103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22029902967581243482159061 516325850802685394113103)
                    ·
                      rfl

theorem cell23_3016623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_3016623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016623 prefixEnd_3016623 := by exact prefixLift 3016623
  have htrace : WordTrace (prefixWord ++ tailWord_3016623) baseStart_3016623 baseEnd_3016623 := by
    simpa [prefixWord, tailWord_3016623, baseEnd_3016623] using wordTrace_append hprefix tailTrace_3016623
  have hstable : (prefixWord ++ tailWord_3016623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016623).length < 2 ^ (prefixWord ++ tailWord_3016623).sum := by decide
  have hdescent : baseEnd_3016623 < baseStart_3016623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016640 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 2, 5]
def baseStart_3016640 : Nat := 118140960795 + 3016640 * 2 ^ 59
def prefixEnd_3016640 : Nat := 4983230072969 + 3 ^ 40 * 3016640 * 2
def baseEnd_3016640 : Nat := 516328760526394205275577

theorem tailTrace_3016640 : CollatzResearch.WordTrace tailWord_3016640 prefixEnd_3016640 516328760526394205275577 := by
  unfold tailWord_3016640
  simp only [CollatzResearch.WordTrace]
  refine ⟨55012949895617977969927687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73350599860823970626570249 55012949895617977969927687)
  ·
    refine ⟨82519424843426966954891531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55012949895617977969927687 82519424843426966954891531)
    ·
      refine ⟨123779137265140450432337297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82519424843426966954891531 123779137265140450432337297)
      ·
        refine ⟨92834352948855337824252973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123779137265140450432337297 92834352948855337824252973)
        ·
          refine ⟨34812882355820751684094865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92834352948855337824252973 34812882355820751684094865)
          ·
            refine ⟨26109661766865563763071149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34812882355820751684094865 26109661766865563763071149)
            ·
              refine ⟨9791123162574586411151681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26109661766865563763071149 9791123162574586411151681)
              ·
                refine ⟨7343342371930939808363761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9791123162574586411151681 7343342371930939808363761)
                ·
                  refine ⟨5507506778948204856272821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7343342371930939808363761 5507506778948204856272821)
                  ·
                    refine ⟨516328760526394205275577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5507506778948204856272821 516328760526394205275577)
                    ·
                      rfl

theorem cell23_3016640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_3016640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016640 prefixEnd_3016640 := by exact prefixLift 3016640
  have htrace : WordTrace (prefixWord ++ tailWord_3016640) baseStart_3016640 baseEnd_3016640 := by
    simpa [prefixWord, tailWord_3016640, baseEnd_3016640] using wordTrace_append hprefix tailTrace_3016640
  have hstable : (prefixWord ++ tailWord_3016640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016640).length < 2 ^ (prefixWord ++ tailWord_3016640).sum := by decide
  have hdescent : baseEnd_3016640 < baseStart_3016640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016683 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 10]
def baseStart_3016683 : Nat := 118140960795 + 3016683 * 2 ^ 59
def prefixEnd_3016683 : Nat := 4983230072969 + 3 ^ 40 * 3016683 * 2
def baseEnd_3016683 : Nat := 172112040138591771954337

theorem tailTrace_3016683 : CollatzResearch.WordTrace tailWord_3016683 prefixEnd_3016683 172112040138591771954337 := by
  unfold tailWord_3016683
  simp only [CollatzResearch.WordTrace]
  refine ⟨110027468130080174283670703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73351645420053449522447135 110027468130080174283670703)
  ·
    refine ⟨165041202195120261425506055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110027468130080174283670703 165041202195120261425506055)
    ·
      refine ⟨247561803292680392138259083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165041202195120261425506055 247561803292680392138259083)
      ·
        refine ⟨371342704939020588207388625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247561803292680392138259083 371342704939020588207388625)
        ·
          refine ⟨278507028704265441155541469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371342704939020588207388625 278507028704265441155541469)
          ·
            refine ⟨104440135764099540433328051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278507028704265441155541469 104440135764099540433328051)
            ·
              refine ⟨156660203646149310649992077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104440135764099540433328051 156660203646149310649992077)
              ·
                refine ⟨58747576367305991493747029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156660203646149310649992077 58747576367305991493747029)
                ·
                  refine ⟨172112040138591771954337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 58747576367305991493747029 172112040138591771954337)
                  ·
                    rfl

theorem cell23_3016683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 10].length) (baseStart_3016683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016683 prefixEnd_3016683 := by exact prefixLift 3016683
  have htrace : WordTrace (prefixWord ++ tailWord_3016683) baseStart_3016683 baseEnd_3016683 := by
    simpa [prefixWord, tailWord_3016683, baseEnd_3016683] using wordTrace_append hprefix tailTrace_3016683
  have hstable : (prefixWord ++ tailWord_3016683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016683).length < 2 ^ (prefixWord ++ tailWord_3016683).sum := by decide
  have hdescent : baseEnd_3016683 < baseStart_3016683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016697 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 3]
def baseStart_3016697 : Nat := 118140960795 + 3016697 * 2 ^ 59
def prefixEnd_3016697 : Nat := 4983230072969 + 3 ^ 40 * 3016697 * 2
def baseEnd_3016697 : Nat := 1549015549976488892813969

theorem tailTrace_3016697 : CollatzResearch.WordTrace tailWord_3016697 prefixEnd_3016697 1549015549976488892813969 := by
  unfold tailWord_3016697
  simp only [CollatzResearch.WordTrace]
  refine ⟨110027978752029454674680345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73351985834686303116453563 110027978752029454674680345)
  ·
    refine ⟨82520984064022091006010259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110027978752029454674680345 82520984064022091006010259)
    ·
      refine ⟨123781476096033136509015389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82520984064022091006010259 123781476096033136509015389)
      ·
        refine ⟨46418053536012426190880771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123781476096033136509015389 46418053536012426190880771)
        ·
          refine ⟨69627080304018639286321157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46418053536012426190880771 69627080304018639286321157)
          ·
            refine ⟨13055077557003494866185217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69627080304018639286321157 13055077557003494866185217)
            ·
              refine ⟨9791308167752621149638913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13055077557003494866185217 9791308167752621149638913)
              ·
                refine ⟨7343481125814465862229185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9791308167752621149638913 7343481125814465862229185)
                ·
                  refine ⟨5507610844360849396671889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7343481125814465862229185 5507610844360849396671889)
                  ·
                    refine ⟨4130708133270637047503917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5507610844360849396671889 4130708133270637047503917)
                    ·
                      refine ⟨1549015549976488892813969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4130708133270637047503917 1549015549976488892813969)
                      ·
                        rfl

theorem cell23_3016697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_3016697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016697 prefixEnd_3016697 := by exact prefixLift 3016697
  have htrace : WordTrace (prefixWord ++ tailWord_3016697) baseStart_3016697 baseEnd_3016697 := by
    simpa [prefixWord, tailWord_3016697, baseEnd_3016697] using wordTrace_append hprefix tailTrace_3016697
  have hstable : (prefixWord ++ tailWord_3016697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016697).length < 2 ^ (prefixWord ++ tailWord_3016697).sum := by decide
  have hdescent : baseEnd_3016697 < baseStart_3016697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016761 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3016761 : Nat := 118140960795 + 3016761 * 2 ^ 59
def prefixEnd_3016761 : Nat := 4983230072969 + 3 ^ 40 * 3016761 * 2
def baseEnd_3016761 : Nat := 1549048412738376642413675

theorem tailTrace_3016761 : CollatzResearch.WordTrace tailWord_3016761 prefixEnd_3016761 1549048412738376642413675 := by
  unfold tailWord_3016761
  simp only [CollatzResearch.WordTrace]
  refine ⟨110030313023797593605010137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73353542015865062403340091 110030313023797593605010137)
  ·
    refine ⟨82522734767848195203757603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110030313023797593605010137 82522734767848195203757603)
    ·
      refine ⟨123784102151772292805636405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82522734767848195203757603 123784102151772292805636405)
      ·
        refine ⟨11604759576728652450528413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123784102151772292805636405 11604759576728652450528413)
        ·
          refine ⟨4351784841273244668948155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11604759576728652450528413 4351784841273244668948155)
          ·
            refine ⟨6527677261909867003422233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351784841273244668948155 6527677261909867003422233)
            ·
              refine ⟨4895757946432400252566675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6527677261909867003422233 4895757946432400252566675)
              ·
                refine ⟨7343636919648600378850013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895757946432400252566675 7343636919648600378850013)
                ·
                  refine ⟨2753863844868225142068755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7343636919648600378850013 2753863844868225142068755)
                  ·
                    refine ⟨4130795767302337713103133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2753863844868225142068755 4130795767302337713103133)
                    ·
                      refine ⟨1549048412738376642413675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4130795767302337713103133 1549048412738376642413675)
                      ·
                        rfl

theorem cell23_3016761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3016761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016761 prefixEnd_3016761 := by exact prefixLift 3016761
  have htrace : WordTrace (prefixWord ++ tailWord_3016761) baseStart_3016761 baseEnd_3016761 := by
    simpa [prefixWord, tailWord_3016761, baseEnd_3016761] using wordTrace_append hprefix tailTrace_3016761
  have hstable : (prefixWord ++ tailWord_3016761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016761).length < 2 ^ (prefixWord ++ tailWord_3016761).sum := by decide
  have hdescent : baseEnd_3016761 < baseStart_3016761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016804 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_3016804 : Nat := 118140960795 + 3016804 * 2 ^ 59
def prefixEnd_3016804 : Nat := 4983230072969 + 3 ^ 40 * 3016804 * 2
def baseEnd_3016804 : Nat := 1549070492406519974175977

theorem tailTrace_3016804 : CollatzResearch.WordTrace tailWord_3016804 prefixEnd_3016804 1549070492406519974175977 := by
  unfold tailWord_3016804
  simp only [CollatzResearch.WordTrace]
  refine ⟨55015940681320905974412733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73354587575094541299216977 55015940681320905974412733)
  ·
    refine ⟨20630977755495339740404775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55015940681320905974412733 20630977755495339740404775)
    ·
      refine ⟨30946466633243009610607163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20630977755495339740404775 30946466633243009610607163)
      ·
        refine ⟨46419699949864514415910745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30946466633243009610607163 46419699949864514415910745)
        ·
          refine ⟨34814774962398385811933059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46419699949864514415910745 34814774962398385811933059)
          ·
            refine ⟨52222162443597578717899589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34814774962398385811933059 52222162443597578717899589)
            ·
              refine ⟨9791655458174546009606173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52222162443597578717899589 9791655458174546009606173)
              ·
                refine ⟨3671870796815454753602315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9791655458174546009606173 3671870796815454753602315)
                ·
                  refine ⟨5507806195223182130403473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671870796815454753602315 5507806195223182130403473)
                  ·
                    refine ⟨4130854646417386597802605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5507806195223182130403473 4130854646417386597802605)
                    ·
                      refine ⟨1549070492406519974175977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4130854646417386597802605 1549070492406519974175977)
                      ·
                        rfl

theorem cell23_3016804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_3016804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016804 prefixEnd_3016804 := by exact prefixLift 3016804
  have htrace : WordTrace (prefixWord ++ tailWord_3016804) baseStart_3016804 baseEnd_3016804 := by
    simpa [prefixWord, tailWord_3016804, baseEnd_3016804] using wordTrace_append hprefix tailTrace_3016804
  have hstable : (prefixWord ++ tailWord_3016804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016804).length < 2 ^ (prefixWord ++ tailWord_3016804).sum := by decide
  have hdescent : baseEnd_3016804 < baseStart_3016804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016818 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_3016818 : Nat := 118140960795 + 3016818 * 2 ^ 59
def prefixEnd_3016818 : Nat := 4983230072969 + 3 ^ 40 * 3016818 * 2
def baseEnd_3016818 : Nat := 1549077681135682919400913

theorem tailTrace_3016818 : CollatzResearch.WordTrace tailWord_3016818 prefixEnd_3016818 1549077681135682919400913 := by
  unfold tailWord_3016818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27508097996147773084958777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73354927989727394893223405 27508097996147773084958777)
  ·
    refine ⟨20631073497110829813719083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27508097996147773084958777 20631073497110829813719083)
    ·
      refine ⟨30946610245666244720578625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20631073497110829813719083 30946610245666244720578625)
      ·
        refine ⟨23209957684249683540433969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30946610245666244720578625 23209957684249683540433969)
        ·
          refine ⟨17407468263187262655325477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23209957684249683540433969 17407468263187262655325477)
          ·
            refine ⟨3263900299347611747873527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17407468263187262655325477 3263900299347611747873527)
            ·
              refine ⟨4895850449021417621810291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263900299347611747873527 4895850449021417621810291)
              ·
                refine ⟨7343775673532126432715437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895850449021417621810291 7343775673532126432715437)
                ·
                  refine ⟨2753915877574547412268289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7343775673532126432715437 2753915877574547412268289)
                  ·
                    refine ⟨2065436908180910559201217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2753915877574547412268289 2065436908180910559201217)
                    ·
                      refine ⟨1549077681135682919400913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065436908180910559201217 1549077681135682919400913)
                      ·
                        rfl

theorem cell23_3016818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_3016818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016818 prefixEnd_3016818 := by exact prefixLift 3016818
  have htrace : WordTrace (prefixWord ++ tailWord_3016818) baseStart_3016818 baseEnd_3016818 := by
    simpa [prefixWord, tailWord_3016818, baseEnd_3016818] using wordTrace_append hprefix tailTrace_3016818
  have hstable : (prefixWord ++ tailWord_3016818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016818).length < 2 ^ (prefixWord ++ tailWord_3016818).sum := by decide
  have hdescent : baseEnd_3016818 < baseStart_3016818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016827 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 9, 2]
def baseStart_3016827 : Nat := 118140960795 + 3016827 * 2 ^ 59
def prefixEnd_3016827 : Nat := 4983230072969 + 3 ^ 40 * 3016827 * 2
def baseEnd_3016827 : Nat := 1549082302461573384188371

theorem tailTrace_3016827 : CollatzResearch.WordTrace tailWord_3016827 prefixEnd_3016827 1549082302461573384188371 := by
  unfold tailWord_3016827
  simp only [CollatzResearch.WordTrace]
  refine ⟨110032720241558486876912735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73355146827705657917941823 110032720241558486876912735)
  ·
    refine ⟨165049080362337730315369103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110032720241558486876912735 165049080362337730315369103)
    ·
      refine ⟨247573620543506595473053655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165049080362337730315369103 247573620543506595473053655)
      ·
        refine ⟨371360430815259893209580483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247573620543506595473053655 371360430815259893209580483)
        ·
          refine ⟨557040646222889839814370725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371360430815259893209580483 557040646222889839814370725)
          ·
            refine ⟨104445121166791844965194511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 557040646222889839814370725 104445121166791844965194511)
            ·
              refine ⟨156667681750187767447791767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104445121166791844965194511 156667681750187767447791767)
              ·
                refine ⟨235001522625281651171687651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156667681750187767447791767 235001522625281651171687651)
                ·
                  refine ⟨352502283937922476757531477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235001522625281651171687651 352502283937922476757531477)
                  ·
                    refine ⟨2065443069948764512251161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 352502283937922476757531477 2065443069948764512251161)
                    ·
                      refine ⟨1549082302461573384188371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065443069948764512251161 1549082302461573384188371)
                      ·
                        rfl

theorem cell23_3016827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 9, 2].length) (baseStart_3016827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016827 prefixEnd_3016827 := by exact prefixLift 3016827
  have htrace : WordTrace (prefixWord ++ tailWord_3016827) baseStart_3016827 baseEnd_3016827 := by
    simpa [prefixWord, tailWord_3016827, baseEnd_3016827] using wordTrace_append hprefix tailTrace_3016827
  have hstable : (prefixWord ++ tailWord_3016827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016827).length < 2 ^ (prefixWord ++ tailWord_3016827).sum := by decide
  have hdescent : baseEnd_3016827 < baseStart_3016827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016868 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_3016868 : Nat := 118140960795 + 3016868 * 2 ^ 59
def prefixEnd_3016868 : Nat := 4983230072969 + 3 ^ 40 * 3016868 * 2
def baseEnd_3016868 : Nat := 1549103355168407723775683

theorem tailTrace_3016868 : CollatzResearch.WordTrace tailWord_3016868 prefixEnd_3016868 1549103355168407723775683 := by
  unfold tailWord_3016868
  simp only [CollatzResearch.WordTrace]
  refine ⟨55017107817204975439577629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73356143756273300586103505 55017107817204975439577629)
  ·
    refine ⟨20631415431451865789841611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55017107817204975439577629 20631415431451865789841611)
    ·
      refine ⟨30947123147177798684762417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20631415431451865789841611 30947123147177798684762417)
      ·
        refine ⟨23210342360383349013571813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30947123147177798684762417 23210342360383349013571813)
        ·
          refine ⟨4351939192571877940044715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23210342360383349013571813 4351939192571877940044715)
          ·
            refine ⟨6527908788857816910067073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351939192571877940044715 6527908788857816910067073)
            ·
              refine ⟨4895931591643362682550305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6527908788857816910067073 4895931591643362682550305)
              ·
                refine ⟨3671948693732522011912729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4895931591643362682550305 3671948693732522011912729)
                ·
                  refine ⟨2753961520299391508934547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3671948693732522011912729 2753961520299391508934547)
                  ·
                    refine ⟨4130942280449087263401821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2753961520299391508934547 4130942280449087263401821)
                    ·
                      refine ⟨1549103355168407723775683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4130942280449087263401821 1549103355168407723775683)
                      ·
                        rfl

theorem cell23_3016868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_3016868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016868 prefixEnd_3016868 := by exact prefixLift 3016868
  have htrace : WordTrace (prefixWord ++ tailWord_3016868) baseStart_3016868 baseEnd_3016868 := by
    simpa [prefixWord, tailWord_3016868, baseEnd_3016868] using wordTrace_append hprefix tailTrace_3016868
  have hstable : (prefixWord ++ tailWord_3016868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016868).length < 2 ^ (prefixWord ++ tailWord_3016868).sum := by decide
  have hdescent : baseEnd_3016868 < baseStart_3016868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016887 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_3016887 : Nat := 118140960795 + 3016887 * 2 ^ 59
def prefixEnd_3016887 : Nat := 4983230072969 + 3 ^ 40 * 3016887 * 2
def baseEnd_3016887 : Nat := 1549113111300843149438095

theorem tailTrace_3016887 : CollatzResearch.WordTrace tailWord_3016887 prefixEnd_3016887 1549113111300843149438095 := by
  unfold tailWord_3016887
  simp only [CollatzResearch.WordTrace]
  refine ⟨110034908621341117124096915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73356605747560744749397943 110034908621341117124096915)
  ·
    refine ⟨165052362932011675686145373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110034908621341117124096915 165052362932011675686145373)
    ·
      refine ⟨61894636099504378382304515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165052362932011675686145373 61894636099504378382304515)
      ·
        refine ⟨92841954149256567573456773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61894636099504378382304515 92841954149256567573456773)
        ·
          refine ⟨17407866402985606420023145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92841954149256567573456773 17407866402985606420023145)
          ·
            refine ⟨13055899802239204815017359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17407866402985606420023145 13055899802239204815017359)
            ·
              refine ⟨19583849703358807222526039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13055899802239204815017359 19583849703358807222526039)
              ·
                refine ⟨29375774555038210833789059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19583849703358807222526039 29375774555038210833789059)
                ·
                  refine ⟨44063661832557316250683589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29375774555038210833789059 44063661832557316250683589)
                  ·
                    refine ⟨8261936593604496797003173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44063661832557316250683589 8261936593604496797003173)
                    ·
                      refine ⟨1549113111300843149438095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8261936593604496797003173 1549113111300843149438095)
                      ·
                        rfl

theorem cell23_3016887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_3016887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016887 prefixEnd_3016887 := by exact prefixLift 3016887
  have htrace : WordTrace (prefixWord ++ tailWord_3016887) baseStart_3016887 baseEnd_3016887 := by
    simpa [prefixWord, tailWord_3016887, baseEnd_3016887] using wordTrace_append hprefix tailTrace_3016887
  have hstable : (prefixWord ++ tailWord_3016887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016887).length < 2 ^ (prefixWord ++ tailWord_3016887).sum := by decide
  have hdescent : baseEnd_3016887 < baseStart_3016887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016891 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 2, 2, 2]
def baseStart_3016891 : Nat := 118140960795 + 3016891 * 2 ^ 59
def prefixEnd_3016891 : Nat := 4983230072969 + 3 ^ 40 * 3016891 * 2
def baseEnd_3016891 : Nat := 1549115165223461133788077

theorem tailTrace_3016891 : CollatzResearch.WordTrace tailWord_3016891 prefixEnd_3016891 1549115165223461133788077 := by
  unfold tailWord_3016891
  simp only [CollatzResearch.WordTrace]
  refine ⟨110035054513326625807242527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73356703008884417204828351 110035054513326625807242527)
  ·
    refine ⟨165052581769989938710863791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110035054513326625807242527 165052581769989938710863791)
    ·
      refine ⟨247578872654984908066295687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165052581769989938710863791 247578872654984908066295687)
      ·
        refine ⟨371368308982477362099443531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247578872654984908066295687 371368308982477362099443531)
        ·
          refine ⟨557052463473716043149165297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371368308982477362099443531 557052463473716043149165297)
          ·
            refine ⟨417789347605287032361873973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557052463473716043149165297 417789347605287032361873973)
            ·
              refine ⟨39167751337995659283925685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 417789347605287032361873973 39167751337995659283925685)
              ·
                refine ⟨3671976687937093057868033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39167751337995659283925685 3671976687937093057868033)
                ·
                  refine ⟨2753982515952819793401025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3671976687937093057868033 2753982515952819793401025)
                  ·
                    refine ⟨2065486886964614845050769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2753982515952819793401025 2065486886964614845050769)
                    ·
                      refine ⟨1549115165223461133788077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065486886964614845050769 1549115165223461133788077)
                      ·
                        rfl

theorem cell23_3016891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 2, 2].length) (baseStart_3016891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016891 prefixEnd_3016891 := by exact prefixLift 3016891
  have htrace : WordTrace (prefixWord ++ tailWord_3016891) baseStart_3016891 baseEnd_3016891 := by
    simpa [prefixWord, tailWord_3016891, baseEnd_3016891] using wordTrace_append hprefix tailTrace_3016891
  have hstable : (prefixWord ++ tailWord_3016891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016891).length < 2 ^ (prefixWord ++ tailWord_3016891).sum := by decide
  have hdescent : baseEnd_3016891 < baseStart_3016891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016907 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 3]
def baseStart_3016907 : Nat := 118140960795 + 3016907 * 2 ^ 59
def prefixEnd_3016907 : Nat := 4983230072969 + 3 ^ 40 * 3016907 * 2
def baseEnd_3016907 : Nat := 1549123380913933071188003

theorem tailTrace_3016907 : CollatzResearch.WordTrace tailWord_3016907 prefixEnd_3016907 1549123380913933071188003 := by
  unfold tailWord_3016907
  simp only [CollatzResearch.WordTrace]
  refine ⟨110035638081268660539824975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73357092054179107026549983 110035638081268660539824975)
  ·
    refine ⟨165053457121902990809737463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110035638081268660539824975 165053457121902990809737463)
    ·
      refine ⟨247580185682854486214606195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165053457121902990809737463 247580185682854486214606195)
      ·
        refine ⟨371370278524281729321909293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247580185682854486214606195 371370278524281729321909293)
        ·
          refine ⟨139263854446605648495715985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371370278524281729321909293 139263854446605648495715985)
          ·
            refine ⟨104447890834954236371786989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139263854446605648495715985 104447890834954236371786989)
            ·
              refine ⟨39167959063107838639420121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104447890834954236371786989 39167959063107838639420121)
              ·
                refine ⟨29375969297330878979565091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39167959063107838639420121 29375969297330878979565091)
                ·
                  refine ⟨44063953945996318469347637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29375969297330878979565091 44063953945996318469347637)
                  ·
                    refine ⟨4130995682437154856501341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44063953945996318469347637 4130995682437154856501341)
                    ·
                      refine ⟨1549123380913933071188003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4130995682437154856501341 1549123380913933071188003)
                      ·
                        rfl

theorem cell23_3016907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 3].length) (baseStart_3016907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016907 prefixEnd_3016907 := by exact prefixLift 3016907
  have htrace : WordTrace (prefixWord ++ tailWord_3016907) baseStart_3016907 baseEnd_3016907 := by
    simpa [prefixWord, tailWord_3016907, baseEnd_3016907] using wordTrace_append hprefix tailTrace_3016907
  have hstable : (prefixWord ++ tailWord_3016907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016907).length < 2 ^ (prefixWord ++ tailWord_3016907).sum := by decide
  have hdescent : baseEnd_3016907 < baseStart_3016907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016925 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_3016925 : Nat := 118140960795 + 3016925 * 2 ^ 59
def prefixEnd_3016925 : Nat := 4983230072969 + 3 ^ 40 * 3016925 * 2
def baseEnd_3016925 : Nat := 1549132623565714000762921

theorem tailTrace_3016925 : CollatzResearch.WordTrace tailWord_3016925 prefixEnd_3016925 1549132623565714000762921 := by
  unfold tailWord_3016925
  simp only [CollatzResearch.WordTrace]
  refine ⟨110036294595203449613980229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73357529730135633075986819 110036294595203449613980229)
  ·
    refine ⟨20631805236600646802621293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110036294595203449613980229 20631805236600646802621293)
    ·
      refine ⟨7736926963725242550982985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20631805236600646802621293 7736926963725242550982985)
      ·
        refine ⟨5802695222793931913237239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7736926963725242550982985 5802695222793931913237239)
        ·
          refine ⟨8704042834190897869855859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5802695222793931913237239 8704042834190897869855859)
          ·
            refine ⟨13056064251286346804783789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8704042834190897869855859 13056064251286346804783789)
            ·
              refine ⟨4896024094232380051793921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13056064251286346804783789 4896024094232380051793921)
              ·
                refine ⟨3672018070674285038845441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4896024094232380051793921 3672018070674285038845441)
                ·
                  refine ⟨2754013553005713779134081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3672018070674285038845441 2754013553005713779134081)
                  ·
                    refine ⟨2065510164754285334350561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2754013553005713779134081 2065510164754285334350561)
                    ·
                      refine ⟨1549132623565714000762921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065510164754285334350561 1549132623565714000762921)
                      ·
                        rfl

theorem cell23_3016925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_3016925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016925 prefixEnd_3016925 := by exact prefixLift 3016925
  have htrace : WordTrace (prefixWord ++ tailWord_3016925) baseStart_3016925 baseEnd_3016925 := by
    simpa [prefixWord, tailWord_3016925, baseEnd_3016925] using wordTrace_append hprefix tailTrace_3016925
  have hstable : (prefixWord ++ tailWord_3016925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016925).length < 2 ^ (prefixWord ++ tailWord_3016925).sum := by decide
  have hdescent : baseEnd_3016925 < baseStart_3016925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016927 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 4, 5]
def baseStart_3016927 : Nat := 118140960795 + 3016927 * 2 ^ 59
def prefixEnd_3016927 : Nat := 4983230072969 + 3 ^ 40 * 3016927 * 2
def baseEnd_3016927 : Nat := 516377883509007664312637

theorem tailTrace_3016927 : CollatzResearch.WordTrace tailWord_3016927 prefixEnd_3016927 516377883509007664312637 := by
  unfold tailWord_3016927
  simp only [CollatzResearch.WordTrace]
  refine ⟨110036367541196203955553035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73357578360797469303702023 110036367541196203955553035)
  ·
    refine ⟨165054551311794305933329553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110036367541196203955553035 165054551311794305933329553)
    ·
      refine ⟨123790913483845729449997165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165054551311794305933329553 123790913483845729449997165)
      ·
        refine ⟨46421592556442148543748937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123790913483845729449997165 46421592556442148543748937)
        ·
          refine ⟨34816194417331611407811703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46421592556442148543748937 34816194417331611407811703)
          ·
            refine ⟨52224291625997417111717555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34816194417331611407811703 52224291625997417111717555)
            ·
              refine ⟨78336437438996125667576333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52224291625997417111717555 78336437438996125667576333)
              ·
                refine ⟨29376164039623547125341125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78336437438996125667576333 29376164039623547125341125)
                ·
                  refine ⟨5508030757429415086001461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29376164039623547125341125 5508030757429415086001461)
                  ·
                    refine ⟨516377883509007664312637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5508030757429415086001461 516377883509007664312637)
                    ·
                      rfl

theorem cell23_3016927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_3016927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016927 prefixEnd_3016927 := by exact prefixLift 3016927
  have htrace : WordTrace (prefixWord ++ tailWord_3016927) baseStart_3016927 baseEnd_3016927 := by
    simpa [prefixWord, tailWord_3016927, baseEnd_3016927] using wordTrace_append hprefix tailTrace_3016927
  have hstable : (prefixWord ++ tailWord_3016927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016927).length < 2 ^ (prefixWord ++ tailWord_3016927).sum := by decide
  have hdescent : baseEnd_3016927 < baseStart_3016927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016931 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 7]
def baseStart_3016931 : Nat := 118140960795 + 3016931 * 2 ^ 59
def prefixEnd_3016931 : Nat := 4983230072969 + 3 ^ 40 * 3016931 * 2
def baseEnd_3016931 : Nat := 172126189383293441920877

theorem tailTrace_3016931 : CollatzResearch.WordTrace tailWord_3016931 prefixEnd_3016931 172126189383293441920877 := by
  unfold tailWord_3016931
  simp only [CollatzResearch.WordTrace]
  refine ⟨110036513433181712638698647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73357675622121141759132431 110036513433181712638698647)
  ·
    refine ⟨165054770149772568958047971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110036513433181712638698647 165054770149772568958047971)
    ·
      refine ⟨247582155224658853437071957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165054770149772568958047971 247582155224658853437071957)
      ·
        refine ⟨2901353381538970938715687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 247582155224658853437071957 2901353381538970938715687)
        ·
          refine ⟨4352030072308456408073531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901353381538970938715687 4352030072308456408073531)
          ·
            refine ⟨6528045108462684612110297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352030072308456408073531 6528045108462684612110297)
            ·
              refine ⟨4896033831347013459082723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6528045108462684612110297 4896033831347013459082723)
              ·
                refine ⟨7344050747020520188624085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4896033831347013459082723 7344050747020520188624085)
                ·
                  refine ⟨172126189383293441920877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7344050747020520188624085 172126189383293441920877)
                  ·
                    rfl

theorem cell23_3016931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 7].length) (baseStart_3016931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016931 prefixEnd_3016931 := by exact prefixLift 3016931
  have htrace : WordTrace (prefixWord ++ tailWord_3016931) baseStart_3016931 baseEnd_3016931 := by
    simpa [prefixWord, tailWord_3016931, baseEnd_3016931] using wordTrace_append hprefix tailTrace_3016931
  have hstable : (prefixWord ++ tailWord_3016931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016931).length < 2 ^ (prefixWord ++ tailWord_3016931).sum := by decide
  have hdescent : baseEnd_3016931 < baseStart_3016931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016947 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 4]
def baseStart_3016947 : Nat := 118140960795 + 3016947 * 2 ^ 59
def prefixEnd_3016947 : Nat := 4983230072969 + 3 ^ 40 * 3016947 * 2
def baseEnd_3016947 : Nat := 1549143920140112914687819

theorem tailTrace_3016947 : CollatzResearch.WordTrace tailWord_3016947 prefixEnd_3016947 1549143920140112914687819 := by
  unfold tailWord_3016947
  simp only [CollatzResearch.WordTrace]
  refine ⟨110037097001123747371281095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73358064667415831580854063 110037097001123747371281095)
  ·
    refine ⟨165055645501685621056921643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110037097001123747371281095 165055645501685621056921643)
    ·
      refine ⟨247583468252528431585382465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165055645501685621056921643 247583468252528431585382465)
      ·
        refine ⟨185687601189396323689036849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247583468252528431585382465 185687601189396323689036849)
        ·
          refine ⟨139265700892047242766777637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185687601189396323689036849 139265700892047242766777637)
          ·
            refine ⟨26112318917258858018770807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139265700892047242766777637 26112318917258858018770807)
            ·
              refine ⟨39168478375888287028156211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26112318917258858018770807 39168478375888287028156211)
              ·
                refine ⟨58752717563832430542234317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39168478375888287028156211 58752717563832430542234317)
                ·
                  refine ⟨22032269086437161453337869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58752717563832430542234317 22032269086437161453337869)
                  ·
                    refine ⟨8262100907413935545001701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22032269086437161453337869 8262100907413935545001701)
                    ·
                      refine ⟨1549143920140112914687819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8262100907413935545001701 1549143920140112914687819)
                      ·
                        rfl

theorem cell23_3016947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_3016947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016947 prefixEnd_3016947 := by exact prefixLift 3016947
  have htrace : WordTrace (prefixWord ++ tailWord_3016947) baseStart_3016947 baseEnd_3016947 := by
    simpa [prefixWord, tailWord_3016947, baseEnd_3016947] using wordTrace_append hprefix tailTrace_3016947
  have hstable : (prefixWord ++ tailWord_3016947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016947).length < 2 ^ (prefixWord ++ tailWord_3016947).sum := by decide
  have hdescent : baseEnd_3016947 < baseStart_3016947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016987 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 8]
def baseStart_3016987 : Nat := 118140960795 + 3016987 * 2 ^ 59
def prefixEnd_3016987 : Nat := 4983230072969 + 3 ^ 40 * 3016987 * 2
def baseEnd_3016987 : Nat := 172129384374032528687515

theorem tailTrace_3016987 : CollatzResearch.WordTrace tailWord_3016987 prefixEnd_3016987 172129384374032528687515 := by
  unfold tailWord_3016987
  simp only [CollatzResearch.WordTrace]
  refine ⟨110038555920978834202737215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73359037280652556135158143 110038555920978834202737215)
  ·
    refine ⟨165057833881468251304105823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110038555920978834202737215 165057833881468251304105823)
    ·
      refine ⟨247586750822202376956158735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165057833881468251304105823 247586750822202376956158735)
      ·
        refine ⟨371380126233303565434238103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247586750822202376956158735 371380126233303565434238103)
        ·
          refine ⟨557070189349955348151357155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371380126233303565434238103 557070189349955348151357155)
          ·
            refine ⟨835605284024933022227035733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557070189349955348151357155 835605284024933022227035733)
            ·
              refine ⟨9792249422167183854223075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 835605284024933022227035733 9792249422167183854223075)
              ·
                refine ⟨14688374133250775781334613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9792249422167183854223075 14688374133250775781334613)
                ·
                  refine ⟨172129384374032528687515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14688374133250775781334613 172129384374032528687515)
                  ·
                    rfl

theorem cell23_3016987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 8].length) (baseStart_3016987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016987 prefixEnd_3016987 := by exact prefixLift 3016987
  have htrace : WordTrace (prefixWord ++ tailWord_3016987) baseStart_3016987 baseEnd_3016987 := by
    simpa [prefixWord, tailWord_3016987, baseEnd_3016987] using wordTrace_append hprefix tailTrace_3016987
  have hstable : (prefixWord ++ tailWord_3016987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016987).length < 2 ^ (prefixWord ++ tailWord_3016987).sum := by decide
  have hdescent : baseEnd_3016987 < baseStart_3016987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3016991 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 3, 4]
def baseStart_3016991 : Nat := 118140960795 + 3016991 * 2 ^ 59
def prefixEnd_3016991 : Nat := 4983230072969 + 3 ^ 40 * 3016991 * 2
def baseEnd_3016991 : Nat := 516388837762970247512539

theorem tailTrace_3016991 : CollatzResearch.WordTrace tailWord_3016991 prefixEnd_3016991 516388837762970247512539 := by
  unfold tailWord_3016991
  simp only [CollatzResearch.WordTrace]
  refine ⟨110038701812964342885882827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73359134541976228590588551 110038701812964342885882827)
  ·
    refine ⟨165058052719446514328824241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110038701812964342885882827 165058052719446514328824241)
    ·
      refine ⟨123793539539584885746618181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165058052719446514328824241 123793539539584885746618181)
      ·
        refine ⟨23211288663672166077490909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123793539539584885746618181 23211288663672166077490909)
        ·
          refine ⟨8704233248877062279059091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23211288663672166077490909 8704233248877062279059091)
          ·
            refine ⟨13056349873315593418588637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8704233248877062279059091 13056349873315593418588637)
            ·
              refine ⟨4896131202493347531970739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13056349873315593418588637 4896131202493347531970739)
              ·
                refine ⟨7344196803740021297956109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4896131202493347531970739 7344196803740021297956109)
                ·
                  refine ⟨2754073801402507986733541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7344196803740021297956109 2754073801402507986733541)
                  ·
                    refine ⟨516388837762970247512539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2754073801402507986733541 516388837762970247512539)
                    ·
                      rfl

theorem cell23_3016991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 4].length) (baseStart_3016991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3016991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3016991 prefixEnd_3016991 := by exact prefixLift 3016991
  have htrace : WordTrace (prefixWord ++ tailWord_3016991) baseStart_3016991 baseEnd_3016991 := by
    simpa [prefixWord, tailWord_3016991, baseEnd_3016991] using wordTrace_append hprefix tailTrace_3016991
  have hstable : (prefixWord ++ tailWord_3016991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3016991).length < 2 ^ (prefixWord ++ tailWord_3016991).sum := by decide
  have hdescent : baseEnd_3016991 < baseStart_3016991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3016991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017007 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_3017007 : Nat := 118140960795 + 3017007 * 2 ^ 59
def prefixEnd_3017007 : Nat := 4983230072969 + 3 ^ 40 * 3017007 * 2
def baseEnd_3017007 : Nat := 1549174728979382679937543

theorem tailTrace_3017007 : CollatzResearch.WordTrace tailWord_3017007 prefixEnd_3017007 1549174728979382679937543 := by
  unfold tailWord_3017007
  simp only [CollatzResearch.WordTrace]
  refine ⟨110039285380906377618465275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73359523587270918412310183 110039285380906377618465275)
  ·
    refine ⟨165058928071359566427697913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110039285380906377618465275 165058928071359566427697913)
    ·
      refine ⟨123794196053519674820773435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165058928071359566427697913 123794196053519674820773435)
      ·
        refine ⟨185691294080279512231160153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123794196053519674820773435 185691294080279512231160153)
        ·
          refine ⟨139268470560209634173370115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185691294080279512231160153 139268470560209634173370115)
          ·
            refine ⟨208902705840314451260055173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139268470560209634173370115 208902705840314451260055173)
            ·
              refine ⟨39169257345058959611260345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208902705840314451260055173 39169257345058959611260345)
              ·
                refine ⟨29376943008794219708445259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39169257345058959611260345 29376943008794219708445259)
                ·
                  refine ⟨44065414513191329562667889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29376943008794219708445259 44065414513191329562667889)
                  ·
                    refine ⟨33049060884893497172000917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44065414513191329562667889 33049060884893497172000917)
                    ·
                      refine ⟨1549174728979382679937543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33049060884893497172000917 1549174728979382679937543)
                      ·
                        rfl

theorem cell23_3017007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_3017007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017007 prefixEnd_3017007 := by exact prefixLift 3017007
  have htrace : WordTrace (prefixWord ++ tailWord_3017007) baseStart_3017007 baseEnd_3017007 := by
    simpa [prefixWord, tailWord_3017007, baseEnd_3017007] using wordTrace_append hprefix tailTrace_3017007
  have hstable : (prefixWord ++ tailWord_3017007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017007).length < 2 ^ (prefixWord ++ tailWord_3017007).sum := by decide
  have hdescent : baseEnd_3017007 < baseStart_3017007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017084 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_3017084 : Nat := 118140960795 + 3017084 * 2 ^ 59
def prefixEnd_3017084 : Nat := 4983230072969 + 3 ^ 40 * 3017084 * 2
def baseEnd_3017084 : Nat := 1549214266989778878674689

theorem tailTrace_3017084 : CollatzResearch.WordTrace tailWord_3017084 prefixEnd_3017084 1549214266989778878674689 := by
  unfold tailWord_3017084
  simp only [CollatzResearch.WordTrace]
  refine ⟨55021046900813709884509153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73361395867751613179345537 55021046900813709884509153)
  ·
    refine ⟨41265785175610282413381865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55021046900813709884509153 41265785175610282413381865)
    ·
      refine ⟨30949338881707711810036399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41265785175610282413381865 30949338881707711810036399)
      ·
        refine ⟨46424008322561567715054599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30949338881707711810036399 46424008322561567715054599)
        ·
          refine ⟨69636012483842351572581899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46424008322561567715054599 69636012483842351572581899)
          ·
            refine ⟨104454018725763527358872849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69636012483842351572581899 104454018725763527358872849)
            ·
              refine ⟨78340514044322645519154637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104454018725763527358872849 78340514044322645519154637)
              ·
                refine ⟨29377692766620992069682989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78340514044322645519154637 29377692766620992069682989)
                ·
                  refine ⟨11016634787482872026131121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29377692766620992069682989 11016634787482872026131121)
                  ·
                    refine ⟨8262476090612154019598341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11016634787482872026131121 8262476090612154019598341)
                    ·
                      refine ⟨1549214266989778878674689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8262476090612154019598341 1549214266989778878674689)
                      ·
                        rfl

theorem cell23_3017084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_3017084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017084 prefixEnd_3017084 := by exact prefixLift 3017084
  have htrace : WordTrace (prefixWord ++ tailWord_3017084) baseStart_3017084 baseEnd_3017084 := by
    simpa [prefixWord, tailWord_3017084, baseEnd_3017084] using wordTrace_append hprefix tailTrace_3017084
  have hstable : (prefixWord ++ tailWord_3017084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017084).length < 2 ^ (prefixWord ++ tailWord_3017084).sum := by decide
  have hdescent : baseEnd_3017084 < baseStart_3017084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017108 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_3017108 : Nat := 118140960795 + 3017108 * 2 ^ 59
def prefixEnd_3017108 : Nat := 4983230072969 + 3 ^ 40 * 3017108 * 2
def baseEnd_3017108 : Nat := 1549226590525486784774579

theorem tailTrace_3017108 : CollatzResearch.WordTrace tailWord_3017108 prefixEnd_3017108 1549226590525486784774579 := by
  unfold tailWord_3017108
  simp only [CollatzResearch.WordTrace]
  refine ⟨55021484576770235933945989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73361979435693647911927985 55021484576770235933945989)
  ·
    refine ⟨10316528358144419237614873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55021484576770235933945989 10316528358144419237614873)
    ·
      refine ⟨7737396268608314428211155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10316528358144419237614873 7737396268608314428211155)
      ·
        refine ⟨11606094402912471642316733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737396268608314428211155 11606094402912471642316733)
        ·
          refine ⟨4352285401092176865868775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11606094402912471642316733 4352285401092176865868775)
          ·
            refine ⟨6528428101638265298803163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352285401092176865868775 6528428101638265298803163)
            ·
              refine ⟨9792642152457397948204745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6528428101638265298803163 9792642152457397948204745)
              ·
                refine ⟨7344481614343048461153559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9792642152457397948204745 7344481614343048461153559)
                ·
                  refine ⟨11016722421514572691730339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7344481614343048461153559 11016722421514572691730339)
                  ·
                    refine ⟨16525083632271859037595509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11016722421514572691730339 16525083632271859037595509)
                    ·
                      refine ⟨1549226590525486784774579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16525083632271859037595509 1549226590525486784774579)
                      ·
                        rfl

theorem cell23_3017108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_3017108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017108 prefixEnd_3017108 := by exact prefixLift 3017108
  have htrace : WordTrace (prefixWord ++ tailWord_3017108) baseStart_3017108 baseEnd_3017108 := by
    simpa [prefixWord, tailWord_3017108, baseEnd_3017108] using wordTrace_append hprefix tailTrace_3017108
  have hstable : (prefixWord ++ tailWord_3017108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017108).length < 2 ^ (prefixWord ++ tailWord_3017108).sum := by decide
  have hdescent : baseEnd_3017108 < baseStart_3017108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017118 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3017118 : Nat := 118140960795 + 3017118 * 2 ^ 59
def prefixEnd_3017118 : Nat := 4983230072969 + 3 ^ 40 * 3017118 * 2
def baseEnd_3017118 : Nat := 1549231725332031745649533

theorem tailTrace_3017118 : CollatzResearch.WordTrace tailWord_3017118 prefixEnd_3017118 1549231725332031745649533 := by
  unfold tailWord_3017118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13755416735438030446969501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73362222589002829050504005 13755416735438030446969501)
  ·
    refine ⟨5158281275789261417613563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13755416735438030446969501 5158281275789261417613563)
    ·
      refine ⟨7737421913683892126420345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5158281275789261417613563 7737421913683892126420345)
      ·
        refine ⟨5803066435262919094815259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7737421913683892126420345 5803066435262919094815259)
        ·
          refine ⟨8704599652894378642222889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5803066435262919094815259 8704599652894378642222889)
          ·
            refine ⟨6528449739670783981667167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8704599652894378642222889 6528449739670783981667167)
            ·
              refine ⟨9792674609506175972500751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6528449739670783981667167 9792674609506175972500751)
              ·
                refine ⟨14689011914259263958751127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9792674609506175972500751 14689011914259263958751127)
                ·
                  refine ⟨22033517871388895938126691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14689011914259263958751127 22033517871388895938126691)
                  ·
                    refine ⟨33050276807083343907190037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22033517871388895938126691 33050276807083343907190037)
                    ·
                      refine ⟨1549231725332031745649533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33050276807083343907190037 1549231725332031745649533)
                      ·
                        rfl

theorem cell23_3017118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3017118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017118 prefixEnd_3017118 := by exact prefixLift 3017118
  have htrace : WordTrace (prefixWord ++ tailWord_3017118) baseStart_3017118 baseEnd_3017118 := by
    simpa [prefixWord, tailWord_3017118, baseEnd_3017118] using wordTrace_append hprefix tailTrace_3017118
  have hstable : (prefixWord ++ tailWord_3017118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017118).length < 2 ^ (prefixWord ++ tailWord_3017118).sum := by decide
  have hdescent : baseEnd_3017118 < baseStart_3017118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017124 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_3017124 : Nat := 118140960795 + 3017124 * 2 ^ 59
def prefixEnd_3017124 : Nat := 4983230072969 + 3 ^ 40 * 3017124 * 2
def baseEnd_3017124 : Nat := 516411602071986240724835

theorem tailTrace_3017124 : CollatzResearch.WordTrace tailWord_3017124 prefixEnd_3017124 516411602071986240724835 := by
  unfold tailWord_3017124
  simp only [CollatzResearch.WordTrace]
  refine ⟨55021776360741253300237213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73362368480988337733649617 55021776360741253300237213)
  ·
    refine ⟨20633166135277969987588955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55021776360741253300237213 20633166135277969987588955)
    ·
      refine ⟨30949749202916954981383433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20633166135277969987588955 30949749202916954981383433)
      ·
        refine ⟨23212311902187716236037575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30949749202916954981383433 23212311902187716236037575)
        ·
          refine ⟨34818467853281574354056363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23212311902187716236037575 34818467853281574354056363)
          ·
            refine ⟨52227701779922361531084545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34818467853281574354056363 52227701779922361531084545)
            ·
              refine ⟨39170776334941771148313409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52227701779922361531084545 39170776334941771148313409)
              ·
                refine ⟨29378082251206328361235057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39170776334941771148313409 29378082251206328361235057)
                ·
                  refine ⟨22033561688404746270926293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29378082251206328361235057 22033561688404746270926293)
                  ·
                    refine ⟨516411602071986240724835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22033561688404746270926293 516411602071986240724835)
                    ·
                      rfl

theorem cell23_3017124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_3017124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017124 prefixEnd_3017124 := by exact prefixLift 3017124
  have htrace : WordTrace (prefixWord ++ tailWord_3017124) baseStart_3017124 baseEnd_3017124 := by
    simpa [prefixWord, tailWord_3017124, baseEnd_3017124] using wordTrace_append hprefix tailTrace_3017124
  have hstable : (prefixWord ++ tailWord_3017124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017124).length < 2 ^ (prefixWord ++ tailWord_3017124).sum := by decide
  have hdescent : baseEnd_3017124 < baseStart_3017124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017128 : List Nat := [2, 1, 6, 1, 1, 1, 4, 7]
def baseStart_3017128 : Nat := 118140960795 + 3017128 * 2 ^ 59
def prefixEnd_3017128 : Nat := 4983230072969 + 3 ^ 40 * 3017128 * 2
def baseEnd_3017128 : Nat := 57379142968095433574981

theorem tailTrace_3017128 : CollatzResearch.WordTrace tailWord_3017128 prefixEnd_3017128 57379142968095433574981 := by
  unfold tailWord_3017128
  simp only [CollatzResearch.WordTrace]
  refine ⟨55021849306734007641810019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73362465742312010189080025 55021849306734007641810019)
  ·
    refine ⟨82532773960101011462715029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55021849306734007641810019 82532773960101011462715029)
    ·
      refine ⟨3868723779379734912314767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82532773960101011462715029 3868723779379734912314767)
      ·
        refine ⟨5803085669069602368472151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868723779379734912314767 5803085669069602368472151)
        ·
          refine ⟨8704628503604403552708227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5803085669069602368472151 8704628503604403552708227)
          ·
            refine ⟨13056942755406605329062341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8704628503604403552708227 13056942755406605329062341)
            ·
              refine ⟨2448176766638738499199189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13056942755406605329062341 2448176766638738499199189)
              ·
                refine ⟨57379142968095433574981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2448176766638738499199189 57379142968095433574981)
                ·
                  rfl

theorem cell23_3017128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 7].length) (baseStart_3017128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017128 prefixEnd_3017128 := by exact prefixLift 3017128
  have htrace : WordTrace (prefixWord ++ tailWord_3017128) baseStart_3017128 baseEnd_3017128 := by
    simpa [prefixWord, tailWord_3017128, baseEnd_3017128] using wordTrace_append hprefix tailTrace_3017128
  have hstable : (prefixWord ++ tailWord_3017128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017128).length < 2 ^ (prefixWord ++ tailWord_3017128).sum := by decide
  have hdescent : baseEnd_3017128 < baseStart_3017128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017144 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_3017144 : Nat := 118140960795 + 3017144 * 2 ^ 59
def prefixEnd_3017144 : Nat := 4983230072969 + 3 ^ 40 * 3017144 * 2
def baseEnd_3017144 : Nat := 1549245075829048643924413

theorem tailTrace_3017144 : CollatzResearch.WordTrace tailWord_3017144 prefixEnd_3017144 1549245075829048643924413 := by
  unfold tailWord_3017144
  simp only [CollatzResearch.WordTrace]
  refine ⟨55022141090705025008101243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73362854787606700010801657 55022141090705025008101243)
  ·
    refine ⟨82533211636057537512151865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55022141090705025008101243 82533211636057537512151865)
    ·
      refine ⟨61899908727043153134113899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82533211636057537512151865 61899908727043153134113899)
      ·
        refine ⟨92849863090564729701170849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61899908727043153134113899 92849863090564729701170849)
        ·
          refine ⟨69637397317923547275878137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92849863090564729701170849 69637397317923547275878137)
          ·
            refine ⟨52228047988442660456908603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69637397317923547275878137 52228047988442660456908603)
            ·
              refine ⟨78342071982663990685362905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52228047988442660456908603 78342071982663990685362905)
              ·
                refine ⟨58756553986997993014022179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78342071982663990685362905 58756553986997993014022179)
                ·
                  refine ⟨88134830980496989521033269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58756553986997993014022179 88134830980496989521033269)
                  ·
                    refine ⟨8262640404421592767596869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88134830980496989521033269 8262640404421592767596869)
                    ·
                      refine ⟨1549245075829048643924413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8262640404421592767596869 1549245075829048643924413)
                      ·
                        rfl

theorem cell23_3017144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_3017144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017144 prefixEnd_3017144 := by exact prefixLift 3017144
  have htrace : WordTrace (prefixWord ++ tailWord_3017144) baseStart_3017144 baseEnd_3017144 := by
    simpa [prefixWord, tailWord_3017144, baseEnd_3017144] using wordTrace_append hprefix tailTrace_3017144
  have hstable : (prefixWord ++ tailWord_3017144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017144).length < 2 ^ (prefixWord ++ tailWord_3017144).sum := by decide
  have hdescent : baseEnd_3017144 < baseStart_3017144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017156 : List Nat := [2, 3, 3, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3017156 : Nat := 118140960795 + 3017156 * 2 ^ 59
def prefixEnd_3017156 : Nat := 4983230072969 + 3 ^ 40 * 3017156 * 2
def baseEnd_3017156 : Nat := 1549251237596902596974359

theorem tailTrace_3017156 : CollatzResearch.WordTrace tailWord_3017156 prefixEnd_3017156 1549251237596902596974359 := by
  unfold tailWord_3017156
  simp only [CollatzResearch.WordTrace]
  refine ⟨55022359928683288032819661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73363146571577717377092881 55022359928683288032819661)
  ·
    refine ⟨20633384973256233012307373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55022359928683288032819661 20633384973256233012307373)
    ·
      refine ⟨7737519364971087379615265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20633384973256233012307373 7737519364971087379615265)
      ·
        refine ⟨5803139523728315534711449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7737519364971087379615265 5803139523728315534711449)
        ·
          refine ⟨4352354642796236651033587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5803139523728315534711449 4352354642796236651033587)
          ·
            refine ⟨6528531964194354976550381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352354642796236651033587 6528531964194354976550381)
            ·
              refine ⟨2448199486572883116206393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6528531964194354976550381 2448199486572883116206393)
              ·
                refine ⟨1836149614929662337154795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448199486572883116206393 1836149614929662337154795)
                ·
                  refine ⟨2754224422394493505732193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836149614929662337154795 2754224422394493505732193)
                  ·
                    refine ⟨2065668316795870129299145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2754224422394493505732193 2065668316795870129299145)
                    ·
                      refine ⟨1549251237596902596974359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065668316795870129299145 1549251237596902596974359)
                      ·
                        rfl

theorem cell23_3017156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3017156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017156 prefixEnd_3017156 := by exact prefixLift 3017156
  have htrace : WordTrace (prefixWord ++ tailWord_3017156) baseStart_3017156 baseEnd_3017156 := by
    simpa [prefixWord, tailWord_3017156, baseEnd_3017156] using wordTrace_append hprefix tailTrace_3017156
  have hstable : (prefixWord ++ tailWord_3017156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017156).length < 2 ^ (prefixWord ++ tailWord_3017156).sum := by decide
  have hdescent : baseEnd_3017156 < baseStart_3017156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017172 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_3017172 : Nat := 118140960795 + 3017172 * 2 ^ 59
def prefixEnd_3017172 : Nat := 4983230072969 + 3 ^ 40 * 3017172 * 2
def baseEnd_3017172 : Nat := 1549259453287374534374285

theorem tailTrace_3017172 : CollatzResearch.WordTrace tailWord_3017172 prefixEnd_3017172 1549259453287374534374285 := by
  unfold tailWord_3017172
  simp only [CollatzResearch.WordTrace]
  refine ⟨55022651712654305399110885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73363535616872407198814513 55022651712654305399110885)
  ·
    refine ⟨10316747196122682262333291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55022651712654305399110885 10316747196122682262333291)
    ·
      refine ⟨15475120794184023393499937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10316747196122682262333291 15475120794184023393499937)
      ·
        refine ⟨11606340595638017545124953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15475120794184023393499937 11606340595638017545124953)
        ·
          refine ⟨8704755446728513158843715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11606340595638017545124953 8704755446728513158843715)
          ·
            refine ⟨13057133170092769738265573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8704755446728513158843715 13057133170092769738265573)
            ·
              refine ⟨2448212469392394325924795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13057133170092769738265573 2448212469392394325924795)
              ·
                refine ⟨3672318704088591488887193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2448212469392394325924795 3672318704088591488887193)
                ·
                  refine ⟨2754239028066443616665395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3672318704088591488887193 2754239028066443616665395)
                  ·
                    refine ⟨4131358542099665424998093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2754239028066443616665395 4131358542099665424998093)
                    ·
                      refine ⟨1549259453287374534374285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4131358542099665424998093 1549259453287374534374285)
                      ·
                        rfl

theorem cell23_3017172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_3017172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017172 prefixEnd_3017172 := by exact prefixLift 3017172
  have htrace : WordTrace (prefixWord ++ tailWord_3017172) baseStart_3017172 baseEnd_3017172 := by
    simpa [prefixWord, tailWord_3017172, baseEnd_3017172] using wordTrace_append hprefix tailTrace_3017172
  have hstable : (prefixWord ++ tailWord_3017172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017172).length < 2 ^ (prefixWord ++ tailWord_3017172).sum := by decide
  have hdescent : baseEnd_3017172 < baseStart_3017172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017178 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2]
def baseStart_3017178 : Nat := 118140960795 + 3017178 * 2 ^ 59
def prefixEnd_3017178 : Nat := 4983230072969 + 3 ^ 40 * 3017178 * 2
def baseEnd_3017178 : Nat := 1549262534171301510899257

theorem tailTrace_3017178 : CollatzResearch.WordTrace tailWord_3017178 prefixEnd_3017178 1549262534171301510899257 := by
  unfold tailWord_3017178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27511380565821718455735047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73363681508857915881960125 27511380565821718455735047)
  ·
    refine ⟨41267070848732577683602571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27511380565821718455735047 41267070848732577683602571)
    ·
      refine ⟨61900606273098866525403857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41267070848732577683602571 61900606273098866525403857)
      ·
        refine ⟨46425454704824149894052893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61900606273098866525403857 46425454704824149894052893)
        ·
          refine ⟨17409545514309056210269835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46425454704824149894052893 17409545514309056210269835)
          ·
            refine ⟨26114318271463584315404753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17409545514309056210269835 26114318271463584315404753)
            ·
              refine ⟨19585738703597688236553565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26114318271463584315404753 19585738703597688236553565)
              ·
                refine ⟨7344652013849133088707587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19585738703597688236553565 7344652013849133088707587)
                ·
                  refine ⟨11016978020773699633061381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7344652013849133088707587 11016978020773699633061381)
                  ·
                    refine ⟨2065683378895068681199009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11016978020773699633061381 2065683378895068681199009)
                    ·
                      refine ⟨1549262534171301510899257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065683378895068681199009 1549262534171301510899257)
                      ·
                        rfl

theorem cell23_3017178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_3017178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017178 prefixEnd_3017178 := by exact prefixLift 3017178
  have htrace : WordTrace (prefixWord ++ tailWord_3017178) baseStart_3017178 baseEnd_3017178 := by
    simpa [prefixWord, tailWord_3017178, baseEnd_3017178] using wordTrace_append hprefix tailTrace_3017178
  have hstable : (prefixWord ++ tailWord_3017178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017178).length < 2 ^ (prefixWord ++ tailWord_3017178).sum := by decide
  have hdescent : baseEnd_3017178 < baseStart_3017178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017181 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3017181 : Nat := 118140960795 + 3017181 * 2 ^ 59
def prefixEnd_3017181 : Nat := 4983230072969 + 3 ^ 40 * 3017181 * 2
def baseEnd_3017181 : Nat := 1549264074613264999161743

theorem tailTrace_3017181 : CollatzResearch.WordTrace tailWord_3017181 prefixEnd_3017181 1549264074613264999161743 := by
  unfold tailWord_3017181
  simp only [CollatzResearch.WordTrace]
  refine ⟨110045631682276005335299397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73363754454850670223532931 110045631682276005335299397)
  ·
    refine ⟨20633555940426751000368637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110045631682276005335299397 20633555940426751000368637)
    ·
      refine ⟨7737583477660031625138239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20633555940426751000368637 7737583477660031625138239)
      ·
        refine ⟨11606375216490047437707359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737583477660031625138239 11606375216490047437707359)
        ·
          refine ⟨17409562824735071156561039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11606375216490047437707359 17409562824735071156561039)
          ·
            refine ⟨26114344237102606734841559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17409562824735071156561039 26114344237102606734841559)
            ·
              refine ⟨39171516355653910102262339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26114344237102606734841559 39171516355653910102262339)
              ·
                refine ⟨58757274533480865153393509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39171516355653910102262339 58757274533480865153393509)
                ·
                  refine ⟨11016988975027662216261283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58757274533480865153393509 11016988975027662216261283)
                  ·
                    refine ⟨16525483462541493324391925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11016988975027662216261283 16525483462541493324391925)
                    ·
                      refine ⟨1549264074613264999161743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16525483462541493324391925 1549264074613264999161743)
                      ·
                        rfl

theorem cell23_3017181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3017181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017181 prefixEnd_3017181 := by exact prefixLift 3017181
  have htrace : WordTrace (prefixWord ++ tailWord_3017181) baseStart_3017181 baseEnd_3017181 := by
    simpa [prefixWord, tailWord_3017181, baseEnd_3017181] using wordTrace_append hprefix tailTrace_3017181
  have hstable : (prefixWord ++ tailWord_3017181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017181).length < 2 ^ (prefixWord ++ tailWord_3017181).sum := by decide
  have hdescent : baseEnd_3017181 < baseStart_3017181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017184 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 9]
def baseStart_3017184 : Nat := 118140960795 + 3017184 * 2 ^ 59
def prefixEnd_3017184 : Nat := 4983230072969 + 3 ^ 40 * 3017184 * 2
def baseEnd_3017184 : Nat := 172140623895025387491581

theorem tailTrace_3017184 : CollatzResearch.WordTrace tailWord_3017184 prefixEnd_3017184 172140623895025387491581 := by
  unfold tailWord_3017184
  simp only [CollatzResearch.WordTrace]
  refine ⟨55022870550632568423829303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73363827400843424565105737 55022870550632568423829303)
  ·
    refine ⟨82534305825948852635743955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55022870550632568423829303 82534305825948852635743955)
    ·
      refine ⟨123801458738923278953615933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82534305825948852635743955 123801458738923278953615933)
      ·
        refine ⟨46425547027096229607605975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123801458738923278953615933 46425547027096229607605975)
        ·
          refine ⟨69638320540644344411408963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46425547027096229607605975 69638320540644344411408963)
          ·
            refine ⟨104457480810966516617113445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69638320540644344411408963 104457480810966516617113445)
            ·
              refine ⟨19585777652056221865708771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104457480810966516617113445 19585777652056221865708771)
              ·
                refine ⟨29378666478084332798563157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19585777652056221865708771 29378666478084332798563157)
                ·
                  refine ⟨172140623895025387491581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29378666478084332798563157 172140623895025387491581)
                  ·
                    rfl

theorem cell23_3017184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 9].length) (baseStart_3017184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017184 prefixEnd_3017184 := by exact prefixLift 3017184
  have htrace : WordTrace (prefixWord ++ tailWord_3017184) baseStart_3017184 baseEnd_3017184 := by
    simpa [prefixWord, tailWord_3017184, baseEnd_3017184] using wordTrace_append hprefix tailTrace_3017184
  have hstable : (prefixWord ++ tailWord_3017184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017184).length < 2 ^ (prefixWord ++ tailWord_3017184).sum := by decide
  have hdescent : baseEnd_3017184 < baseStart_3017184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017222 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3017222 : Nat := 118140960795 + 3017222 * 2 ^ 59
def prefixEnd_3017222 : Nat := 4983230072969 + 3 ^ 40 * 3017222 * 2
def baseEnd_3017222 : Nat := 516428375773366446249685

theorem tailTrace_3017222 : CollatzResearch.WordTrace tailWord_3017222 prefixEnd_3017222 516428375773366446249685 := by
  unfold tailWord_3017222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3438972721097733416798185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73364751383418312891694613 3438972721097733416798185)
  ·
    refine ⟨2579229540823300062598639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3438972721097733416798185 2579229540823300062598639)
    ·
      refine ⟨3868844311234950093897959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2579229540823300062598639 3868844311234950093897959)
      ·
        refine ⟨5803266466852425140846939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868844311234950093897959 5803266466852425140846939)
        ·
          refine ⟨8704899700278637711270409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5803266466852425140846939 8704899700278637711270409)
          ·
            refine ⟨6528674775208978283452807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8704899700278637711270409 6528674775208978283452807)
            ·
              refine ⟨9793012162813467425179211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6528674775208978283452807 9793012162813467425179211)
              ·
                refine ⟨14689518244220201137768817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9793012162813467425179211 14689518244220201137768817)
                ·
                  refine ⟨11017138683165150853326613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14689518244220201137768817 11017138683165150853326613)
                  ·
                    refine ⟨516428375773366446249685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11017138683165150853326613 516428375773366446249685)
                    ·
                      rfl

theorem cell23_3017222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3017222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017222 prefixEnd_3017222 := by exact prefixLift 3017222
  have htrace : WordTrace (prefixWord ++ tailWord_3017222) baseStart_3017222 baseEnd_3017222 := by
    simpa [prefixWord, tailWord_3017222, baseEnd_3017222] using wordTrace_append hprefix tailTrace_3017222
  have hstable : (prefixWord ++ tailWord_3017222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017222).length < 2 ^ (prefixWord ++ tailWord_3017222).sum := by decide
  have hdescent : baseEnd_3017222 < baseStart_3017222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017228 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_3017228 : Nat := 118140960795 + 3017228 * 2 ^ 59
def prefixEnd_3017228 : Nat := 4983230072969 + 3 ^ 40 * 3017228 * 2
def baseEnd_3017228 : Nat := 1549288208204026315274027

theorem tailTrace_3017228 : CollatzResearch.WordTrace tailWord_3017228 prefixEnd_3017228 1549288208204026315274027 := by
  unfold tailWord_3017228
  simp only [CollatzResearch.WordTrace]
  refine ⟨55023672956552866181130169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73364897275403821574840225 55023672956552866181130169)
  ·
    refine ⟨41267754717414649635847627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55023672956552866181130169 41267754717414649635847627)
    ·
      refine ⟨61901632076121974453771441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41267754717414649635847627 61901632076121974453771441)
      ·
        refine ⟨46426224057091480840328581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61901632076121974453771441 46426224057091480840328581)
        ·
          refine ⟨8704917010704652657561609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46426224057091480840328581 8704917010704652657561609)
          ·
            refine ⟨6528687758028489493171207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8704917010704652657561609 6528687758028489493171207)
            ·
              refine ⟨9793031637042734239756811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6528687758028489493171207 9793031637042734239756811)
              ·
                refine ⟨14689547455564101359635217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9793031637042734239756811 14689547455564101359635217)
                ·
                  refine ⟨11017160591673076019726413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14689547455564101359635217 11017160591673076019726413)
                  ·
                    refine ⟨4131435221877403507397405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11017160591673076019726413 4131435221877403507397405)
                    ·
                      refine ⟨1549288208204026315274027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4131435221877403507397405 1549288208204026315274027)
                      ·
                        rfl

theorem cell23_3017228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_3017228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017228 prefixEnd_3017228 := by exact prefixLift 3017228
  have htrace : WordTrace (prefixWord ++ tailWord_3017228) baseStart_3017228 baseEnd_3017228 := by
    simpa [prefixWord, tailWord_3017228, baseEnd_3017228] using wordTrace_append hprefix tailTrace_3017228
  have hstable : (prefixWord ++ tailWord_3017228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017228).length < 2 ^ (prefixWord ++ tailWord_3017228).sum := by decide
  have hdescent : baseEnd_3017228 < baseStart_3017228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017229 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3017229 : Nat := 118140960795 + 3017229 * 2 ^ 59
def prefixEnd_3017229 : Nat := 4983230072969 + 3 ^ 40 * 3017229 * 2
def baseEnd_3017229 : Nat := 1549288721684680811361523

theorem tailTrace_3017229 : CollatzResearch.WordTrace tailWord_3017229 prefixEnd_3017229 1549288721684680811361523 := by
  unfold tailWord_3017229
  simp only [CollatzResearch.WordTrace]
  refine ⟨110047382386102109533046741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73364921590734739688697827 110047382386102109533046741)
  ·
    refine ⟨2579235524674268192180783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 110047382386102109533046741 2579235524674268192180783)
    ·
      refine ⟨3868853287011402288271175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2579235524674268192180783 3868853287011402288271175)
      ·
        refine ⟨5803279930517103432406763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868853287011402288271175 5803279930517103432406763)
        ·
          refine ⟨8704919895775655148610145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5803279930517103432406763 8704919895775655148610145)
          ·
            refine ⟨6528689921831741361457609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8704919895775655148610145 6528689921831741361457609)
            ·
              refine ⟨4896517441373806021093207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6528689921831741361457609 4896517441373806021093207)
              ·
                refine ⟨7344776162060709031639811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4896517441373806021093207 7344776162060709031639811)
                ·
                  refine ⟨11017164243091063547459717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7344776162060709031639811 11017164243091063547459717)
                  ·
                    refine ⟨2065718295579574415148697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11017164243091063547459717 2065718295579574415148697)
                    ·
                      refine ⟨1549288721684680811361523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065718295579574415148697 1549288721684680811361523)
                      ·
                        rfl

theorem cell23_3017229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3017229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017229 prefixEnd_3017229 := by exact prefixLift 3017229
  have htrace : WordTrace (prefixWord ++ tailWord_3017229) baseStart_3017229 baseEnd_3017229 := by
    simpa [prefixWord, tailWord_3017229, baseEnd_3017229] using wordTrace_append hprefix tailTrace_3017229
  have hstable : (prefixWord ++ tailWord_3017229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017229).length < 2 ^ (prefixWord ++ tailWord_3017229).sum := by decide
  have hdescent : baseEnd_3017229 < baseStart_3017229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017248 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 1, 7]
def baseStart_3017248 : Nat := 118140960795 + 3017248 * 2 ^ 59
def prefixEnd_3017248 : Nat := 4983230072969 + 3 ^ 40 * 3017248 * 2
def baseEnd_3017248 : Nat := 516432825939038745674645

theorem tailTrace_3017248 : CollatzResearch.WordTrace tailWord_3017248 prefixEnd_3017248 516432825939038745674645 := by
  unfold tailWord_3017248
  simp only [CollatzResearch.WordTrace]
  refine ⟨55024037686516637888994199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73365383582022183851992265 55024037686516637888994199)
  ·
    refine ⟨82536056529774956833491299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55024037686516637888994199 82536056529774956833491299)
    ·
      refine ⟨123804084794662435250236949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82536056529774956833491299 123804084794662435250236949)
      ·
        refine ⟨5803316474749801652354857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 123804084794662435250236949 5803316474749801652354857)
        ·
          refine ⟨4352487356062351239266143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5803316474749801652354857 4352487356062351239266143)
          ·
            refine ⟨6528731034093526858899215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352487356062351239266143 6528731034093526858899215)
            ·
              refine ⟨9793096551140290288348823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6528731034093526858899215 9793096551140290288348823)
              ·
                refine ⟨14689644826710435432523235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9793096551140290288348823 14689644826710435432523235)
                ·
                  refine ⟨22034467240065653148784853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14689644826710435432523235 22034467240065653148784853)
                  ·
                    refine ⟨516432825939038745674645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22034467240065653148784853 516432825939038745674645)
                    ·
                      rfl

theorem cell23_3017248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_3017248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017248 prefixEnd_3017248 := by exact prefixLift 3017248
  have htrace : WordTrace (prefixWord ++ tailWord_3017248) baseStart_3017248 baseEnd_3017248 := by
    simpa [prefixWord, tailWord_3017248, baseEnd_3017248] using wordTrace_append hprefix tailTrace_3017248
  have hstable : (prefixWord ++ tailWord_3017248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017248).length < 2 ^ (prefixWord ++ tailWord_3017248).sum := by decide
  have hdescent : baseEnd_3017248 < baseStart_3017248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017252 : List Nat := [2, 3, 1, 5, 1, 1, 2, 3, 5]
def baseStart_3017252 : Nat := 118140960795 + 3017252 * 2 ^ 59
def prefixEnd_3017252 : Nat := 4983230072969 + 3 ^ 40 * 3017252 * 2
def baseEnd_3017252 : Nat := 172144503526637135708213

theorem tailTrace_3017252 : CollatzResearch.WordTrace tailWord_3017252 prefixEnd_3017252 172144503526637135708213 := by
  unfold tailWord_3017252
  simp only [CollatzResearch.WordTrace]
  refine ⟨55024110632509392230567005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73365480843345856307422673 55024110632509392230567005)
  ·
    refine ⟨20634041487191022086462627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55024110632509392230567005 20634041487191022086462627)
    ·
      refine ⟨30951062230786533129693941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20634041487191022086462627 30951062230786533129693941)
      ·
        refine ⟨2901662084136237480908807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30951062230786533129693941 2901662084136237480908807)
        ·
          refine ⟨4352493126204356221363211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901662084136237480908807 4352493126204356221363211)
          ·
            refine ⟨6528739689306534332044817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352493126204356221363211 6528739689306534332044817)
            ·
              refine ⟨4896554766979900749033613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6528739689306534332044817 4896554766979900749033613)
              ·
                refine ⟨1836208037617462780887605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4896554766979900749033613 1836208037617462780887605)
                ·
                  refine ⟨172144503526637135708213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1836208037617462780887605 172144503526637135708213)
                  ·
                    rfl

theorem cell23_3017252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_3017252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017252 prefixEnd_3017252 := by exact prefixLift 3017252
  have htrace : WordTrace (prefixWord ++ tailWord_3017252) baseStart_3017252 baseEnd_3017252 := by
    simpa [prefixWord, tailWord_3017252, baseEnd_3017252] using wordTrace_append hprefix tailTrace_3017252
  have hstable : (prefixWord ++ tailWord_3017252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017252).length < 2 ^ (prefixWord ++ tailWord_3017252).sum := by decide
  have hdescent : baseEnd_3017252 < baseStart_3017252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017291 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 6]
def baseStart_3017291 : Nat := 118140960795 + 3017291 * 2 ^ 59
def prefixEnd_3017291 : Nat := 4983230072969 + 3 ^ 40 * 3017291 * 2
def baseEnd_3017291 : Nat := 172146728609473285420693

theorem tailTrace_3017291 : CollatzResearch.WordTrace tailWord_3017291 prefixEnd_3017291 172146728609473285420693 := by
  unfold tailWord_3017291
  simp only [CollatzResearch.WordTrace]
  refine ⟨110049643711877494121803727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73366429141251662747869151 110049643711877494121803727)
  ·
    refine ⟨165074465567816241182705591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110049643711877494121803727 165074465567816241182705591)
    ·
      refine ⟨247611698351724361774058387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165074465567816241182705591 247611698351724361774058387)
      ·
        refine ⟨371417547527586542661087581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247611698351724361774058387 371417547527586542661087581)
        ·
          refine ⟨139281580322844953497907843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371417547527586542661087581 139281580322844953497907843)
          ·
            refine ⟨208922370484267430246861765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139281580322844953497907843 208922370484267430246861765)
            ·
              refine ⟨39172944465800143171286581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208922370484267430246861765 39172944465800143171286581)
              ·
                refine ⟨3672463543668763422308117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39172944465800143171286581 3672463543668763422308117)
                ·
                  refine ⟨172146728609473285420693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3672463543668763422308117 172146728609473285420693)
                  ·
                    rfl

theorem cell23_3017291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 6].length) (baseStart_3017291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017291 prefixEnd_3017291 := by exact prefixLift 3017291
  have htrace : WordTrace (prefixWord ++ tailWord_3017291) baseStart_3017291 baseEnd_3017291 := by
    simpa [prefixWord, tailWord_3017291, baseEnd_3017291] using wordTrace_append hprefix tailTrace_3017291
  have hstable : (prefixWord ++ tailWord_3017291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017291).length < 2 ^ (prefixWord ++ tailWord_3017291).sum := by decide
  have hdescent : baseEnd_3017291 < baseStart_3017291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017321 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 5, 5]
def baseStart_3017321 : Nat := 118140960795 + 3017321 * 2 ^ 59
def prefixEnd_3017321 : Nat := 4983230072969 + 3 ^ 40 * 3017321 * 2
def baseEnd_3017321 : Nat := 516445320634964817137033

theorem tailTrace_3017321 : CollatzResearch.WordTrace tailWord_3017321 prefixEnd_3017321 516445320634964817137033 := by
  unfold tailWord_3017321
  simp only [CollatzResearch.WordTrace]
  refine ⟨110050737901768809245395817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73367158601179206163597211 110050737901768809245395817)
  ·
    refine ⟨82538053426326606934046863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110050737901768809245395817 82538053426326606934046863)
    ·
      refine ⟨123807080139489910401070295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82538053426326606934046863 123807080139489910401070295)
      ·
        refine ⟨185710620209234865601605443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123807080139489910401070295 185710620209234865601605443)
        ·
          refine ⟨278565930313852298402408165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185710620209234865601605443 278565930313852298402408165)
          ·
            refine ⟨52231111933847305950451531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278565930313852298402408165 52231111933847305950451531)
            ·
              refine ⟨78346667900770958925677297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52231111933847305950451531 78346667900770958925677297)
              ·
                refine ⟨58760000925578219194257973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78346667900770958925677297 58760000925578219194257973)
                ·
                  refine ⟨5508750086772958049461685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58760000925578219194257973 5508750086772958049461685)
                  ·
                    refine ⟨516445320634964817137033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5508750086772958049461685 516445320634964817137033)
                    ·
                      rfl

theorem cell23_3017321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_3017321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017321 prefixEnd_3017321 := by exact prefixLift 3017321
  have htrace : WordTrace (prefixWord ++ tailWord_3017321) baseStart_3017321 baseEnd_3017321 := by
    simpa [prefixWord, tailWord_3017321, baseEnd_3017321] using wordTrace_append hprefix tailTrace_3017321
  have hstable : (prefixWord ++ tailWord_3017321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017321).length < 2 ^ (prefixWord ++ tailWord_3017321).sum := by decide
  have hdescent : baseEnd_3017321 < baseStart_3017321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017335 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 3]
def baseStart_3017335 : Nat := 118140960795 + 3017335 * 2 ^ 59
def prefixEnd_3017335 : Nat := 4983230072969 + 3 ^ 40 * 3017335 * 2
def baseEnd_3017335 : Nat := 1549343150634057396636035

theorem tailTrace_3017335 : CollatzResearch.WordTrace tailWord_3017335 prefixEnd_3017335 1549343150634057396636035 := by
  unfold tailWord_3017335
  simp only [CollatzResearch.WordTrace]
  refine ⟨110051248523718089636405459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73367499015812059757603639 110051248523718089636405459)
  ·
    refine ⟨165076872785577134454608189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110051248523718089636405459 165076872785577134454608189)
    ·
      refine ⟨61903827294591425420478071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165076872785577134454608189 61903827294591425420478071)
      ·
        refine ⟨92855740941887138130717107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61903827294591425420478071 92855740941887138130717107)
        ·
          refine ⟨139283611412830707196075661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92855740941887138130717107 139283611412830707196075661)
          ·
            refine ⟨52231354279811515198528373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139283611412830707196075661 52231354279811515198528373)
            ·
              refine ⟨4896689463732329549862035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52231354279811515198528373 4896689463732329549862035)
              ·
                refine ⟨7345034195598494324793053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4896689463732329549862035 7345034195598494324793053)
                ·
                  refine ⟨2754387823349435371797395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7345034195598494324793053 2754387823349435371797395)
                  ·
                    refine ⟨4131581735024153057696093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2754387823349435371797395 4131581735024153057696093)
                    ·
                      refine ⟨1549343150634057396636035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4131581735024153057696093 1549343150634057396636035)
                      ·
                        rfl

theorem cell23_3017335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_3017335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017335 prefixEnd_3017335 := by exact prefixLift 3017335
  have htrace : WordTrace (prefixWord ++ tailWord_3017335) baseStart_3017335 baseEnd_3017335 := by
    simpa [prefixWord, tailWord_3017335, baseEnd_3017335] using wordTrace_append hprefix tailTrace_3017335
  have hstable : (prefixWord ++ tailWord_3017335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017335).length < 2 ^ (prefixWord ++ tailWord_3017335).sum := by decide
  have hdescent : baseEnd_3017335 < baseStart_3017335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017345 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_3017345 : Nat := 118140960795 + 3017345 * 2 ^ 59
def prefixEnd_3017345 : Nat := 4983230072969 + 3 ^ 40 * 3017345 * 2
def baseEnd_3017345 : Nat := 1549348285440602357510989

theorem tailTrace_3017345 : CollatzResearch.WordTrace tailWord_3017345 prefixEnd_3017345 1549348285440602357510989 := by
  unfold tailWord_3017345
  simp only [CollatzResearch.WordTrace]
  refine ⟨110051613253681861344269489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73367742169121240896179659 110051613253681861344269489)
  ·
    refine ⟨82538709940261396008202117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110051613253681861344269489 82538709940261396008202117)
    ·
      refine ⟨15476008113799011751537897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82538709940261396008202117 15476008113799011751537897)
      ·
        refine ⟨11607006085349258813653423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15476008113799011751537897 11607006085349258813653423)
        ·
          refine ⟨17410509128023888220480135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11607006085349258813653423 17410509128023888220480135)
          ·
            refine ⟨26115763692035832330720203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17410509128023888220480135 26115763692035832330720203)
            ·
              refine ⟨39173645538053748496080305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26115763692035832330720203 39173645538053748496080305)
              ·
                refine ⟨29380234153540311372060229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39173645538053748496080305 29380234153540311372060229)
                ·
                  refine ⟨5508793903788808382261293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29380234153540311372060229 5508793903788808382261293)
                  ·
                    refine ⟨2065797713920803143347985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5508793903788808382261293 2065797713920803143347985)
                    ·
                      refine ⟨1549348285440602357510989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065797713920803143347985 1549348285440602357510989)
                      ·
                        rfl

theorem cell23_3017345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_3017345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017345 prefixEnd_3017345 := by exact prefixLift 3017345
  have htrace : WordTrace (prefixWord ++ tailWord_3017345) baseStart_3017345 baseEnd_3017345 := by
    simpa [prefixWord, tailWord_3017345, baseEnd_3017345] using wordTrace_append hprefix tailTrace_3017345
  have hstable : (prefixWord ++ tailWord_3017345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017345).length < 2 ^ (prefixWord ++ tailWord_3017345).sum := by decide
  have hdescent : baseEnd_3017345 < baseStart_3017345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017362 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_3017362 : Nat := 118140960795 + 3017362 * 2 ^ 59
def prefixEnd_3017362 : Nat := 4983230072969 + 3 ^ 40 * 3017362 * 2
def baseEnd_3017362 : Nat := 1549357014611728790998411

theorem tailTrace_3017362 : CollatzResearch.WordTrace tailWord_3017362 prefixEnd_3017362 1549357014611728790998411 := by
  unfold tailWord_3017362
  simp only [CollatzResearch.WordTrace]
  refine ⟨27513058323655068311909585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73368155529746848831758893 27513058323655068311909585)
  ·
    refine ⟨20634793742741301233932189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27513058323655068311909585 20634793742741301233932189)
    ·
      refine ⟨7738047653527987962724571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20634793742741301233932189 7738047653527987962724571)
      ·
        refine ⟨11607071480291981944086857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7738047653527987962724571 11607071480291981944086857)
        ·
          refine ⟨8705303610218986458065143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11607071480291981944086857 8705303610218986458065143)
          ·
            refine ⟨13057955415328479687097715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8705303610218986458065143 13057955415328479687097715)
            ·
              refine ⟨19586933122992719530646573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13057955415328479687097715 19586933122992719530646573)
              ·
                refine ⟨7345099921122269823992465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19586933122992719530646573 7345099921122269823992465)
                ·
                  refine ⟨5508824940841702367994349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7345099921122269823992465 5508824940841702367994349)
                  ·
                    refine ⟨2065809352815638387997881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5508824940841702367994349 2065809352815638387997881)
                    ·
                      refine ⟨1549357014611728790998411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065809352815638387997881 1549357014611728790998411)
                      ·
                        rfl

theorem cell23_3017362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_3017362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017362 prefixEnd_3017362 := by exact prefixLift 3017362
  have htrace : WordTrace (prefixWord ++ tailWord_3017362) baseStart_3017362 baseEnd_3017362 := by
    simpa [prefixWord, tailWord_3017362, baseEnd_3017362] using wordTrace_append hprefix tailTrace_3017362
  have hstable : (prefixWord ++ tailWord_3017362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017362).length < 2 ^ (prefixWord ++ tailWord_3017362).sum := by decide
  have hdescent : baseEnd_3017362 < baseStart_3017362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017368 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 1, 6]
def baseStart_3017368 : Nat := 118140960795 + 3017368 * 2 ^ 59
def prefixEnd_3017368 : Nat := 4983230072969 + 3 ^ 40 * 3017368 * 2
def baseEnd_3017368 : Nat := 516453365165218589174461

theorem tailTrace_3017368 : CollatzResearch.WordTrace tailWord_3017368 prefixEnd_3017368 516453365165218589174461 := by
  unfold tailWord_3017368
  simp only [CollatzResearch.WordTrace]
  refine ⟨55026226066299268136178379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73368301421732357514904505 55026226066299268136178379)
  ·
    refine ⟨82539339099448902204267569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55026226066299268136178379 82539339099448902204267569)
    ·
      refine ⟨61904504324586676653200677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82539339099448902204267569 61904504324586676653200677)
      ·
        refine ⟨11607094560860001872475127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61904504324586676653200677 11607094560860001872475127)
        ·
          refine ⟨17410641841290002808712691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11607094560860001872475127 17410641841290002808712691)
          ·
            refine ⟨26115962761935004213069037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17410641841290002808712691 26115962761935004213069037)
            ·
              refine ⟨9793486035725626579900889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26115962761935004213069037 9793486035725626579900889)
              ·
                refine ⟨7345114526794219934925667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9793486035725626579900889 7345114526794219934925667)
                ·
                  refine ⟨11017671790191329902388501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7345114526794219934925667 11017671790191329902388501)
                  ·
                    refine ⟨516453365165218589174461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11017671790191329902388501 516453365165218589174461)
                    ·
                      rfl

theorem cell23_3017368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_3017368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017368 prefixEnd_3017368 := by exact prefixLift 3017368
  have htrace : WordTrace (prefixWord ++ tailWord_3017368) baseStart_3017368 baseEnd_3017368 := by
    simpa [prefixWord, tailWord_3017368, baseEnd_3017368] using wordTrace_append hprefix tailTrace_3017368
  have hstable : (prefixWord ++ tailWord_3017368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017368).length < 2 ^ (prefixWord ++ tailWord_3017368).sum := by decide
  have hdescent : baseEnd_3017368 < baseStart_3017368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017372 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_3017372 : Nat := 118140960795 + 3017372 * 2 ^ 59
def prefixEnd_3017372 : Nat := 4983230072969 + 3 ^ 40 * 3017372 * 2
def baseEnd_3017372 : Nat := 516454049806091250624455

theorem tailTrace_3017372 : CollatzResearch.WordTrace tailWord_3017372 prefixEnd_3017372 516454049806091250624455 := by
  unfold tailWord_3017372
  simp only [CollatzResearch.WordTrace]
  refine ⟨55026299012292022477751185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73368398683056029970334913 55026299012292022477751185)
  ·
    refine ⟨41269724259219016858313389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55026299012292022477751185 41269724259219016858313389)
    ·
      refine ⟨15476146597207131321867521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41269724259219016858313389 15476146597207131321867521)
      ·
        refine ⟨11607109947905348491400641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15476146597207131321867521 11607109947905348491400641)
        ·
          refine ⟨8705332460929011368550481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11607109947905348491400641 8705332460929011368550481)
          ·
            refine ⟨6528999345696758526412861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8705332460929011368550481 6528999345696758526412861)
            ·
              refine ⟨2448374754636284447404823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6528999345696758526412861 2448374754636284447404823)
              ·
                refine ⟨3672562131954426671107235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2448374754636284447404823 3672562131954426671107235)
                ·
                  refine ⟨5508843197931640006660853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672562131954426671107235 5508843197931640006660853)
                  ·
                    refine ⟨516454049806091250624455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5508843197931640006660853 516454049806091250624455)
                    ·
                      rfl

theorem cell23_3017372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_3017372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017372 prefixEnd_3017372 := by exact prefixLift 3017372
  have htrace : WordTrace (prefixWord ++ tailWord_3017372) baseStart_3017372 baseEnd_3017372 := by
    simpa [prefixWord, tailWord_3017372, baseEnd_3017372] using wordTrace_append hprefix tailTrace_3017372
  have hstable : (prefixWord ++ tailWord_3017372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017372).length < 2 ^ (prefixWord ++ tailWord_3017372).sum := by decide
  have hdescent : baseEnd_3017372 < baseStart_3017372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017405 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_3017405 : Nat := 118140960795 + 3017405 * 2 ^ 59
def prefixEnd_3017405 : Nat := 4983230072969 + 3 ^ 40 * 3017405 * 2
def baseEnd_3017405 : Nat := 1549379094279872122760713

theorem tailTrace_3017405 : CollatzResearch.WordTrace tailWord_3017405 prefixEnd_3017405 1549379094279872122760713 := by
  unfold tailWord_3017405
  simp only [CollatzResearch.WordTrace]
  refine ⟨110053801633464491591453669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73369201088976327727635779 110053801633464491591453669)
  ·
    refine ⟨20635087806274592173397563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110053801633464491591453669 20635087806274592173397563)
    ·
      refine ⟨30952631709411888260096345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20635087806274592173397563 30952631709411888260096345)
      ·
        refine ⟨23214473782058916195072259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30952631709411888260096345 23214473782058916195072259)
        ·
          refine ⟨34821710673088374292608389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23214473782058916195072259 34821710673088374292608389)
          ·
            refine ⟨6529070751204070179864073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34821710673088374292608389 6529070751204070179864073)
            ·
              refine ⟨4896803063403052634898055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6529070751204070179864073 4896803063403052634898055)
              ·
                refine ⟨7345204595104578952347083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4896803063403052634898055 7345204595104578952347083)
                ·
                  refine ⟨11017806892656868428520625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7345204595104578952347083 11017806892656868428520625)
                  ·
                    refine ⟨8263355169492651321390469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11017806892656868428520625 8263355169492651321390469)
                    ·
                      refine ⟨1549379094279872122760713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8263355169492651321390469 1549379094279872122760713)
                      ·
                        rfl

theorem cell23_3017405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_3017405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017405 prefixEnd_3017405 := by exact prefixLift 3017405
  have htrace : WordTrace (prefixWord ++ tailWord_3017405) baseStart_3017405 baseEnd_3017405 := by
    simpa [prefixWord, tailWord_3017405, baseEnd_3017405] using wordTrace_append hprefix tailTrace_3017405
  have hstable : (prefixWord ++ tailWord_3017405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017405).length < 2 ^ (prefixWord ++ tailWord_3017405).sum := by decide
  have hdescent : baseEnd_3017405 < baseStart_3017405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017425 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 3]
def baseStart_3017425 : Nat := 118140960795 + 3017425 * 2 ^ 59
def prefixEnd_3017425 : Nat := 4983230072969 + 3 ^ 40 * 3017425 * 2
def baseEnd_3017425 : Nat := 1549389363892962044510621

theorem tailTrace_3017425 : CollatzResearch.WordTrace tailWord_3017425 prefixEnd_3017425 1549389363892962044510621 := by
  unfold tailWord_3017425
  simp only [CollatzResearch.WordTrace]
  refine ⟨110054531093392035007181729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73369687395594690004787819 110054531093392035007181729)
  ·
    refine ⟨82540898320044026255386297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110054531093392035007181729 82540898320044026255386297)
    ·
      refine ⟨61905673740033019691539723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82540898320044026255386297 61905673740033019691539723)
      ·
        refine ⟨92858510610049529537309585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61905673740033019691539723 92858510610049529537309585)
        ·
          refine ⟨69643882957537147152982189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92858510610049529537309585 69643882957537147152982189)
          ·
            refine ⟨26116456109076430182368321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69643882957537147152982189 26116456109076430182368321)
            ·
              refine ⟨19587342081807322636776241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26116456109076430182368321 19587342081807322636776241)
              ·
                refine ⟨14690506561355491977582181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19587342081807322636776241 14690506561355491977582181)
                ·
                  refine ⟨2754469980254154745796659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14690506561355491977582181 2754469980254154745796659)
                  ·
                    refine ⟨4131704970381232118694989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2754469980254154745796659 4131704970381232118694989)
                    ·
                      refine ⟨1549389363892962044510621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4131704970381232118694989 1549389363892962044510621)
                      ·
                        rfl

theorem cell23_3017425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_3017425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017425 prefixEnd_3017425 := by exact prefixLift 3017425
  have htrace : WordTrace (prefixWord ++ tailWord_3017425) baseStart_3017425 baseEnd_3017425 := by
    simpa [prefixWord, tailWord_3017425, baseEnd_3017425] using wordTrace_append hprefix tailTrace_3017425
  have hstable : (prefixWord ++ tailWord_3017425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017425).length < 2 ^ (prefixWord ++ tailWord_3017425).sum := by decide
  have hdescent : baseEnd_3017425 < baseStart_3017425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017426 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_3017426 : Nat := 118140960795 + 3017426 * 2 ^ 59
def prefixEnd_3017426 : Nat := 4983230072969 + 3 ^ 40 * 3017426 * 2
def baseEnd_3017426 : Nat := 1549389877373616540598117

theorem tailTrace_3017426 : CollatzResearch.WordTrace tailWord_3017426 prefixEnd_3017426 1549389877373616540598117 := by
  unfold tailWord_3017426
  simp only [CollatzResearch.WordTrace]
  refine ⟨27513641891597103044492033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73369711710925608118645421 27513641891597103044492033)
  ·
    refine ⟨20635231418697827283369025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27513641891597103044492033 20635231418697827283369025)
    ·
      refine ⟨15476423564023370462526769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20635231418697827283369025 15476423564023370462526769)
      ·
        refine ⟨11607317673017527846895077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15476423564023370462526769 11607317673017527846895077)
        ·
          refine ⟨2176372063690786471292827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11607317673017527846895077 2176372063690786471292827)
          ·
            refine ⟨3264558095536179706939241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176372063690786471292827 3264558095536179706939241)
            ·
              refine ⟨2448418571652134780204431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264558095536179706939241 2448418571652134780204431)
              ·
                refine ⟨3672627857478202170306647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2448418571652134780204431 3672627857478202170306647)
                ·
                  refine ⟨5508941786217303255459971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672627857478202170306647 5508941786217303255459971)
                  ·
                    refine ⟨8263412679325954883189957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5508941786217303255459971 8263412679325954883189957)
                    ·
                      refine ⟨1549389877373616540598117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8263412679325954883189957 1549389877373616540598117)
                      ·
                        rfl

theorem cell23_3017426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_3017426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017426 prefixEnd_3017426 := by exact prefixLift 3017426
  have htrace : WordTrace (prefixWord ++ tailWord_3017426) baseStart_3017426 baseEnd_3017426 := by
    simpa [prefixWord, tailWord_3017426, baseEnd_3017426] using wordTrace_append hprefix tailTrace_3017426
  have hstable : (prefixWord ++ tailWord_3017426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017426).length < 2 ^ (prefixWord ++ tailWord_3017426).sum := by decide
  have hdescent : baseEnd_3017426 < baseStart_3017426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017429 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3017429 : Nat := 118140960795 + 3017429 * 2 ^ 59
def prefixEnd_3017429 : Nat := 4983230072969 + 3 ^ 40 * 3017429 * 2
def baseEnd_3017429 : Nat := 1549391417815580028860603

theorem tailTrace_3017429 : CollatzResearch.WordTrace tailWord_3017429 prefixEnd_3017429 1549391417815580028860603 := by
  unfold tailWord_3017429
  simp only [CollatzResearch.WordTrace]
  refine ⟨110054676985377543690327341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73369784656918362460218227 110054676985377543690327341)
  ·
    refine ⟨41270503869516578883872753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110054676985377543690327341 41270503869516578883872753)
    ·
      refine ⟨30952877902137434162904565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41270503869516578883872753 30952877902137434162904565)
      ·
        refine ⟨2901832303325384452772303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30952877902137434162904565 2901832303325384452772303)
        ·
          refine ⟨4352748454988076679158455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901832303325384452772303 4352748454988076679158455)
          ·
            refine ⟨6529122682482115018737683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352748454988076679158455 6529122682482115018737683)
            ·
              refine ⟨9793684023723172528106525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6529122682482115018737683 9793684023723172528106525)
              ·
                refine ⟨3672631508896189698039947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9793684023723172528106525 3672631508896189698039947)
                ·
                  refine ⟨5508947263344284547059921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672631508896189698039947 5508947263344284547059921)
                  ·
                    refine ⟨4131710447508213410294941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5508947263344284547059921 4131710447508213410294941)
                    ·
                      refine ⟨1549391417815580028860603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4131710447508213410294941 1549391417815580028860603)
                      ·
                        rfl

theorem cell23_3017429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3017429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017429 prefixEnd_3017429 := by exact prefixLift 3017429
  have htrace : WordTrace (prefixWord ++ tailWord_3017429) baseStart_3017429 baseEnd_3017429 := by
    simpa [prefixWord, tailWord_3017429, baseEnd_3017429] using wordTrace_append hprefix tailTrace_3017429
  have hstable : (prefixWord ++ tailWord_3017429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017429).length < 2 ^ (prefixWord ++ tailWord_3017429).sum := by decide
  have hdescent : baseEnd_3017429 < baseStart_3017429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017482 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_3017482 : Nat := 118140960795 + 3017482 * 2 ^ 59
def prefixEnd_3017482 : Nat := 4983230072969 + 3 ^ 40 * 3017482 * 2
def baseEnd_3017482 : Nat := 1549418632290268321497859

theorem tailTrace_3017482 : CollatzResearch.WordTrace tailWord_3017482 prefixEnd_3017482 1549418632290268321497859 := by
  unfold tailWord_3017482
  simp only [CollatzResearch.WordTrace]
  refine ⟨27514152513546383435501675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73371073369457022494671133 27514152513546383435501675)
  ·
    refine ⟨41271228770319575153252513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27514152513546383435501675 41271228770319575153252513)
    ·
      refine ⟨30953421577739681364939385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41271228770319575153252513 30953421577739681364939385)
      ·
        refine ⟨23215066183304761023704539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30953421577739681364939385 23215066183304761023704539)
        ·
          refine ⟨34822599274957141535556809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23215066183304761023704539 34822599274957141535556809)
          ·
            refine ⟨26116949456217856151667607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34822599274957141535556809 26116949456217856151667607)
            ·
              refine ⟨39175424184326784227501411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26116949456217856151667607 39175424184326784227501411)
              ·
                refine ⟨58763136276490176341252117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39175424184326784227501411 58763136276490176341252117)
                ·
                  refine ⟨2754522012960477015996193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58763136276490176341252117 2754522012960477015996193)
                  ·
                    refine ⟨2065891509720357761997145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2754522012960477015996193 2065891509720357761997145)
                    ·
                      refine ⟨1549418632290268321497859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065891509720357761997145 1549418632290268321497859)
                      ·
                        rfl

theorem cell23_3017482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_3017482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017482 prefixEnd_3017482 := by exact prefixLift 3017482
  have htrace : WordTrace (prefixWord ++ tailWord_3017482) baseStart_3017482 baseEnd_3017482 := by
    simpa [prefixWord, tailWord_3017482, baseEnd_3017482] using wordTrace_append hprefix tailTrace_3017482
  have hstable : (prefixWord ++ tailWord_3017482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017482).length < 2 ^ (prefixWord ++ tailWord_3017482).sum := by decide
  have hdescent : baseEnd_3017482 < baseStart_3017482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017498 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_3017498 : Nat := 118140960795 + 3017498 * 2 ^ 59
def prefixEnd_3017498 : Nat := 4983230072969 + 3 ^ 40 * 3017498 * 2
def baseEnd_3017498 : Nat := 1549426847980740258897785

theorem tailTrace_3017498 : CollatzResearch.WordTrace tailWord_3017498 prefixEnd_3017498 1549426847980740258897785 := by
  unfold tailWord_3017498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27514298405531892118647287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73371462414751712316392765 27514298405531892118647287)
  ·
    refine ⟨41271447608297838177970931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27514298405531892118647287 41271447608297838177970931)
    ·
      refine ⟨61907171412446757266956397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41271447608297838177970931 61907171412446757266956397)
      ·
        refine ⟨23215189279667533975108649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61907171412446757266956397 23215189279667533975108649)
        ·
          refine ⟨17411391959750650481331487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23215189279667533975108649 17411391959750650481331487)
          ·
            refine ⟨26117087939625975721997231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17411391959750650481331487 26117087939625975721997231)
            ·
              refine ⟨39175631909438963582995847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26117087939625975721997231 39175631909438963582995847)
              ·
                refine ⟨58763447864158445374493771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39175631909438963582995847 58763447864158445374493771)
                ·
                  refine ⟨88145171796237668061740657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58763447864158445374493771 88145171796237668061740657)
                  ·
                    refine ⟨66108878847178251046305493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88145171796237668061740657 66108878847178251046305493)
                    ·
                      refine ⟨1549426847980740258897785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66108878847178251046305493 1549426847980740258897785)
                      ·
                        rfl

theorem cell23_3017498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_3017498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017498 prefixEnd_3017498 := by exact prefixLift 3017498
  have htrace : WordTrace (prefixWord ++ tailWord_3017498) baseStart_3017498 baseEnd_3017498 := by
    simpa [prefixWord, tailWord_3017498, baseEnd_3017498] using wordTrace_append hprefix tailTrace_3017498
  have hstable : (prefixWord ++ tailWord_3017498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017498).length < 2 ^ (prefixWord ++ tailWord_3017498).sum := by decide
  have hdescent : baseEnd_3017498 < baseStart_3017498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017528 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_3017528 : Nat := 118140960795 + 3017528 * 2 ^ 59
def prefixEnd_3017528 : Nat := 4983230072969 + 3 ^ 40 * 3017528 * 2
def baseEnd_3017528 : Nat := 1549442252400375141522647

theorem tailTrace_3017528 : CollatzResearch.WordTrace tailWord_3017528 prefixEnd_3017528 1549442252400375141522647 := by
  unfold tailWord_3017528
  simp only [CollatzResearch.WordTrace]
  refine ⟨55029143906009441799090619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73372191874679255732120825 55029143906009441799090619)
  ·
    refine ⟨82543715859014162698635929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55029143906009441799090619 82543715859014162698635929)
    ·
      refine ⟨61907786894260622023976947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82543715859014162698635929 61907786894260622023976947)
      ·
        refine ⟨92861680341390933035965421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61907786894260622023976947 92861680341390933035965421)
        ·
          refine ⟨34823130128021599888487033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92861680341390933035965421 34823130128021599888487033)
          ·
            refine ⟨26117347596016199916365275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34823130128021599888487033 26117347596016199916365275)
            ·
              refine ⟨39176021394024299874547913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26117347596016199916365275 39176021394024299874547913)
              ·
                refine ⟨29382016045518224905910935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39176021394024299874547913 29382016045518224905910935)
                ·
                  refine ⟨44073024068277337358866403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29382016045518224905910935 44073024068277337358866403)
                  ·
                    refine ⟨66109536102416006038299605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44073024068277337358866403 66109536102416006038299605)
                    ·
                      refine ⟨1549442252400375141522647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66109536102416006038299605 1549442252400375141522647)
                      ·
                        rfl

theorem cell23_3017528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_3017528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017528 prefixEnd_3017528 := by exact prefixLift 3017528
  have htrace : WordTrace (prefixWord ++ tailWord_3017528) baseStart_3017528 baseEnd_3017528 := by
    simpa [prefixWord, tailWord_3017528, baseEnd_3017528] using wordTrace_append hprefix tailTrace_3017528
  have hstable : (prefixWord ++ tailWord_3017528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017528).length < 2 ^ (prefixWord ++ tailWord_3017528).sum := by decide
  have hdescent : baseEnd_3017528 < baseStart_3017528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017535 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 2, 5]
def baseStart_3017535 : Nat := 118140960795 + 3017535 * 2 ^ 59
def prefixEnd_3017535 : Nat := 4983230072969 + 3 ^ 40 * 3017535 * 2
def baseEnd_3017535 : Nat := 516481948921652204711705

theorem tailTrace_3017535 : CollatzResearch.WordTrace tailWord_3017535 prefixEnd_3017535 516481948921652204711705 := by
  unfold tailWord_3017535
  simp only [CollatzResearch.WordTrace]
  refine ⟨110058543122993523793686059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73372362081995682529124039 110058543122993523793686059)
  ·
    refine ⟨165087814684490285690529089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110058543122993523793686059 165087814684490285690529089)
    ·
      refine ⟨123815861013367714267896817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165087814684490285690529089 123815861013367714267896817)
      ·
        refine ⟨92861895760025785700922613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123815861013367714267896817 92861895760025785700922613)
        ·
          refine ⟨8705802727502417409461495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92861895760025785700922613 8705802727502417409461495)
          ·
            refine ⟨13058704091253626114192243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8705802727502417409461495 13058704091253626114192243)
            ·
              refine ⟨19588056136880439171288365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13058704091253626114192243 19588056136880439171288365)
              ·
                refine ⟨7345521051330164689233137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19588056136880439171288365 7345521051330164689233137)
                ·
                  refine ⟨5509140788497623516924853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7345521051330164689233137 5509140788497623516924853)
                  ·
                    refine ⟨516481948921652204711705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5509140788497623516924853 516481948921652204711705)
                    ·
                      rfl

theorem cell23_3017535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_3017535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017535 prefixEnd_3017535 := by exact prefixLift 3017535
  have htrace : WordTrace (prefixWord ++ tailWord_3017535) baseStart_3017535 baseEnd_3017535 := by
    simpa [prefixWord, tailWord_3017535, baseEnd_3017535] using wordTrace_append hprefix tailTrace_3017535
  have hstable : (prefixWord ++ tailWord_3017535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017535).length < 2 ^ (prefixWord ++ tailWord_3017535).sum := by decide
  have hdescent : baseEnd_3017535 < baseStart_3017535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017555 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 3, 6, 2]
def baseStart_3017555 : Nat := 118140960795 + 3017555 * 2 ^ 59
def prefixEnd_3017555 : Nat := 4983230072969 + 3 ^ 40 * 3017555 * 2
def baseEnd_3017555 : Nat := 1549456116378046535885023

theorem tailTrace_3017555 : CollatzResearch.WordTrace tailWord_3017555 prefixEnd_3017555 1549456116378046535885023 := by
  unfold tailWord_3017555
  simp only [CollatzResearch.WordTrace]
  refine ⟨110059272582921067209414119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73372848388614044806276079 110059272582921067209414119)
  ·
    refine ⟨165088908874381600814121179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110059272582921067209414119 165088908874381600814121179)
    ·
      refine ⟨247633363311572401221181769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165088908874381600814121179 247633363311572401221181769)
      ·
        refine ⟨185725022483679300915886327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247633363311572401221181769 185725022483679300915886327)
        ·
          refine ⟨278587533725518951373829491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185725022483679300915886327 278587533725518951373829491)
          ·
            refine ⟨417881300588278427060744237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278587533725518951373829491 417881300588278427060744237)
            ·
              refine ⟨156705487720604410147779089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417881300588278427060744237 156705487720604410147779089)
              ·
                refine ⟨117529115790453307610834317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156705487720604410147779089 117529115790453307610834317)
                ·
                  refine ⟨44073418421419990354062869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117529115790453307610834317 44073418421419990354062869)
                  ·
                    refine ⟨2065941488504062047846697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44073418421419990354062869 2065941488504062047846697)
                    ·
                      refine ⟨1549456116378046535885023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065941488504062047846697 1549456116378046535885023)
                      ·
                        rfl

theorem cell23_3017555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 6, 2].length) (baseStart_3017555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017555 prefixEnd_3017555 := by exact prefixLift 3017555
  have htrace : WordTrace (prefixWord ++ tailWord_3017555) baseStart_3017555 baseEnd_3017555 := by
    simpa [prefixWord, tailWord_3017555, baseEnd_3017555] using wordTrace_append hprefix tailTrace_3017555
  have hstable : (prefixWord ++ tailWord_3017555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017555).length < 2 ^ (prefixWord ++ tailWord_3017555).sum := by decide
  have hdescent : baseEnd_3017555 < baseStart_3017555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017556 : List Nat := [2, 4, 1, 1, 4, 2, 2, 2, 5]
def baseStart_3017556 : Nat := 118140960795 + 3017556 * 2 ^ 59
def prefixEnd_3017556 : Nat := 4983230072969 + 3 ^ 40 * 3017556 * 2
def baseEnd_3017556 : Nat := 172161847762077892441391

theorem tailTrace_3017556 : CollatzResearch.WordTrace tailWord_3017556 prefixEnd_3017556 172161847762077892441391 := by
  unfold tailWord_3017556
  simp only [CollatzResearch.WordTrace]
  refine ⟨55029654527958722190100261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73372872703944962920133681 55029654527958722190100261)
  ·
    refine ⟨10318060223992260410643799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55029654527958722190100261 10318060223992260410643799)
    ·
      refine ⟨15477090335988390615965699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10318060223992260410643799 15477090335988390615965699)
      ·
        refine ⟨23215635503982585923948549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15477090335988390615965699 23215635503982585923948549)
        ·
          refine ⟨4352931656996734860740353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23215635503982585923948549 4352931656996734860740353)
          ·
            refine ⟨3264698742747551145555265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4352931656996734860740353 3264698742747551145555265)
            ·
              refine ⟨2448524057060663359166449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264698742747551145555265 2448524057060663359166449)
              ·
                refine ⟨1836393042795497519374837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448524057060663359166449 1836393042795497519374837)
                ·
                  refine ⟨172161847762077892441391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1836393042795497519374837 172161847762077892441391)
                  ·
                    rfl

theorem cell23_3017556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_3017556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017556 prefixEnd_3017556 := by exact prefixLift 3017556
  have htrace : WordTrace (prefixWord ++ tailWord_3017556) baseStart_3017556 baseEnd_3017556 := by
    simpa [prefixWord, tailWord_3017556, baseEnd_3017556] using wordTrace_append hprefix tailTrace_3017556
  have hstable : (prefixWord ++ tailWord_3017556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017556).length < 2 ^ (prefixWord ++ tailWord_3017556).sum := by decide
  have hdescent : baseEnd_3017556 < baseStart_3017556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017572 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_3017572 : Nat := 118140960795 + 3017572 * 2 ^ 59
def prefixEnd_3017572 : Nat := 4983230072969 + 3 ^ 40 * 3017572 * 2
def baseEnd_3017572 : Nat := 1549464845549172969372445

theorem tailTrace_3017572 : CollatzResearch.WordTrace tailWord_3017572 prefixEnd_3017572 1549464845549172969372445 := by
  unfold tailWord_3017572
  simp only [CollatzResearch.WordTrace]
  refine ⟨55029946311929739556391485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73373261749239652741855313 55029946311929739556391485)
  ·
    refine ⟨20636229866973652333646807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55029946311929739556391485 20636229866973652333646807)
    ·
      refine ⟨30954344800460478500470211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20636229866973652333646807 30954344800460478500470211)
      ·
        refine ⟨46431517200690717750705317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30954344800460478500470211 46431517200690717750705317)
        ·
          refine ⟨8705909475129509578257247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46431517200690717750705317 8705909475129509578257247)
          ·
            refine ⟨13058864212694264367385871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8705909475129509578257247 13058864212694264367385871)
            ·
              refine ⟨19588296319041396551078807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13058864212694264367385871 19588296319041396551078807)
              ·
                refine ⟨29382444478562094826618211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19588296319041396551078807 29382444478562094826618211)
                ·
                  refine ⟨44073666717843142239927317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29382444478562094826618211 44073666717843142239927317)
                  ·
                    refine ⟨2065953127398897292496593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44073666717843142239927317 2065953127398897292496593)
                    ·
                      refine ⟨1549464845549172969372445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065953127398897292496593 1549464845549172969372445)
                      ·
                        rfl

theorem cell23_3017572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_3017572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017572 prefixEnd_3017572 := by exact prefixLift 3017572
  have htrace : WordTrace (prefixWord ++ tailWord_3017572) baseStart_3017572 baseEnd_3017572 := by
    simpa [prefixWord, tailWord_3017572, baseEnd_3017572] using wordTrace_append hprefix tailTrace_3017572
  have hstable : (prefixWord ++ tailWord_3017572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017572).length < 2 ^ (prefixWord ++ tailWord_3017572).sum := by decide
  have hdescent : baseEnd_3017572 < baseStart_3017572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017589 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3017589 : Nat := 118140960795 + 3017589 * 2 ^ 59
def prefixEnd_3017589 : Nat := 4983230072969 + 3 ^ 40 * 3017589 * 2
def baseEnd_3017589 : Nat := 1549473574720299402859867

theorem tailTrace_3017589 : CollatzResearch.WordTrace tailWord_3017589 prefixEnd_3017589 1549473574720299402859867 := by
  unfold tailWord_3017589
  simp only [CollatzResearch.WordTrace]
  refine ⟨110060512664797891016151821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73373675109865260677434547 110060512664797891016151821)
  ·
    refine ⟨41272692249299209131056933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110060512664797891016151821 41272692249299209131056933)
    ·
      refine ⟨7738629796743601712073175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41272692249299209131056933 7738629796743601712073175)
      ·
        refine ⟨11607944695115402568109763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7738629796743601712073175 11607944695115402568109763)
        ·
          refine ⟨17411917042673103852164645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11607944695115402568109763 17411917042673103852164645)
          ·
            refine ⟨3264734445501206972280871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17411917042673103852164645 3264734445501206972280871)
            ·
              refine ⟨4897101668251810458421307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3264734445501206972280871 4897101668251810458421307)
              ·
                refine ⟨7345652502377715687631961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897101668251810458421307 7345652502377715687631961)
                ·
                  refine ⟨5509239376783286765723971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7345652502377715687631961 5509239376783286765723971)
                  ·
                    refine ⟨8263859065174930148585957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5509239376783286765723971 8263859065174930148585957)
                    ·
                      refine ⟨1549473574720299402859867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8263859065174930148585957 1549473574720299402859867)
                      ·
                        rfl

theorem cell23_3017589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3017589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017589 prefixEnd_3017589 := by exact prefixLift 3017589
  have htrace : WordTrace (prefixWord ++ tailWord_3017589) baseStart_3017589 baseEnd_3017589 := by
    simpa [prefixWord, tailWord_3017589, baseEnd_3017589] using wordTrace_append hprefix tailTrace_3017589
  have hstable : (prefixWord ++ tailWord_3017589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017589).length < 2 ^ (prefixWord ++ tailWord_3017589).sum := by decide
  have hdescent : baseEnd_3017589 < baseStart_3017589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017632 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 1, 5, 2]
def baseStart_3017632 : Nat := 118140960795 + 3017632 * 2 ^ 59
def prefixEnd_3017632 : Nat := 4983230072969 + 3 ^ 40 * 3017632 * 2
def baseEnd_3017632 : Nat := 1549495654388442734622169

theorem tailTrace_3017632 : CollatzResearch.WordTrace tailWord_3017632 prefixEnd_3017632 1549495654388442734622169 := by
  unfold tailWord_3017632
  simp only [CollatzResearch.WordTrace]
  refine ⟨55031040501821054679983575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73374720669094739573311433 55031040501821054679983575)
  ·
    refine ⟨82546560752731582019975363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55031040501821054679983575 82546560752731582019975363)
    ·
      refine ⟨123819841129097373029963045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82546560752731582019975363 123819841129097373029963045)
      ·
        refine ⟨23216220211705757443118071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123819841129097373029963045 23216220211705757443118071)
        ·
          refine ⟨34824330317558636164677107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23216220211705757443118071 34824330317558636164677107)
          ·
            refine ⟨52236495476337954247015661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34824330317558636164677107 52236495476337954247015661)
            ·
              refine ⟨19588685803626732842630873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52236495476337954247015661 19588685803626732842630873)
              ·
                refine ⟨14691514352720049631973155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19588685803626732842630873 14691514352720049631973155)
                ·
                  refine ⟨22037271529080074447959733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14691514352720049631973155 22037271529080074447959733)
                  ·
                    refine ⟨2065994205851256979496225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22037271529080074447959733 2065994205851256979496225)
                    ·
                      refine ⟨1549495654388442734622169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2065994205851256979496225 1549495654388442734622169)
                      ·
                        rfl

theorem cell23_3017632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_3017632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017632 prefixEnd_3017632 := by exact prefixLift 3017632
  have htrace : WordTrace (prefixWord ++ tailWord_3017632) baseStart_3017632 baseEnd_3017632 := by
    simpa [prefixWord, tailWord_3017632, baseEnd_3017632] using wordTrace_append hprefix tailTrace_3017632
  have hstable : (prefixWord ++ tailWord_3017632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017632).length < 2 ^ (prefixWord ++ tailWord_3017632).sum := by decide
  have hdescent : baseEnd_3017632 < baseStart_3017632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017655 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 1, 6]
def baseStart_3017655 : Nat := 118140960795 + 3017655 * 2 ^ 59
def prefixEnd_3017655 : Nat := 4983230072969 + 3 ^ 40 * 3017655 * 2
def baseEnd_3017655 : Nat := 516502488147832048211521

theorem tailTrace_3017655 : CollatzResearch.WordTrace tailWord_3017655 prefixEnd_3017655 516502488147832048211521 := by
  unfold tailWord_3017655
  simp only [CollatzResearch.WordTrace]
  refine ⟨110062919882558784288054419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73375279921705856192036279 110062919882558784288054419)
  ·
    refine ⟨165094379823838176432081629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110062919882558784288054419 165094379823838176432081629)
    ·
      refine ⟨61910392433939316162030611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165094379823838176432081629 61910392433939316162030611)
      ·
        refine ⟨92865588650908974243045917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61910392433939316162030611 92865588650908974243045917)
        ·
          refine ⟨34824595744090865341142219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92865588650908974243045917 34824595744090865341142219)
          ·
            refine ⟨52236893616136298011713329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34824595744090865341142219 52236893616136298011713329)
            ·
              refine ⟨39177670212102223508784997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52236893616136298011713329 39177670212102223508784997)
              ·
                refine ⟨7345813164769166907897187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39177670212102223508784997 7345813164769166907897187)
                ·
                  refine ⟨11018719747153750361845781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7345813164769166907897187 11018719747153750361845781)
                  ·
                    refine ⟨516502488147832048211521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11018719747153750361845781 516502488147832048211521)
                    ·
                      rfl

theorem cell23_3017655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_3017655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017655 prefixEnd_3017655 := by exact prefixLift 3017655
  have htrace : WordTrace (prefixWord ++ tailWord_3017655) baseStart_3017655 baseEnd_3017655 := by
    simpa [prefixWord, tailWord_3017655, baseEnd_3017655] using wordTrace_append hprefix tailTrace_3017655
  have hstable : (prefixWord ++ tailWord_3017655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017655).length < 2 ^ (prefixWord ++ tailWord_3017655).sum := by decide
  have hdescent : baseEnd_3017655 < baseStart_3017655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017656 : List Nat := [2, 1, 2, 1, 2, 4, 3, 3, 1, 1, 3]
def baseStart_3017656 : Nat := 118140960795 + 3017656 * 2 ^ 59
def prefixEnd_3017656 : Nat := 4983230072969 + 3 ^ 40 * 3017656 * 2
def baseEnd_3017656 : Nat := 1549507977924150640722059

theorem tailTrace_3017656 : CollatzResearch.WordTrace tailWord_3017656 prefixEnd_3017656 1549507977924150640722059 := by
  unfold tailWord_3017656
  simp only [CollatzResearch.WordTrace]
  refine ⟨55031478177777580729420411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73375304237036774305893881 55031478177777580729420411)
  ·
    refine ⟨82547217266666371094130617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55031478177777580729420411 82547217266666371094130617)
    ·
      refine ⟨61910412949999778320597963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82547217266666371094130617 61910412949999778320597963)
      ·
        refine ⟨92865619424999667480896945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61910412949999778320597963 92865619424999667480896945)
        ·
          refine ⟨69649214568749750610672709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92865619424999667480896945 69649214568749750610672709)
          ·
            refine ⟨13059227731640578239501133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69649214568749750610672709 13059227731640578239501133)
            ·
              refine ⟨4897210399365216839812925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13059227731640578239501133 4897210399365216839812925)
              ·
                refine ⟨1836453899761956314929847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4897210399365216839812925 1836453899761956314929847)
                ·
                  refine ⟨2754680849642934472394771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836453899761956314929847 2754680849642934472394771)
                  ·
                    refine ⟨4132021274464401708592157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2754680849642934472394771 4132021274464401708592157)
                    ·
                      refine ⟨1549507977924150640722059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4132021274464401708592157 1549507977924150640722059)
                      ·
                        rfl

theorem cell23_3017656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 1, 3].length) (baseStart_3017656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017656 prefixEnd_3017656 := by exact prefixLift 3017656
  have htrace : WordTrace (prefixWord ++ tailWord_3017656) baseStart_3017656 baseEnd_3017656 := by
    simpa [prefixWord, tailWord_3017656, baseEnd_3017656] using wordTrace_append hprefix tailTrace_3017656
  have hstable : (prefixWord ++ tailWord_3017656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017656).length < 2 ^ (prefixWord ++ tailWord_3017656).sum := by decide
  have hdescent : baseEnd_3017656 < baseStart_3017656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017675 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 6]
def baseStart_3017675 : Nat := 118140960795 + 3017675 * 2 ^ 59
def prefixEnd_3017675 : Nat := 4983230072969 + 3 ^ 40 * 3017675 * 2
def baseEnd_3017675 : Nat := 1549517734056586066384471

theorem tailTrace_3017675 : CollatzResearch.WordTrace tailWord_3017675 prefixEnd_3017675 1549517734056586066384471 := by
  unfold tailWord_3017675
  simp only [CollatzResearch.WordTrace]
  refine ⟨110063649342486327703782479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73375766228324218469188319 110063649342486327703782479)
  ·
    refine ⟨165095474013729491555673719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110063649342486327703782479 165095474013729491555673719)
    ·
      refine ⟨247643211020594237333510579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165095474013729491555673719 247643211020594237333510579)
      ·
        refine ⟨371464816530891356000265869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247643211020594237333510579 371464816530891356000265869)
        ·
          refine ⟨139299306199084258500099701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371464816530891356000265869 139299306199084258500099701)
          ·
            refine ⟨13059309956164149234384347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139299306199084258500099701 13059309956164149234384347)
            ·
              refine ⟨19588964934246223851576521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13059309956164149234384347 19588964934246223851576521)
              ·
                refine ⟨14691723700684667888682391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19588964934246223851576521 14691723700684667888682391)
                ·
                  refine ⟨22037585551027001833023587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14691723700684667888682391 22037585551027001833023587)
                  ·
                    refine ⟨33056378326540502749535381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22037585551027001833023587 33056378326540502749535381)
                    ·
                      refine ⟨1549517734056586066384471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33056378326540502749535381 1549517734056586066384471)
                      ·
                        rfl

theorem cell23_3017675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_3017675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017675 prefixEnd_3017675 := by exact prefixLift 3017675
  have htrace : WordTrace (prefixWord ++ tailWord_3017675) baseStart_3017675 baseEnd_3017675 := by
    simpa [prefixWord, tailWord_3017675, baseEnd_3017675] using wordTrace_append hprefix tailTrace_3017675
  have hstable : (prefixWord ++ tailWord_3017675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017675).length < 2 ^ (prefixWord ++ tailWord_3017675).sum := by decide
  have hdescent : baseEnd_3017675 < baseStart_3017675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017689 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 2, 4]
def baseStart_3017689 : Nat := 118140960795 + 3017689 * 2 ^ 59
def prefixEnd_3017689 : Nat := 4983230072969 + 3 ^ 40 * 3017689 * 2
def baseEnd_3017689 : Nat := 516508307595249670536469

theorem tailTrace_3017689 : CollatzResearch.WordTrace tailWord_3017689 prefixEnd_3017689 516508307595249670536469 := by
  unfold tailWord_3017689
  simp only [CollatzResearch.WordTrace]
  refine ⟨110064159964435608094792121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73376106642957072063194747 110064159964435608094792121)
  ·
    refine ⟨82548119973326706071094091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110064159964435608094792121 82548119973326706071094091)
    ·
      refine ⟨123822179959990059106641137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82548119973326706071094091 123822179959990059106641137)
      ·
        refine ⟨92866634969992544329980853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123822179959990059106641137 92866634969992544329980853)
        ·
          refine ⟨8706247028436801030935705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92866634969992544329980853 8706247028436801030935705)
          ·
            refine ⟨6529685271327600773201779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8706247028436801030935705 6529685271327600773201779)
            ·
              refine ⟨9794527906991401159802669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6529685271327600773201779 9794527906991401159802669)
              ·
                refine ⟨3672947965121775434926001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9794527906991401159802669 3672947965121775434926001)
                ·
                  refine ⟨2754710973841331576194501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3672947965121775434926001 2754710973841331576194501)
                  ·
                    refine ⟨516508307595249670536469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2754710973841331576194501 516508307595249670536469)
                    ·
                      rfl

theorem cell23_3017689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 4].length) (baseStart_3017689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017689 prefixEnd_3017689 := by exact prefixLift 3017689
  have htrace : WordTrace (prefixWord ++ tailWord_3017689) baseStart_3017689 baseEnd_3017689 := by
    simpa [prefixWord, tailWord_3017689, baseEnd_3017689] using wordTrace_append hprefix tailTrace_3017689
  have hstable : (prefixWord ++ tailWord_3017689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017689).length < 2 ^ (prefixWord ++ tailWord_3017689).sum := by decide
  have hdescent : baseEnd_3017689 < baseStart_3017689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017739 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 3, 3, 2]
def baseStart_3017739 : Nat := 118140960795 + 3017739 * 2 ^ 59
def prefixEnd_3017739 : Nat := 4983230072969 + 3 ^ 40 * 3017739 * 2
def baseEnd_3017739 : Nat := 1549550596818473815984177

theorem tailTrace_3017739 : CollatzResearch.WordTrace tailWord_3017739 prefixEnd_3017739 1549550596818473815984177 := by
  unfold tailWord_3017739
  simp only [CollatzResearch.WordTrace]
  refine ⟨110065983614254466634112271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73377322409502977756074847 110065983614254466634112271)
  ·
    refine ⟨165098975421381699951168407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110065983614254466634112271 165098975421381699951168407)
    ·
      refine ⟨247648463132072549926752611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165098975421381699951168407 247648463132072549926752611)
      ·
        refine ⟨371472694698108824890128917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247648463132072549926752611 371472694698108824890128917)
        ·
          refine ⟨17412782563973851166724793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 371472694698108824890128917 17412782563973851166724793)
          ·
            refine ⟨13059586922980388375043595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17412782563973851166724793 13059586922980388375043595)
            ·
              refine ⟨19589380384470582562565393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13059586922980388375043595 19589380384470582562565393)
              ·
                refine ⟨14692035288352936921924045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19589380384470582562565393 14692035288352936921924045)
                ·
                  refine ⟨5509513233132351345721517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14692035288352936921924045 5509513233132351345721517)
                  ·
                    refine ⟨2066067462424631754645569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5509513233132351345721517 2066067462424631754645569)
                    ·
                      refine ⟨1549550596818473815984177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066067462424631754645569 1549550596818473815984177)
                      ·
                        rfl

theorem cell23_3017739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 3, 2].length) (baseStart_3017739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017739 prefixEnd_3017739 := by exact prefixLift 3017739
  have htrace : WordTrace (prefixWord ++ tailWord_3017739) baseStart_3017739 baseEnd_3017739 := by
    simpa [prefixWord, tailWord_3017739, baseEnd_3017739] using wordTrace_append hprefix tailTrace_3017739
  have hstable : (prefixWord ++ tailWord_3017739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017739).length < 2 ^ (prefixWord ++ tailWord_3017739).sum := by decide
  have hdescent : baseEnd_3017739 < baseStart_3017739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017780 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3017780 : Nat := 118140960795 + 3017780 * 2 ^ 59
def prefixEnd_3017780 : Nat := 4983230072969 + 3 ^ 40 * 3017780 * 2
def baseEnd_3017780 : Nat := 1549571649525308155571489

theorem tailTrace_3017780 : CollatzResearch.WordTrace tailWord_3017780 prefixEnd_3017780 1549571649525308155571489 := by
  unfold tailWord_3017780
  simp only [CollatzResearch.WordTrace]
  refine ⟨55033739503552965318177397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73378319338070620424236529 55033739503552965318177397)
  ·
    refine ⟨5159413078458090498579131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55033739503552965318177397 5159413078458090498579131)
    ·
      refine ⟨7739119617687135747868697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5159413078458090498579131 7739119617687135747868697)
      ·
        refine ⟨5804339713265351810901523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7739119617687135747868697 5804339713265351810901523)
        ·
          refine ⟨8706509569898027716352285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5804339713265351810901523 8706509569898027716352285)
          ·
            refine ⟨3264941088711760393632107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8706509569898027716352285 3264941088711760393632107)
            ·
              refine ⟨4897411633067640590448161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3264941088711760393632107 4897411633067640590448161)
              ·
                refine ⟨3673058724800730442836121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4897411633067640590448161 3673058724800730442836121)
                ·
                  refine ⟨2754794043600547832127091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3673058724800730442836121 2754794043600547832127091)
                  ·
                    refine ⟨4132191065400821748190637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2754794043600547832127091 4132191065400821748190637)
                    ·
                      refine ⟨1549571649525308155571489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4132191065400821748190637 1549571649525308155571489)
                      ·
                        rfl

theorem cell23_3017780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3017780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017780 prefixEnd_3017780 := by exact prefixLift 3017780
  have htrace : WordTrace (prefixWord ++ tailWord_3017780) baseStart_3017780 baseEnd_3017780 := by
    simpa [prefixWord, tailWord_3017780, baseEnd_3017780] using wordTrace_append hprefix tailTrace_3017780
  have hstable : (prefixWord ++ tailWord_3017780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017780).length < 2 ^ (prefixWord ++ tailWord_3017780).sum := by decide
  have hdescent : baseEnd_3017780 < baseStart_3017780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017792 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 7]
def baseStart_3017792 : Nat := 118140960795 + 3017792 * 2 ^ 59
def prefixEnd_3017792 : Nat := 4983230072969 + 3 ^ 40 * 3017792 * 2
def baseEnd_3017792 : Nat := 172175312365906900957937

theorem tailTrace_3017792 : CollatzResearch.WordTrace tailWord_3017792 prefixEnd_3017792 172175312365906900957937 := by
  unfold tailWord_3017792
  simp only [CollatzResearch.WordTrace]
  refine ⟨55033958341531228342895815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73378611122041637790527753 55033958341531228342895815)
  ·
    refine ⟨82550937512296842514343723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55033958341531228342895815 82550937512296842514343723)
    ·
      refine ⟨123826406268445263771515585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82550937512296842514343723 123826406268445263771515585)
      ·
        refine ⟨92869804701333947828636689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123826406268445263771515585 92869804701333947828636689)
        ·
          refine ⟨69652353526000460871477517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92869804701333947828636689 69652353526000460871477517)
          ·
            refine ⟨26119632572250172826804069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69652353526000460871477517 26119632572250172826804069)
            ·
              refine ⟨4897431107296907405025763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26119632572250172826804069 4897431107296907405025763)
              ·
                refine ⟨7346146660945361107538645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897431107296907405025763 7346146660945361107538645)
                ·
                  refine ⟨172175312365906900957937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7346146660945361107538645 172175312365906900957937)
                  ·
                    rfl

theorem cell23_3017792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 7].length) (baseStart_3017792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017792 prefixEnd_3017792 := by exact prefixLift 3017792
  have htrace : WordTrace (prefixWord ++ tailWord_3017792) baseStart_3017792 baseEnd_3017792 := by
    simpa [prefixWord, tailWord_3017792, baseEnd_3017792] using wordTrace_append hprefix tailTrace_3017792
  have hstable : (prefixWord ++ tailWord_3017792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017792).length < 2 ^ (prefixWord ++ tailWord_3017792).sum := by decide
  have hdescent : baseEnd_3017792 < baseStart_3017792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017846 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_3017846 : Nat := 118140960795 + 3017846 * 2 ^ 59
def prefixEnd_3017846 : Nat := 4983230072969 + 3 ^ 40 * 3017846 * 2
def baseEnd_3017846 : Nat := 1549605539248504897346185

theorem tailTrace_3017846 : CollatzResearch.WordTrace tailWord_3017846 prefixEnd_3017846 1549605539248504897346185 := by
  unfold tailWord_3017846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879367889054176494266087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73379924149911215938838261 6879367889054176494266087)
  ·
    refine ⟨10319051833581264741399131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6879367889054176494266087 10319051833581264741399131)
    ·
      refine ⟨15478577750371897112098697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10319051833581264741399131 15478577750371897112098697)
      ·
        refine ⟨11608933312778922834074023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15478577750371897112098697 11608933312778922834074023)
        ·
          refine ⟨17413399969168384251111035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11608933312778922834074023 17413399969168384251111035)
          ·
            refine ⟨26120099953752576376666553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17413399969168384251111035 26120099953752576376666553)
            ·
              refine ⟨19590074965314432282499915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26120099953752576376666553 19590074965314432282499915)
              ·
                refine ⟨29385112447971648423749873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19590074965314432282499915 29385112447971648423749873)
                ·
                  refine ⟨22038834335978736317812405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29385112447971648423749873 22038834335978736317812405)
                  ·
                    refine ⟨2066140718998006529794913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22038834335978736317812405 2066140718998006529794913)
                    ·
                      refine ⟨1549605539248504897346185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066140718998006529794913 1549605539248504897346185)
                      ·
                        rfl

theorem cell23_3017846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_3017846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017846 prefixEnd_3017846 := by exact prefixLift 3017846
  have htrace : WordTrace (prefixWord ++ tailWord_3017846) baseStart_3017846 baseEnd_3017846 := by
    simpa [prefixWord, tailWord_3017846, baseEnd_3017846] using wordTrace_append hprefix tailTrace_3017846
  have hstable : (prefixWord ++ tailWord_3017846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017846).length < 2 ^ (prefixWord ++ tailWord_3017846).sum := by decide
  have hdescent : baseEnd_3017846 < baseStart_3017846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017849 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 5]
def baseStart_3017849 : Nat := 118140960795 + 3017849 * 2 ^ 59
def prefixEnd_3017849 : Nat := 4983230072969 + 3 ^ 40 * 3017849 * 2
def baseEnd_3017849 : Nat := 1549607079690468385608671

theorem tailTrace_3017849 : CollatzResearch.WordTrace tailWord_3017849 prefixEnd_3017849 1549607079690468385608671 := by
  unfold tailWord_3017849
  simp only [CollatzResearch.WordTrace]
  refine ⟨110069995643855955420616601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73379997095903970280411067 110069995643855955420616601)
  ·
    refine ⟨82552496732891966565462451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110069995643855955420616601 82552496732891966565462451)
    ·
      refine ⟨123828745099337949848193677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82552496732891966565462451 123828745099337949848193677)
      ·
        refine ⟨46435779412251731193072629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123828745099337949848193677 46435779412251731193072629)
        ·
          refine ⟨4353354319898599799350559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46435779412251731193072629 4353354319898599799350559)
          ·
            refine ⟨6530031479847899699025839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4353354319898599799350559 6530031479847899699025839)
            ·
              refine ⟨9795047219771849548538759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530031479847899699025839 9795047219771849548538759)
              ·
                refine ⟨14692570829657774322808139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9795047219771849548538759 14692570829657774322808139)
                ·
                  refine ⟨22038856244486661484212209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14692570829657774322808139 22038856244486661484212209)
                  ·
                    refine ⟨16529142183364996113159157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22038856244486661484212209 16529142183364996113159157)
                    ·
                      refine ⟨1549607079690468385608671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16529142183364996113159157 1549607079690468385608671)
                      ·
                        rfl

theorem cell23_3017849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_3017849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017849 prefixEnd_3017849 := by exact prefixLift 3017849
  have htrace : WordTrace (prefixWord ++ tailWord_3017849) baseStart_3017849 baseEnd_3017849 := by
    simpa [prefixWord, tailWord_3017849, baseEnd_3017849] using wordTrace_append hprefix tailTrace_3017849
  have hstable : (prefixWord ++ tailWord_3017849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017849).length < 2 ^ (prefixWord ++ tailWord_3017849).sum := by decide
  have hdescent : baseEnd_3017849 < baseStart_3017849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017854 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3017854 : Nat := 118140960795 + 3017854 * 2 ^ 59
def prefixEnd_3017854 : Nat := 4983230072969 + 3 ^ 40 * 3017854 * 2
def baseEnd_3017854 : Nat := 1549609647093740866046149

theorem tailTrace_3017854 : CollatzResearch.WordTrace tailWord_3017854 prefixEnd_3017854 1549609647093740866046149 := by
  unfold tailWord_3017854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13758772251104730159318577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73380118672558560849699077 13758772251104730159318577)
  ·
    refine ⟨10319079188328547619488933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13758772251104730159318577 10319079188328547619488933)
    ·
      refine ⟨1934827347811602678654175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10319079188328547619488933 1934827347811602678654175)
      ·
        refine ⟨2902241021717404017981263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934827347811602678654175 2902241021717404017981263)
        ·
          refine ⟨4353361532576106026971895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2902241021717404017981263 4353361532576106026971895)
          ·
            refine ⟨6530042298864159040457843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4353361532576106026971895 6530042298864159040457843)
            ·
              refine ⟨9795063448296238560686765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530042298864159040457843 9795063448296238560686765)
              ·
                refine ⟨3673148793111089460257537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9795063448296238560686765 3673148793111089460257537)
                ·
                  refine ⟨2754861594833317095193153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3673148793111089460257537 2754861594833317095193153)
                  ·
                    refine ⟨2066146196124987821394865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2754861594833317095193153 2066146196124987821394865)
                    ·
                      refine ⟨1549609647093740866046149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066146196124987821394865 1549609647093740866046149)
                      ·
                        rfl

theorem cell23_3017854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3017854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017854 prefixEnd_3017854 := by exact prefixLift 3017854
  have htrace : WordTrace (prefixWord ++ tailWord_3017854) baseStart_3017854 baseEnd_3017854 := by
    simpa [prefixWord, tailWord_3017854, baseEnd_3017854] using wordTrace_append hprefix tailTrace_3017854
  have hstable : (prefixWord ++ tailWord_3017854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017854).length < 2 ^ (prefixWord ++ tailWord_3017854).sum := by decide
  have hdescent : baseEnd_3017854 < baseStart_3017854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017859 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 1, 6, 2]
def baseStart_3017859 : Nat := 118140960795 + 3017859 * 2 ^ 59
def prefixEnd_3017859 : Nat := 4983230072969 + 3 ^ 40 * 3017859 * 2
def baseEnd_3017859 : Nat := 1549612214497013346483625

theorem tailTrace_3017859 : CollatzResearch.WordTrace tailWord_3017859 prefixEnd_3017859 1549612214497013346483625 := by
  unfold tailWord_3017859
  simp only [CollatzResearch.WordTrace]
  refine ⟨110070360373819727128480631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73380240249213151418987087 110070360373819727128480631)
  ·
    refine ⟨165105540560729590692720947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110070360373819727128480631 165105540560729590692720947)
    ·
      refine ⟨247658310841094386039081421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165105540560729590692720947 247658310841094386039081421)
      ·
        refine ⟨92871866565410394764655533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247658310841094386039081421 92871866565410394764655533)
        ·
          refine ⟨34826949962028898036745825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92871866565410394764655533 34826949962028898036745825)
          ·
            refine ⟨26120212471521673527559369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34826949962028898036745825 26120212471521673527559369)
            ·
              refine ⟨19590159353641255145669527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26120212471521673527559369 19590159353641255145669527)
              ·
                refine ⟨29385239030461882718504291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19590159353641255145669527 29385239030461882718504291)
                ·
                  refine ⟨44077858545692824077756437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29385239030461882718504291 44077858545692824077756437)
                  ·
                    refine ⟨2066149619329351128644833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44077858545692824077756437 2066149619329351128644833)
                    ·
                      refine ⟨1549612214497013346483625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066149619329351128644833 1549612214497013346483625)
                      ·
                        rfl

theorem cell23_3017859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_3017859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017859 prefixEnd_3017859 := by exact prefixLift 3017859
  have htrace : WordTrace (prefixWord ++ tailWord_3017859) baseStart_3017859 baseEnd_3017859 := by
    simpa [prefixWord, tailWord_3017859, baseEnd_3017859] using wordTrace_append hprefix tailTrace_3017859
  have hstable : (prefixWord ++ tailWord_3017859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017859).length < 2 ^ (prefixWord ++ tailWord_3017859).sum := by decide
  have hdescent : baseEnd_3017859 < baseStart_3017859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017903 : List Nat := [1, 1, 2, 1, 2, 3, 6, 2, 1, 4]
def baseStart_3017903 : Nat := 118140960795 + 3017903 * 2 ^ 59
def prefixEnd_3017903 : Nat := 4983230072969 + 3 ^ 40 * 3017903 * 2
def baseEnd_3017903 : Nat := 516544935881937058111141

theorem tailTrace_3017903 : CollatzResearch.WordTrace tailWord_3017903 prefixEnd_3017903 516544935881937058111141 := by
  unfold tailWord_3017903
  simp only [CollatzResearch.WordTrace]
  refine ⟨110071965185660322643082363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73381310123773548428721575 110071965185660322643082363)
  ·
    refine ⟨165107947778490483964623545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110071965185660322643082363 165107947778490483964623545)
    ·
      refine ⟨123830960833867862973467659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165107947778490483964623545 123830960833867862973467659)
      ·
        refine ⟨185746441250801794460201489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123830960833867862973467659 185746441250801794460201489)
        ·
          refine ⟨139309830938101345845151117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185746441250801794460201489 139309830938101345845151117)
          ·
            refine ⟨52241186601788004691931669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139309830938101345845151117 52241186601788004691931669)
            ·
              refine ⟨2448805621958812719934297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52241186601788004691931669 2448805621958812719934297)
              ·
                refine ⟨1836604216469109539950723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448805621958812719934297 1836604216469109539950723)
                ·
                  refine ⟨2754906324703664309926085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836604216469109539950723 2754906324703664309926085)
                  ·
                    refine ⟨516544935881937058111141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2754906324703664309926085 516544935881937058111141)
                    ·
                      rfl

theorem cell23_3017903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 4].length) (baseStart_3017903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017903 prefixEnd_3017903 := by exact prefixLift 3017903
  have htrace : WordTrace (prefixWord ++ tailWord_3017903) baseStart_3017903 baseEnd_3017903 := by
    simpa [prefixWord, tailWord_3017903, baseEnd_3017903] using wordTrace_append hprefix tailTrace_3017903
  have hstable : (prefixWord ++ tailWord_3017903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017903).length < 2 ^ (prefixWord ++ tailWord_3017903).sum := by decide
  have hdescent : baseEnd_3017903 < baseStart_3017903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017943 : List Nat := [1, 1, 3, 2, 1, 2, 3, 5, 1, 1, 3]
def baseStart_3017943 : Nat := 118140960795 + 3017943 * 2 ^ 59
def prefixEnd_3017943 : Nat := 4983230072969 + 3 ^ 40 * 3017943 * 2
def baseEnd_3017943 : Nat := 1549655346871991017833239

theorem tailTrace_3017943 : CollatzResearch.WordTrace tailWord_3017943 prefixEnd_3017943 1549655346871991017833239 := by
  unfold tailWord_3017943
  simp only [CollatzResearch.WordTrace]
  refine ⟨110073424105515409474538483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73382282737010272983025655 110073424105515409474538483)
  ·
    refine ⟨165110136158273114211807725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110073424105515409474538483 165110136158273114211807725)
    ·
      refine ⟨61916301059352417829427897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165110136158273114211807725 61916301059352417829427897)
      ·
        refine ⟨46437225794514313372070923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61916301059352417829427897 46437225794514313372070923)
        ·
          refine ⟨69655838691771470058106385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46437225794514313372070923 69655838691771470058106385)
          ·
            refine ⟨52241879018828602543579789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69655838691771470058106385 52241879018828602543579789)
            ·
              refine ⟨19590704632060725953842421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52241879018828602543579789 19590704632060725953842421)
              ·
                refine ⟨1836628559255693058172727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19590704632060725953842421 1836628559255693058172727)
                ·
                  refine ⟨2754942838883539587259091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836628559255693058172727 2754942838883539587259091)
                  ·
                    refine ⟨4132414258325309380888637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2754942838883539587259091 4132414258325309380888637)
                    ·
                      refine ⟨1549655346871991017833239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4132414258325309380888637 1549655346871991017833239)
                      ·
                        rfl

theorem cell23_3017943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_3017943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017943 prefixEnd_3017943 := by exact prefixLift 3017943
  have htrace : WordTrace (prefixWord ++ tailWord_3017943) baseStart_3017943 baseEnd_3017943 := by
    simpa [prefixWord, tailWord_3017943, baseEnd_3017943] using wordTrace_append hprefix tailTrace_3017943
  have hstable : (prefixWord ++ tailWord_3017943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017943).length < 2 ^ (prefixWord ++ tailWord_3017943).sum := by decide
  have hdescent : baseEnd_3017943 < baseStart_3017943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3017983 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 3, 2, 2]
def baseStart_3017983 : Nat := 118140960795 + 3017983 * 2 ^ 59
def prefixEnd_3017983 : Nat := 4983230072969 + 3 ^ 40 * 3017983 * 2
def baseEnd_3017983 : Nat := 1549675886098170861333055

theorem tailTrace_3017983 : CollatzResearch.WordTrace tailWord_3017983 prefixEnd_3017983 1549675886098170861333055 := by
  unfold tailWord_3017983
  simp only [CollatzResearch.WordTrace]
  refine ⟨110074883025370496305994603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73383255350246997537329735 110074883025370496305994603)
  ·
    refine ⟨165112324538055744458991905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110074883025370496305994603 165112324538055744458991905)
    ·
      refine ⟨123834243403541808344243929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165112324538055744458991905 123834243403541808344243929)
      ·
        refine ⟨92875682552656356258182947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123834243403541808344243929 92875682552656356258182947)
        ·
          refine ⟨139313523828984534387274421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92875682552656356258182947 139313523828984534387274421)
          ·
            refine ⟨13060642858967300098806977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139313523828984534387274421 13060642858967300098806977)
            ·
              refine ⟨9795482144225475074105233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13060642858967300098806977 9795482144225475074105233)
              ·
                refine ⟨7346611608169106305578925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9795482144225475074105233 7346611608169106305578925)
                ·
                  refine ⟨2754979353063414864592097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7346611608169106305578925 2754979353063414864592097)
                  ·
                    refine ⟨2066234514797561148444073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2754979353063414864592097 2066234514797561148444073)
                    ·
                      refine ⟨1549675886098170861333055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066234514797561148444073 1549675886098170861333055)
                      ·
                        rfl

theorem cell23_3017983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_3017983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3017983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3017983 prefixEnd_3017983 := by exact prefixLift 3017983
  have htrace : WordTrace (prefixWord ++ tailWord_3017983) baseStart_3017983 baseEnd_3017983 := by
    simpa [prefixWord, tailWord_3017983, baseEnd_3017983] using wordTrace_append hprefix tailTrace_3017983
  have hstable : (prefixWord ++ tailWord_3017983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3017983).length < 2 ^ (prefixWord ++ tailWord_3017983).sum := by decide
  have hdescent : baseEnd_3017983 < baseStart_3017983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3017983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018054 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3018054 : Nat := 118140960795 + 3018054 * 2 ^ 59
def prefixEnd_3018054 : Nat := 4983230072969 + 3 ^ 40 * 3018054 * 2
def baseEnd_3018054 : Nat := 1549712343224640083545229

theorem tailTrace_3018054 : CollatzResearch.WordTrace tailWord_3018054 prefixEnd_3018054 1549712343224640083545229 := by
  unfold tailWord_3018054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3439921019003539857244663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73384981738742183621219477 3439921019003539857244663)
  ·
    refine ⟨5159881528505309785866995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3439921019003539857244663 5159881528505309785866995)
    ·
      refine ⟨7739822292757964678800493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5159881528505309785866995 7739822292757964678800493)
      ·
        refine ⟨2902433359784236754550185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7739822292757964678800493 2902433359784236754550185)
        ·
          refine ⟨2176825019838177565912639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2902433359784236754550185 2176825019838177565912639)
          ·
            refine ⟨3265237529757266348868959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176825019838177565912639 3265237529757266348868959)
            ·
              refine ⟨4897856294635899523303439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265237529757266348868959 4897856294635899523303439)
              ·
                refine ⟨7346784441953849284955159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897856294635899523303439 7346784441953849284955159)
                ·
                  refine ⟨11020176662930773927432739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7346784441953849284955159 11020176662930773927432739)
                  ·
                    refine ⟨16530264994396160891149109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11020176662930773927432739 16530264994396160891149109)
                    ·
                      refine ⟨1549712343224640083545229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16530264994396160891149109 1549712343224640083545229)
                      ·
                        rfl

theorem cell23_3018054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3018054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018054 prefixEnd_3018054 := by exact prefixLift 3018054
  have htrace : WordTrace (prefixWord ++ tailWord_3018054) baseStart_3018054 baseEnd_3018054 := by
    simpa [prefixWord, tailWord_3018054, baseEnd_3018054] using wordTrace_append hprefix tailTrace_3018054
  have hstable : (prefixWord ++ tailWord_3018054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018054).length < 2 ^ (prefixWord ++ tailWord_3018054).sum := by decide
  have hdescent : baseEnd_3018054 < baseStart_3018054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018073 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 4, 2, 2]
def baseStart_3018073 : Nat := 118140960795 + 3018073 * 2 ^ 59
def prefixEnd_3018073 : Nat := 4983230072969 + 3 ^ 40 * 3018073 * 2
def baseEnd_3018073 : Nat := 1549722099357075509207641

theorem tailTrace_3018073 : CollatzResearch.WordTrace tailWord_3018073 prefixEnd_3018073 1549722099357075509207641 := by
  unfold tailWord_3018073
  simp only [CollatzResearch.WordTrace]
  refine ⟨110078165595044441676770873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73385443730029627784513915 110078165595044441676770873)
  ·
    refine ⟨82558624196283331257578155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110078165595044441676770873 82558624196283331257578155)
    ·
      refine ⟨123837936294424996886367233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82558624196283331257578155 123837936294424996886367233)
      ·
        refine ⟨92878452220818747664775425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123837936294424996886367233 92878452220818747664775425)
        ·
          refine ⟨69658839165614060748581569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92878452220818747664775425 69658839165614060748581569)
          ·
            refine ⟨52244129374210545561436177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69658839165614060748581569 52244129374210545561436177)
            ·
              refine ⟨39183097030657909171077133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52244129374210545561436177 39183097030657909171077133)
              ·
                refine ⟨14693661386496715939153925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39183097030657909171077133 14693661386496715939153925)
                ·
                  refine ⟨2755061509968134238591361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14693661386496715939153925 2755061509968134238591361)
                  ·
                    refine ⟨2066296132476100678943521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2755061509968134238591361 2066296132476100678943521)
                    ·
                      refine ⟨1549722099357075509207641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066296132476100678943521 1549722099357075509207641)
                      ·
                        rfl

theorem cell23_3018073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_3018073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018073 prefixEnd_3018073 := by exact prefixLift 3018073
  have htrace : WordTrace (prefixWord ++ tailWord_3018073) baseStart_3018073 baseEnd_3018073 := by
    simpa [prefixWord, tailWord_3018073, baseEnd_3018073] using wordTrace_append hprefix tailTrace_3018073
  have hstable : (prefixWord ++ tailWord_3018073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018073).length < 2 ^ (prefixWord ++ tailWord_3018073).sum := by decide
  have hdescent : baseEnd_3018073 < baseStart_3018073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018079 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 7]
def baseStart_3018079 : Nat := 118140960795 + 3018079 * 2 ^ 59
def prefixEnd_3018079 : Nat := 4983230072969 + 3 ^ 40 * 3018079 * 2
def baseEnd_3018079 : Nat := 172191686693444720636957

theorem tailTrace_3018079 : CollatzResearch.WordTrace tailWord_3018079 prefixEnd_3018079 172191686693444720636957 := by
  unfold tailWord_3018079
  simp only [CollatzResearch.WordTrace]
  refine ⟨110078384433022704701489291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73385589622015136467659527 110078384433022704701489291)
  ·
    refine ⟨165117576649534057052233937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110078384433022704701489291 165117576649534057052233937)
    ·
      refine ⟨123838182487150542789175453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165117576649534057052233937 123838182487150542789175453)
      ·
        refine ⟨46439318432681453545940795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123838182487150542789175453 46439318432681453545940795)
        ·
          refine ⟨69658977649022180318911193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46439318432681453545940795 69658977649022180318911193)
          ·
            refine ⟨52244233236766635239183395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69658977649022180318911193 52244233236766635239183395)
            ·
              refine ⟨78366349855149952858775093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52244233236766635239183395 78366349855149952858775093)
              ·
                refine ⟨7346845298920308080510165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78366349855149952858775093 7346845298920308080510165)
                ·
                  refine ⟨172191686693444720636957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7346845298920308080510165 172191686693444720636957)
                  ·
                    rfl

theorem cell23_3018079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 7].length) (baseStart_3018079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018079 prefixEnd_3018079 := by exact prefixLift 3018079
  have htrace : WordTrace (prefixWord ++ tailWord_3018079) baseStart_3018079 baseEnd_3018079 := by
    simpa [prefixWord, tailWord_3018079, baseEnd_3018079] using wordTrace_append hprefix tailTrace_3018079
  have hstable : (prefixWord ++ tailWord_3018079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018079).length < 2 ^ (prefixWord ++ tailWord_3018079).sum := by decide
  have hdescent : baseEnd_3018079 < baseStart_3018079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018130 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 7]
def baseStart_3018130 : Nat := 118140960795 + 3018130 * 2 ^ 59
def prefixEnd_3018130 : Nat := 4983230072969 + 3 ^ 40 * 3018130 * 2
def baseEnd_3018130 : Nat := 172194596417153531799431

theorem tailTrace_3018130 : CollatzResearch.WordTrace tailWord_3018130 prefixEnd_3018130 172194596417153531799431 := by
  unfold tailWord_3018130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27520061138959485102898961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73386829703891960274397229 27520061138959485102898961)
  ·
    refine ⟨20640045854219613827174221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27520061138959485102898961 20640045854219613827174221)
    ·
      refine ⟨7740017195332355185190333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20640045854219613827174221 7740017195332355185190333)
      ·
        refine ⟨2902506448249633194446375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7740017195332355185190333 2902506448249633194446375)
        ·
          refine ⟨4353759672374449791669563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2902506448249633194446375 4353759672374449791669563)
          ·
            refine ⟨6530639508561674687504345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4353759672374449791669563 6530639508561674687504345)
            ·
              refine ⟨4897979631421256015628259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6530639508561674687504345 4897979631421256015628259)
              ·
                refine ⟨7346969447131884023442389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897979631421256015628259 7346969447131884023442389)
                ·
                  refine ⟨172194596417153531799431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7346969447131884023442389 172194596417153531799431)
                  ·
                    rfl

theorem cell23_3018130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_3018130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018130 prefixEnd_3018130 := by exact prefixLift 3018130
  have htrace : WordTrace (prefixWord ++ tailWord_3018130) baseStart_3018130 baseEnd_3018130 := by
    simpa [prefixWord, tailWord_3018130, baseEnd_3018130] using wordTrace_append hprefix tailTrace_3018130
  have hstable : (prefixWord ++ tailWord_3018130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018130).length < 2 ^ (prefixWord ++ tailWord_3018130).sum := by decide
  have hdescent : baseEnd_3018130 < baseStart_3018130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018180 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3018180 : Nat := 118140960795 + 3018180 * 2 ^ 59
def prefixEnd_3018180 : Nat := 4983230072969 + 3 ^ 40 * 3018180 * 2
def baseEnd_3018180 : Nat := 1549777041787106590569649

theorem tailTrace_3018180 : CollatzResearch.WordTrace tailWord_3018180 prefixEnd_3018180 1549777041787106590569649 := by
  unfold tailWord_3018180
  simp only [CollatzResearch.WordTrace]
  refine ⟨55041034102828399475457997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73388045470437865967277329 55041034102828399475457997)
  ·
    refine ⟨20640387788560649803296749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55041034102828399475457997 20640387788560649803296749)
    ·
      refine ⟨7740145420710243676236281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20640387788560649803296749 7740145420710243676236281)
      ·
        refine ⟨5805109065532682757177211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7740145420710243676236281 5805109065532682757177211)
        ·
          refine ⟨8707663598299024135765817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5805109065532682757177211 8707663598299024135765817)
          ·
            refine ⟨6530747698724268101824363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8707663598299024135765817 6530747698724268101824363)
            ·
              refine ⟨9796121548086402152736545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530747698724268101824363 9796121548086402152736545)
              ·
                refine ⟨7347091161064801614552409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9796121548086402152736545 7347091161064801614552409)
                ·
                  refine ⟨5510318370798601210914307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7347091161064801614552409 5510318370798601210914307)
                  ·
                    refine ⟨8265477556197901816371461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5510318370798601210914307 8265477556197901816371461)
                    ·
                      refine ⟨1549777041787106590569649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8265477556197901816371461 1549777041787106590569649)
                      ·
                        rfl

theorem cell23_3018180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3018180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018180 prefixEnd_3018180 := by exact prefixLift 3018180
  have htrace : WordTrace (prefixWord ++ tailWord_3018180) baseStart_3018180 baseEnd_3018180 := by
    simpa [prefixWord, tailWord_3018180, baseEnd_3018180] using wordTrace_append hprefix tailTrace_3018180
  have hstable : (prefixWord ++ tailWord_3018180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018180).length < 2 ^ (prefixWord ++ tailWord_3018180).sum := by decide
  have hdescent : baseEnd_3018180 < baseStart_3018180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018183 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_3018183 : Nat := 118140960795 + 3018183 * 2 ^ 59
def prefixEnd_3018183 : Nat := 4983230072969 + 3 ^ 40 * 3018183 * 2
def baseEnd_3018183 : Nat := 1549778582229070078832135

theorem tailTrace_3018183 : CollatzResearch.WordTrace tailWord_3018183 prefixEnd_3018183 1549778582229070078832135 := by
  unfold tailWord_3018183
  simp only [CollatzResearch.WordTrace]
  refine ⟨110082177624645930463275203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73388118416430620308850135 110082177624645930463275203)
  ·
    refine ⟨165123266436968895694912805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110082177624645930463275203 165123266436968895694912805)
    ·
      refine ⟨30960612456931667942796151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165123266436968895694912805 30960612456931667942796151)
      ·
        refine ⟨46440918685397501914194227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30960612456931667942796151 46440918685397501914194227)
        ·
          refine ⟨69661378028096252871291341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46440918685397501914194227 69661378028096252871291341)
          ·
            refine ⟨26123016760536094826734253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69661378028096252871291341 26123016760536094826734253)
            ·
              refine ⟨9796131285201035560025345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26123016760536094826734253 9796131285201035560025345)
              ·
                refine ⟨7347098463900776670019009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9796131285201035560025345 7347098463900776670019009)
                ·
                  refine ⟨5510323847925582502514257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7347098463900776670019009 5510323847925582502514257)
                  ·
                    refine ⟨4132742885944186876885693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5510323847925582502514257 4132742885944186876885693)
                    ·
                      refine ⟨1549778582229070078832135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4132742885944186876885693 1549778582229070078832135)
                      ·
                        rfl

theorem cell23_3018183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_3018183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018183 prefixEnd_3018183 := by exact prefixLift 3018183
  have htrace : WordTrace (prefixWord ++ tailWord_3018183) baseStart_3018183 baseEnd_3018183 := by
    simpa [prefixWord, tailWord_3018183, baseEnd_3018183] using wordTrace_append hprefix tailTrace_3018183
  have hstable : (prefixWord ++ tailWord_3018183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018183).length < 2 ^ (prefixWord ++ tailWord_3018183).sum := by decide
  have hdescent : baseEnd_3018183 < baseStart_3018183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018186 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 8]
def baseStart_3018186 : Nat := 118140960795 + 3018186 * 2 ^ 59
def prefixEnd_3018186 : Nat := 4983230072969 + 3 ^ 40 * 3018186 * 2
def baseEnd_3018186 : Nat := 172197791407892618566069

theorem tailTrace_3018186 : CollatzResearch.WordTrace tailWord_3018186 prefixEnd_3018186 172197791407892618566069 := by
  unfold tailWord_3018186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27520571760908765493908603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73388191362423374650422941 27520571760908765493908603)
  ·
    refine ⟨41280857641363148240862905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27520571760908765493908603 41280857641363148240862905)
    ·
      refine ⟨30960643231022361180647179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41280857641363148240862905 30960643231022361180647179)
      ·
        refine ⟨46440964846533541770970769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30960643231022361180647179 46440964846533541770970769)
        ·
          refine ⟨34830723634900156328228077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46440964846533541770970769 34830723634900156328228077)
          ·
            refine ⟨13061521363087558623085529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34830723634900156328228077 13061521363087558623085529)
            ·
              refine ⟨9796141022315668967314147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13061521363087558623085529 9796141022315668967314147)
              ·
                refine ⟨14694211533473503450971221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796141022315668967314147 14694211533473503450971221)
                ·
                  refine ⟨172197791407892618566069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14694211533473503450971221 172197791407892618566069)
                  ·
                    rfl

theorem cell23_3018186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_3018186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018186 prefixEnd_3018186 := by exact prefixLift 3018186
  have htrace : WordTrace (prefixWord ++ tailWord_3018186) baseStart_3018186 baseEnd_3018186 := by
    simpa [prefixWord, tailWord_3018186, baseEnd_3018186] using wordTrace_append hprefix tailTrace_3018186
  have hstable : (prefixWord ++ tailWord_3018186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018186).length < 2 ^ (prefixWord ++ tailWord_3018186).sum := by decide
  have hdescent : baseEnd_3018186 < baseStart_3018186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018190 : List Nat := [4, 1, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_3018190 : Nat := 118140960795 + 3018190 * 2 ^ 59
def prefixEnd_3018190 : Nat := 4983230072969 + 3 ^ 40 * 3018190 * 2
def baseEnd_3018190 : Nat := 516594058864550517148201

theorem tailTrace_3018190 : CollatzResearch.WordTrace tailWord_3018190 prefixEnd_3018190 516594058864550517148201 := by
  unfold tailWord_3018190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13760304116952571332347503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73388288623747047105853349 13760304116952571332347503)
  ·
    refine ⟨20640456175428856998521255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13760304116952571332347503 20640456175428856998521255)
    ·
      refine ⟨30960684263143285497781883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20640456175428856998521255 30960684263143285497781883)
      ·
        refine ⟨46441026394714928246672825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30960684263143285497781883 46441026394714928246672825)
        ·
          refine ⟨34830769796036196185004619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46441026394714928246672825 34830769796036196185004619)
          ·
            refine ⟨52246154694054294277506929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34830769796036196185004619 52246154694054294277506929)
            ·
              refine ⟨39184616020540720708130197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52246154694054294277506929 39184616020540720708130197)
              ·
                refine ⟨1836778875962846283193603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39184616020540720708130197 1836778875962846283193603)
                ·
                  refine ⟨2755168313944269424790405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836778875962846283193603 2755168313944269424790405)
                  ·
                    refine ⟨516594058864550517148201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755168313944269424790405 516594058864550517148201)
                    ·
                      rfl

theorem cell23_3018190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_3018190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018190 prefixEnd_3018190 := by exact prefixLift 3018190
  have htrace : WordTrace (prefixWord ++ tailWord_3018190) baseStart_3018190 baseEnd_3018190 := by
    simpa [prefixWord, tailWord_3018190, baseEnd_3018190] using wordTrace_append hprefix tailTrace_3018190
  have hstable : (prefixWord ++ tailWord_3018190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018190).length < 2 ^ (prefixWord ++ tailWord_3018190).sum := by decide
  have hdescent : baseEnd_3018190 < baseStart_3018190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018223 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 1, 5, 2]
def baseStart_3018223 : Nat := 118140960795 + 3018223 * 2 ^ 59
def prefixEnd_3018223 : Nat := 4983230072969 + 3 ^ 40 * 3018223 * 2
def baseEnd_3018223 : Nat := 1549799121455249922331951

theorem tailTrace_3018223 : CollatzResearch.WordTrace tailWord_3018223 prefixEnd_3018223 1549799121455249922331951 := by
  unfold tailWord_3018223
  simp only [CollatzResearch.WordTrace]
  refine ⟨110083636544501017294731323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73389091029667344863154215 110083636544501017294731323)
  ·
    refine ⟨165125454816751525942096985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110083636544501017294731323 165125454816751525942096985)
    ·
      refine ⟨123844091112563644456572739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165125454816751525942096985 123844091112563644456572739)
      ·
        refine ⟨185766136668845466684859109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123844091112563644456572739 185766136668845466684859109)
        ·
          refine ⟨34831150625408525003411083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185766136668845466684859109 34831150625408525003411083)
          ·
            refine ⟨52246725938112787505116625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34831150625408525003411083 52246725938112787505116625)
            ·
              refine ⟨39185044453584590628837469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52246725938112787505116625 39185044453584590628837469)
              ·
                refine ⟨14694391670094221485814051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39185044453584590628837469 14694391670094221485814051)
                ·
                  refine ⟨22041587505141332228721077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14694391670094221485814051 22041587505141332228721077)
                  ·
                    refine ⟨2066398828606999896442601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22041587505141332228721077 2066398828606999896442601)
                    ·
                      refine ⟨1549799121455249922331951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066398828606999896442601 1549799121455249922331951)
                      ·
                        rfl

theorem cell23_3018223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 5, 2].length) (baseStart_3018223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018223 prefixEnd_3018223 := by exact prefixLift 3018223
  have htrace : WordTrace (prefixWord ++ tailWord_3018223) baseStart_3018223 baseEnd_3018223 := by
    simpa [prefixWord, tailWord_3018223, baseEnd_3018223] using wordTrace_append hprefix tailTrace_3018223
  have hstable : (prefixWord ++ tailWord_3018223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018223).length < 2 ^ (prefixWord ++ tailWord_3018223).sum := by decide
  have hdescent : baseEnd_3018223 < baseStart_3018223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018241 : List Nat := [1, 2, 4, 1, 5, 1, 2, 2, 1, 4]
def baseStart_3018241 : Nat := 118140960795 + 3018241 * 2 ^ 59
def prefixEnd_3018241 : Nat := 4983230072969 + 3 ^ 40 * 3018241 * 2
def baseEnd_3018241 : Nat := 516602788035676950635623

theorem tailTrace_3018241 : CollatzResearch.WordTrace tailWord_3018241 prefixEnd_3018241 516602788035676950635623 := by
  unfold tailWord_3018241
  simp only [CollatzResearch.WordTrace]
  refine ⟨110084293058435806368886577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73389528705623870912591051 110084293058435806368886577)
  ·
    refine ⟨82563219793826854776664933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110084293058435806368886577 82563219793826854776664933)
    ·
      refine ⟨15480603711342535270624675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82563219793826854776664933 15480603711342535270624675)
      ·
        refine ⟨23220905567013802905937013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15480603711342535270624675 23220905567013802905937013)
        ·
          refine ⟨2176959896907544022431595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23220905567013802905937013 2176959896907544022431595)
          ·
            refine ⟨3265439845361316033647393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176959896907544022431595 3265439845361316033647393)
            ·
              refine ⟨2449079884020987025235545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3265439845361316033647393 2449079884020987025235545)
              ·
                refine ⟨1836809913015740268926659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2449079884020987025235545 1836809913015740268926659)
                ·
                  refine ⟨2755214869523610403389989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836809913015740268926659 2755214869523610403389989)
                  ·
                    refine ⟨516602788035676950635623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755214869523610403389989 516602788035676950635623)
                    ·
                      rfl

theorem cell23_3018241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_3018241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018241 prefixEnd_3018241 := by exact prefixLift 3018241
  have htrace : WordTrace (prefixWord ++ tailWord_3018241) baseStart_3018241 baseEnd_3018241 := by
    simpa [prefixWord, tailWord_3018241, baseEnd_3018241] using wordTrace_append hprefix tailTrace_3018241
  have hstable : (prefixWord ++ tailWord_3018241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018241).length < 2 ^ (prefixWord ++ tailWord_3018241).sum := by decide
  have hdescent : baseEnd_3018241 < baseStart_3018241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018297 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 2, 4]
def baseStart_3018297 : Nat := 118140960795 + 3018297 * 2 ^ 59
def prefixEnd_3018297 : Nat := 4983230072969 + 3 ^ 40 * 3018297 * 2
def baseEnd_3018297 : Nat := 516612373007894210935537

theorem tailTrace_3018297 : CollatzResearch.WordTrace tailWord_3018297 prefixEnd_3018297 516612373007894210935537 := by
  unfold tailWord_3018297
  simp only [CollatzResearch.WordTrace]
  refine ⟨110086335546232927932925145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73390890364155285288616763 110086335546232927932925145)
  ·
    refine ⟨82564751659674695949693859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110086335546232927932925145 82564751659674695949693859)
    ·
      refine ⟨123847127489512043924540789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82564751659674695949693859 123847127489512043924540789)
      ·
        refine ⟨11610668202141754117925699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123847127489512043924540789 11610668202141754117925699)
        ·
          refine ⟨17416002303212631176888549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11610668202141754117925699 17416002303212631176888549)
          ·
            refine ⟨3265500431852368345666603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17416002303212631176888549 3265500431852368345666603)
            ·
              refine ⟨4898250647778552518499905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265500431852368345666603 4898250647778552518499905)
              ·
                refine ⟨3673687985833914388874929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4898250647778552518499905 3673687985833914388874929)
                ·
                  refine ⟨2755265989375435791656197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3673687985833914388874929 2755265989375435791656197)
                  ·
                    refine ⟨516612373007894210935537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755265989375435791656197 516612373007894210935537)
                    ·
                      rfl

theorem cell23_3018297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 4].length) (baseStart_3018297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018297 prefixEnd_3018297 := by exact prefixLift 3018297
  have htrace : WordTrace (prefixWord ++ tailWord_3018297) baseStart_3018297 baseEnd_3018297 := by
    simpa [prefixWord, tailWord_3018297, baseEnd_3018297] using wordTrace_append hprefix tailTrace_3018297
  have hstable : (prefixWord ++ tailWord_3018297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018297).length < 2 ^ (prefixWord ++ tailWord_3018297).sum := by decide
  have hdescent : baseEnd_3018297 < baseStart_3018297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018330 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2]
def baseStart_3018330 : Nat := 118140960795 + 3018330 * 2 ^ 59
def prefixEnd_3018330 : Nat := 4983230072969 + 3 ^ 40 * 3018330 * 2
def baseEnd_3018330 : Nat := 1549854063885281003693959

theorem tailTrace_3018330 : CollatzResearch.WordTrace tailWord_3018330 prefixEnd_3018330 1549854063885281003693959 := by
  unfold tailWord_3018330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27521884788778343642219111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73391692770075583045917629 27521884788778343642219111)
  ·
    refine ⟨41282827183167515463328667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27521884788778343642219111 41282827183167515463328667)
    ·
      refine ⟨61924240774751273194993001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41282827183167515463328667 61924240774751273194993001)
      ·
        refine ⟨46443180581063454896244751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61924240774751273194993001 46443180581063454896244751)
        ·
          refine ⟨69664770871595182344367127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46443180581063454896244751 69664770871595182344367127)
          ·
            refine ⟨104497156307392773516550691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69664770871595182344367127 104497156307392773516550691)
            ·
              refine ⟨156745734461089160274826037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104497156307392773516550691 156745734461089160274826037)
              ·
                refine ⟨14694912605727108775764941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156745734461089160274826037 14694912605727108775764941)
                ·
                  refine ⟨5510592227147665790911853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14694912605727108775764941 5510592227147665790911853)
                  ·
                    refine ⟨2066472085180374671591945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5510592227147665790911853 2066472085180374671591945)
                    ·
                      refine ⟨1549854063885281003693959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066472085180374671591945 1549854063885281003693959)
                      ·
                        rfl

theorem cell23_3018330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_3018330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018330 prefixEnd_3018330 := by exact prefixLift 3018330
  have htrace : WordTrace (prefixWord ++ tailWord_3018330) baseStart_3018330 baseEnd_3018330 := by
    simpa [prefixWord, tailWord_3018330, baseEnd_3018330] using wordTrace_append hprefix tailTrace_3018330
  have hstable : (prefixWord ++ tailWord_3018330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018330).length < 2 ^ (prefixWord ++ tailWord_3018330).sum := by decide
  have hdescent : baseEnd_3018330 < baseStart_3018330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018363 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 3]
def baseStart_3018363 : Nat := 118140960795 + 3018363 * 2 ^ 59
def prefixEnd_3018363 : Nat := 4983230072969 + 3 ^ 40 * 3018363 * 2
def baseEnd_3018363 : Nat := 1549871008746879374581307

theorem tailTrace_3018363 : CollatzResearch.WordTrace tailWord_3018363 prefixEnd_3018363 1549871008746879374581307 := by
  unfold tailWord_3018363
  simp only [CollatzResearch.WordTrace]
  refine ⟨110088742763993821204827743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73392495175995880803218495 110088742763993821204827743)
  ·
    refine ⟨165133114145990731807241615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110088742763993821204827743 165133114145990731807241615)
    ·
      refine ⟨247699671218986097710862423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165133114145990731807241615 247699671218986097710862423)
      ·
        refine ⟨371549506828479146566293635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247699671218986097710862423 371549506828479146566293635)
        ·
          refine ⟨557324260242718719849440453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371549506828479146566293635 557324260242718719849440453)
          ·
            refine ⟨104498298795509759971770085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 557324260242718719849440453 104498298795509759971770085)
            ·
              refine ⟨19593431024158079994706891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104498298795509759971770085 19593431024158079994706891)
              ·
                refine ⟨29390146536237119992060337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19593431024158079994706891 29390146536237119992060337)
                ·
                  refine ⟨22042609902177839994045253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29390146536237119992060337 22042609902177839994045253)
                  ·
                    refine ⟨4132989356658344998883485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22042609902177839994045253 4132989356658344998883485)
                    ·
                      refine ⟨1549871008746879374581307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4132989356658344998883485 1549871008746879374581307)
                      ·
                        rfl

theorem cell23_3018363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 3].length) (baseStart_3018363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018363 prefixEnd_3018363 := by exact prefixLift 3018363
  have htrace : WordTrace (prefixWord ++ tailWord_3018363) baseStart_3018363 baseEnd_3018363 := by
    simpa [prefixWord, tailWord_3018363, baseEnd_3018363] using wordTrace_append hprefix tailTrace_3018363
  have hstable : (prefixWord ++ tailWord_3018363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018363).length < 2 ^ (prefixWord ++ tailWord_3018363).sum := by decide
  have hdescent : baseEnd_3018363 < baseStart_3018363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018373 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_3018373 : Nat := 118140960795 + 3018373 * 2 ^ 59
def prefixEnd_3018373 : Nat := 4983230072969 + 3 ^ 40 * 3018373 * 2
def baseEnd_3018373 : Nat := 1549876143553424335456261

theorem tailTrace_3018373 : CollatzResearch.WordTrace tailWord_3018373 prefixEnd_3018373 1549876143553424335456261 := by
  unfold tailWord_3018373
  simp only [CollatzResearch.WordTrace]
  refine ⟨110089107493957592912691773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73392738329305061941794515 110089107493957592912691773)
  ·
    refine ⟨41283415310234097342259415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110089107493957592912691773 41283415310234097342259415)
    ·
      refine ⟨61925122965351146013389123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41283415310234097342259415 61925122965351146013389123)
      ·
        refine ⟨92887684448026719020083685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61925122965351146013389123 92887684448026719020083685)
        ·
          refine ⟨17416440834005009816265691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92887684448026719020083685 17416440834005009816265691)
          ·
            refine ⟨26124661251007514724398537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17416440834005009816265691 26124661251007514724398537)
            ·
              refine ⟨19593495938255636043298903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26124661251007514724398537 19593495938255636043298903)
              ·
                refine ⟨29390243907383454064948355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19593495938255636043298903 29390243907383454064948355)
                ·
                  refine ⟨44085365861075181097422533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29390243907383454064948355 44085365861075181097422533)
                  ·
                    refine ⟨8266006098951596455766725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44085365861075181097422533 8266006098951596455766725)
                    ·
                      refine ⟨1549876143553424335456261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8266006098951596455766725 1549876143553424335456261)
                      ·
                        rfl

theorem cell23_3018373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_3018373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018373 prefixEnd_3018373 := by exact prefixLift 3018373
  have htrace : WordTrace (prefixWord ++ tailWord_3018373) baseStart_3018373 baseEnd_3018373 := by
    simpa [prefixWord, tailWord_3018373, baseEnd_3018373] using wordTrace_append hprefix tailTrace_3018373
  have hstable : (prefixWord ++ tailWord_3018373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018373).length < 2 ^ (prefixWord ++ tailWord_3018373).sum := by decide
  have hdescent : baseEnd_3018373 < baseStart_3018373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018393 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 3]
def baseStart_3018393 : Nat := 118140960795 + 3018393 * 2 ^ 59
def prefixEnd_3018393 : Nat := 4983230072969 + 3 ^ 40 * 3018393 * 2
def baseEnd_3018393 : Nat := 1549886413166514257206169

theorem tailTrace_3018393 : CollatzResearch.WordTrace tailWord_3018393 prefixEnd_3018393 1549886413166514257206169 := by
  unfold tailWord_3018393
  simp only [CollatzResearch.WordTrace]
  refine ⟨110089836953885136328419833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73393224635923424218946555 110089836953885136328419833)
  ·
    refine ⟨82567377715413852246314875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110089836953885136328419833 82567377715413852246314875)
    ·
      refine ⟨123851066573120778369472313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82567377715413852246314875 123851066573120778369472313)
      ·
        refine ⟨92888299929840583777104235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123851066573120778369472313 92888299929840583777104235)
        ·
          refine ⟨139332449894760875665656353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92888299929840583777104235 139332449894760875665656353)
          ·
            refine ⟨104499337421070656749242265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139332449894760875665656353 104499337421070656749242265)
            ·
              refine ⟨78374503065802992561931699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104499337421070656749242265 78374503065802992561931699)
              ·
                refine ⟨117561754598704488842897549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78374503065802992561931699 117561754598704488842897549)
                ·
                  refine ⟨44085657974514183316086581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117561754598704488842897549 44085657974514183316086581)
                  ·
                    refine ⟨4133030435110704685883117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44085657974514183316086581 4133030435110704685883117)
                    ·
                      refine ⟨1549886413166514257206169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4133030435110704685883117 1549886413166514257206169)
                      ·
                        rfl

theorem cell23_3018393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_3018393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018393 prefixEnd_3018393 := by exact prefixLift 3018393
  have htrace : WordTrace (prefixWord ++ tailWord_3018393) baseStart_3018393 baseEnd_3018393 := by
    simpa [prefixWord, tailWord_3018393, baseEnd_3018393] using wordTrace_append hprefix tailTrace_3018393
  have hstable : (prefixWord ++ tailWord_3018393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018393).length < 2 ^ (prefixWord ++ tailWord_3018393).sum := by decide
  have hdescent : baseEnd_3018393 < baseStart_3018393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018463 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_3018463 : Nat := 118140960795 + 3018463 * 2 ^ 59
def prefixEnd_3018463 : Nat := 4983230072969 + 3 ^ 40 * 3018463 * 2
def baseEnd_3018463 : Nat := 1549922356812328983330847

theorem tailTrace_3018463 : CollatzResearch.WordTrace tailWord_3018463 prefixEnd_3018463 1549922356812328983330847 := by
  unfold tailWord_3018463
  simp only [CollatzResearch.WordTrace]
  refine ⟨110092390063631538283468043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73394926709087692188978695 110092390063631538283468043)
  ·
    refine ⟨165138585095447307425202065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110092390063631538283468043 165138585095447307425202065)
    ·
      refine ⟨123853938821585480568901549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165138585095447307425202065 123853938821585480568901549)
      ·
        refine ⟨46445227058094555213338081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123853938821585480568901549 46445227058094555213338081)
        ·
          refine ⟨34833920293570916410003561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46445227058094555213338081 34833920293570916410003561)
          ·
            refine ⟨26125440220178187307502671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34833920293570916410003561 26125440220178187307502671)
            ·
              refine ⟨39188160330267280961254007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26125440220178187307502671 39188160330267280961254007)
              ·
                refine ⟨58782240495400921441881011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39188160330267280961254007 58782240495400921441881011)
                ·
                  refine ⟨88173360743101382162821517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58782240495400921441881011 88173360743101382162821517)
                  ·
                    refine ⟨33065010278663018311058069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88173360743101382162821517 33065010278663018311058069)
                    ·
                      refine ⟨1549922356812328983330847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33065010278663018311058069 1549922356812328983330847)
                      ·
                        rfl

theorem cell23_3018463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_3018463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018463 prefixEnd_3018463 := by exact prefixLift 3018463
  have htrace : WordTrace (prefixWord ++ tailWord_3018463) baseStart_3018463 baseEnd_3018463 := by
    simpa [prefixWord, tailWord_3018463, baseEnd_3018463] using wordTrace_append hprefix tailTrace_3018463
  have hstable : (prefixWord ++ tailWord_3018463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018463).length < 2 ^ (prefixWord ++ tailWord_3018463).sum := by decide
  have hdescent : baseEnd_3018463 < baseStart_3018463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018477 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_3018477 : Nat := 118140960795 + 3018477 * 2 ^ 59
def prefixEnd_3018477 : Nat := 4983230072969 + 3 ^ 40 * 3018477 * 2
def baseEnd_3018477 : Nat := 516643181847163976185261

theorem tailTrace_3018477 : CollatzResearch.WordTrace tailWord_3018477 prefixEnd_3018477 516643181847163976185261 := by
  unfold tailWord_3018477
  simp only [CollatzResearch.WordTrace]
  refine ⟨110092900685580818674477685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73395267123720545782985123 110092900685580818674477685)
  ·
    refine ⟨10321209439273201750732283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110092900685580818674477685 10321209439273201750732283)
    ·
      refine ⟨15481814158909802626098425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10321209439273201750732283 15481814158909802626098425)
      ·
        refine ⟨11611360619182351969573819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15481814158909802626098425 11611360619182351969573819)
        ·
          refine ⟨17417040928773527954360729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11611360619182351969573819 17417040928773527954360729)
          ·
            refine ⟨13062780696580145965770547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17417040928773527954360729 13062780696580145965770547)
            ·
              refine ⟨19594171044870218948655821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062780696580145965770547 19594171044870218948655821)
              ·
                refine ⟨7347814141826332105745933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19594171044870218948655821 7347814141826332105745933)
                ·
                  refine ⟨2755430303184874539654725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7347814141826332105745933 2755430303184874539654725)
                  ·
                    refine ⟨516643181847163976185261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755430303184874539654725 516643181847163976185261)
                    ·
                      rfl

theorem cell23_3018477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_3018477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018477 prefixEnd_3018477 := by exact prefixLift 3018477
  have htrace : WordTrace (prefixWord ++ tailWord_3018477) baseStart_3018477 baseEnd_3018477 := by
    simpa [prefixWord, tailWord_3018477, baseEnd_3018477] using wordTrace_append hprefix tailTrace_3018477
  have hstable : (prefixWord ++ tailWord_3018477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018477).length < 2 ^ (prefixWord ++ tailWord_3018477).sum := by decide
  have hdescent : baseEnd_3018477 < baseStart_3018477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018484 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3018484 : Nat := 118140960795 + 3018484 * 2 ^ 59
def prefixEnd_3018484 : Nat := 4983230072969 + 3 ^ 40 * 3018484 * 2
def baseEnd_3018484 : Nat := 1549933139906073401168251

theorem tailTrace_3018484 : CollatzResearch.WordTrace tailWord_3018484 prefixEnd_3018484 1549933139906073401168251 := by
  unfold tailWord_3018484
  simp only [CollatzResearch.WordTrace]
  refine ⟨55046577998277729434991253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73395437331036972579988337 55046577998277729434991253)
  ·
    refine ⟨2580308343669268567265215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55046577998277729434991253 2580308343669268567265215)
    ·
      refine ⟨3870462515503902850897823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580308343669268567265215 3870462515503902850897823)
      ·
        refine ⟨5805693773255854276346735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870462515503902850897823 5805693773255854276346735)
        ·
          refine ⟨8708540659883781414520103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5805693773255854276346735 8708540659883781414520103)
          ·
            refine ⟨13062810989825672121780155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708540659883781414520103 13062810989825672121780155)
            ·
              refine ⟨19594216484738508182670233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062810989825672121780155 19594216484738508182670233)
              ·
                refine ⟨14695662363553881137002675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19594216484738508182670233 14695662363553881137002675)
                ·
                  refine ⟨22043493545330821705504013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14695662363553881137002675 22043493545330821705504013)
                  ·
                    refine ⟨8266310079499058139564005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22043493545330821705504013 8266310079499058139564005)
                    ·
                      refine ⟨1549933139906073401168251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8266310079499058139564005 1549933139906073401168251)
                      ·
                        rfl

theorem cell23_3018484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3018484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018484 prefixEnd_3018484 := by exact prefixLift 3018484
  have htrace : WordTrace (prefixWord ++ tailWord_3018484) baseStart_3018484 baseEnd_3018484 := by
    simpa [prefixWord, tailWord_3018484, baseEnd_3018484] using wordTrace_append hprefix tailTrace_3018484
  have hstable : (prefixWord ++ tailWord_3018484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018484).length < 2 ^ (prefixWord ++ tailWord_3018484).sum := by decide
  have hdescent : baseEnd_3018484 < baseStart_3018484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018502 : List Nat := [6, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3018502 : Nat := 118140960795 + 3018502 * 2 ^ 59
def prefixEnd_3018502 : Nat := 4983230072969 + 3 ^ 40 * 3018502 * 2
def baseEnd_3018502 : Nat := 172215820284206036749241

theorem tailTrace_3018502 : CollatzResearch.WordTrace tailWord_3018502 prefixEnd_3018502 172215820284206036749241 := by
  unfold tailWord_3018502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440431640952820248254305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73395875006993498629425173 3440431640952820248254305)
  ·
    refine ⟨2580323730714615186190729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3440431640952820248254305 2580323730714615186190729)
    ·
      refine ⟨1935242798035961389643047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2580323730714615186190729 1935242798035961389643047)
      ·
        refine ⟨2902864197053942084464571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1935242798035961389643047 2902864197053942084464571)
        ·
          refine ⟨4354296295580913126696857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2902864197053942084464571 4354296295580913126696857)
          ·
            refine ⟨3265722221685684845022643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4354296295580913126696857 3265722221685684845022643)
            ·
              refine ⟨4898583332528527267533965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265722221685684845022643 4898583332528527267533965)
              ·
                refine ⟨1836968749698197725325237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4898583332528527267533965 1836968749698197725325237)
                ·
                  refine ⟨172215820284206036749241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1836968749698197725325237 172215820284206036749241)
                  ·
                    rfl

theorem cell23_3018502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3018502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018502 prefixEnd_3018502 := by exact prefixLift 3018502
  have htrace : WordTrace (prefixWord ++ tailWord_3018502) baseStart_3018502 baseEnd_3018502 := by
    simpa [prefixWord, tailWord_3018502, baseEnd_3018502] using wordTrace_append hprefix tailTrace_3018502
  have hstable : (prefixWord ++ tailWord_3018502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018502).length < 2 ^ (prefixWord ++ tailWord_3018502).sum := by decide
  have hdescent : baseEnd_3018502 < baseStart_3018502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018554 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_3018554 : Nat := 118140960795 + 3018554 * 2 ^ 59
def prefixEnd_3018554 : Nat := 4983230072969 + 3 ^ 40 * 3018554 * 2
def baseEnd_3018554 : Nat := 516656361183962709097643

theorem tailTrace_3018554 : CollatzResearch.WordTrace tailWord_3018554 prefixEnd_3018554 516656361183962709097643 := by
  unfold tailWord_3018554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27523927276575465206257679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73397139404201240550020477 27523927276575465206257679)
  ·
    refine ⟨41285890914863197809386519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27523927276575465206257679 41285890914863197809386519)
    ·
      refine ⟨61928836372294796714079779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41285890914863197809386519 61928836372294796714079779)
      ·
        refine ⟨92893254558442195071119669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61928836372294796714079779 92893254558442195071119669)
        ·
          refine ⟨8708742614853955787917469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92893254558442195071119669 8708742614853955787917469)
          ·
            refine ⟨3265778480570233420469051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8708742614853955787917469 3265778480570233420469051)
            ·
              refine ⟨4898667720855350130703577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265778480570233420469051 4898667720855350130703577)
              ·
                refine ⟨3674000790641512598027683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4898667720855350130703577 3674000790641512598027683)
                ·
                  refine ⟨5511001185962268897041525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674000790641512598027683 5511001185962268897041525)
                  ·
                    refine ⟨516656361183962709097643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5511001185962268897041525 516656361183962709097643)
                    ·
                      rfl

theorem cell23_3018554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_3018554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018554 prefixEnd_3018554 := by exact prefixLift 3018554
  have htrace : WordTrace (prefixWord ++ tailWord_3018554) baseStart_3018554 baseEnd_3018554 := by
    simpa [prefixWord, tailWord_3018554, baseEnd_3018554] using wordTrace_append hprefix tailTrace_3018554
  have hstable : (prefixWord ++ tailWord_3018554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018554).length < 2 ^ (prefixWord ++ tailWord_3018554).sum := by decide
  have hdescent : baseEnd_3018554 < baseStart_3018554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018577 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_3018577 : Nat := 118140960795 + 3018577 * 2 ^ 59
def prefixEnd_3018577 : Nat := 4983230072969 + 3 ^ 40 * 3018577 * 2
def baseEnd_3018577 : Nat := 1549980893606941537305323

theorem tailTrace_3018577 : CollatzResearch.WordTrace tailWord_3018577 prefixEnd_3018577 1549980893606941537305323 := by
  unfold tailWord_3018577
  simp only [CollatzResearch.WordTrace]
  refine ⟨110096547985218535753117985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73397698656812357168745323 110096547985218535753117985)
  ·
    refine ⟨82572410988913901814838489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110096547985218535753117985 82572410988913901814838489)
    ·
      refine ⟨61929308241685426361128867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82572410988913901814838489 61929308241685426361128867)
      ·
        refine ⟨92893962362528139541693301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61929308241685426361128867 92893962362528139541693301)
        ·
          refine ⟨8708808971487013082033747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92893962362528139541693301 8708808971487013082033747)
          ·
            refine ⟨13063213457230519623050621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708808971487013082033747 13063213457230519623050621)
            ·
              refine ⟨4898705046461444858643983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13063213457230519623050621 4898705046461444858643983)
              ·
                refine ⟨7348057569692167287965975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898705046461444858643983 7348057569692167287965975)
                ·
                  refine ⟨11022086354538250931948963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7348057569692167287965975 11022086354538250931948963)
                  ·
                    refine ⟨16533129531807376397923445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11022086354538250931948963 16533129531807376397923445)
                    ·
                      refine ⟨1549980893606941537305323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16533129531807376397923445 1549980893606941537305323)
                      ·
                        rfl

theorem cell23_3018577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_3018577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018577 prefixEnd_3018577 := by exact prefixLift 3018577
  have htrace : WordTrace (prefixWord ++ tailWord_3018577) baseStart_3018577 baseEnd_3018577 := by
    simpa [prefixWord, tailWord_3018577, baseEnd_3018577] using wordTrace_append hprefix tailTrace_3018577
  have hstable : (prefixWord ++ tailWord_3018577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018577).length < 2 ^ (prefixWord ++ tailWord_3018577).sum := by decide
  have hdescent : baseEnd_3018577 < baseStart_3018577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018580 : List Nat := [2, 4, 1, 1, 3, 12]
def baseStart_3018580 : Nat := 118140960795 + 3018580 * 2 ^ 59
def prefixEnd_3018580 : Nat := 4983230072969 + 3 ^ 40 * 3018580 * 2
def baseEnd_3018580 : Nat := 6378528535180679117563

theorem tailTrace_3018580 : CollatzResearch.WordTrace tailWord_3018580 prefixEnd_3018580 6378528535180679117563 := by
  unfold tailWord_3018580
  simp only [CollatzResearch.WordTrace]
  refine ⟨55048328702103833632738597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73397771602805111510318129 55048328702103833632738597)
  ·
    refine ⟨10321561631644468806138487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55048328702103833632738597 10321561631644468806138487)
    ·
      refine ⟨15482342447466703209207731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10321561631644468806138487 15482342447466703209207731)
      ·
        refine ⟨23223513671200054813811597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15482342447466703209207731 23223513671200054813811597)
        ·
          refine ⟨8708817626700020555179349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23223513671200054813811597 8708817626700020555179349)
          ·
            refine ⟨6378528535180679117563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8708817626700020555179349 6378528535180679117563)
            ·
              rfl

theorem cell23_3018580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 12].length) (baseStart_3018580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018580 prefixEnd_3018580 := by exact prefixLift 3018580
  have htrace : WordTrace (prefixWord ++ tailWord_3018580) baseStart_3018580 baseEnd_3018580 := by
    simpa [prefixWord, tailWord_3018580, baseEnd_3018580] using wordTrace_append hprefix tailTrace_3018580
  have hstable : (prefixWord ++ tailWord_3018580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018580).length < 2 ^ (prefixWord ++ tailWord_3018580).sum := by decide
  have hdescent : baseEnd_3018580 < baseStart_3018580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018594 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3018594 : Nat := 118140960795 + 3018594 * 2 ^ 59
def prefixEnd_3018594 : Nat := 4983230072969 + 3 ^ 40 * 3018594 * 2
def baseEnd_3018594 : Nat := 1549989622778067970792745

theorem tailTrace_3018594 : CollatzResearch.WordTrace tailWord_3018594 prefixEnd_3018594 1549989622778067970792745 := by
  unfold tailWord_3018594
  simp only [CollatzResearch.WordTrace]
  refine ⟨27524292006539236914121709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73398112017437965104324557 27524292006539236914121709)
  ·
    refine ⟨10321609502452213842795641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27524292006539236914121709 10321609502452213842795641)
    ·
      refine ⟨7741207126839160382096731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10321609502452213842795641 7741207126839160382096731)
      ·
        refine ⟨11611810690258740573145097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7741207126839160382096731 11611810690258740573145097)
        ·
          refine ⟨8708858017694055429858823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11611810690258740573145097 8708858017694055429858823)
          ·
            refine ⟨13063287026541083144788235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708858017694055429858823 13063287026541083144788235)
            ·
              refine ⟨19594930539811624717182353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13063287026541083144788235 19594930539811624717182353)
              ·
                refine ⟨14696197904858718537886765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19594930539811624717182353 14696197904858718537886765)
                ·
                  refine ⟨5511074214322019451707537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14696197904858718537886765 5511074214322019451707537)
                  ·
                    refine ⟨4133305660741514588780653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5511074214322019451707537 4133305660741514588780653)
                    ·
                      refine ⟨1549989622778067970792745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4133305660741514588780653 1549989622778067970792745)
                      ·
                        rfl

theorem cell23_3018594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3018594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018594 prefixEnd_3018594 := by exact prefixLift 3018594
  have htrace : WordTrace (prefixWord ++ tailWord_3018594) baseStart_3018594 baseEnd_3018594 := by
    simpa [prefixWord, tailWord_3018594, baseEnd_3018594] using wordTrace_append hprefix tailTrace_3018594
  have hstable : (prefixWord ++ tailWord_3018594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018594).length < 2 ^ (prefixWord ++ tailWord_3018594).sum := by decide
  have hdescent : baseEnd_3018594 < baseStart_3018594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018607 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 3]
def baseStart_3018607 : Nat := 118140960795 + 3018607 * 2 ^ 59
def prefixEnd_3018607 : Nat := 4983230072969 + 3 ^ 40 * 3018607 * 2
def baseEnd_3018607 : Nat := 1549996298026576419930185

theorem tailTrace_3018607 : CollatzResearch.WordTrace tailWord_3018607 prefixEnd_3018607 1549996298026576419930185 := by
  unfold tailWord_3018607
  simp only [CollatzResearch.WordTrace]
  refine ⟨110097642175109850876710075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73398428116739900584473383 110097642175109850876710075)
  ·
    refine ⟨165146463262664776315065113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110097642175109850876710075 165146463262664776315065113)
    ·
      refine ⟨123859847446998582236298835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165146463262664776315065113 123859847446998582236298835)
      ·
        refine ⟨185789771170497873354448253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123859847446998582236298835 185789771170497873354448253)
        ·
          refine ⟨69671164188936702507918095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185789771170497873354448253 69671164188936702507918095)
          ·
            refine ⟨104506746283405053761877143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69671164188936702507918095 104506746283405053761877143)
            ·
              refine ⟨156760119425107580642815715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104506746283405053761877143 156760119425107580642815715)
              ·
                refine ⟨235140179137661370964223573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156760119425107580642815715 235140179137661370964223573)
                ·
                  refine ⟨2755548974269469190986995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 235140179137661370964223573 2755548974269469190986995)
                  ·
                    refine ⟨4133323461404203786480493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2755548974269469190986995 4133323461404203786480493)
                    ·
                      refine ⟨1549996298026576419930185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4133323461404203786480493 1549996298026576419930185)
                      ·
                        rfl

theorem cell23_3018607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 3].length) (baseStart_3018607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018607 prefixEnd_3018607 := by exact prefixLift 3018607
  have htrace : WordTrace (prefixWord ++ tailWord_3018607) baseStart_3018607 baseEnd_3018607 := by
    simpa [prefixWord, tailWord_3018607, baseEnd_3018607] using wordTrace_append hprefix tailTrace_3018607
  have hstable : (prefixWord ++ tailWord_3018607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018607).length < 2 ^ (prefixWord ++ tailWord_3018607).sum := by decide
  have hdescent : baseEnd_3018607 < baseStart_3018607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018610 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_3018610 : Nat := 118140960795 + 3018610 * 2 ^ 59
def prefixEnd_3018610 : Nat := 4983230072969 + 3 ^ 40 * 3018610 * 2
def baseEnd_3018610 : Nat := 516665946156179969397557

theorem tailTrace_3018610 : CollatzResearch.WordTrace tailWord_3018610 prefixEnd_3018610 516665946156179969397557 := by
  unfold tailWord_3018610
  simp only [CollatzResearch.WordTrace]
  refine ⟨27524437898524745597267321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73398501062732654926046189 27524437898524745597267321)
  ·
    refine ⟨20643328423893559197950491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27524437898524745597267321 20643328423893559197950491)
    ·
      refine ⟨30964992635840338796925737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20643328423893559197950491 30964992635840338796925737)
      ·
        refine ⟨23223744476880254097694303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30964992635840338796925737 23223744476880254097694303)
        ·
          refine ⟨34835616715320381146541455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23223744476880254097694303 34835616715320381146541455)
          ·
            refine ⟨52253425072980571719812183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34835616715320381146541455 52253425072980571719812183)
            ·
              refine ⟨78380137609470857579718275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52253425072980571719812183 78380137609470857579718275)
              ·
                refine ⟨117570206414206286369577413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78380137609470857579718275 117570206414206286369577413)
                ·
                  refine ⟨22044413702663678694295765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117570206414206286369577413 22044413702663678694295765)
                  ·
                    refine ⟨516665946156179969397557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22044413702663678694295765 516665946156179969397557)
                    ·
                      rfl

theorem cell23_3018610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_3018610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018610 prefixEnd_3018610 := by exact prefixLift 3018610
  have htrace : WordTrace (prefixWord ++ tailWord_3018610) baseStart_3018610 baseEnd_3018610 := by
    simpa [prefixWord, tailWord_3018610, baseEnd_3018610] using wordTrace_append hprefix tailTrace_3018610
  have hstable : (prefixWord ++ tailWord_3018610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018610).length < 2 ^ (prefixWord ++ tailWord_3018610).sum := by decide
  have hdescent : baseEnd_3018610 < baseStart_3018610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018625 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_3018625 : Nat := 118140960795 + 3018625 * 2 ^ 59
def prefixEnd_3018625 : Nat := 4983230072969 + 3 ^ 40 * 3018625 * 2
def baseEnd_3018625 : Nat := 1550005540678357349505103

theorem tailTrace_3018625 : CollatzResearch.WordTrace tailWord_3018625 prefixEnd_3018625 1550005540678357349505103 := by
  unfold tailWord_3018625
  simp only [CollatzResearch.WordTrace]
  refine ⟨110098298689044639950865329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73398865792696426633910219 110098298689044639950865329)
  ·
    refine ⟨82573724016783479963148997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110098298689044639950865329 82573724016783479963148997)
    ·
      refine ⟨15482573253146902493090437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82573724016783479963148997 15482573253146902493090437)
      ·
        refine ⟨2902982484965044217454457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15482573253146902493090437 2902982484965044217454457)
        ·
          refine ⟨2177236863723783163090843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2902982484965044217454457 2177236863723783163090843)
          ·
            refine ⟨3265855295585674744636265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177236863723783163090843 3265855295585674744636265)
            ·
              refine ⟨2449391471689256058477199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3265855295585674744636265 2449391471689256058477199)
              ·
                refine ⟨3674087207533884087715799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449391471689256058477199 3674087207533884087715799)
                ·
                  refine ⟨5511130811300826131573699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674087207533884087715799 5511130811300826131573699)
                  ·
                    refine ⟨8266696216951239197360549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511130811300826131573699 8266696216951239197360549)
                    ·
                      refine ⟨1550005540678357349505103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8266696216951239197360549 1550005540678357349505103)
                      ·
                        rfl

theorem cell23_3018625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_3018625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018625 prefixEnd_3018625 := by exact prefixLift 3018625
  have htrace : WordTrace (prefixWord ++ tailWord_3018625) baseStart_3018625 baseEnd_3018625 := by
    simpa [prefixWord, tailWord_3018625, baseEnd_3018625] using wordTrace_append hprefix tailTrace_3018625
  have hstable : (prefixWord ++ tailWord_3018625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018625).length < 2 ^ (prefixWord ++ tailWord_3018625).sum := by decide
  have hdescent : baseEnd_3018625 < baseStart_3018625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018640 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 2, 6]
def baseStart_3018640 : Nat := 118140960795 + 3018640 * 2 ^ 59
def prefixEnd_3018640 : Nat := 4983230072969 + 3 ^ 40 * 3018640 * 2
def baseEnd_3018640 : Nat := 516671080962724930272511

theorem tailTrace_3018640 : CollatzResearch.WordTrace tailWord_3018640 prefixEnd_3018640 516671080962724930272511 := by
  unfold tailWord_3018640
  simp only [CollatzResearch.WordTrace]
  refine ⟨55049422891995148756330687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73399230522660198341774249 55049422891995148756330687)
  ·
    refine ⟨82574134337992723134496031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55049422891995148756330687 82574134337992723134496031)
    ·
      refine ⟨123861201506989084701744047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82574134337992723134496031 123861201506989084701744047)
      ·
        refine ⟨185791802260483627052616071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123861201506989084701744047 185791802260483627052616071)
        ·
          refine ⟨278687703390725440578924107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185791802260483627052616071 278687703390725440578924107)
          ·
            refine ⟨418031555086088160868386161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278687703390725440578924107 418031555086088160868386161)
            ·
              refine ⟨313523666314566120651289621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418031555086088160868386161 313523666314566120651289621)
              ·
                refine ⟨14696421858495286905529201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 313523666314566120651289621 14696421858495286905529201)
                ·
                  refine ⟨11022316393871465179146901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14696421858495286905529201 11022316393871465179146901)
                  ·
                    refine ⟨516671080962724930272511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11022316393871465179146901 516671080962724930272511)
                    ·
                      rfl

theorem cell23_3018640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_3018640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018640 prefixEnd_3018640 := by exact prefixLift 3018640
  have htrace : WordTrace (prefixWord ++ tailWord_3018640) baseStart_3018640 baseEnd_3018640 := by
    simpa [prefixWord, tailWord_3018640, baseEnd_3018640] using wordTrace_append hprefix tailTrace_3018640
  have hstable : (prefixWord ++ tailWord_3018640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018640).length < 2 ^ (prefixWord ++ tailWord_3018640).sum := by decide
  have hdescent : baseEnd_3018640 < baseStart_3018640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018658 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_3018658 : Nat := 118140960795 + 3018658 * 2 ^ 59
def prefixEnd_3018658 : Nat := 4983230072969 + 3 ^ 40 * 3018658 * 2
def baseEnd_3018658 : Nat := 1550022485539955720392451

theorem tailTrace_3018658 : CollatzResearch.WordTrace tailWord_3018658 prefixEnd_3018658 1550022485539955720392451 := by
  unfold tailWord_3018658
  simp only [CollatzResearch.WordTrace]
  refine ⟨27524875574481271646704157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73399668198616724391211085 27524875574481271646704157)
  ·
    refine ⟨10321828340430476867514059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27524875574481271646704157 10321828340430476867514059)
    ·
      refine ⟨15482742510645715301271089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10321828340430476867514059 15482742510645715301271089)
      ·
        refine ⟨11612056882984286475953317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15482742510645715301271089 11612056882984286475953317)
        ·
          refine ⟨2177260665559553714241247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11612056882984286475953317 2177260665559553714241247)
          ·
            refine ⟨3265890998339330571361871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177260665559553714241247 3265890998339330571361871)
            ·
              refine ⟨4898836497508995857042807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265890998339330571361871 4898836497508995857042807)
              ·
                refine ⟨7348254746263493785564211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898836497508995857042807 7348254746263493785564211)
                ·
                  refine ⟨11022382119395240678346317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7348254746263493785564211 11022382119395240678346317)
                  ·
                    refine ⟨4133393294773215254379869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11022382119395240678346317 4133393294773215254379869)
                    ·
                      refine ⟨1550022485539955720392451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4133393294773215254379869 1550022485539955720392451)
                      ·
                        rfl

theorem cell23_3018658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_3018658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018658 prefixEnd_3018658 := by exact prefixLift 3018658
  have htrace : WordTrace (prefixWord ++ tailWord_3018658) baseStart_3018658 baseEnd_3018658 := by
    simpa [prefixWord, tailWord_3018658, baseEnd_3018658] using wordTrace_append hprefix tailTrace_3018658
  have hstable : (prefixWord ++ tailWord_3018658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018658).length < 2 ^ (prefixWord ++ tailWord_3018658).sum := by decide
  have hdescent : baseEnd_3018658 < baseStart_3018658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018734 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3018734 : Nat := 118140960795 + 3018734 * 2 ^ 59
def prefixEnd_3018734 : Nat := 4983230072969 + 3 ^ 40 * 3018734 * 2
def baseEnd_3018734 : Nat := 516687170023232474347367

theorem tailTrace_3018734 : CollatzResearch.WordTrace tailWord_3018734 prefixEnd_3018734 516687170023232474347367 := by
  unfold tailWord_3018734
  simp only [CollatzResearch.WordTrace]
  refine ⟨13762784280706218945822907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73401516163766501044388837 13762784280706218945822907)
  ·
    refine ⟨20644176421059328418734361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13762784280706218945822907 20644176421059328418734361)
    ·
      refine ⟨15483132315794496314050771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20644176421059328418734361 15483132315794496314050771)
      ·
        refine ⟨23224698473691744471076157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15483132315794496314050771 23224698473691744471076157)
        ·
          refine ⟨8709261927634404176653559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23224698473691744471076157 8709261927634404176653559)
          ·
            refine ⟨13063892891451606264980339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709261927634404176653559 13063892891451606264980339)
            ·
              refine ⟨19595839337177409397470509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13063892891451606264980339 19595839337177409397470509)
              ·
                refine ⟨7348439751441528524051441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19595839337177409397470509 7348439751441528524051441)
                ·
                  refine ⟨5511329813581146393038581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348439751441528524051441 5511329813581146393038581)
                  ·
                    refine ⟨516687170023232474347367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5511329813581146393038581 516687170023232474347367)
                    ·
                      rfl

theorem cell23_3018734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3018734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018734 prefixEnd_3018734 := by exact prefixLift 3018734
  have htrace : WordTrace (prefixWord ++ tailWord_3018734) baseStart_3018734 baseEnd_3018734 := by
    simpa [prefixWord, tailWord_3018734, baseEnd_3018734] using wordTrace_append hprefix tailTrace_3018734
  have hstable : (prefixWord ++ tailWord_3018734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018734).length < 2 ^ (prefixWord ++ tailWord_3018734).sum := by decide
  have hdescent : baseEnd_3018734 < baseStart_3018734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018764 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_3018764 : Nat := 118140960795 + 3018764 * 2 ^ 59
def prefixEnd_3018764 : Nat := 4983230072969 + 3 ^ 40 * 3018764 * 2
def baseEnd_3018764 : Nat := 516692304829777435222321

theorem tailTrace_3018764 : CollatzResearch.WordTrace tailWord_3018764 prefixEnd_3018764 516692304829777435222321 := by
  unfold tailWord_3018764
  simp only [CollatzResearch.WordTrace]
  refine ⟨55051684217770533345087673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73402245623694044460116897 55051684217770533345087673)
  ·
    refine ⟨41288763163327900008815755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55051684217770533345087673 41288763163327900008815755)
    ·
      refine ⟨61933144744991850013223633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41288763163327900008815755 61933144744991850013223633)
      ·
        refine ⟨46449858558743887509917725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61933144744991850013223633 46449858558743887509917725)
        ·
          refine ⟨17418696959528957816219147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46449858558743887509917725 17418696959528957816219147)
          ·
            refine ⟨26128045439293436724328721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17418696959528957816219147 26128045439293436724328721)
            ·
              refine ⟨19596034079470077543246541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26128045439293436724328721 19596034079470077543246541)
              ·
                refine ⟨7348512779801279078717453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19596034079470077543246541 7348512779801279078717453)
                ·
                  refine ⟨2755692292425479654519045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7348512779801279078717453 2755692292425479654519045)
                  ·
                    refine ⟨516692304829777435222321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755692292425479654519045 516692304829777435222321)
                    ·
                      rfl

theorem cell23_3018764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_3018764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018764 prefixEnd_3018764 := by exact prefixLift 3018764
  have htrace : WordTrace (prefixWord ++ tailWord_3018764) baseStart_3018764 baseEnd_3018764 := by
    simpa [prefixWord, tailWord_3018764, baseEnd_3018764] using wordTrace_append hprefix tailTrace_3018764
  have hstable : (prefixWord ++ tailWord_3018764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018764).length < 2 ^ (prefixWord ++ tailWord_3018764).sum := by decide
  have hdescent : baseEnd_3018764 < baseStart_3018764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018765 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3018765 : Nat := 118140960795 + 3018765 * 2 ^ 59
def prefixEnd_3018765 : Nat := 4983230072969 + 3 ^ 40 * 3018765 * 2
def baseEnd_3018765 : Nat := 1550077427969986801754459

theorem tailTrace_3018765 : CollatzResearch.WordTrace tailWord_3018765 prefixEnd_3018765 1550077427969986801754459 := by
  unfold tailWord_3018765
  simp only [CollatzResearch.WordTrace]
  refine ⟨110103404908537443860961749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73402269939024962573974499 110103404908537443860961749)
  ·
    refine ⟨2580548552543846340491291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 110103404908537443860961749 2580548552543846340491291)
    ·
      refine ⟨3870822828815769510736937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580548552543846340491291 3870822828815769510736937)
      ·
        refine ⟨2903117121611827133052703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3870822828815769510736937 2903117121611827133052703)
        ·
          refine ⟨4354675682417740699579055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2903117121611827133052703 4354675682417740699579055)
          ·
            refine ⟨6532013523626611049368583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354675682417740699579055 6532013523626611049368583)
            ·
              refine ⟨9798020285439916574052875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6532013523626611049368583 9798020285439916574052875)
              ·
                refine ⟨14697030428159874861079313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9798020285439916574052875 14697030428159874861079313)
                ·
                  refine ⟨11022772821119906145809485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14697030428159874861079313 11022772821119906145809485)
                  ·
                    refine ⟨4133539807919964804678557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11022772821119906145809485 4133539807919964804678557)
                    ·
                      refine ⟨1550077427969986801754459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4133539807919964804678557 1550077427969986801754459)
                      ·
                        rfl

theorem cell23_3018765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3018765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018765 prefixEnd_3018765 := by exact prefixLift 3018765
  have htrace : WordTrace (prefixWord ++ tailWord_3018765) baseStart_3018765 baseEnd_3018765 := by
    simpa [prefixWord, tailWord_3018765, baseEnd_3018765] using wordTrace_append hprefix tailTrace_3018765
  have hstable : (prefixWord ++ tailWord_3018765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018765).length < 2 ^ (prefixWord ++ tailWord_3018765).sum := by decide
  have hdescent : baseEnd_3018765 < baseStart_3018765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018781 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_3018781 : Nat := 118140960795 + 3018781 * 2 ^ 59
def prefixEnd_3018781 : Nat := 4983230072969 + 3 ^ 40 * 3018781 * 2
def baseEnd_3018781 : Nat := 516695214553486246384795

theorem tailTrace_3018781 : CollatzResearch.WordTrace tailWord_3018781 prefixEnd_3018781 516695214553486246384795 := by
  unfold tailWord_3018781
  simp only [CollatzResearch.WordTrace]
  refine ⟨110103988476479478593544197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73402658984319652395696131 110103988476479478593544197)
  ·
    refine ⟨20644497839339902236289537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110103988476479478593544197 20644497839339902236289537)
    ·
      refine ⟨15483373379504926677217153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20644497839339902236289537 15483373379504926677217153)
      ·
        refine ⟨11612530034628695007912865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15483373379504926677217153 11612530034628695007912865)
        ·
          refine ⟨8709397525971521255934649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11612530034628695007912865 8709397525971521255934649)
          ·
            refine ⟨6532048144478640941950987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8709397525971521255934649 6532048144478640941950987)
            ·
              refine ⟨9798072216717961412926481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6532048144478640941950987 9798072216717961412926481)
              ·
                refine ⟨7348554162538471059694861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9798072216717961412926481 7348554162538471059694861)
                ·
                  refine ⟨2755707810951926647385573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7348554162538471059694861 2755707810951926647385573)
                  ·
                    refine ⟨516695214553486246384795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755707810951926647385573 516695214553486246384795)
                    ·
                      rfl

theorem cell23_3018781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_3018781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018781 prefixEnd_3018781 := by exact prefixLift 3018781
  have htrace : WordTrace (prefixWord ++ tailWord_3018781) baseStart_3018781 baseEnd_3018781 := by
    simpa [prefixWord, tailWord_3018781, baseEnd_3018781] using wordTrace_append hprefix tailTrace_3018781
  have hstable : (prefixWord ++ tailWord_3018781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018781).length < 2 ^ (prefixWord ++ tailWord_3018781).sum := by decide
  have hdescent : baseEnd_3018781 < baseStart_3018781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018788 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3018788 : Nat := 118140960795 + 3018788 * 2 ^ 59
def prefixEnd_3018788 : Nat := 4983230072969 + 3 ^ 40 * 3018788 * 2
def baseEnd_3018788 : Nat := 1550089238025040211766853

theorem tailTrace_3018788 : CollatzResearch.WordTrace tailWord_3018788 prefixEnd_3018788 1550089238025040211766853 := by
  unfold tailWord_3018788
  simp only [CollatzResearch.WordTrace]
  refine ⟨55052121893727059394524509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73402829191636079192699345 55052121893727059394524509)
  ·
    refine ⟨20644545710147647272946691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55052121893727059394524509 20644545710147647272946691)
    ·
      refine ⟨30966818565221470909420037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20644545710147647272946691 30966818565221470909420037)
      ·
        refine ⟨5806278480979025795516257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30966818565221470909420037 5806278480979025795516257)
        ·
          refine ⟨4354708860734269346637193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5806278480979025795516257 4354708860734269346637193)
          ·
            refine ⟨3266031645550702009977895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4354708860734269346637193 3266031645550702009977895)
            ·
              refine ⟨4899047468326053014966843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3266031645550702009977895 4899047468326053014966843)
              ·
                refine ⟨7348571202489079522450265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899047468326053014966843 7348571202489079522450265)
                ·
                  refine ⟨5511428401866809641837699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7348571202489079522450265 5511428401866809641837699)
                  ·
                    refine ⟨8267142602800214462756549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511428401866809641837699 8267142602800214462756549)
                    ·
                      refine ⟨1550089238025040211766853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8267142602800214462756549 1550089238025040211766853)
                      ·
                        rfl

theorem cell23_3018788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3018788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018788 prefixEnd_3018788 := by exact prefixLift 3018788
  have htrace : WordTrace (prefixWord ++ tailWord_3018788) baseStart_3018788 baseEnd_3018788 := by
    simpa [prefixWord, tailWord_3018788, baseEnd_3018788] using wordTrace_append hprefix tailTrace_3018788
  have hstable : (prefixWord ++ tailWord_3018788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018788).length < 2 ^ (prefixWord ++ tailWord_3018788).sum := by decide
  have hdescent : baseEnd_3018788 < baseStart_3018788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018798 : List Nat := [4, 1, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3018798 : Nat := 118140960795 + 3018798 * 2 ^ 59
def prefixEnd_3018798 : Nat := 4983230072969 + 3 ^ 40 * 3018798 * 2
def baseEnd_3018798 : Nat := 516698124277195057547269

theorem tailTrace_3018798 : CollatzResearch.WordTrace tailWord_3018798 prefixEnd_3018798 516698124277195057547269 := by
  unfold tailWord_3018798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13763076064677236312114131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73403072344945260331275365 13763076064677236312114131)
  ·
    refine ⟨20644614097015854468171197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13763076064677236312114131 20644614097015854468171197)
    ·
      refine ⟨7741730286380945425564199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20644614097015854468171197 7741730286380945425564199)
      ·
        refine ⟨11612595429571418138346299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7741730286380945425564199 11612595429571418138346299)
        ·
          refine ⟨17418893144357127207519449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11612595429571418138346299 17418893144357127207519449)
          ·
            refine ⟨13064169858267845405639587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17418893144357127207519449 13064169858267845405639587)
            ·
              refine ⟨19596254787401768108459381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064169858267845405639587 19596254787401768108459381)
              ·
                refine ⟨1837148886318915760168067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19596254787401768108459381 1837148886318915760168067)
                ·
                  refine ⟨2755723329478373640252101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837148886318915760168067 2755723329478373640252101)
                  ·
                    refine ⟨516698124277195057547269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755723329478373640252101 516698124277195057547269)
                    ·
                      rfl

theorem cell23_3018798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3018798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018798 prefixEnd_3018798 := by exact prefixLift 3018798
  have htrace : WordTrace (prefixWord ++ tailWord_3018798) baseStart_3018798 baseEnd_3018798 := by
    simpa [prefixWord, tailWord_3018798, baseEnd_3018798] using wordTrace_append hprefix tailTrace_3018798
  have hstable : (prefixWord ++ tailWord_3018798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018798).length < 2 ^ (prefixWord ++ tailWord_3018798).sum := by decide
  have hdescent : baseEnd_3018798 < baseStart_3018798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018861 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3018861 : Nat := 118140960795 + 3018861 * 2 ^ 59
def prefixEnd_3018861 : Nat := 4983230072969 + 3 ^ 40 * 3018861 * 2
def baseEnd_3018861 : Nat := 1550126722112818426154017

theorem tailTrace_3018861 : CollatzResearch.WordTrace tailWord_3018861 prefixEnd_3018861 1550126722112818426154017 := by
  unfold tailWord_3018861
  simp only [CollatzResearch.WordTrace]
  refine ⟨110106906316189652256456437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73404604210793101504304291 110106906316189652256456437)
  ·
    refine ⟨10322522467142779899042791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110106906316189652256456437 10322522467142779899042791)
    ·
      refine ⟨15483783700714169848564187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10322522467142779899042791 15483783700714169848564187)
      ·
        refine ⟨23225675551071254772846281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15483783700714169848564187 23225675551071254772846281)
        ·
          refine ⟨17419256663303441079634711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23225675551071254772846281 17419256663303441079634711)
          ·
            refine ⟨26128884994955161619452067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17419256663303441079634711 26128884994955161619452067)
            ·
              refine ⟨39193327492432742429178101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26128884994955161619452067 39193327492432742429178101)
              ·
                refine ⟨3674374452415569602735447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39193327492432742429178101 3674374452415569602735447)
                ·
                  refine ⟨5511561678623354404103171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674374452415569602735447 5511561678623354404103171)
                  ·
                    refine ⟨8267342517935031606154757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511561678623354404103171 8267342517935031606154757)
                    ·
                      refine ⟨1550126722112818426154017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8267342517935031606154757 1550126722112818426154017)
                      ·
                        rfl

theorem cell23_3018861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3018861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018861 prefixEnd_3018861 := by exact prefixLift 3018861
  have htrace : WordTrace (prefixWord ++ tailWord_3018861) baseStart_3018861 baseEnd_3018861 := by
    simpa [prefixWord, tailWord_3018861, baseEnd_3018861] using wordTrace_append hprefix tailTrace_3018861
  have hstable : (prefixWord ++ tailWord_3018861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018861).length < 2 ^ (prefixWord ++ tailWord_3018861).sum := by decide
  have hdescent : baseEnd_3018861 < baseStart_3018861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018864 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_3018864 : Nat := 118140960795 + 3018864 * 2 ^ 59
def prefixEnd_3018864 : Nat := 4983230072969 + 3 ^ 40 * 3018864 * 2
def baseEnd_3018864 : Nat := 1550128262554781914416503

theorem tailTrace_3018864 : CollatzResearch.WordTrace tailWord_3018864 prefixEnd_3018864 1550128262554781914416503 := by
  unfold tailWord_3018864
  simp only [CollatzResearch.WordTrace]
  refine ⟨55053507867589391884407823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73404677156785855845877097 55053507867589391884407823)
  ·
    refine ⟨82580261801384087826611735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55053507867589391884407823 82580261801384087826611735)
    ·
      refine ⟨123870392702076131739917603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82580261801384087826611735 123870392702076131739917603)
      ·
        refine ⟨185805589053114197609876405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123870392702076131739917603 185805589053114197609876405)
        ·
          refine ⟨17419273973729456025925913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185805589053114197609876405 17419273973729456025925913)
          ·
            refine ⟨13064455480297092019444435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17419273973729456025925913 13064455480297092019444435)
            ·
              refine ⟨19596683220445638029166653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064455480297092019444435 19596683220445638029166653)
              ·
                refine ⟨7348756207667114260937495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19596683220445638029166653 7348756207667114260937495)
                ·
                  refine ⟨11023134311500671391406243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7348756207667114260937495 11023134311500671391406243)
                  ·
                    refine ⟨16534701467251007087109365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11023134311500671391406243 16534701467251007087109365)
                    ·
                      refine ⟨1550128262554781914416503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16534701467251007087109365 1550128262554781914416503)
                      ·
                        rfl

theorem cell23_3018864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_3018864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018864 prefixEnd_3018864 := by exact prefixLift 3018864
  have htrace : WordTrace (prefixWord ++ tailWord_3018864) baseStart_3018864 baseEnd_3018864 := by
    simpa [prefixWord, tailWord_3018864, baseEnd_3018864] using wordTrace_append hprefix tailTrace_3018864
  have hstable : (prefixWord ++ tailWord_3018864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018864).length < 2 ^ (prefixWord ++ tailWord_3018864).sum := by decide
  have hdescent : baseEnd_3018864 < baseStart_3018864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018884 : List Nat := [2, 3, 2, 1, 2, 1, 4, 8]
def baseStart_3018884 : Nat := 118140960795 + 3018884 * 2 ^ 59
def prefixEnd_3018884 : Nat := 4983230072969 + 3 ^ 40 * 3018884 * 2
def baseEnd_3018884 : Nat := 57412538228439697635793

theorem tailTrace_3018884 : CollatzResearch.WordTrace tailWord_3018884 prefixEnd_3018884 57412538228439697635793 := by
  unfold tailWord_3018884
  simp only [CollatzResearch.WordTrace]
  refine ⟨55053872597553163592271853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73405163463404218123029137 55053872597553163592271853)
  ·
    refine ⟨20645202224082436347101945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55053872597553163592271853 20645202224082436347101945)
    ·
      refine ⟨15483901668061827260326459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20645202224082436347101945 15483901668061827260326459)
      ·
        refine ⟨23225852502092740890489689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15483901668061827260326459 23225852502092740890489689)
        ·
          refine ⟨17419389376569555667867267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23225852502092740890489689 17419389376569555667867267)
          ·
            refine ⟨26129084064854333501800901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17419389376569555667867267 26129084064854333501800901)
            ·
              refine ⟨4899203262160187531587669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26129084064854333501800901 4899203262160187531587669)
              ·
                refine ⟨57412538228439697635793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4899203262160187531587669 57412538228439697635793)
                ·
                  rfl

theorem cell23_3018884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 8].length) (baseStart_3018884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018884 prefixEnd_3018884 := by exact prefixLift 3018884
  have htrace : WordTrace (prefixWord ++ tailWord_3018884) baseStart_3018884 baseEnd_3018884 := by
    simpa [prefixWord, tailWord_3018884, baseEnd_3018884] using wordTrace_append hprefix tailTrace_3018884
  have hstable : (prefixWord ++ tailWord_3018884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018884).length < 2 ^ (prefixWord ++ tailWord_3018884).sum := by decide
  have hdescent : baseEnd_3018884 < baseStart_3018884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018888 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 2, 4]
def baseStart_3018888 : Nat := 118140960795 + 3018888 * 2 ^ 59
def prefixEnd_3018888 : Nat := 4983230072969 + 3 ^ 40 * 3018888 * 2
def baseEnd_3018888 : Nat := 516713528696829940172131

theorem tailTrace_3018888 : CollatzResearch.WordTrace tailWord_3018888 prefixEnd_3018888 516713528696829940172131 := by
  unfold tailWord_3018888
  simp only [CollatzResearch.WordTrace]
  refine ⟨55053945543545917933844659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73405260724727890578459545 55053945543545917933844659)
  ·
    refine ⟨82580918315318876900766989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55053945543545917933844659 82580918315318876900766989)
    ·
      refine ⟨30967844368244578837787621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82580918315318876900766989 30967844368244578837787621)
      ·
        refine ⟨5806470819045858532085179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30967844368244578837787621 5806470819045858532085179)
        ·
          refine ⟨8709706228568787798127769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5806470819045858532085179 8709706228568787798127769)
          ·
            refine ⟨6532279671426590848595827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8709706228568787798127769 6532279671426590848595827)
            ·
              refine ⟨9798419507139886272893741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6532279671426590848595827 9798419507139886272893741)
              ·
                refine ⟨3674407315177457352335153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9798419507139886272893741 3674407315177457352335153)
                ·
                  refine ⟨2755805486383093014251365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3674407315177457352335153 2755805486383093014251365)
                  ·
                    refine ⟨516713528696829940172131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755805486383093014251365 516713528696829940172131)
                    ·
                      rfl

theorem cell23_3018888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_3018888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018888 prefixEnd_3018888 := by exact prefixLift 3018888
  have htrace : WordTrace (prefixWord ++ tailWord_3018888) baseStart_3018888 baseEnd_3018888 := by
    simpa [prefixWord, tailWord_3018888, baseEnd_3018888] using wordTrace_append hprefix tailTrace_3018888
  have hstable : (prefixWord ++ tailWord_3018888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018888).length < 2 ^ (prefixWord ++ tailWord_3018888).sum := by decide
  have hdescent : baseEnd_3018888 < baseStart_3018888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018911 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3018911 : Nat := 118140960795 + 3018911 * 2 ^ 59
def prefixEnd_3018911 : Nat := 4983230072969 + 3 ^ 40 * 3018911 * 2
def baseEnd_3018911 : Nat := 1550152396145543230528787

theorem tailTrace_3018911 : CollatzResearch.WordTrace tailWord_3018911 prefixEnd_3018911 1550152396145543230528787 := by
  unfold tailWord_3018911
  simp only [CollatzResearch.WordTrace]
  refine ⟨110108729966008510795776587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73405819977339007197184391 110108729966008510795776587)
  ·
    refine ⟨165163094949012766193664881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110108729966008510795776587 165163094949012766193664881)
    ·
      refine ⟨123872321211759574645248661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165163094949012766193664881 123872321211759574645248661)
      ·
        refine ⟨5806515056801230061496031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 123872321211759574645248661 5806515056801230061496031)
        ·
          refine ⟨8709772585201845092244047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5806515056801230061496031 8709772585201845092244047)
          ·
            refine ⟨13064658877802767638366071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709772585201845092244047 13064658877802767638366071)
            ·
              refine ⟨19596988316704151457549107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064658877802767638366071 19596988316704151457549107)
              ·
                refine ⟨29395482475056227186323661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19596988316704151457549107 29395482475056227186323661)
                ·
                  refine ⟨11023305928146085194871373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29395482475056227186323661 11023305928146085194871373)
                  ·
                    refine ⟨4133739723054781948076765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11023305928146085194871373 4133739723054781948076765)
                    ·
                      refine ⟨1550152396145543230528787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4133739723054781948076765 1550152396145543230528787)
                      ·
                        rfl

theorem cell23_3018911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3018911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018911 prefixEnd_3018911 := by exact prefixLift 3018911
  have htrace : WordTrace (prefixWord ++ tailWord_3018911) baseStart_3018911 baseEnd_3018911 := by
    simpa [prefixWord, tailWord_3018911, baseEnd_3018911] using wordTrace_append hprefix tailTrace_3018911
  have hstable : (prefixWord ++ tailWord_3018911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018911).length < 2 ^ (prefixWord ++ tailWord_3018911).sum := by decide
  have hdescent : baseEnd_3018911 < baseStart_3018911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018944 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 1, 8]
def baseStart_3018944 : Nat := 118140960795 + 3018944 * 2 ^ 59
def prefixEnd_3018944 : Nat := 4983230072969 + 3 ^ 40 * 3018944 * 2
def baseEnd_3018944 : Nat := 516723113669047200472045

theorem tailTrace_3018944 : CollatzResearch.WordTrace tailWord_3018944 prefixEnd_3018944 516723113669047200472045 := by
  unfold tailWord_3018944
  simp only [CollatzResearch.WordTrace]
  refine ⟨55054966787444478715863943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73406622383259304954485257 55054966787444478715863943)
  ·
    refine ⟨82582450181166718073795915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55054966787444478715863943 82582450181166718073795915)
    ·
      refine ⟨123873675271750077110693873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82582450181166718073795915 123873675271750077110693873)
      ·
        refine ⟨92905256453812557833020405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123873675271750077110693873 92905256453812557833020405)
        ·
          refine ⟨8709867792544927296845663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92905256453812557833020405 8709867792544927296845663)
          ·
            refine ⟨13064801688817390945268495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709867792544927296845663 13064801688817390945268495)
            ·
              refine ⟨19597202533226086417902743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064801688817390945268495 19597202533226086417902743)
              ·
                refine ⟨29395803799839129626854115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19597202533226086417902743 29395803799839129626854115)
                ·
                  refine ⟨44093705699758694440281173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29395803799839129626854115 44093705699758694440281173)
                  ·
                    refine ⟨516723113669047200472045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44093705699758694440281173 516723113669047200472045)
                    ·
                      rfl

theorem cell23_3018944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_3018944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018944 prefixEnd_3018944 := by exact prefixLift 3018944
  have htrace : WordTrace (prefixWord ++ tailWord_3018944) baseStart_3018944 baseEnd_3018944 := by
    simpa [prefixWord, tailWord_3018944, baseEnd_3018944] using wordTrace_append hprefix tailTrace_3018944
  have hstable : (prefixWord ++ tailWord_3018944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018944).length < 2 ^ (prefixWord ++ tailWord_3018944).sum := by decide
  have hdescent : baseEnd_3018944 < baseStart_3018944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018945 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3018945 : Nat := 118140960795 + 3018945 * 2 ^ 59
def prefixEnd_3018945 : Nat := 4983230072969 + 3 ^ 40 * 3018945 * 2
def baseEnd_3018945 : Nat := 1550169854487796097503631

theorem tailTrace_3018945 : CollatzResearch.WordTrace tailWord_3018945 prefixEnd_3018945 1550169854487796097503631 := by
  unfold tailWord_3018945
  simp only [CollatzResearch.WordTrace]
  refine ⟨110109970047885334602514289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73406646698590223068342859 110109970047885334602514289)
  ·
    refine ⟨82582477535914000951885717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110109970047885334602514289 82582477535914000951885717)
    ·
      refine ⟨3871053634495968794619643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82582477535914000951885717 3871053634495968794619643)
      ·
        refine ⟨5806580451743953191929465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3871053634495968794619643 5806580451743953191929465)
        ·
          refine ⟨4354935338807964893947099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5806580451743953191929465 4354935338807964893947099)
          ·
            refine ⟨6532403008211947340920649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354935338807964893947099 6532403008211947340920649)
            ·
              refine ⟨4899302256158960505690487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6532403008211947340920649 4899302256158960505690487)
              ·
                refine ⟨7348953384238440758535731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899302256158960505690487 7348953384238440758535731)
                ·
                  refine ⟨11023430076357661137803597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7348953384238440758535731 11023430076357661137803597)
                  ·
                    refine ⟨4133786278634122926676349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11023430076357661137803597 4133786278634122926676349)
                    ·
                      refine ⟨1550169854487796097503631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4133786278634122926676349 1550169854487796097503631)
                      ·
                        rfl

theorem cell23_3018945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3018945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018945 prefixEnd_3018945 := by exact prefixLift 3018945
  have htrace : WordTrace (prefixWord ++ tailWord_3018945) baseStart_3018945 baseEnd_3018945 := by
    simpa [prefixWord, tailWord_3018945, baseEnd_3018945] using wordTrace_append hprefix tailTrace_3018945
  have hstable : (prefixWord ++ tailWord_3018945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018945).length < 2 ^ (prefixWord ++ tailWord_3018945).sum := by decide
  have hdescent : baseEnd_3018945 < baseStart_3018945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018968 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 1, 4, 2]
def baseStart_3018968 : Nat := 118140960795 + 3018968 * 2 ^ 59
def prefixEnd_3018968 : Nat := 4983230072969 + 3 ^ 40 * 3018968 * 2
def baseEnd_3018968 : Nat := 1550181664542849507516025

theorem tailTrace_3018968 : CollatzResearch.WordTrace tailWord_3018968 prefixEnd_3018968 1550181664542849507516025 := by
  unfold tailWord_3018968
  simp only [CollatzResearch.WordTrace]
  refine ⟨55055404463401004765300779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73407205951201339687067705 55055404463401004765300779)
  ·
    refine ⟨82583106695101507147951169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55055404463401004765300779 82583106695101507147951169)
    ·
      refine ⟨61937330021326130360963377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82583106695101507147951169 61937330021326130360963377)
      ·
        refine ⟨46452997515994597770722533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61937330021326130360963377 46452997515994597770722533)
        ·
          refine ⟨8709937034248987082010475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46452997515994597770722533 8709937034248987082010475)
          ·
            refine ⟨13064905551373480623015713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709937034248987082010475 13064905551373480623015713)
            ·
              refine ⟨9798679163530110467261785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13064905551373480623015713 9798679163530110467261785)
              ·
                refine ⟨7349009372647582850446339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9798679163530110467261785 7349009372647582850446339)
                ·
                  refine ⟨11023514058971374275669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7349009372647582850446339 11023514058971374275669509)
                  ·
                    refine ⟨2066908886057132676688033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11023514058971374275669509 2066908886057132676688033)
                    ·
                      refine ⟨1550181664542849507516025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066908886057132676688033 1550181664542849507516025)
                      ·
                        rfl

theorem cell23_3018968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_3018968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018968 prefixEnd_3018968 := by exact prefixLift 3018968
  have htrace : WordTrace (prefixWord ++ tailWord_3018968) baseStart_3018968 baseEnd_3018968 := by
    simpa [prefixWord, tailWord_3018968, baseEnd_3018968] using wordTrace_append hprefix tailTrace_3018968
  have hstable : (prefixWord ++ tailWord_3018968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018968).length < 2 ^ (prefixWord ++ tailWord_3018968).sum := by decide
  have hdescent : baseEnd_3018968 < baseStart_3018968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018979 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3018979 : Nat := 118140960795 + 3018979 * 2 ^ 59
def prefixEnd_3018979 : Nat := 4983230072969 + 3 ^ 40 * 3018979 * 2
def baseEnd_3018979 : Nat := 1550187312830048964478475

theorem tailTrace_3018979 : CollatzResearch.WordTrace tailWord_3018979 prefixEnd_3018979 1550187312830048964478475 := by
  unfold tailWord_3018979
  simp only [CollatzResearch.WordTrace]
  refine ⟨110111210129762158409251991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73407473419841438939501327 110111210129762158409251991)
  ·
    refine ⟨165166815194643237613877987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110111210129762158409251991 165166815194643237613877987)
    ·
      refine ⟨247750222791964856420816981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165166815194643237613877987 247750222791964856420816981)
      ·
        refine ⟨2903322923343338161181449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 247750222791964856420816981 2903322923343338161181449)
        ·
          refine ⟨2177492192507503620886087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903322923343338161181449 2177492192507503620886087)
          ·
            refine ⟨3266238288761255431329131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177492192507503620886087 3266238288761255431329131)
            ·
              refine ⟨4899357433141883146993697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3266238288761255431329131 4899357433141883146993697)
              ·
                refine ⟨3674518074856412360245273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4899357433141883146993697 3674518074856412360245273)
                ·
                  refine ⟨2755888556142309270183955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3674518074856412360245273 2755888556142309270183955)
                  ·
                    refine ⟨4133832834213463905275933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2755888556142309270183955 4133832834213463905275933)
                    ·
                      refine ⟨1550187312830048964478475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4133832834213463905275933 1550187312830048964478475)
                      ·
                        rfl

theorem cell23_3018979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3018979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018979 prefixEnd_3018979 := by exact prefixLift 3018979
  have htrace : WordTrace (prefixWord ++ tailWord_3018979) baseStart_3018979 baseEnd_3018979 := by
    simpa [prefixWord, tailWord_3018979, baseEnd_3018979] using wordTrace_append hprefix tailTrace_3018979
  have hstable : (prefixWord ++ tailWord_3018979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018979).length < 2 ^ (prefixWord ++ tailWord_3018979).sum := by decide
  have hdescent : baseEnd_3018979 < baseStart_3018979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018981 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3018981 : Nat := 118140960795 + 3018981 * 2 ^ 59
def prefixEnd_3018981 : Nat := 4983230072969 + 3 ^ 40 * 3018981 * 2
def baseEnd_3018981 : Nat := 1550188339791357956653465

theorem tailTrace_3018981 : CollatzResearch.WordTrace tailWord_3018981 prefixEnd_3018981 1550188339791357956653465 := by
  unfold tailWord_3018981
  simp only [CollatzResearch.WordTrace]
  refine ⟨110111283075754912750824797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73407522050503275167216531 110111283075754912750824797)
  ·
    refine ⟨41291731153408092281559299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110111283075754912750824797 41291731153408092281559299)
    ·
      refine ⟨61937596730112138422338949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41291731153408092281559299 61937596730112138422338949)
      ·
        refine ⟨11613299386896025954188553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61937596730112138422338949 11613299386896025954188553)
        ·
          refine ⟨8709974540172019465641415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11613299386896025954188553 8709974540172019465641415)
          ·
            refine ⟨13064961810258029198462123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709974540172019465641415 13064961810258029198462123)
            ·
              refine ⟨19597442715387043797693185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064961810258029198462123 19597442715387043797693185)
              ·
                refine ⟨14698082036540282848269889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19597442715387043797693185 14698082036540282848269889)
                ·
                  refine ⟨11023561527405212136202417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14698082036540282848269889 11023561527405212136202417)
                  ·
                    refine ⟨8267671145553909102151813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11023561527405212136202417 8267671145553909102151813)
                    ·
                      refine ⟨1550188339791357956653465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8267671145553909102151813 1550188339791357956653465)
                      ·
                        rfl

theorem cell23_3018981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3018981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018981 prefixEnd_3018981 := by exact prefixLift 3018981
  have htrace : WordTrace (prefixWord ++ tailWord_3018981) baseStart_3018981 baseEnd_3018981 := by
    simpa [prefixWord, tailWord_3018981, baseEnd_3018981] using wordTrace_append hprefix tailTrace_3018981
  have hstable : (prefixWord ++ tailWord_3018981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018981).length < 2 ^ (prefixWord ++ tailWord_3018981).sum := by decide
  have hdescent : baseEnd_3018981 < baseStart_3018981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3018991 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 7]
def baseStart_3018991 : Nat := 118140960795 + 3018991 * 2 ^ 59
def prefixEnd_3018991 : Nat := 4983230072969 + 3 ^ 40 * 3018991 * 2
def baseEnd_3018991 : Nat := 172243719399766990836491

theorem tailTrace_3018991 : CollatzResearch.WordTrace tailWord_3018991 prefixEnd_3018991 172243719399766990836491 := by
  unfold tailWord_3018991
  simp only [CollatzResearch.WordTrace]
  refine ⟨110111647805718684458688827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73407765203812456305792551 110111647805718684458688827)
  ·
    refine ⟨165167471708578026688033241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110111647805718684458688827 165167471708578026688033241)
    ·
      refine ⟨123875603781433520016024931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165167471708578026688033241 123875603781433520016024931)
      ·
        refine ⟨185813405672150280024037397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123875603781433520016024931 185813405672150280024037397)
        ·
          refine ⟨8710003390882044376126753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185813405672150280024037397 8710003390882044376126753)
          ·
            refine ⟨6532502543161533282095065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8710003390882044376126753 6532502543161533282095065)
            ·
              refine ⟨4899376907371149961571299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6532502543161533282095065 4899376907371149961571299)
              ·
                refine ⟨7349065361056724942356949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899376907371149961571299 7349065361056724942356949)
                ·
                  refine ⟨172243719399766990836491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7349065361056724942356949 172243719399766990836491)
                  ·
                    rfl

theorem cell23_3018991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 7].length) (baseStart_3018991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3018991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3018991 prefixEnd_3018991 := by exact prefixLift 3018991
  have htrace : WordTrace (prefixWord ++ tailWord_3018991) baseStart_3018991 baseEnd_3018991 := by
    simpa [prefixWord, tailWord_3018991, baseEnd_3018991] using wordTrace_append hprefix tailTrace_3018991
  have hstable : (prefixWord ++ tailWord_3018991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3018991).length < 2 ^ (prefixWord ++ tailWord_3018991).sum := by decide
  have hdescent : baseEnd_3018991 < baseStart_3018991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3018991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019002 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2]
def baseStart_3019002 : Nat := 118140960795 + 3019002 * 2 ^ 59
def prefixEnd_3019002 : Nat := 4983230072969 + 3 ^ 40 * 3019002 * 2
def baseEnd_3019002 : Nat := 1550199122885102374490869

theorem tailTrace_3019002 : CollatzResearch.WordTrace tailWord_3019002 prefixEnd_3019002 1550199122885102374490869 := by
  unfold tailWord_3019002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27528012252169708334334815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73408032672452555558226173 27528012252169708334334815)
  ·
    refine ⟨41292018378254562501502223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27528012252169708334334815 41292018378254562501502223)
    ·
      refine ⟨61938027567381843752253335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41292018378254562501502223 61938027567381843752253335)
      ·
        refine ⟨92907041351072765628380003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61938027567381843752253335 92907041351072765628380003)
        ·
          refine ⟨139360562026609148442570005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92907041351072765628380003 139360562026609148442570005)
          ·
            refine ⟨6532526344997303833245469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139360562026609148442570005 6532526344997303833245469)
            ·
              refine ⟨2449697379373988937467051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6532526344997303833245469 2449697379373988937467051)
              ·
                refine ⟨3674546069060983406200577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449697379373988937467051 3674546069060983406200577)
                ·
                  refine ⟨2755909551795737554650433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3674546069060983406200577 2755909551795737554650433)
                  ·
                    refine ⟨2066932163846803165987825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2755909551795737554650433 2066932163846803165987825)
                    ·
                      refine ⟨1550199122885102374490869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066932163846803165987825 1550199122885102374490869)
                      ·
                        rfl

theorem cell23_3019002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_3019002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019002 prefixEnd_3019002 := by exact prefixLift 3019002
  have htrace : WordTrace (prefixWord ++ tailWord_3019002) baseStart_3019002 baseEnd_3019002 := by
    simpa [prefixWord, tailWord_3019002, baseEnd_3019002] using wordTrace_append hprefix tailTrace_3019002
  have hstable : (prefixWord ++ tailWord_3019002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019002).length < 2 ^ (prefixWord ++ tailWord_3019002).sum := by decide
  have hdescent : baseEnd_3019002 < baseStart_3019002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019041 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3019041 : Nat := 118140960795 + 3019041 * 2 ^ 59
def prefixEnd_3019041 : Nat := 4983230072969 + 3 ^ 40 * 3019041 * 2
def baseEnd_3019041 : Nat := 1550219148630627721903189

theorem tailTrace_3019041 : CollatzResearch.WordTrace tailWord_3019041 prefixEnd_3019041 1550219148630627721903189 := by
  unfold tailWord_3019041
  simp only [CollatzResearch.WordTrace]
  refine ⟨110113471455537542998008977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73408980970358361998672651 110113471455537542998008977)
  ·
    refine ⟨82585103591653157248506733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110113471455537542998008977 82585103591653157248506733)
    ·
      refine ⟨30969413846869933968190025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82585103591653157248506733 30969413846869933968190025)
      ·
        refine ⟨23227060385152450476142519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30969413846869933968190025 23227060385152450476142519)
        ·
          refine ⟨34840590577728675714213779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23227060385152450476142519 34840590577728675714213779)
          ·
            refine ⟨52260885866593013571320669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34840590577728675714213779 52260885866593013571320669)
            ·
              refine ⟨19597832199972380089245251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52260885866593013571320669 19597832199972380089245251)
              ·
                refine ⟨29396748299958570133867877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19597832199972380089245251 29396748299958570133867877)
                ·
                  refine ⟨5511890306242231900100227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29396748299958570133867877 5511890306242231900100227)
                  ·
                    refine ⟨8267835459363347850150341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5511890306242231900100227 8267835459363347850150341)
                    ·
                      refine ⟨1550219148630627721903189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8267835459363347850150341 1550219148630627721903189)
                      ·
                        rfl

theorem cell23_3019041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3019041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019041 prefixEnd_3019041 := by exact prefixLift 3019041
  have htrace : WordTrace (prefixWord ++ tailWord_3019041) baseStart_3019041 baseEnd_3019041 := by
    simpa [prefixWord, tailWord_3019041, baseEnd_3019041] using wordTrace_append hprefix tailTrace_3019041
  have hstable : (prefixWord ++ tailWord_3019041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019041).length < 2 ^ (prefixWord ++ tailWord_3019041).sum := by decide
  have hdescent : baseEnd_3019041 < baseStart_3019041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019048 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_3019048 : Nat := 118140960795 + 3019048 * 2 ^ 59
def prefixEnd_3019048 : Nat := 4983230072969 + 3 ^ 40 * 3019048 * 2
def baseEnd_3019048 : Nat := 1550222742995209194515657

theorem tailTrace_3019048 : CollatzResearch.WordTrace tailWord_3019048 prefixEnd_3019048 1550222742995209194515657 := by
  unfold tailWord_3019048
  simp only [CollatzResearch.WordTrace]
  refine ⟨55056863383256091596756899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73409151177674788795675865 55056863383256091596756899)
  ·
    refine ⟨82585295074884137395135349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55056863383256091596756899 82585295074884137395135349)
    ·
      refine ⟨7742371413270387880793939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82585295074884137395135349 7742371413270387880793939)
      ·
        refine ⟨11613557119905581821190909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7742371413270387880793939 11613557119905581821190909)
        ·
          refine ⟨4355083919964593182946591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11613557119905581821190909 4355083919964593182946591)
          ·
            refine ⟨6532625879946889774419887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355083919964593182946591 6532625879946889774419887)
            ·
              refine ⟨9798938819920334661629831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6532625879946889774419887 9798938819920334661629831)
              ·
                refine ⟨14698408229880501992444747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9798938819920334661629831 14698408229880501992444747)
                ·
                  refine ⟨22047612344820752988667121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14698408229880501992444747 22047612344820752988667121)
                  ·
                    refine ⟨16535709258615564741500341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22047612344820752988667121 16535709258615564741500341)
                    ·
                      refine ⟨1550222742995209194515657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16535709258615564741500341 1550222742995209194515657)
                      ·
                        rfl

theorem cell23_3019048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_3019048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019048 prefixEnd_3019048 := by exact prefixLift 3019048
  have htrace : WordTrace (prefixWord ++ tailWord_3019048) baseStart_3019048 baseEnd_3019048 := by
    simpa [prefixWord, tailWord_3019048, baseEnd_3019048] using wordTrace_append hprefix tailTrace_3019048
  have hstable : (prefixWord ++ tailWord_3019048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019048).length < 2 ^ (prefixWord ++ tailWord_3019048).sum := by decide
  have hdescent : baseEnd_3019048 < baseStart_3019048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019053 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3019053 : Nat := 118140960795 + 3019053 * 2 ^ 59
def prefixEnd_3019053 : Nat := 4983230072969 + 3 ^ 40 * 3019053 * 2
def baseEnd_3019053 : Nat := 1550225310398481674953135

theorem tailTrace_3019053 : CollatzResearch.WordTrace tailWord_3019053 prefixEnd_3019053 1550225310398481674953135 := by
  unfold tailWord_3019053
  simp only [CollatzResearch.WordTrace]
  refine ⟨110113909131494069047445813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73409272754329379364963875 110113909131494069047445813)
  ·
    refine ⟨10323178981077568973198045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110113909131494069047445813 10323178981077568973198045)
    ·
      refine ⟨3871192117904088364949267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10323178981077568973198045 3871192117904088364949267)
      ·
        refine ⟨5806788176856132547423901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3871192117904088364949267 5806788176856132547423901)
        ·
          refine ⟨2177545566321049705283963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5806788176856132547423901 2177545566321049705283963)
          ·
            refine ⟨3266318349481574557925945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177545566321049705283963 3266318349481574557925945)
            ·
              refine ⟨2449738762111180918444459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3266318349481574557925945 2449738762111180918444459)
              ·
                refine ⟨3674608143166771377666689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449738762111180918444459 3674608143166771377666689)
                ·
                  refine ⟨2755956107375078533250017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3674608143166771377666689 2755956107375078533250017)
                  ·
                    refine ⟨2066967080531308899937513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2755956107375078533250017 2066967080531308899937513)
                    ·
                      refine ⟨1550225310398481674953135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2066967080531308899937513 1550225310398481674953135)
                      ·
                        rfl

theorem cell23_3019053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3019053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019053 prefixEnd_3019053 := by exact prefixLift 3019053
  have htrace : WordTrace (prefixWord ++ tailWord_3019053) baseStart_3019053 baseEnd_3019053 := by
    simpa [prefixWord, tailWord_3019053, baseEnd_3019053] using wordTrace_append hprefix tailTrace_3019053
  have hstable : (prefixWord ++ tailWord_3019053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019053).length < 2 ^ (prefixWord ++ tailWord_3019053).sum := by decide
  have hdescent : baseEnd_3019053 < baseStart_3019053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019125 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3019125 : Nat := 118140960795 + 3019125 * 2 ^ 59
def prefixEnd_3019125 : Nat := 4983230072969 + 3 ^ 40 * 3019125 * 2
def baseEnd_3019125 : Nat := 1550262281005605393252803

theorem tailTrace_3019125 : CollatzResearch.WordTrace tailWord_3019125 prefixEnd_3019125 1550262281005605393252803 := by
  unfold tailWord_3019125
  simp only [CollatzResearch.WordTrace]
  refine ⟨110116535187233225344066829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73411023458155483562711219 110116535187233225344066829)
  ·
    refine ⟨41293700695212459504025061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110116535187233225344066829 41293700695212459504025061)
    ·
      refine ⟨7742568880352336157004699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41293700695212459504025061 7742568880352336157004699)
      ·
        refine ⟨11613853320528504235507049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7742568880352336157004699 11613853320528504235507049)
        ·
          refine ⟨8710389990396378176630287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11613853320528504235507049 8710389990396378176630287)
          ·
            refine ⟨13065584985594567264945431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8710389990396378176630287 13065584985594567264945431)
            ·
              refine ⟨19598377478391850897418147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13065584985594567264945431 19598377478391850897418147)
              ·
                refine ⟨29397566217587776346127221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19598377478391850897418147 29397566217587776346127221)
                ·
                  refine ⟨2756021832898854032449427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29397566217587776346127221 2756021832898854032449427)
                  ·
                    refine ⟨4134032749348281048674141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2756021832898854032449427 4134032749348281048674141)
                    ·
                      refine ⟨1550262281005605393252803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4134032749348281048674141 1550262281005605393252803)
                      ·
                        rfl

theorem cell23_3019125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3019125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019125 prefixEnd_3019125 := by exact prefixLift 3019125
  have htrace : WordTrace (prefixWord ++ tailWord_3019125) baseStart_3019125 baseEnd_3019125 := by
    simpa [prefixWord, tailWord_3019125, baseEnd_3019125] using wordTrace_append hprefix tailTrace_3019125
  have hstable : (prefixWord ++ tailWord_3019125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019125).length < 2 ^ (prefixWord ++ tailWord_3019125).sum := by decide
  have hdescent : baseEnd_3019125 < baseStart_3019125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019145 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 1, 5]
def baseStart_3019145 : Nat := 118140960795 + 3019145 * 2 ^ 59
def prefixEnd_3019145 : Nat := 4983230072969 + 3 ^ 40 * 3019145 * 2
def baseEnd_3019145 : Nat := 516757516872898438334237

theorem tailTrace_3019145 : CollatzResearch.WordTrace tailWord_3019145 prefixEnd_3019145 516757516872898438334237 := by
  unfold tailWord_3019145
  simp only [CollatzResearch.WordTrace]
  refine ⟨110117264647160768759794889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73411509764773845839863259 110117264647160768759794889)
  ·
    refine ⟨82587948485370576569846167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110117264647160768759794889 82587948485370576569846167)
    ·
      refine ⟨123881922728055864854769251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82587948485370576569846167 123881922728055864854769251)
      ·
        refine ⟨185822884092083797282153877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123881922728055864854769251 185822884092083797282153877)
        ·
          refine ⟨8710447691816427997600963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185822884092083797282153877 8710447691816427997600963)
          ·
            refine ⟨13065671537724641996401445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8710447691816427997600963 13065671537724641996401445)
            ·
              refine ⟨2449813413323370374325271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13065671537724641996401445 2449813413323370374325271)
              ·
                refine ⟨3674720119985055561487907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449813413323370374325271 3674720119985055561487907)
                ·
                  refine ⟨5512080179977583342231861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674720119985055561487907 5512080179977583342231861)
                  ·
                    refine ⟨516757516872898438334237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5512080179977583342231861 516757516872898438334237)
                    ·
                      rfl

theorem cell23_3019145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 5].length) (baseStart_3019145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019145 prefixEnd_3019145 := by exact prefixLift 3019145
  have htrace : WordTrace (prefixWord ++ tailWord_3019145) baseStart_3019145 baseEnd_3019145 := by
    simpa [prefixWord, tailWord_3019145, baseEnd_3019145] using wordTrace_append hprefix tailTrace_3019145
  have hstable : (prefixWord ++ tailWord_3019145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019145).length < 2 ^ (prefixWord ++ tailWord_3019145).sum := by decide
  have hdescent : baseEnd_3019145 < baseStart_3019145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019161 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_3019161 : Nat := 118140960795 + 3019161 * 2 ^ 59
def prefixEnd_3019161 : Nat := 4983230072969 + 3 ^ 40 * 3019161 * 2
def baseEnd_3019161 : Nat := 1550280766309167252402637

theorem tailTrace_3019161 : CollatzResearch.WordTrace tailWord_3019161 prefixEnd_3019161 1550280766309167252402637 := by
  unfold tailWord_3019161
  simp only [CollatzResearch.WordTrace]
  refine ⟨110117848215102803492377337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73411898810068535661584891 110117848215102803492377337)
  ·
    refine ⟨82588386161327102619283003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110117848215102803492377337 82588386161327102619283003)
    ·
      refine ⟨123882579241990653928924505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82588386161327102619283003 123882579241990653928924505)
      ·
        refine ⟨92911934431492990446693379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123882579241990653928924505 92911934431492990446693379)
        ·
          refine ⟨139367901647239485670040069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92911934431492990446693379 139367901647239485670040069)
          ·
            refine ⟨26131481558857403563132513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139367901647239485670040069 26131481558857403563132513)
            ·
              refine ⟨19598611169143052672349385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26131481558857403563132513 19598611169143052672349385)
              ·
                refine ⟨14698958376857289504262039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19598611169143052672349385 14698958376857289504262039)
                ·
                  refine ⟨22048437565285934256393059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14698958376857289504262039 22048437565285934256393059)
                  ·
                    refine ⟨33072656347928901384589589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22048437565285934256393059 33072656347928901384589589)
                    ·
                      refine ⟨1550280766309167252402637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33072656347928901384589589 1550280766309167252402637)
                      ·
                        rfl

theorem cell23_3019161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_3019161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019161 prefixEnd_3019161 := by exact prefixLift 3019161
  have htrace : WordTrace (prefixWord ++ tailWord_3019161) baseStart_3019161 baseEnd_3019161 := by
    simpa [prefixWord, tailWord_3019161, baseEnd_3019161] using wordTrace_append hprefix tailTrace_3019161
  have hstable : (prefixWord ++ tailWord_3019161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019161).length < 2 ^ (prefixWord ++ tailWord_3019161).sum := by decide
  have hdescent : baseEnd_3019161 < baseStart_3019161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019168 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3019168 : Nat := 118140960795 + 3019168 * 2 ^ 59
def prefixEnd_3019168 : Nat := 4983230072969 + 3 ^ 40 * 3019168 * 2
def baseEnd_3019168 : Nat := 1550284360673748725015105

theorem tailTrace_3019168 : CollatzResearch.WordTrace tailWord_3019168 prefixEnd_3019168 1550284360673748725015105 := by
  unfold tailWord_3019168
  simp only [CollatzResearch.WordTrace]
  refine ⟨55059051763038721843941079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73412069017384962458588105 55059051763038721843941079)
  ·
    refine ⟨82588577644558082765911619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55059051763038721843941079 82588577644558082765911619)
    ·
      refine ⟨123882866466837124148867429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82588577644558082765911619 123882866466837124148867429)
      ·
        refine ⟨23228037462531960777912643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123882866466837124148867429 23228037462531960777912643)
        ·
          refine ⟨34842056193797941166868965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23228037462531960777912643 34842056193797941166868965)
          ·
            refine ⟨6532885536337113968787931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34842056193797941166868965 6532885536337113968787931)
            ·
              refine ⟨9799328304505670953181897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6532885536337113968787931 9799328304505670953181897)
              ·
                refine ⟨7349496228379253214886423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9799328304505670953181897 7349496228379253214886423)
                ·
                  refine ⟨11024244342568879822329635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7349496228379253214886423 11024244342568879822329635)
                  ·
                    refine ⟨16536366513853319733494453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11024244342568879822329635 16536366513853319733494453)
                    ·
                      refine ⟨1550284360673748725015105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16536366513853319733494453 1550284360673748725015105)
                      ·
                        rfl

theorem cell23_3019168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3019168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019168 prefixEnd_3019168 := by exact prefixLift 3019168
  have htrace : WordTrace (prefixWord ++ tailWord_3019168) baseStart_3019168 baseEnd_3019168 := by
    simpa [prefixWord, tailWord_3019168, baseEnd_3019168] using wordTrace_append hprefix tailTrace_3019168
  have hstable : (prefixWord ++ tailWord_3019168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019168).length < 2 ^ (prefixWord ++ tailWord_3019168).sum := by decide
  have hdescent : baseEnd_3019168 < baseStart_3019168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019175 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3019175 : Nat := 118140960795 + 3019175 * 2 ^ 59
def prefixEnd_3019175 : Nat := 4983230072969 + 3 ^ 40 * 3019175 * 2
def baseEnd_3019175 : Nat := 516762651679443399209191

theorem tailTrace_3019175 : CollatzResearch.WordTrace tailWord_3019175 prefixEnd_3019175 516762651679443399209191 := by
  unfold tailWord_3019175
  simp only [CollatzResearch.WordTrace]
  refine ⟨110118358837052083883386979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73412239224701389255591319 110118358837052083883386979)
  ·
    refine ⟨165177538255578125825080469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110118358837052083883386979 165177538255578125825080469)
    ·
      refine ⟨7742697105730224648050647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 165177538255578125825080469 7742697105730224648050647)
      ·
        refine ⟨11614045658595336972075971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7742697105730224648050647 11614045658595336972075971)
        ·
          refine ⟨17421068487893005458113957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11614045658595336972075971 17421068487893005458113957)
          ·
            refine ⟨3266450341479938523396367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17421068487893005458113957 3266450341479938523396367)
            ·
              refine ⟨4899675512219907785094551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3266450341479938523396367 4899675512219907785094551)
              ·
                refine ⟨7349513268329861677641827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899675512219907785094551 7349513268329861677641827)
                ·
                  refine ⟨11024269902494792516462741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7349513268329861677641827 11024269902494792516462741)
                  ·
                    refine ⟨516762651679443399209191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11024269902494792516462741 516762651679443399209191)
                    ·
                      rfl

theorem cell23_3019175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3019175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019175 prefixEnd_3019175 := by exact prefixLift 3019175
  have htrace : WordTrace (prefixWord ++ tailWord_3019175) baseStart_3019175 baseEnd_3019175 := by
    simpa [prefixWord, tailWord_3019175, baseEnd_3019175] using wordTrace_append hprefix tailTrace_3019175
  have hstable : (prefixWord ++ tailWord_3019175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019175).length < 2 ^ (prefixWord ++ tailWord_3019175).sum := by decide
  have hdescent : baseEnd_3019175 < baseStart_3019175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019185 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3019185 : Nat := 118140960795 + 3019185 * 2 ^ 59
def prefixEnd_3019185 : Nat := 4983230072969 + 3 ^ 40 * 3019185 * 2
def baseEnd_3019185 : Nat := 1550293089844875158502527

theorem tailTrace_3019185 : CollatzResearch.WordTrace tailWord_3019185 prefixEnd_3019185 1550293089844875158502527 := by
  unfold tailWord_3019185
  simp only [CollatzResearch.WordTrace]
  refine ⟨110118723567015855591251009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73412482378010570394167339 110118723567015855591251009)
  ·
    refine ⟨82589042675261891693438257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110118723567015855591251009 82589042675261891693438257)
    ·
      refine ⟨61941782006446418770078693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82589042675261891693438257 61941782006446418770078693)
      ·
        refine ⟨11614084126208703519389755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61941782006446418770078693 11614084126208703519389755)
        ·
          refine ⟨17421126189313055279084633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11614084126208703519389755 17421126189313055279084633)
          ·
            refine ⟨13065844641984791459313475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17421126189313055279084633 13065844641984791459313475)
            ·
              refine ⟨19598766962977187188970213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13065844641984791459313475 19598766962977187188970213)
              ·
                refine ⟨3674768805558222597931915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19598766962977187188970213 3674768805558222597931915)
                ·
                  refine ⟨5512153208337333896897873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674768805558222597931915 5512153208337333896897873)
                  ·
                    refine ⟨4134114906253000422673405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5512153208337333896897873 4134114906253000422673405)
                    ·
                      refine ⟨1550293089844875158502527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4134114906253000422673405 1550293089844875158502527)
                      ·
                        rfl

theorem cell23_3019185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3019185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019185 prefixEnd_3019185 := by exact prefixLift 3019185
  have htrace : WordTrace (prefixWord ++ tailWord_3019185) baseStart_3019185 baseEnd_3019185 := by
    simpa [prefixWord, tailWord_3019185, baseEnd_3019185] using wordTrace_append hprefix tailTrace_3019185
  have hstable : (prefixWord ++ tailWord_3019185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019185).length < 2 ^ (prefixWord ++ tailWord_3019185).sum := by decide
  have hdescent : baseEnd_3019185 < baseStart_3019185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019211 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 5]
def baseStart_3019211 : Nat := 118140960795 + 3019211 * 2 ^ 59
def prefixEnd_3019211 : Nat := 4983230072969 + 3 ^ 40 * 3019211 * 2
def baseEnd_3019211 : Nat := 1550306440341892056777407

theorem tailTrace_3019211 : CollatzResearch.WordTrace tailWord_3019211 prefixEnd_3019211 1550306440341892056777407 := by
  unfold tailWord_3019211
  simp only [CollatzResearch.WordTrace]
  refine ⟨110119671864921662031697487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73413114576614441354464991 110119671864921662031697487)
  ·
    refine ⟨165179507797382493047546231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110119671864921662031697487 165179507797382493047546231)
    ·
      refine ⟨247769261696073739571319347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165179507797382493047546231 247769261696073739571319347)
      ·
        refine ⟨371653892544110609356979021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247769261696073739571319347 371653892544110609356979021)
        ·
          refine ⟨139370209704041478508867133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371653892544110609356979021 139370209704041478508867133)
          ·
            refine ⟨52263828639015554440825175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139370209704041478508867133 52263828639015554440825175)
            ·
              refine ⟨78395742958523331661237763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52263828639015554440825175 78395742958523331661237763)
              ·
                refine ⟨117593614437784997491856645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78395742958523331661237763 117593614437784997491856645)
                ·
                  refine ⟨22048802707084687029723121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117593614437784997491856645 22048802707084687029723121)
                  ·
                    refine ⟨16536602030313515272292341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22048802707084687029723121 16536602030313515272292341)
                    ·
                      refine ⟨1550306440341892056777407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16536602030313515272292341 1550306440341892056777407)
                      ·
                        rfl

theorem cell23_3019211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_3019211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019211 prefixEnd_3019211 := by exact prefixLift 3019211
  have htrace : WordTrace (prefixWord ++ tailWord_3019211) baseStart_3019211 baseEnd_3019211 := by
    simpa [prefixWord, tailWord_3019211, baseEnd_3019211] using wordTrace_append hprefix tailTrace_3019211
  have hstable : (prefixWord ++ tailWord_3019211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019211).length < 2 ^ (prefixWord ++ tailWord_3019211).sum := by decide
  have hdescent : baseEnd_3019211 < baseStart_3019211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019215 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 3]
def baseStart_3019215 : Nat := 118140960795 + 3019215 * 2 ^ 59
def prefixEnd_3019215 : Nat := 4983230072969 + 3 ^ 40 * 3019215 * 2
def baseEnd_3019215 : Nat := 1550308494264510041127389

theorem tailTrace_3019215 : CollatzResearch.WordTrace tailWord_3019215 prefixEnd_3019215 1550308494264510041127389 := by
  unfold tailWord_3019215
  simp only [CollatzResearch.WordTrace]
  refine ⟨110119817756907170714843099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73413211837938113809895399 110119817756907170714843099)
  ·
    refine ⟨165179726635360756072264649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110119817756907170714843099 165179726635360756072264649)
    ·
      refine ⟨123884794976520567054198487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165179726635360756072264649 123884794976520567054198487)
      ·
        refine ⟨185827192464780850581297731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123884794976520567054198487 185827192464780850581297731)
        ·
          refine ⟨278740788697171275871946597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185827192464780850581297731 278740788697171275871946597)
          ·
            refine ⟨52263897880719614225989987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278740788697171275871946597 52263897880719614225989987)
            ·
              refine ⟨78395846821079421338984981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52263897880719614225989987 78395846821079421338984981)
              ·
                refine ⟨3674805319738097875264921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78395846821079421338984981 3674805319738097875264921)
                ·
                  refine ⟨2756103989803573406448691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3674805319738097875264921 2756103989803573406448691)
                  ·
                    refine ⟨4134155984705360109673037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2756103989803573406448691 4134155984705360109673037)
                    ·
                      refine ⟨1550308494264510041127389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4134155984705360109673037 1550308494264510041127389)
                      ·
                        rfl

theorem cell23_3019215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 3].length) (baseStart_3019215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019215 prefixEnd_3019215 := by exact prefixLift 3019215
  have htrace : WordTrace (prefixWord ++ tailWord_3019215) baseStart_3019215 baseEnd_3019215 := by
    simpa [prefixWord, tailWord_3019215, baseEnd_3019215] using wordTrace_append hprefix tailTrace_3019215
  have hstable : (prefixWord ++ tailWord_3019215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019215).length < 2 ^ (prefixWord ++ tailWord_3019215).sum := by decide
  have hdescent : baseEnd_3019215 < baseStart_3019215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019225 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 3, 3, 2]
def baseStart_3019225 : Nat := 118140960795 + 3019225 * 2 ^ 59
def prefixEnd_3019225 : Nat := 4983230072969 + 3 ^ 40 * 3019225 * 2
def baseEnd_3019225 : Nat := 1550313629071055002002343

theorem tailTrace_3019225 : CollatzResearch.WordTrace tailWord_3019225 prefixEnd_3019225 1550313629071055002002343 := by
  unfold tailWord_3019225
  simp only [CollatzResearch.WordTrace]
  refine ⟨110120182486870942422707129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73413454991247294948471419 110120182486870942422707129)
  ·
    refine ⟨82590136865153206817030347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110120182486870942422707129 82590136865153206817030347)
    ·
      refine ⟨123885205297729810225545521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82590136865153206817030347 123885205297729810225545521)
      ·
        refine ⟨92913903973297357669159141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123885205297729810225545521 92913903973297357669159141)
        ·
          refine ⟨17421356994993254562967339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92913903973297357669159141 17421356994993254562967339)
          ·
            refine ⟨26132035492489881844451009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17421356994993254562967339 26132035492489881844451009)
            ·
              refine ⟨19599026619367411383338257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26132035492489881844451009 19599026619367411383338257)
              ·
                refine ⟨14699269964525558537503693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19599026619367411383338257 14699269964525558537503693)
                ·
                  refine ⟨5512226236697084451563885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14699269964525558537503693 5512226236697084451563885)
                  ·
                    refine ⟨2067084838761406669336457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5512226236697084451563885 2067084838761406669336457)
                    ·
                      refine ⟨1550313629071055002002343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067084838761406669336457 1550313629071055002002343)
                      ·
                        rfl

theorem cell23_3019225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_3019225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019225 prefixEnd_3019225 := by exact prefixLift 3019225
  have htrace : WordTrace (prefixWord ++ tailWord_3019225) baseStart_3019225 baseEnd_3019225 := by
    simpa [prefixWord, tailWord_3019225, baseEnd_3019225] using wordTrace_append hprefix tailTrace_3019225
  have hstable : (prefixWord ++ tailWord_3019225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019225).length < 2 ^ (prefixWord ++ tailWord_3019225).sum := by decide
  have hdescent : baseEnd_3019225 < baseStart_3019225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019242 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_3019242 : Nat := 118140960795 + 3019242 * 2 ^ 59
def prefixEnd_3019242 : Nat := 4983230072969 + 3 ^ 40 * 3019242 * 2
def baseEnd_3019242 : Nat := 1550322358242181435489765

theorem tailTrace_3019242 : CollatzResearch.WordTrace tailWord_3019242 prefixEnd_3019242 1550322358242181435489765 := by
  unfold tailWord_3019242
  simp only [CollatzResearch.WordTrace]
  refine ⟨27530200631952338581518995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73413868351872902884050653 27530200631952338581518995)
  ·
    refine ⟨41295300947928507872278493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27530200631952338581518995 41295300947928507872278493)
    ·
      refine ⟨15485737855473190452104435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41295300947928507872278493 15485737855473190452104435)
      ·
        refine ⟨23228606783209785678156653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15485737855473190452104435 23228606783209785678156653)
        ·
          refine ⟨8710727543703669629308745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23228606783209785678156653 8710727543703669629308745)
          ·
            refine ⟨6533045657777752221981559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8710727543703669629308745 6533045657777752221981559)
            ·
              refine ⟨9799568486666628332972339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6533045657777752221981559 9799568486666628332972339)
              ·
                refine ⟨14699352729999942499458509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9799568486666628332972339 14699352729999942499458509)
                ·
                  refine ⟨5512257273749978437296941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14699352729999942499458509 5512257273749978437296941)
                  ·
                    refine ⟨2067096477656241913986353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5512257273749978437296941 2067096477656241913986353)
                    ·
                      refine ⟨1550322358242181435489765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067096477656241913986353 1550322358242181435489765)
                      ·
                        rfl

theorem cell23_3019242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_3019242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019242 prefixEnd_3019242 := by exact prefixLift 3019242
  have htrace : WordTrace (prefixWord ++ tailWord_3019242) baseStart_3019242 baseEnd_3019242 := by
    simpa [prefixWord, tailWord_3019242, baseEnd_3019242] using wordTrace_append hprefix tailTrace_3019242
  have hstable : (prefixWord ++ tailWord_3019242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019242).length < 2 ^ (prefixWord ++ tailWord_3019242).sum := by decide
  have hdescent : baseEnd_3019242 < baseStart_3019242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019266 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3019266 : Nat := 118140960795 + 3019266 * 2 ^ 59
def prefixEnd_3019266 : Nat := 4983230072969 + 3 ^ 40 * 3019266 * 2
def baseEnd_3019266 : Nat := 1550334681777889341589655

theorem tailTrace_3019266 : CollatzResearch.WordTrace tailWord_3019266 prefixEnd_3019266 1550334681777889341589655 := by
  unfold tailWord_3019266
  simp only [CollatzResearch.WordTrace]
  refine ⟨27530419469930601606237413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73414451919814937616633101 27530419469930601606237413)
  ·
    refine ⟨5161953650611987801169515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27530419469930601606237413 5161953650611987801169515)
    ·
      refine ⟨7742930475917981701754273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5161953650611987801169515 7742930475917981701754273)
      ·
        refine ⟨5807197856938486276315705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7742930475917981701754273 5807197856938486276315705)
        ·
          refine ⟨4355398392703864707236779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5807197856938486276315705 4355398392703864707236779)
          ·
            refine ⟨6533097589055797060855169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355398392703864707236779 6533097589055797060855169)
            ·
              refine ⟨4899823191791847795641377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6533097589055797060855169 4899823191791847795641377)
              ·
                refine ⟨3674867393843885846731033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4899823191791847795641377 3674867393843885846731033)
                ·
                  refine ⟨2756150545382914385048275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3674867393843885846731033 2756150545382914385048275)
                  ·
                    refine ⟨4134225818074371577572413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2756150545382914385048275 4134225818074371577572413)
                    ·
                      refine ⟨1550334681777889341589655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4134225818074371577572413 1550334681777889341589655)
                      ·
                        rfl

theorem cell23_3019266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3019266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019266 prefixEnd_3019266 := by exact prefixLift 3019266
  have htrace : WordTrace (prefixWord ++ tailWord_3019266) baseStart_3019266 baseEnd_3019266 := by
    simpa [prefixWord, tailWord_3019266, baseEnd_3019266] using wordTrace_append hprefix tailTrace_3019266
  have hstable : (prefixWord ++ tailWord_3019266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019266).length < 2 ^ (prefixWord ++ tailWord_3019266).sum := by decide
  have hdescent : baseEnd_3019266 < baseStart_3019266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019388 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_3019388 : Nat := 118140960795 + 3019388 * 2 ^ 59
def prefixEnd_3019388 : Nat := 4983230072969 + 3 ^ 40 * 3019388 * 2
def baseEnd_3019388 : Nat := 1550397326417737864264093

theorem tailTrace_3019388 : CollatzResearch.WordTrace tailWord_3019388 prefixEnd_3019388 1550397326417737864264093 := by
  unfold tailWord_3019388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55063063792640210630445409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73417418390186947507260545 55063063792640210630445409)
  ·
    refine ⟨41297297844480157972834057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55063063792640210630445409 41297297844480157972834057)
    ·
      refine ⟨30972973383360118479625543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41297297844480157972834057 30972973383360118479625543)
      ·
        refine ⟨46459460075040177719438315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30972973383360118479625543 46459460075040177719438315)
        ·
          refine ⟨69689190112560266579157473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46459460075040177719438315 69689190112560266579157473)
          ·
            refine ⟨52266892584420199934368105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69689190112560266579157473 52266892584420199934368105)
            ·
              refine ⟨39200169438315149950776079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52266892584420199934368105 39200169438315149950776079)
              ·
                refine ⟨58800254157472724926164119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39200169438315149950776079 58800254157472724926164119)
                ·
                  refine ⟨88200381236209087389246179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58800254157472724926164119 88200381236209087389246179)
                  ·
                    refine ⟨132300571854313631083869269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88200381236209087389246179 132300571854313631083869269)
                    ·
                      refine ⟨1550397326417737864264093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 132300571854313631083869269 1550397326417737864264093)
                      ·
                        rfl

theorem cell23_3019388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_3019388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019388 prefixEnd_3019388 := by exact prefixLift 3019388
  have htrace : WordTrace (prefixWord ++ tailWord_3019388) baseStart_3019388 baseEnd_3019388 := by
    simpa [prefixWord, tailWord_3019388, baseEnd_3019388] using wordTrace_append hprefix tailTrace_3019388
  have hstable : (prefixWord ++ tailWord_3019388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019388).length < 2 ^ (prefixWord ++ tailWord_3019388).sum := by decide
  have hdescent : baseEnd_3019388 < baseStart_3019388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019389 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_3019389 : Nat := 118140960795 + 3019389 * 2 ^ 59
def prefixEnd_3019389 : Nat := 4983230072969 + 3 ^ 40 * 3019389 * 2
def baseEnd_3019389 : Nat := 516799279966130786783863

theorem tailTrace_3019389 : CollatzResearch.WordTrace tailWord_3019389 prefixEnd_3019389 516799279966130786783863 := by
  unfold tailWord_3019389
  simp only [CollatzResearch.WordTrace]
  refine ⟨110126164058276798431677221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73417442705517865621118147 110126164058276798431677221)
  ·
    refine ⟨20648655760926899705939479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110126164058276798431677221 20648655760926899705939479)
    ·
      refine ⟨30972983641390349558909219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20648655760926899705939479 30972983641390349558909219)
      ·
        refine ⟨46459475462085524338363829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30972983641390349558909219 46459475462085524338363829)
        ·
          refine ⟨4355575824570517906721609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46459475462085524338363829 4355575824570517906721609)
          ·
            refine ⟨3266681868427888430041207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4355575824570517906721609 3266681868427888430041207)
            ·
              refine ⟨4900022802641832645061811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3266681868427888430041207 4900022802641832645061811)
              ·
                refine ⟨7350034203962748967592717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4900022802641832645061811 7350034203962748967592717)
                ·
                  refine ⟨2756262826486030862847269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7350034203962748967592717 2756262826486030862847269)
                  ·
                    refine ⟨516799279966130786783863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2756262826486030862847269 516799279966130786783863)
                    ·
                      rfl

theorem cell23_3019389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_3019389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019389 prefixEnd_3019389 := by exact prefixLift 3019389
  have htrace : WordTrace (prefixWord ++ tailWord_3019389) baseStart_3019389 baseEnd_3019389 := by
    simpa [prefixWord, tailWord_3019389, baseEnd_3019389] using wordTrace_append hprefix tailTrace_3019389
  have hstable : (prefixWord ++ tailWord_3019389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019389).length < 2 ^ (prefixWord ++ tailWord_3019389).sum := by decide
  have hdescent : baseEnd_3019389 < baseStart_3019389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019402 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 6]
def baseStart_3019402 : Nat := 118140960795 + 3019402 * 2 ^ 59
def prefixEnd_3019402 : Nat := 4983230072969 + 3 ^ 40 * 3019402 * 2
def baseEnd_3019402 : Nat := 172267168349655645498781

theorem tailTrace_3019402 : CollatzResearch.WordTrace tailWord_3019402 prefixEnd_3019402 172267168349655645498781 := by
  unfold tailWord_3019402
  simp only [CollatzResearch.WordTrace]
  refine ⟨27531659551807425412975115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73417758804819801101266973 27531659551807425412975115)
  ·
    refine ⟨41297489327711138119462673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27531659551807425412975115 41297489327711138119462673)
    ·
      refine ⟨30973116995783353589597005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41297489327711138119462673 30973116995783353589597005)
      ·
        refine ⟨11614918873418757596098877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30973116995783353589597005 11614918873418757596098877)
        ·
          refine ⟨4355594577532034098537079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11614918873418757596098877 4355594577532034098537079)
          ·
            refine ⟨6533391866298051147805619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355594577532034098537079 6533391866298051147805619)
            ·
              refine ⟨9800087799447076721708429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6533391866298051147805619 9800087799447076721708429)
              ·
                refine ⟨3675032924792653770640661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9800087799447076721708429 3675032924792653770640661)
                ·
                  refine ⟨172267168349655645498781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3675032924792653770640661 172267168349655645498781)
                  ·
                    rfl

theorem cell23_3019402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_3019402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019402 prefixEnd_3019402 := by exact prefixLift 3019402
  have htrace : WordTrace (prefixWord ++ tailWord_3019402) baseStart_3019402 baseEnd_3019402 := by
    simpa [prefixWord, tailWord_3019402, baseEnd_3019402] using wordTrace_append hprefix tailTrace_3019402
  have hstable : (prefixWord ++ tailWord_3019402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019402).length < 2 ^ (prefixWord ++ tailWord_3019402).sum := by decide
  have hdescent : baseEnd_3019402 < baseStart_3019402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019415 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 3, 5]
def baseStart_3019415 : Nat := 118140960795 + 3019415 * 2 ^ 59
def prefixEnd_3019415 : Nat := 4983230072969 + 3 ^ 40 * 3019415 * 2
def baseEnd_3019415 : Nat := 516803730131803086208823

theorem tailTrace_3019415 : CollatzResearch.WordTrace tailWord_3019415 prefixEnd_3019415 516803730131803086208823 := by
  unfold tailWord_3019415
  simp only [CollatzResearch.WordTrace]
  refine ⟨110127112356182604872123699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73418074904121736581415799 110127112356182604872123699)
  ·
    refine ⟨165190668534273907308185549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110127112356182604872123699 165190668534273907308185549)
    ·
      refine ⟨61946500700352715240569581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165190668534273907308185549 61946500700352715240569581)
      ·
        refine ⟨23229937762632268215213593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61946500700352715240569581 23229937762632268215213593)
        ·
          refine ⟨17422453321974201161410195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23229937762632268215213593 17422453321974201161410195)
          ·
            refine ⟨26133679982961301742115293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17422453321974201161410195 26133679982961301742115293)
            ·
              refine ⟨9800129993610488153293235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26133679982961301742115293 9800129993610488153293235)
              ·
                refine ⟨14700194990415732229939853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9800129993610488153293235 14700194990415732229939853)
                ·
                  refine ⟨5512573121405899586227445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14700194990415732229939853 5512573121405899586227445)
                  ·
                    refine ⟨516803730131803086208823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5512573121405899586227445 516803730131803086208823)
                    ·
                      rfl

theorem cell23_3019415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_3019415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019415 prefixEnd_3019415 := by exact prefixLift 3019415
  have htrace : WordTrace (prefixWord ++ tailWord_3019415) baseStart_3019415 baseEnd_3019415 := by
    simpa [prefixWord, tailWord_3019415, baseEnd_3019415] using wordTrace_append hprefix tailTrace_3019415
  have hstable : (prefixWord ++ tailWord_3019415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019415).length < 2 ^ (prefixWord ++ tailWord_3019415).sum := by decide
  have hdescent : baseEnd_3019415 < baseStart_3019415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019429 : List Nat := [1, 3, 1, 2, 1, 2, 1, 7, 1, 1, 3]
def baseStart_3019429 : Nat := 118140960795 + 3019429 * 2 ^ 59
def prefixEnd_3019429 : Nat := 4983230072969 + 3 ^ 40 * 3019429 * 2
def baseEnd_3019429 : Nat := 1550418379124572203851405

theorem tailTrace_3019429 : CollatzResearch.WordTrace tailWord_3019429 prefixEnd_3019429 1550418379124572203851405 := by
  unfold tailWord_3019429
  simp only [CollatzResearch.WordTrace]
  refine ⟨110127622978131885263133341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73418415318754590175422227 110127622978131885263133341)
  ·
    refine ⟨41297858616799456973675003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110127622978131885263133341 41297858616799456973675003)
    ·
      refine ⟨61946787925199185460512505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41297858616799456973675003 61946787925199185460512505)
      ·
        refine ⟨46460090943899389095384379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61946787925199185460512505 46460090943899389095384379)
        ·
          refine ⟨69690136415849083643076569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46460090943899389095384379 69690136415849083643076569)
          ·
            refine ⟨52267602311886812732307427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69690136415849083643076569 52267602311886812732307427)
            ·
              refine ⟨78401403467830219098461141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52267602311886812732307427 78401403467830219098461141)
              ·
                refine ⟨1837532893777270760120183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78401403467830219098461141 1837532893777270760120183)
                ·
                  refine ⟨2756299340665906140180275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837532893777270760120183 2756299340665906140180275)
                  ·
                    refine ⟨4134449010998859210270413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2756299340665906140180275 4134449010998859210270413)
                    ·
                      refine ⟨1550418379124572203851405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4134449010998859210270413 1550418379124572203851405)
                      ·
                        rfl

theorem cell23_3019429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_3019429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019429 prefixEnd_3019429 := by exact prefixLift 3019429
  have htrace : WordTrace (prefixWord ++ tailWord_3019429) baseStart_3019429 baseEnd_3019429 := by
    simpa [prefixWord, tailWord_3019429, baseEnd_3019429] using wordTrace_append hprefix tailTrace_3019429
  have hstable : (prefixWord ++ tailWord_3019429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019429).length < 2 ^ (prefixWord ++ tailWord_3019429).sum := by decide
  have hdescent : baseEnd_3019429 < baseStart_3019429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019489 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_3019489 : Nat := 118140960795 + 3019489 * 2 ^ 59
def prefixEnd_3019489 : Nat := 4983230072969 + 3 ^ 40 * 3019489 * 2
def baseEnd_3019489 : Nat := 1550449187963841969101129

theorem tailTrace_3019489 : CollatzResearch.WordTrace tailWord_3019489 prefixEnd_3019489 1550449187963841969101129 := by
  unfold tailWord_3019489
  simp only [CollatzResearch.WordTrace]
  refine ⟨110129811357914515510317521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73419874238609677006878347 110129811357914515510317521)
  ·
    refine ⟨82597358518435886632738141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110129811357914515510317521 82597358518435886632738141)
    ·
      refine ⟨30974009444413457487276803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82597358518435886632738141 30974009444413457487276803)
      ·
        refine ⟨46461014166620186230915205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30974009444413457487276803 46461014166620186230915205)
        ·
          refine ⟨8711440156241284918296601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46461014166620186230915205 8711440156241284918296601)
          ·
            refine ⟨6533580117180963688722451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8711440156241284918296601 6533580117180963688722451)
            ·
              refine ⟨9800370175771445533083677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6533580117180963688722451 9800370175771445533083677)
              ·
                refine ⟨3675138815914292074906379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9800370175771445533083677 3675138815914292074906379)
                ·
                  refine ⟨5512708223871438112359569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675138815914292074906379 5512708223871438112359569)
                  ·
                    refine ⟨4134531167903578584269677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5512708223871438112359569 4134531167903578584269677)
                    ·
                      refine ⟨1550449187963841969101129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4134531167903578584269677 1550449187963841969101129)
                      ·
                        rfl

theorem cell23_3019489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_3019489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019489 prefixEnd_3019489 := by exact prefixLift 3019489
  have htrace : WordTrace (prefixWord ++ tailWord_3019489) baseStart_3019489 baseEnd_3019489 := by
    simpa [prefixWord, tailWord_3019489, baseEnd_3019489] using wordTrace_append hprefix tailTrace_3019489
  have hstable : (prefixWord ++ tailWord_3019489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019489).length < 2 ^ (prefixWord ++ tailWord_3019489).sum := by decide
  have hdescent : baseEnd_3019489 < baseStart_3019489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019496 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 2, 4]
def baseStart_3019496 : Nat := 118140960795 + 3019496 * 2 ^ 59
def prefixEnd_3019496 : Nat := 4983230072969 + 3 ^ 40 * 3019496 * 2
def baseEnd_3019496 : Nat := 516817594109474480571199

theorem tailTrace_3019496 : CollatzResearch.WordTrace tailWord_3019496 prefixEnd_3019496 516817594109474480571199 := by
  unfold tailWord_3019496
  simp only [CollatzResearch.WordTrace]
  refine ⟨55065033334444577852911171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73420044445926103803881561 55065033334444577852911171)
  ·
    refine ⟨82597550001666866779366757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55065033334444577852911171 82597550001666866779366757)
    ·
      refine ⟨15487040625312537521131267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82597550001666866779366757 15487040625312537521131267)
      ·
        refine ⟨23230560937968806281696901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15487040625312537521131267 23230560937968806281696901)
        ·
          refine ⟨4355730175869151177818169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23230560937968806281696901 4355730175869151177818169)
          ·
            refine ⟨3266797631901863383363627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4355730175869151177818169 3266797631901863383363627)
            ·
              refine ⟨4900196447852795075045441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3266797631901863383363627 4900196447852795075045441)
              ·
                refine ⟨3675147335889596306284081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4900196447852795075045441 3675147335889596306284081)
                ·
                  refine ⟨2756360501917197229713061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3675147335889596306284081 2756360501917197229713061)
                  ·
                    refine ⟨516817594109474480571199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2756360501917197229713061 516817594109474480571199)
                    ·
                      rfl

theorem cell23_3019496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_3019496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019496 prefixEnd_3019496 := by exact prefixLift 3019496
  have htrace : WordTrace (prefixWord ++ tailWord_3019496) baseStart_3019496 baseEnd_3019496 := by
    simpa [prefixWord, tailWord_3019496, baseEnd_3019496] using wordTrace_append hprefix tailTrace_3019496
  have hstable : (prefixWord ++ tailWord_3019496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019496).length < 2 ^ (prefixWord ++ tailWord_3019496).sum := by decide
  have hdescent : baseEnd_3019496 < baseStart_3019496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019525 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_3019525 : Nat := 118140960795 + 3019525 * 2 ^ 59
def prefixEnd_3019525 : Nat := 4983230072969 + 3 ^ 40 * 3019525 * 2
def baseEnd_3019525 : Nat := 1550467673267403828250963

theorem tailTrace_3019525 : CollatzResearch.WordTrace tailWord_3019525 prefixEnd_3019525 1550467673267403828250963 := by
  unfold tailWord_3019525
  simp only [CollatzResearch.WordTrace]
  refine ⟨110131124385784093658628029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73420749590522729105752019 110131124385784093658628029)
  ·
    refine ⟨41299171644669035121985511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110131124385784093658628029 41299171644669035121985511)
    ·
      refine ⟨61948757467003552682978267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41299171644669035121985511 61948757467003552682978267)
      ·
        refine ⟨92923136200505329024467401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61948757467003552682978267 92923136200505329024467401)
        ·
          refine ⟨69692352150378996768350551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92923136200505329024467401 69692352150378996768350551)
          ·
            refine ⟨104538528225568495152525827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69692352150378996768350551 104538528225568495152525827)
            ·
              refine ⟨156807792338352742728788741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104538528225568495152525827 156807792338352742728788741)
              ·
                refine ⟨29401461063441139261647889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156807792338352742728788741 29401461063441139261647889)
                ·
                  refine ⟨22051095797580854446235917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29401461063441139261647889 22051095797580854446235917)
                  ·
                    refine ⟨8269160924092820417338469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22051095797580854446235917 8269160924092820417338469)
                    ·
                      refine ⟨1550467673267403828250963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8269160924092820417338469 1550467673267403828250963)
                      ·
                        rfl

theorem cell23_3019525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_3019525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019525 prefixEnd_3019525 := by exact prefixLift 3019525
  have htrace : WordTrace (prefixWord ++ tailWord_3019525) baseStart_3019525 baseEnd_3019525 := by
    simpa [prefixWord, tailWord_3019525, baseEnd_3019525] using wordTrace_append hprefix tailTrace_3019525
  have hstable : (prefixWord ++ tailWord_3019525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019525).length < 2 ^ (prefixWord ++ tailWord_3019525).sum := by decide
  have hdescent : baseEnd_3019525 < baseStart_3019525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019529 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 1, 3, 2]
def baseStart_3019529 : Nat := 118140960795 + 3019529 * 2 ^ 59
def prefixEnd_3019529 : Nat := 4983230072969 + 3 ^ 40 * 3019529 * 2
def baseEnd_3019529 : Nat := 1550469727190021812600945

theorem tailTrace_3019529 : CollatzResearch.WordTrace tailWord_3019529 prefixEnd_3019529 1550469727190021812600945 := by
  unfold tailWord_3019529
  simp only [CollatzResearch.WordTrace]
  refine ⟨110131270277769602341773641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73420846851846401561182427 110131270277769602341773641)
  ·
    refine ⟨82598452708327201756330231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110131270277769602341773641 82598452708327201756330231)
    ·
      refine ⟨123897679062490802634495347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82598452708327201756330231 123897679062490802634495347)
      ·
        refine ⟨185846518593736203951743021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123897679062490802634495347 185846518593736203951743021)
        ·
          refine ⟨69692444472651076481903633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185846518593736203951743021 69692444472651076481903633)
          ·
            refine ⟨52269333354488307361427725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69692444472651076481903633 52269333354488307361427725)
            ·
              refine ⟨19601000007933115260535397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52269333354488307361427725 19601000007933115260535397)
              ·
                refine ⟨3675187501487459111350387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19601000007933115260535397 3675187501487459111350387)
                ·
                  refine ⟨5512781252231188667025581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675187501487459111350387 5512781252231188667025581)
                  ·
                    refine ⟨2067292969586695750134593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5512781252231188667025581 2067292969586695750134593)
                    ·
                      refine ⟨1550469727190021812600945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067292969586695750134593 1550469727190021812600945)
                      ·
                        rfl

theorem cell23_3019529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 3, 2].length) (baseStart_3019529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019529 prefixEnd_3019529 := by exact prefixLift 3019529
  have htrace : WordTrace (prefixWord ++ tailWord_3019529) baseStart_3019529 baseEnd_3019529 := by
    simpa [prefixWord, tailWord_3019529, baseEnd_3019529] using wordTrace_append hprefix tailTrace_3019529
  have hstable : (prefixWord ++ tailWord_3019529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019529).length < 2 ^ (prefixWord ++ tailWord_3019529).sum := by decide
  have hdescent : baseEnd_3019529 < baseStart_3019529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019576 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 2, 2, 2]
def baseStart_3019576 : Nat := 118140960795 + 3019576 * 2 ^ 59
def prefixEnd_3019576 : Nat := 4983230072969 + 3 ^ 40 * 3019576 * 2
def baseEnd_3019576 : Nat := 1550493860780783128713229

theorem tailTrace_3019576 : CollatzResearch.WordTrace tailWord_3019576 prefixEnd_3019576 1550493860780783128713229 := by
  unfold tailWord_3019576
  simp only [CollatzResearch.WordTrace]
  refine ⟨55066492254299664684367291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73421989672399552912489721 55066492254299664684367291)
  ·
    refine ⟨82599738381449497026550937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55066492254299664684367291 82599738381449497026550937)
    ·
      refine ⟨61949803786087122769913203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82599738381449497026550937 61949803786087122769913203)
      ·
        refine ⟨92924705679130684154869805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61949803786087122769913203 92924705679130684154869805)
        ·
          refine ⟨34846764629674006558076177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92924705679130684154869805 34846764629674006558076177)
          ·
            refine ⟨26135073472255504918557133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34846764629674006558076177 26135073472255504918557133)
            ·
              refine ⟨9800652552095814344458925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26135073472255504918557133 9800652552095814344458925)
              ·
                refine ⟨3675244707035930379172097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9800652552095814344458925 3675244707035930379172097)
                ·
                  refine ⟨2756433530276947784379073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3675244707035930379172097 2756433530276947784379073)
                  ·
                    refine ⟨2067325147707710838284305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2756433530276947784379073 2067325147707710838284305)
                    ·
                      refine ⟨1550493860780783128713229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067325147707710838284305 1550493860780783128713229)
                      ·
                        rfl

theorem cell23_3019576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_3019576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019576 prefixEnd_3019576 := by exact prefixLift 3019576
  have htrace : WordTrace (prefixWord ++ tailWord_3019576) baseStart_3019576 baseEnd_3019576 := by
    simpa [prefixWord, tailWord_3019576, baseEnd_3019576] using wordTrace_append hprefix tailTrace_3019576
  have hstable : (prefixWord ++ tailWord_3019576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019576).length < 2 ^ (prefixWord ++ tailWord_3019576).sum := by decide
  have hdescent : baseEnd_3019576 < baseStart_3019576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019619 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 2, 5, 2]
def baseStart_3019619 : Nat := 118140960795 + 3019619 * 2 ^ 59
def prefixEnd_3019619 : Nat := 4983230072969 + 3 ^ 40 * 3019619 * 2
def baseEnd_3019619 : Nat := 1550515940448926460475531

theorem tailTrace_3019619 : CollatzResearch.WordTrace tailWord_3019619 prefixEnd_3019619 1550515940448926460475531 := by
  unfold tailWord_3019619
  simp only [CollatzResearch.WordTrace]
  refine ⟨110134552847443547712549911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73423035231629031808366607 110134552847443547712549911)
  ·
    refine ⟨165201829271165321568824867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110134552847443547712549911 165201829271165321568824867)
    ·
      refine ⟨247802743906747982353237301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165201829271165321568824867 247802743906747982353237301)
      ·
        refine ⟨23231507241257623345615997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247802743906747982353237301 23231507241257623345615997)
        ·
          refine ⟨8711815215471608754605999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23231507241257623345615997 8711815215471608754605999)
          ·
            refine ⟨13067722823207413131908999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8711815215471608754605999 13067722823207413131908999)
            ·
              refine ⟨19601584234811119697863499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13067722823207413131908999 19601584234811119697863499)
              ·
                refine ⟨29402376352216679546795249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19601584234811119697863499 29402376352216679546795249)
                ·
                  refine ⟨22051782264162509660096437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29402376352216679546795249 22051782264162509660096437)
                  ·
                    refine ⟨2067354587265235280634041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22051782264162509660096437 2067354587265235280634041)
                    ·
                      refine ⟨1550515940448926460475531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067354587265235280634041 1550515940448926460475531)
                      ·
                        rfl

theorem cell23_3019619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_3019619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019619 prefixEnd_3019619 := by exact prefixLift 3019619
  have htrace : WordTrace (prefixWord ++ tailWord_3019619) baseStart_3019619 baseEnd_3019619 := by
    simpa [prefixWord, tailWord_3019619, baseEnd_3019619] using wordTrace_append hprefix tailTrace_3019619
  have hstable : (prefixWord ++ tailWord_3019619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019619).length < 2 ^ (prefixWord ++ tailWord_3019619).sum := by decide
  have hdescent : baseEnd_3019619 < baseStart_3019619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019625 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 4, 8]
def baseStart_3019625 : Nat := 118140960795 + 3019625 * 2 ^ 59
def prefixEnd_3019625 : Nat := 4983230072969 + 3 ^ 40 * 3019625 * 2
def baseEnd_3019625 : Nat := 516839673777617812333501

theorem tailTrace_3019625 : CollatzResearch.WordTrace tailWord_3019625 prefixEnd_3019625 516839673777617812333501 := by
  unfold tailWord_3019625
  simp only [CollatzResearch.WordTrace]
  refine ⟨110134771685421810737268329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73423181123614540491512219 110134771685421810737268329)
  ·
    refine ⟨82601078764066358052951247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110134771685421810737268329 82601078764066358052951247)
    ·
      refine ⟨123901618146099537079426871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82601078764066358052951247 123901618146099537079426871)
      ·
        refine ⟨185852427219149305619140307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123901618146099537079426871 185852427219149305619140307)
        ·
          refine ⟨278778640828723958428710461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185852427219149305619140307 278778640828723958428710461)
          ·
            refine ⟨104541990310771484410766423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278778640828723958428710461 104541990310771484410766423)
            ·
              refine ⟨156812985466157226616149635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104541990310771484410766423 156812985466157226616149635)
              ·
                refine ⟨235219478199235839924224453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156812985466157226616149635 235219478199235839924224453)
                ·
                  refine ⟨44103652162356719985792085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235219478199235839924224453 44103652162356719985792085)
                  ·
                    refine ⟨516839673777617812333501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44103652162356719985792085 516839673777617812333501)
                    ·
                      rfl

theorem cell23_3019625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_3019625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019625 prefixEnd_3019625 := by exact prefixLift 3019625
  have htrace : WordTrace (prefixWord ++ tailWord_3019625) baseStart_3019625 baseEnd_3019625 := by
    simpa [prefixWord, tailWord_3019625, baseEnd_3019625] using wordTrace_append hprefix tailTrace_3019625
  have hstable : (prefixWord ++ tailWord_3019625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019625).length < 2 ^ (prefixWord ++ tailWord_3019625).sum := by decide
  have hdescent : baseEnd_3019625 < baseStart_3019625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019632 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_3019632 : Nat := 118140960795 + 3019632 * 2 ^ 59
def prefixEnd_3019632 : Nat := 4983230072969 + 3 ^ 40 * 3019632 * 2
def baseEnd_3019632 : Nat := 1550522615697434909612971

theorem tailTrace_3019632 : CollatzResearch.WordTrace tailWord_3019632 prefixEnd_3019632 1550522615697434909612971 := by
  unfold tailWord_3019632
  simp only [CollatzResearch.WordTrace]
  refine ⟨55067513498198225466386575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73423351330930967288515433 55067513498198225466386575)
  ·
    refine ⟨82601270247297338199579863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55067513498198225466386575 82601270247297338199579863)
    ·
      refine ⟨123901905370946007299369795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82601270247297338199579863 123901905370946007299369795)
      ·
        refine ⟨185852858056419010949054693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123901905370946007299369795 185852858056419010949054693)
        ·
          refine ⟨34847410885578564552947755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185852858056419010949054693 34847410885578564552947755)
          ·
            refine ⟨52271116328367846829421633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34847410885578564552947755 52271116328367846829421633)
            ·
              refine ⟨39203337246275885122066225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52271116328367846829421633 39203337246275885122066225)
              ·
                refine ⟨29402502934706913841549669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39203337246275885122066225 29402502934706913841549669)
                ·
                  refine ⟨5512969300257546345290563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29402502934706913841549669 5512969300257546345290563)
                  ·
                    refine ⟨8269453950386319517935845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5512969300257546345290563 8269453950386319517935845)
                    ·
                      refine ⟨1550522615697434909612971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8269453950386319517935845 1550522615697434909612971)
                      ·
                        rfl

theorem cell23_3019632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_3019632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019632 prefixEnd_3019632 := by exact prefixLift 3019632
  have htrace : WordTrace (prefixWord ++ tailWord_3019632) baseStart_3019632 baseEnd_3019632 := by
    simpa [prefixWord, tailWord_3019632, baseEnd_3019632] using wordTrace_append hprefix tailTrace_3019632
  have hstable : (prefixWord ++ tailWord_3019632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019632).length < 2 ^ (prefixWord ++ tailWord_3019632).sum := by decide
  have hdescent : baseEnd_3019632 < baseStart_3019632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019646 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3019646 : Nat := 118140960795 + 3019646 * 2 ^ 59
def prefixEnd_3019646 : Nat := 4983230072969 + 3 ^ 40 * 3019646 * 2
def baseEnd_3019646 : Nat := 516843268142199284945969

theorem tailTrace_3019646 : CollatzResearch.WordTrace tailWord_3019646 prefixEnd_3019646 516843268142199284945969 := by
  unfold tailWord_3019646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13766942202293216415472849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73423691745563820882521861 13766942202293216415472849)
  ·
    refine ⟨10325206651719912311604637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13766942202293216415472849 10325206651719912311604637)
    ·
      refine ⟨3871952494394967116851739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10325206651719912311604637 3871952494394967116851739)
      ·
        refine ⟨5807928741592450675277609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3871952494394967116851739 5807928741592450675277609)
        ·
          refine ⟨4355946556194338006458207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5807928741592450675277609 4355946556194338006458207)
          ·
            refine ⟨6533919834291507009687311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355946556194338006458207 6533919834291507009687311)
            ·
              refine ⟨9800879751437260514530967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6533919834291507009687311 9800879751437260514530967)
              ·
                refine ⟨14701319627155890771796451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9800879751437260514530967 14701319627155890771796451)
                ·
                  refine ⟨22051979440733836157694677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14701319627155890771796451 22051979440733836157694677)
                  ·
                    refine ⟨516843268142199284945969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22051979440733836157694677 516843268142199284945969)
                    ·
                      rfl

theorem cell23_3019646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3019646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019646 prefixEnd_3019646 := by exact prefixLift 3019646
  have htrace : WordTrace (prefixWord ++ tailWord_3019646) baseStart_3019646 baseEnd_3019646 := by
    simpa [prefixWord, tailWord_3019646, baseEnd_3019646] using wordTrace_append hprefix tailTrace_3019646
  have hstable : (prefixWord ++ tailWord_3019646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019646).length < 2 ^ (prefixWord ++ tailWord_3019646).sum := by decide
  have hdescent : baseEnd_3019646 < baseStart_3019646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019650 : List Nat := [3, 4, 2, 2, 1, 1, 2, 3, 5]
def baseStart_3019650 : Nat := 118140960795 + 3019650 * 2 ^ 59
def prefixEnd_3019650 : Nat := 4983230072969 + 3 ^ 40 * 3019650 * 2
def baseEnd_3019650 : Nat := 172281317594357315465321

theorem tailTrace_3019650 : CollatzResearch.WordTrace tailWord_3019650 prefixEnd_3019650 172281317594357315465321 := by
  unfold tailWord_3019650
  simp only [CollatzResearch.WordTrace]
  refine ⟨27533920877582810001732101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73423789006887493337952269 27533920877582810001732101)
  ·
    refine ⟨5162610164546776875324769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27533920877582810001732101 5162610164546776875324769)
    ·
      refine ⟨3871957623410082656493577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5162610164546776875324769 3871957623410082656493577)
      ·
        refine ⟨2903968217557561992370183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3871957623410082656493577 2903968217557561992370183)
        ·
          refine ⟨4355952326336342988555275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2903968217557561992370183 4355952326336342988555275)
          ·
            refine ⟨6533928489504514482832913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355952326336342988555275 6533928489504514482832913)
            ·
              refine ⟨4900446367128385862124685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6533928489504514482832913 4900446367128385862124685)
              ·
                refine ⟨1837667387673144698296757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4900446367128385862124685 1837667387673144698296757)
                ·
                  refine ⟨172281317594357315465321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1837667387673144698296757 172281317594357315465321)
                  ·
                    rfl

theorem cell23_3019650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_3019650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019650 prefixEnd_3019650 := by exact prefixLift 3019650
  have htrace : WordTrace (prefixWord ++ tailWord_3019650) baseStart_3019650 baseEnd_3019650 := by
    simpa [prefixWord, tailWord_3019650, baseEnd_3019650] using wordTrace_append hprefix tailTrace_3019650
  have hstable : (prefixWord ++ tailWord_3019650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019650).length < 2 ^ (prefixWord ++ tailWord_3019650).sum := by decide
  have hdescent : baseEnd_3019650 < baseStart_3019650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019689 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 6]
def baseStart_3019689 : Nat := 118140960795 + 3019689 * 2 ^ 59
def prefixEnd_3019689 : Nat := 4983230072969 + 3 ^ 40 * 3019689 * 2
def baseEnd_3019689 : Nat := 172283542677193465177801

theorem tailTrace_3019689 : CollatzResearch.WordTrace tailWord_3019689 prefixEnd_3019689 172283542677193465177801 := by
  unfold tailWord_3019689
  simp only [CollatzResearch.WordTrace]
  refine ⟨110137105957189949667598121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73424737304793299778398747 110137105957189949667598121)
  ·
    refine ⟨82602829467892462250698591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110137105957189949667598121 82602829467892462250698591)
    ·
      refine ⟨123904244201838693376047887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82602829467892462250698591 123904244201838693376047887)
      ·
        refine ⟨185856366302758040064071831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123904244201838693376047887 185856366302758040064071831)
        ·
          refine ⟨278784549454137060096107747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185856366302758040064071831 278784549454137060096107747)
          ·
            refine ⟨418176824181205590144161621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278784549454137060096107747 418176824181205590144161621)
            ·
              refine ⟨2450254829186751504750947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 418176824181205590144161621 2450254829186751504750947)
              ·
                refine ⟨3675382243780127257126421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450254829186751504750947 3675382243780127257126421)
                ·
                  refine ⟨172283542677193465177801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3675382243780127257126421 172283542677193465177801)
                  ·
                    rfl

theorem cell23_3019689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 6].length) (baseStart_3019689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019689 prefixEnd_3019689 := by exact prefixLift 3019689
  have htrace : WordTrace (prefixWord ++ tailWord_3019689) baseStart_3019689 baseEnd_3019689 := by
    simpa [prefixWord, tailWord_3019689, baseEnd_3019689] using wordTrace_append hprefix tailTrace_3019689
  have hstable : (prefixWord ++ tailWord_3019689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019689).length < 2 ^ (prefixWord ++ tailWord_3019689).sum := by decide
  have hdescent : baseEnd_3019689 < baseStart_3019689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019699 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 3]
def baseStart_3019699 : Nat := 118140960795 + 3019699 * 2 ^ 59
def prefixEnd_3019699 : Nat := 4983230072969 + 3 ^ 40 * 3019699 * 2
def baseEnd_3019699 : Nat := 1550557018901286147475163

theorem tailTrace_3019699 : CollatzResearch.WordTrace tailWord_3019699 prefixEnd_3019699 1550557018901286147475163 := by
  unfold tailWord_3019699
  simp only [CollatzResearch.WordTrace]
  refine ⟨110137470687153721375462151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73424980458102480916974767 110137470687153721375462151)
  ·
    refine ⟨165206206030730582063193227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110137470687153721375462151 165206206030730582063193227)
    ·
      refine ⟨247809309046095873094789841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165206206030730582063193227 247809309046095873094789841)
      ·
        refine ⟨185856981784571904821092381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247809309046095873094789841 185856981784571904821092381)
        ·
          refine ⟨69696368169214464307909643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185856981784571904821092381 69696368169214464307909643)
          ·
            refine ⟨104544552253821696461864465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69696368169214464307909643 104544552253821696461864465)
            ·
              refine ⟨78408414190366272346398349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104544552253821696461864465 78408414190366272346398349)
              ·
                refine ⟨29403155321387352129899381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78408414190366272346398349 29403155321387352129899381)
                ·
                  refine ⟨2756545811380064262178067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29403155321387352129899381 2756545811380064262178067)
                  ·
                    refine ⟨4134818717070096393267101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2756545811380064262178067 4134818717070096393267101)
                    ·
                      refine ⟨1550557018901286147475163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4134818717070096393267101 1550557018901286147475163)
                      ·
                        rfl

theorem cell23_3019699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 3].length) (baseStart_3019699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019699 prefixEnd_3019699 := by exact prefixLift 3019699
  have htrace : WordTrace (prefixWord ++ tailWord_3019699) baseStart_3019699 baseEnd_3019699 := by
    simpa [prefixWord, tailWord_3019699, baseEnd_3019699] using wordTrace_append hprefix tailTrace_3019699
  have hstable : (prefixWord ++ tailWord_3019699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019699).length < 2 ^ (prefixWord ++ tailWord_3019699).sum := by decide
  have hdescent : baseEnd_3019699 < baseStart_3019699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019719 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 1, 5]
def baseStart_3019719 : Nat := 118140960795 + 3019719 * 2 ^ 59
def prefixEnd_3019719 : Nat := 4983230072969 + 3 ^ 40 * 3019719 * 2
def baseEnd_3019719 : Nat := 516855762838125356408357

theorem tailTrace_3019719 : CollatzResearch.WordTrace tailWord_3019719 prefixEnd_3019719 516855762838125356408357 := by
  unfold tailWord_3019719
  simp only [CollatzResearch.WordTrace]
  refine ⟨110138200147081264791190211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73425466764720843194126807 110138200147081264791190211)
  ·
    refine ⟨165207300220621897186785317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110138200147081264791190211 165207300220621897186785317)
    ·
      refine ⟨30976368791366605722522247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165207300220621897186785317 30976368791366605722522247)
      ·
        refine ⟨46464553187049908583783371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30976368791366605722522247 46464553187049908583783371)
        ·
          refine ⟨69696829780574862875675057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46464553187049908583783371 69696829780574862875675057)
          ·
            refine ⟨52272622335431147156756293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69696829780574862875675057 52272622335431147156756293)
            ·
              refine ⟨9801116687893340091891805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52272622335431147156756293 9801116687893340091891805)
              ·
                refine ⟨3675418757960002534459427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9801116687893340091891805 3675418757960002534459427)
                ·
                  refine ⟨5513128136940003801689141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675418757960002534459427 5513128136940003801689141)
                  ·
                    refine ⟨516855762838125356408357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5513128136940003801689141 516855762838125356408357)
                    ·
                      rfl

theorem cell23_3019719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_3019719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019719 prefixEnd_3019719 := by exact prefixLift 3019719
  have htrace : WordTrace (prefixWord ++ tailWord_3019719) baseStart_3019719 baseEnd_3019719 := by
    simpa [prefixWord, tailWord_3019719, baseEnd_3019719] using wordTrace_append hprefix tailTrace_3019719
  have hstable : (prefixWord ++ tailWord_3019719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019719).length < 2 ^ (prefixWord ++ tailWord_3019719).sum := by decide
  have hdescent : baseEnd_3019719 < baseStart_3019719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019726 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_3019726 : Nat := 118140960795 + 3019726 * 2 ^ 59
def prefixEnd_3019726 : Nat := 4983230072969 + 3 ^ 40 * 3019726 * 2
def baseEnd_3019726 : Nat := 1550570882878957541837539

theorem tailTrace_3019726 : CollatzResearch.WordTrace tailWord_3019726 prefixEnd_3019726 1550570882878957541837539 := by
  unfold tailWord_3019726
  simp only [CollatzResearch.WordTrace]
  refine ⟨13767306932256988123336879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73425636972037269991130021 13767306932256988123336879)
  ·
    refine ⟨20650960398385482185005319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13767306932256988123336879 20650960398385482185005319)
    ·
      refine ⟨30976440597578223277507979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20650960398385482185005319 30976440597578223277507979)
      ·
        refine ⟨46464660896367334916261969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30976440597578223277507979 46464660896367334916261969)
        ·
          refine ⟨34848495672275501187196477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46464660896367334916261969 34848495672275501187196477)
          ·
            refine ⟨13068185877103312945198679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34848495672275501187196477 13068185877103312945198679)
            ·
              refine ⟨19602278815654969417798019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13068185877103312945198679 19602278815654969417798019)
              ·
                refine ⟨29403418223482454126697029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19602278815654969417798019 29403418223482454126697029)
                ·
                  refine ⟨5513140916902960148755693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29403418223482454126697029 5513140916902960148755693)
                  ·
                    refine ⟨2067427843838610055783385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5513140916902960148755693 2067427843838610055783385)
                    ·
                      refine ⟨1550570882878957541837539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067427843838610055783385 1550570882878957541837539)
                      ·
                        rfl

theorem cell23_3019726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_3019726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019726 prefixEnd_3019726 := by exact prefixLift 3019726
  have htrace : WordTrace (prefixWord ++ tailWord_3019726) baseStart_3019726 baseEnd_3019726 := by
    simpa [prefixWord, tailWord_3019726, baseEnd_3019726] using wordTrace_append hprefix tailTrace_3019726
  have hstable : (prefixWord ++ tailWord_3019726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019726).length < 2 ^ (prefixWord ++ tailWord_3019726).sum := by decide
  have hdescent : baseEnd_3019726 < baseStart_3019726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019766 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_3019766 : Nat := 118140960795 + 3019766 * 2 ^ 59
def prefixEnd_3019766 : Nat := 4983230072969 + 3 ^ 40 * 3019766 * 2
def baseEnd_3019766 : Nat := 516863807368379128445785

theorem tailTrace_3019766 : CollatzResearch.WordTrace tailWord_3019766 prefixEnd_3019766 516863807368379128445785 := by
  unfold tailWord_3019766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6883744648619436988634447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73426609585273994545434101 6883744648619436988634447)
  ·
    refine ⟨10325616972929155482951671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6883744648619436988634447 10325616972929155482951671)
    ·
      refine ⟨15488425459393733224427507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10325616972929155482951671 15488425459393733224427507)
      ·
        refine ⟨23232638189090599836641261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15488425459393733224427507 23232638189090599836641261)
        ·
          refine ⟨8712239320908974938740473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23232638189090599836641261 8712239320908974938740473)
          ·
            refine ⟨6534179490681731204055355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8712239320908974938740473 6534179490681731204055355)
            ·
              refine ⟨9801269236022596806083033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6534179490681731204055355 9801269236022596806083033)
              ·
                refine ⟨7350951927016947604562275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9801269236022596806083033 7350951927016947604562275)
                ·
                  refine ⟨11026427890525421406843413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7350951927016947604562275 11026427890525421406843413)
                  ·
                    refine ⟨516863807368379128445785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11026427890525421406843413 516863807368379128445785)
                    ·
                      rfl

theorem cell23_3019766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_3019766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019766 prefixEnd_3019766 := by exact prefixLift 3019766
  have htrace : WordTrace (prefixWord ++ tailWord_3019766) baseStart_3019766 baseEnd_3019766 := by
    simpa [prefixWord, tailWord_3019766, baseEnd_3019766] using wordTrace_append hprefix tailTrace_3019766
  have hstable : (prefixWord ++ tailWord_3019766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019766).length < 2 ^ (prefixWord ++ tailWord_3019766).sum := by decide
  have hdescent : baseEnd_3019766 < baseStart_3019766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019769 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_3019769 : Nat := 118140960795 + 3019769 * 2 ^ 59
def prefixEnd_3019769 : Nat := 4983230072969 + 3 ^ 40 * 3019769 * 2
def baseEnd_3019769 : Nat := 1550592962547100873599841

theorem tailTrace_3019769 : CollatzResearch.WordTrace tailWord_3019769 prefixEnd_3019769 1550592962547100873599841 := by
  unfold tailWord_3019769
  simp only [CollatzResearch.WordTrace]
  refine ⟨110140023796900123330510361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73426682531266748887006907 110140023796900123330510361)
  ·
    refine ⟨82605017847675092497882771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110140023796900123330510361 82605017847675092497882771)
    ·
      refine ⟨123907526771512638746824157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82605017847675092497882771 123907526771512638746824157)
      ·
        refine ⟨46465322539317239530059059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123907526771512638746824157 46465322539317239530059059)
        ·
          refine ⟨69697983808975859295088589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46465322539317239530059059 69697983808975859295088589)
          ·
            refine ⟨26136743928365947235658221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69697983808975859295088589 26136743928365947235658221)
            ·
              refine ⟨9801278973137230213371833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26136743928365947235658221 9801278973137230213371833)
              ·
                refine ⟨7350959229852922660028875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9801278973137230213371833 7350959229852922660028875)
                ·
                  refine ⟨11026438844779383990043313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7350959229852922660028875 11026438844779383990043313)
                  ·
                    refine ⟨8269829133584537992532485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11026438844779383990043313 8269829133584537992532485)
                    ·
                      refine ⟨1550592962547100873599841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8269829133584537992532485 1550592962547100873599841)
                      ·
                        rfl

theorem cell23_3019769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_3019769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019769 prefixEnd_3019769 := by exact prefixLift 3019769
  have htrace : WordTrace (prefixWord ++ tailWord_3019769) baseStart_3019769 baseEnd_3019769 := by
    simpa [prefixWord, tailWord_3019769, baseEnd_3019769] using wordTrace_append hprefix tailTrace_3019769
  have hstable : (prefixWord ++ tailWord_3019769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019769).length < 2 ^ (prefixWord ++ tailWord_3019769).sum := by decide
  have hdescent : baseEnd_3019769 < baseStart_3019769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019849 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 3]
def baseStart_3019849 : Nat := 118140960795 + 3019849 * 2 ^ 59
def prefixEnd_3019849 : Nat := 4983230072969 + 3 ^ 40 * 3019849 * 2
def baseEnd_3019849 : Nat := 1550634040999460560599473

theorem tailTrace_3019849 : CollatzResearch.WordTrace tailWord_3019849 prefixEnd_3019849 1550634040999460560599473 := by
  unfold tailWord_3019849
  simp only [CollatzResearch.WordTrace]
  refine ⟨110142941636610296993422601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73428627757740197995615067 110142941636610296993422601)
  ·
    refine ⟨82607206227457722745066951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110142941636610296993422601 82607206227457722745066951)
    ·
      refine ⟨123910809341186584117600427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82607206227457722745066951 123910809341186584117600427)
      ·
        refine ⟨185866214011779876176400641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123910809341186584117600427 185866214011779876176400641)
        ·
          refine ⟨139399660508834907132300481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185866214011779876176400641 139399660508834907132300481)
          ·
            refine ⟨104549745381626180349225361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139399660508834907132300481 104549745381626180349225361)
            ·
              refine ⟨78412309036219635261919021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104549745381626180349225361 78412309036219635261919021)
              ·
                refine ⟨29404615888582363223219633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78412309036219635261919021 29404615888582363223219633)
                ·
                  refine ⟨22053461916436772417414725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29404615888582363223219633 22053461916436772417414725)
                  ·
                    refine ⟨4135024109331894828265261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22053461916436772417414725 4135024109331894828265261)
                    ·
                      refine ⟨1550634040999460560599473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4135024109331894828265261 1550634040999460560599473)
                      ·
                        rfl

theorem cell23_3019849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_3019849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019849 prefixEnd_3019849 := by exact prefixLift 3019849
  have htrace : WordTrace (prefixWord ++ tailWord_3019849) baseStart_3019849 baseEnd_3019849 := by
    simpa [prefixWord, tailWord_3019849, baseEnd_3019849] using wordTrace_append hprefix tailTrace_3019849
  have hstable : (prefixWord ++ tailWord_3019849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019849).length < 2 ^ (prefixWord ++ tailWord_3019849).sum := by decide
  have hdescent : baseEnd_3019849 < baseStart_3019849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019953 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3019953 : Nat := 118140960795 + 3019953 * 2 ^ 59
def prefixEnd_3019953 : Nat := 4983230072969 + 3 ^ 40 * 3019953 * 2
def baseEnd_3019953 : Nat := 1550687442987528153698995

theorem tailTrace_3019953 : CollatzResearch.WordTrace tailWord_3019953 prefixEnd_3019953 1550687442987528153698995 := by
  unfold tailWord_3019953
  simp only [CollatzResearch.WordTrace]
  refine ⟨110146734828233522755208513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73431156552155681836805675 110146734828233522755208513)
  ·
    refine ⟨82610051121175142066406385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110146734828233522755208513 82610051121175142066406385)
    ·
      refine ⟨61957538340881356549804789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82610051121175142066406385 61957538340881356549804789)
      ·
        refine ⟨5808519219457627176544199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61957538340881356549804789 5808519219457627176544199)
        ·
          refine ⟨8712778829186440764816299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5808519219457627176544199 8712778829186440764816299)
          ·
            refine ⟨13069168243779661147224449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8712778829186440764816299 13069168243779661147224449)
            ·
              refine ⟨9801876182834745860418337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13069168243779661147224449 9801876182834745860418337)
              ·
                refine ⟨7351407137126059395313753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9801876182834745860418337 7351407137126059395313753)
                ·
                  refine ⟨5513555352844544546485315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7351407137126059395313753 5513555352844544546485315)
                  ·
                    refine ⟨8270333029266816819727973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5513555352844544546485315 8270333029266816819727973)
                    ·
                      refine ⟨1550687442987528153698995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8270333029266816819727973 1550687442987528153698995)
                      ·
                        rfl

theorem cell23_3019953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3019953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019953 prefixEnd_3019953 := by exact prefixLift 3019953
  have htrace : WordTrace (prefixWord ++ tailWord_3019953) baseStart_3019953 baseEnd_3019953 := by
    simpa [prefixWord, tailWord_3019953, baseEnd_3019953] using wordTrace_append hprefix tailTrace_3019953
  have hstable : (prefixWord ++ tailWord_3019953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019953).length < 2 ^ (prefixWord ++ tailWord_3019953).sum := by decide
  have hdescent : baseEnd_3019953 < baseStart_3019953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019976 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 6]
def baseStart_3019976 : Nat := 118140960795 + 3019976 * 2 ^ 59
def prefixEnd_3019976 : Nat := 4983230072969 + 3 ^ 40 * 3019976 * 2
def baseEnd_3019976 : Nat := 172299917004731284856821

theorem tailTrace_3019976 : CollatzResearch.WordTrace tailWord_3019976 prefixEnd_3019976 172299917004731284856821 := by
  unfold tailWord_3019976
  simp only [CollatzResearch.WordTrace]
  refine ⟨55073786853575098841647891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73431715804766798455530521 55073786853575098841647891)
  ·
    refine ⟨82610680280362648262471837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55073786853575098841647891 82610680280362648262471837)
    ·
      refine ⟨30979005105135993098426939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82610680280362648262471837 30979005105135993098426939)
      ·
        refine ⟨46468507657703989647640409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30979005105135993098426939 46468507657703989647640409)
        ·
          refine ⟨34851380743277992235730307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46468507657703989647640409 34851380743277992235730307)
          ·
            refine ⟨52277071114916988353595461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34851380743277992235730307 52277071114916988353595461)
            ·
              refine ⟨9801950834046935316299149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52277071114916988353595461 9801950834046935316299149)
              ·
                refine ⟨3675731562767600743612181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9801950834046935316299149 3675731562767600743612181)
                ·
                  refine ⟨172299917004731284856821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3675731562767600743612181 172299917004731284856821)
                  ·
                    rfl

theorem cell23_3019976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 6].length) (baseStart_3019976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019976 prefixEnd_3019976 := by exact prefixLift 3019976
  have htrace : WordTrace (prefixWord ++ tailWord_3019976) baseStart_3019976 baseEnd_3019976 := by
    simpa [prefixWord, tailWord_3019976, baseEnd_3019976] using wordTrace_append hprefix tailTrace_3019976
  have hstable : (prefixWord ++ tailWord_3019976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019976).length < 2 ^ (prefixWord ++ tailWord_3019976).sum := by decide
  have hdescent : baseEnd_3019976 < baseStart_3019976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3019979 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 6]
def baseStart_3019979 : Nat := 118140960795 + 3019979 * 2 ^ 59
def prefixEnd_3019979 : Nat := 4983230072969 + 3 ^ 40 * 3019979 * 2
def baseEnd_3019979 : Nat := 1550700793484545051973875

theorem tailTrace_3019979 : CollatzResearch.WordTrace tailWord_3019979 prefixEnd_3019979 1550700793484545051973875 := by
  unfold tailWord_3019979
  simp only [CollatzResearch.WordTrace]
  refine ⟨110147683126139329195654991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73431788750759552797103327 110147683126139329195654991)
  ·
    refine ⟨165221524689208993793482487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110147683126139329195654991 165221524689208993793482487)
    ·
      refine ⟨247832287033813490690223731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165221524689208993793482487 247832287033813490690223731)
      ·
        refine ⟨371748430550720236035335597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247832287033813490690223731 371748430550720236035335597)
        ·
          refine ⟨139405661456520088513250849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371748430550720236035335597 139405661456520088513250849)
          ·
            refine ⟨104554246092390066384938137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139405661456520088513250849 104554246092390066384938137)
            ·
              refine ⟨78415684569292549788703603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104554246092390066384938137 78415684569292549788703603)
              ·
                refine ⟨117623526853938824683055405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78415684569292549788703603 117623526853938824683055405)
                ·
                  refine ⟨44108822570227059256145777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117623526853938824683055405 44108822570227059256145777)
                  ·
                    refine ⟨33081616927670294442109333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44108822570227059256145777 33081616927670294442109333)
                    ·
                      refine ⟨1550700793484545051973875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33081616927670294442109333 1550700793484545051973875)
                      ·
                        rfl

theorem cell23_3019979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_3019979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3019979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3019979 prefixEnd_3019979 := by exact prefixLift 3019979
  have htrace : WordTrace (prefixWord ++ tailWord_3019979) baseStart_3019979 baseEnd_3019979 := by
    simpa [prefixWord, tailWord_3019979, baseEnd_3019979] using wordTrace_append hprefix tailTrace_3019979
  have hstable : (prefixWord ++ tailWord_3019979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3019979).length < 2 ^ (prefixWord ++ tailWord_3019979).sum := by decide
  have hdescent : baseEnd_3019979 < baseStart_3019979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3019979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020030 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_3020030 : Nat := 118140960795 + 3020030 * 2 ^ 59
def prefixEnd_3020030 : Nat := 4983230072969 + 3 ^ 40 * 3020030 * 2
def baseEnd_3020030 : Nat := 1550726980997924352436141

theorem tailTrace_3020030 : CollatzResearch.WordTrace tailWord_3020030 prefixEnd_3020030 1550726980997924352436141 := by
  unfold tailWord_3020030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13768692906119320613220193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73433028832636376603841029 13768692906119320613220193)
  ·
    refine ⟨10326519679589490459915145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13768692906119320613220193 10326519679589490459915145)
    ·
      refine ⟨7744889759692117844936359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10326519679589490459915145 7744889759692117844936359)
      ·
        refine ⟨11617334639538176767404539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7744889759692117844936359 11617334639538176767404539)
        ·
          refine ⟨17426001959307265151106809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11617334639538176767404539 17426001959307265151106809)
          ·
            refine ⟨13069501469480448863330107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17426001959307265151106809 13069501469480448863330107)
            ·
              refine ⟨19604252204220673294995161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13069501469480448863330107 19604252204220673294995161)
              ·
                refine ⟨14703189153165504971246371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19604252204220673294995161 14703189153165504971246371)
                ·
                  refine ⟨22054783729748257456869557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14703189153165504971246371 22054783729748257456869557)
                  ·
                    refine ⟨2067635974663899136581521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22054783729748257456869557 2067635974663899136581521)
                    ·
                      refine ⟨1550726980997924352436141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067635974663899136581521 1550726980997924352436141)
                      ·
                        rfl

theorem cell23_3020030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_3020030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020030 prefixEnd_3020030 := by exact prefixLift 3020030
  have htrace : WordTrace (prefixWord ++ tailWord_3020030) baseStart_3020030 baseEnd_3020030 := by
    simpa [prefixWord, tailWord_3020030, baseEnd_3020030] using wordTrace_append hprefix tailTrace_3020030
  have hstable : (prefixWord ++ tailWord_3020030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020030).length < 2 ^ (prefixWord ++ tailWord_3020030).sum := by decide
  have hdescent : baseEnd_3020030 < baseStart_3020030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020040 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 1, 5]
def baseStart_3020040 : Nat := 118140960795 + 3020040 * 2 ^ 59
def prefixEnd_3020040 : Nat := 4983230072969 + 3 ^ 40 * 3020040 * 2
def baseEnd_3020040 : Nat := 516910705268156437770365

theorem tailTrace_3020040 : CollatzResearch.WordTrace tailWord_3020040 prefixEnd_3020040 516910705268156437770365 := by
  unfold tailWord_3020040
  simp only [CollatzResearch.WordTrace]
  refine ⟨55074953989459168306812787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73433271985945557742417049 55074953989459168306812787)
  ·
    refine ⟨82612430984188752460219181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55074953989459168306812787 82612430984188752460219181)
    ·
      refine ⟨30979661619070782172582193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82612430984188752460219181 30979661619070782172582193)
      ·
        refine ⟨23234746214303086629436645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30979661619070782172582193 23234746214303086629436645)
        ·
          refine ⟨4356514915181828743019371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23234746214303086629436645 4356514915181828743019371)
          ·
            refine ⟨6534772372772743114529057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356514915181828743019371 6534772372772743114529057)
            ·
              refine ⟨4901079279579557335896793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6534772372772743114529057 4901079279579557335896793)
              ·
                refine ⟨3675809459684668001922595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901079279579557335896793 3675809459684668001922595)
                ·
                  refine ⟨5513714189527002002883893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675809459684668001922595 5513714189527002002883893)
                  ·
                    refine ⟨516910705268156437770365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5513714189527002002883893 516910705268156437770365)
                    ·
                      rfl

theorem cell23_3020040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_3020040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020040 prefixEnd_3020040 := by exact prefixLift 3020040
  have htrace : WordTrace (prefixWord ++ tailWord_3020040) baseStart_3020040 baseEnd_3020040 := by
    simpa [prefixWord, tailWord_3020040, baseEnd_3020040] using wordTrace_append hprefix tailTrace_3020040
  have hstable : (prefixWord ++ tailWord_3020040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020040).length < 2 ^ (prefixWord ++ tailWord_3020040).sum := by decide
  have hdescent : baseEnd_3020040 < baseStart_3020040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020043 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 4]
def baseStart_3020043 : Nat := 118140960795 + 3020043 * 2 ^ 59
def prefixEnd_3020043 : Nat := 4983230072969 + 3 ^ 40 * 3020043 * 2
def baseEnd_3020043 : Nat := 1550733656246432801573581

theorem tailTrace_3020043 : CollatzResearch.WordTrace tailWord_3020043 prefixEnd_3020043 1550733656246432801573581 := by
  unfold tailWord_3020043
  simp only [CollatzResearch.WordTrace]
  refine ⟨110150017397907468125984783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73433344931938312083989855 110150017397907468125984783)
  ·
    refine ⟨165225026096861202188977175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110150017397907468125984783 165225026096861202188977175)
    ·
      refine ⟨247837539145291803283465763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165225026096861202188977175 247837539145291803283465763)
      ·
        refine ⟨371756308717937704925198645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247837539145291803283465763 371756308717937704925198645)
        ·
          refine ⟨34852153942306659836737373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 371756308717937704925198645 34852153942306659836737373)
          ·
            refine ⟨13069557728364997438776515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34852153942306659836737373 13069557728364997438776515)
            ·
              refine ⟨19604336592547496158164773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13069557728364997438776515 19604336592547496158164773)
              ·
                refine ⟨3675813111102655529655895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19604336592547496158164773 3675813111102655529655895)
                ·
                  refine ⟨5513719666653983294483843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675813111102655529655895 5513719666653983294483843)
                  ·
                    refine ⟨8270579499980974941725765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5513719666653983294483843 8270579499980974941725765)
                    ·
                      refine ⟨1550733656246432801573581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8270579499980974941725765 1550733656246432801573581)
                      ·
                        rfl

theorem cell23_3020043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 4].length) (baseStart_3020043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020043 prefixEnd_3020043 := by exact prefixLift 3020043
  have htrace : WordTrace (prefixWord ++ tailWord_3020043) baseStart_3020043 baseEnd_3020043 := by
    simpa [prefixWord, tailWord_3020043, baseEnd_3020043] using wordTrace_append hprefix tailTrace_3020043
  have hstable : (prefixWord ++ tailWord_3020043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020043).length < 2 ^ (prefixWord ++ tailWord_3020043).sum := by decide
  have hdescent : baseEnd_3020043 < baseStart_3020043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020060 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_3020060 : Nat := 118140960795 + 3020060 * 2 ^ 59
def prefixEnd_3020060 : Nat := 4983230072969 + 3 ^ 40 * 3020060 * 2
def baseEnd_3020060 : Nat := 1550742385417559235061003

theorem tailTrace_3020060 : CollatzResearch.WordTrace tailWord_3020060 prefixEnd_3020060 1550742385417559235061003 := by
  unfold tailWord_3020060
  simp only [CollatzResearch.WordTrace]
  refine ⟨55075318719422940014676817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73433758292563920019569089 55075318719422940014676817)
  ·
    refine ⟨41306489039567205011007613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55075318719422940014676817 41306489039567205011007613)
    ·
      refine ⟨15489933389837701879127855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41306489039567205011007613 15489933389837701879127855)
      ·
        refine ⟨23234900084756552818691783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15489933389837701879127855 23234900084756552818691783)
        ·
          refine ⟨34852350127134829228037675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23234900084756552818691783 34852350127134829228037675)
          ·
            refine ⟨52278525190702243842056513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34852350127134829228037675 52278525190702243842056513)
            ·
              refine ⟨39208893893026682881542385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52278525190702243842056513 39208893893026682881542385)
              ·
                refine ⟨29406670419770012161156789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39208893893026682881542385 29406670419770012161156789)
                ·
                  refine ⟨2756875351853438640108449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29406670419770012161156789 2756875351853438640108449)
                  ·
                    refine ⟨2067656513890078980081337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2756875351853438640108449 2067656513890078980081337)
                    ·
                      refine ⟨1550742385417559235061003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067656513890078980081337 1550742385417559235061003)
                      ·
                        rfl

theorem cell23_3020060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_3020060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020060 prefixEnd_3020060 := by exact prefixLift 3020060
  have htrace : WordTrace (prefixWord ++ tailWord_3020060) baseStart_3020060 baseEnd_3020060 := by
    simpa [prefixWord, tailWord_3020060, baseEnd_3020060] using wordTrace_append hprefix tailTrace_3020060
  have hstable : (prefixWord ++ tailWord_3020060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020060).length < 2 ^ (prefixWord ++ tailWord_3020060).sum := by decide
  have hdescent : baseEnd_3020060 < baseStart_3020060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020097 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3020097 : Nat := 118140960795 + 3020097 * 2 ^ 59
def prefixEnd_3020097 : Nat := 4983230072969 + 3 ^ 40 * 3020097 * 2
def baseEnd_3020097 : Nat := 1550761384201775590298333

theorem tailTrace_3020097 : CollatzResearch.WordTrace tailWord_3020097 prefixEnd_3020097 1550761384201775590298333 := by
  unfold tailWord_3020097
  simp only [CollatzResearch.WordTrace]
  refine ⟨110151986939711835348450545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73434657959807890232300363 110151986939711835348450545)
  ·
    refine ⟨82613990204783876511337909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110151986939711835348450545 82613990204783876511337909)
    ·
      refine ⟨7745061581698488422937929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82613990204783876511337909 7745061581698488422937929)
      ·
        refine ⟨5808796186273866317203447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7745061581698488422937929 5808796186273866317203447)
        ·
          refine ⟨8713194279410799475805171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5808796186273866317203447 8713194279410799475805171)
          ·
            refine ⟨13069791419116199213707757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8713194279410799475805171 13069791419116199213707757)
            ·
              refine ⟨4901171782168574705140409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13069791419116199213707757 4901171782168574705140409)
              ·
                refine ⟨3675878836626431028855307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901171782168574705140409 3675878836626431028855307)
                ·
                  refine ⟨5513818254939646543282961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675878836626431028855307 5513818254939646543282961)
                  ·
                    refine ⟨4135363691204734907462221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5513818254939646543282961 4135363691204734907462221)
                    ·
                      refine ⟨1550761384201775590298333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4135363691204734907462221 1550761384201775590298333)
                      ·
                        rfl

theorem cell23_3020097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3020097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020097 prefixEnd_3020097 := by exact prefixLift 3020097
  have htrace : WordTrace (prefixWord ++ tailWord_3020097) baseStart_3020097 baseEnd_3020097 := by
    simpa [prefixWord, tailWord_3020097, baseEnd_3020097] using wordTrace_append hprefix tailTrace_3020097
  have hstable : (prefixWord ++ tailWord_3020097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020097).length < 2 ^ (prefixWord ++ tailWord_3020097).sum := by decide
  have hdescent : baseEnd_3020097 < baseStart_3020097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020106 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_3020106 : Nat := 118140960795 + 3020106 * 2 ^ 59
def prefixEnd_3020106 : Nat := 4983230072969 + 3 ^ 40 * 3020106 * 2
def baseEnd_3020106 : Nat := 1550766005527666055085791

theorem tailTrace_3020106 : CollatzResearch.WordTrace tailWord_3020106 prefixEnd_3020106 1550766005527666055085791 := by
  unfold tailWord_3020106
  simp only [CollatzResearch.WordTrace]
  refine ⟨27538078799169807471382043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73434876797786153257018781 27538078799169807471382043)
  ·
    refine ⟨41307118198754711207073065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27538078799169807471382043 41307118198754711207073065)
    ·
      refine ⟨30980338649066033405304799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41307118198754711207073065 30980338649066033405304799)
      ·
        refine ⟨46470507973599050107957199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30980338649066033405304799 46470507973599050107957199)
        ·
          refine ⟨69705761960398575161935799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46470507973599050107957199 69705761960398575161935799)
          ·
            refine ⟨104558642940597862742903699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69705761960398575161935799 104558642940597862742903699)
            ·
              refine ⟨156837964410896794114355549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104558642940597862742903699 156837964410896794114355549)
              ·
                refine ⟨58814236654086297792883331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156837964410896794114355549 58814236654086297792883331)
                ·
                  refine ⟨88221354981129446689324997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58814236654086297792883331 88221354981129446689324997)
                  ·
                    refine ⟨16541504058961771254248437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88221354981129446689324997 16541504058961771254248437)
                    ·
                      refine ⟨1550766005527666055085791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16541504058961771254248437 1550766005527666055085791)
                      ·
                        rfl

theorem cell23_3020106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_3020106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020106 prefixEnd_3020106 := by exact prefixLift 3020106
  have htrace : WordTrace (prefixWord ++ tailWord_3020106) baseStart_3020106 baseEnd_3020106 := by
    simpa [prefixWord, tailWord_3020106, baseEnd_3020106] using wordTrace_append hprefix tailTrace_3020106
  have hstable : (prefixWord ++ tailWord_3020106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020106).length < 2 ^ (prefixWord ++ tailWord_3020106).sum := by decide
  have hdescent : baseEnd_3020106 < baseStart_3020106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020176 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_3020176 : Nat := 118140960795 + 3020176 * 2 ^ 59
def prefixEnd_3020176 : Nat := 4983230072969 + 3 ^ 40 * 3020176 * 2
def baseEnd_3020176 : Nat := 1550801949173480781210469

theorem tailTrace_3020176 : CollatzResearch.WordTrace tailWord_3020176 prefixEnd_3020176 1550801949173480781210469 := by
  unfold tailWord_3020176
  simp only [CollatzResearch.WordTrace]
  refine ⟨55077434153212815920288191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73436578870950421227050921 55077434153212815920288191)
  ·
    refine ⟨82616151229819223880432287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55077434153212815920288191 82616151229819223880432287)
    ·
      refine ⟨123924226844728835820648431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82616151229819223880432287 123924226844728835820648431)
      ·
        refine ⟨185886340267093253730972647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123924226844728835820648431 185886340267093253730972647)
        ·
          refine ⟨278829510400639880596458971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185886340267093253730972647 278829510400639880596458971)
          ·
            refine ⟨418244265600959820894688457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278829510400639880596458971 418244265600959820894688457)
            ·
              refine ⟨313683199200719865671016343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418244265600959820894688457 313683199200719865671016343)
              ·
                refine ⟨470524798801079798506524515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313683199200719865671016343 470524798801079798506524515)
                ·
                  refine ⟨705787198201619697759786773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470524798801079798506524515 705787198201619697759786773)
                  ·
                    refine ⟨33083774915700923332490005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 705787198201619697759786773 33083774915700923332490005)
                    ·
                      refine ⟨1550801949173480781210469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33083774915700923332490005 1550801949173480781210469)
                      ·
                        rfl

theorem cell23_3020176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_3020176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020176 prefixEnd_3020176 := by exact prefixLift 3020176
  have htrace : WordTrace (prefixWord ++ tailWord_3020176) baseStart_3020176 baseEnd_3020176 := by
    simpa [prefixWord, tailWord_3020176, baseEnd_3020176] using wordTrace_append hprefix tailTrace_3020176
  have hstable : (prefixWord ++ tailWord_3020176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020176).length < 2 ^ (prefixWord ++ tailWord_3020176).sum := by decide
  have hdescent : baseEnd_3020176 < baseStart_3020176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020178 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3020178 : Nat := 118140960795 + 3020178 * 2 ^ 59
def prefixEnd_3020178 : Nat := 4983230072969 + 3 ^ 40 * 3020178 * 2
def baseEnd_3020178 : Nat := 1550802976134789773385461

theorem tailTrace_3020178 : CollatzResearch.WordTrace tailWord_3020178 prefixEnd_3020178 1550802976134789773385461 := by
  unfold tailWord_3020178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27538735313104596545537297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73436627501612257454766125 27538735313104596545537297)
  ·
    refine ⟨20654051484828447409152973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27538735313104596545537297 20654051484828447409152973)
    ·
      refine ⟨7745269306810667778432365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20654051484828447409152973 7745269306810667778432365)
      ·
        refine ⟨2904475990054000416912137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7745269306810667778432365 2904475990054000416912137)
        ·
          refine ⟨2178356992540500312684103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2904475990054000416912137 2178356992540500312684103)
          ·
            refine ⟨3267535488810750469026155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178356992540500312684103 3267535488810750469026155)
            ·
              refine ⟨4901303233216125703539233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3267535488810750469026155 4901303233216125703539233)
              ·
                refine ⟨3675977424912094277654425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901303233216125703539233 3675977424912094277654425)
                ·
                  refine ⟨2756983068684070708240819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3675977424912094277654425 2756983068684070708240819)
                  ·
                    refine ⟨4135474603026106062361229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2756983068684070708240819 4135474603026106062361229)
                    ·
                      refine ⟨1550802976134789773385461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4135474603026106062361229 1550802976134789773385461)
                      ·
                        rfl

theorem cell23_3020178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3020178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020178 prefixEnd_3020178 := by exact prefixLift 3020178
  have htrace : WordTrace (prefixWord ++ tailWord_3020178) baseStart_3020178 baseEnd_3020178 := by
    simpa [prefixWord, tailWord_3020178, baseEnd_3020178] using wordTrace_append hprefix tailTrace_3020178
  have hstable : (prefixWord ++ tailWord_3020178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020178).length < 2 ^ (prefixWord ++ tailWord_3020178).sum := by decide
  have hdescent : baseEnd_3020178 < baseStart_3020178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020180 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3020180 : Nat := 118140960795 + 3020180 * 2 ^ 59
def prefixEnd_3020180 : Nat := 4983230072969 + 3 ^ 40 * 3020180 * 2
def baseEnd_3020180 : Nat := 1550804003096098765560451

theorem tailTrace_3020180 : CollatzResearch.WordTrace tailWord_3020180 prefixEnd_3020180 1550804003096098765560451 := by
  unfold tailWord_3020180
  simp only [CollatzResearch.WordTrace]
  refine ⟨55077507099205570261860997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73436676132274093682481329 55077507099205570261860997)
  ·
    refine ⟨10327032581101044424098937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55077507099205570261860997 10327032581101044424098937)
    ·
      refine ⟨7745274435825783318074203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10327032581101044424098937 7745274435825783318074203)
      ·
        refine ⟨11617911653738674977111305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7745274435825783318074203 11617911653738674977111305)
        ·
          refine ⟨8713433740304006232833479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11617911653738674977111305 8713433740304006232833479)
          ·
            refine ⟨13070150610456009349250219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8713433740304006232833479 13070150610456009349250219)
            ·
              refine ⟨19605225915684014023875329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13070150610456009349250219 19605225915684014023875329)
              ·
                refine ⟨14703919436763010517906497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19605225915684014023875329 14703919436763010517906497)
                ·
                  refine ⟨11027939577572257888429873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14703919436763010517906497 11027939577572257888429873)
                  ·
                    refine ⟨8270954683179193416322405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11027939577572257888429873 8270954683179193416322405)
                    ·
                      refine ⟨1550804003096098765560451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8270954683179193416322405 1550804003096098765560451)
                      ·
                        rfl

theorem cell23_3020180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3020180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020180 prefixEnd_3020180 := by exact prefixLift 3020180
  have htrace : WordTrace (prefixWord ++ tailWord_3020180) baseStart_3020180 baseEnd_3020180 := by
    simpa [prefixWord, tailWord_3020180, baseEnd_3020180] using wordTrace_append hprefix tailTrace_3020180
  have hstable : (prefixWord ++ tailWord_3020180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020180).length < 2 ^ (prefixWord ++ tailWord_3020180).sum := by decide
  have hdescent : baseEnd_3020180 < baseStart_3020180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020184 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3020184 : Nat := 118140960795 + 3020184 * 2 ^ 59
def prefixEnd_3020184 : Nat := 4983230072969 + 3 ^ 40 * 3020184 * 2
def baseEnd_3020184 : Nat := 1550806057018716749910433

theorem tailTrace_3020184 : CollatzResearch.WordTrace tailWord_3020184 prefixEnd_3020184 1550806057018716749910433 := by
  unfold tailWord_3020184
  simp only [CollatzResearch.WordTrace]
  refine ⟨55077580045198324603433803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73436773393597766137911737 55077580045198324603433803)
  ·
    refine ⟨82616370067797486905150705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55077580045198324603433803 82616370067797486905150705)
    ·
      refine ⟨61962277550848115178863029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82616370067797486905150705 61962277550848115178863029)
      ·
        refine ⟨5808963520392010798018409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61962277550848115178863029 5808963520392010798018409)
        ·
          refine ⟨4356722640294008098513807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5808963520392010798018409 4356722640294008098513807)
          ·
            refine ⟨6535083960441012147770711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356722640294008098513807 6535083960441012147770711)
            ·
              refine ⟨9802625940661518221656067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6535083960441012147770711 9802625940661518221656067)
              ·
                refine ⟨14703938910992277332484101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9802625940661518221656067 14703938910992277332484101)
                ·
                  refine ⟨2756988545811051999840769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14703938910992277332484101 2756988545811051999840769)
                  ·
                    refine ⟨2067741409358288999880577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2756988545811051999840769 2067741409358288999880577)
                    ·
                      refine ⟨1550806057018716749910433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067741409358288999880577 1550806057018716749910433)
                      ·
                        rfl

theorem cell23_3020184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3020184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020184 prefixEnd_3020184 := by exact prefixLift 3020184
  have htrace : WordTrace (prefixWord ++ tailWord_3020184) baseStart_3020184 baseEnd_3020184 := by
    simpa [prefixWord, tailWord_3020184, baseEnd_3020184] using wordTrace_append hprefix tailTrace_3020184
  have hstable : (prefixWord ++ tailWord_3020184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020184).length < 2 ^ (prefixWord ++ tailWord_3020184).sum := by decide
  have hdescent : baseEnd_3020184 < baseStart_3020184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020223 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_3020223 : Nat := 118140960795 + 3020223 * 2 ^ 59
def prefixEnd_3020223 : Nat := 4983230072969 + 3 ^ 40 * 3020223 * 2
def baseEnd_3020223 : Nat := 1550826082764242097322753

theorem tailTrace_3020223 : CollatzResearch.WordTrace tailWord_3020223 prefixEnd_3020223 1550826082764242097322753 := by
  unfold tailWord_3020223
  simp only [CollatzResearch.WordTrace]
  refine ⟨110156582537255358867537323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73437721691503572578358215 110156582537255358867537323)
  ·
    refine ⟨165234873805883038301305985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110156582537255358867537323 165234873805883038301305985)
    ·
      refine ⟨123926155354412278725979489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165234873805883038301305985 123926155354412278725979489)
      ·
        refine ⟨92944616515809209044484617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123926155354412278725979489 92944616515809209044484617)
        ·
          refine ⟨69708462386856906783363463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92944616515809209044484617 69708462386856906783363463)
          ·
            refine ⟨104562693580285360175045195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69708462386856906783363463 104562693580285360175045195)
            ·
              refine ⟨156844040370428040262567793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104562693580285360175045195 156844040370428040262567793)
              ·
                refine ⟨117633030277821030196925845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156844040370428040262567793 117633030277821030196925845)
                ·
                  refine ⟨5514048294272860790480899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117633030277821030196925845 5514048294272860790480899)
                  ·
                    refine ⟨8271072441409291185721349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5514048294272860790480899 8271072441409291185721349)
                    ·
                      refine ⟨1550826082764242097322753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8271072441409291185721349 1550826082764242097322753)
                      ·
                        rfl

theorem cell23_3020223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_3020223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020223 prefixEnd_3020223 := by exact prefixLift 3020223
  have htrace : WordTrace (prefixWord ++ tailWord_3020223) baseStart_3020223 baseEnd_3020223 := by
    simpa [prefixWord, tailWord_3020223, baseEnd_3020223] using wordTrace_append hprefix tailTrace_3020223
  have hstable : (prefixWord ++ tailWord_3020223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020223).length < 2 ^ (prefixWord ++ tailWord_3020223).sum := by decide
  have hdescent : baseEnd_3020223 < baseStart_3020223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020313 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_3020313 : Nat := 118140960795 + 3020313 * 2 ^ 59
def prefixEnd_3020313 : Nat := 4983230072969 + 3 ^ 40 * 3020313 * 2
def baseEnd_3020313 : Nat := 1550872296023146745197339

theorem tailTrace_3020313 : CollatzResearch.WordTrace tailWord_3020313 prefixEnd_3020313 1550872296023146745197339 := by
  unfold tailWord_3020313
  simp only [CollatzResearch.WordTrace]
  refine ⟨110159865106929304238313593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73439910071286202825542395 110159865106929304238313593)
  ·
    refine ⟨82619898830196978178735195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110159865106929304238313593 82619898830196978178735195)
    ·
      refine ⟨123929848245295467268102793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82619898830196978178735195 123929848245295467268102793)
      ·
        refine ⟨92947386183971600451077095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123929848245295467268102793 92947386183971600451077095)
        ·
          refine ⟨139421079275957400676615643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92947386183971600451077095 139421079275957400676615643)
          ·
            refine ⟨209131618913936101014923465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139421079275957400676615643 209131618913936101014923465)
            ·
              refine ⟨156848714185452075761192599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209131618913936101014923465 156848714185452075761192599)
              ·
                refine ⟨235273071278178113641788899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156848714185452075761192599 235273071278178113641788899)
                ·
                  refine ⟨352909606917267170462683349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235273071278178113641788899 352909606917267170462683349)
                  ·
                    refine ⟨8271318912123449307719141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 352909606917267170462683349 8271318912123449307719141)
                    ·
                      refine ⟨1550872296023146745197339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8271318912123449307719141 1550872296023146745197339)
                      ·
                        rfl

theorem cell23_3020313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_3020313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020313 prefixEnd_3020313 := by exact prefixLift 3020313
  have htrace : WordTrace (prefixWord ++ tailWord_3020313) baseStart_3020313 baseEnd_3020313 := by
    simpa [prefixWord, tailWord_3020313, baseEnd_3020313] using wordTrace_append hprefix tailTrace_3020313
  have hstable : (prefixWord ++ tailWord_3020313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020313).length < 2 ^ (prefixWord ++ tailWord_3020313).sum := by decide
  have hdescent : baseEnd_3020313 < baseStart_3020313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020317 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_3020317 : Nat := 118140960795 + 3020317 * 2 ^ 59
def prefixEnd_3020317 : Nat := 4983230072969 + 3 ^ 40 * 3020317 * 2
def baseEnd_3020317 : Nat := 1550874349945764729547321

theorem tailTrace_3020317 : CollatzResearch.WordTrace tailWord_3020317 prefixEnd_3020317 1550874349945764729547321 := by
  unfold tailWord_3020317
  simp only [CollatzResearch.WordTrace]
  refine ⟨110160010998914812921459205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73440007332609875280972803 110160010998914812921459205)
  ·
    refine ⟨20655002062296527422773601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110160010998914812921459205 20655002062296527422773601)
    ·
      refine ⟨15491251546722395567080201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20655002062296527422773601 15491251546722395567080201)
      ·
        refine ⟨11618438660041796675310151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15491251546722395567080201 11618438660041796675310151)
        ·
          refine ⟨17427657990062695012965227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11618438660041796675310151 17427657990062695012965227)
          ·
            refine ⟨26141486985094042519447841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17427657990062695012965227 26141486985094042519447841)
            ·
              refine ⟨19606115238820531889585881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26141486985094042519447841 19606115238820531889585881)
              ·
                refine ⟨14704586429115398917189411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19606115238820531889585881 14704586429115398917189411)
                ·
                  refine ⟨22056879643673098375784117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14704586429115398917189411 22056879643673098375784117)
                  ·
                    refine ⟨2067832466594352972729761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22056879643673098375784117 2067832466594352972729761)
                    ·
                      refine ⟨1550874349945764729547321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067832466594352972729761 1550874349945764729547321)
                      ·
                        rfl

theorem cell23_3020317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_3020317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020317 prefixEnd_3020317 := by exact prefixLift 3020317
  have htrace : WordTrace (prefixWord ++ tailWord_3020317) baseStart_3020317 baseEnd_3020317 := by
    simpa [prefixWord, tailWord_3020317, baseEnd_3020317] using wordTrace_append hprefix tailTrace_3020317
  have hstable : (prefixWord ++ tailWord_3020317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020317).length < 2 ^ (prefixWord ++ tailWord_3020317).sum := by decide
  have hdescent : baseEnd_3020317 < baseStart_3020317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020318 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3020318 : Nat := 118140960795 + 3020318 * 2 ^ 59
def prefixEnd_3020318 : Nat := 4983230072969 + 3 ^ 40 * 3020318 * 2
def baseEnd_3020318 : Nat := 516958287808806408544939

theorem tailTrace_3020318 : CollatzResearch.WordTrace tailWord_3020318 prefixEnd_3020318 516958287808806408544939 := by
  unfold tailWord_3020318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13770005933988898761530701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73440031647940793394830405 13770005933988898761530701)
  ·
    refine ⟨5163752225245837035574013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13770005933988898761530701 5163752225245837035574013)
    ·
      refine ⟨1936407084467188888340255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5163752225245837035574013 1936407084467188888340255)
      ·
        refine ⟨2904610626700783332510383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936407084467188888340255 2904610626700783332510383)
        ·
          refine ⟨4356915940051174998765575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2904610626700783332510383 4356915940051174998765575)
          ·
            refine ⟨6535373910076762498148363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356915940051174998765575 6535373910076762498148363)
            ·
              refine ⟨9803060865115143747222545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6535373910076762498148363 9803060865115143747222545)
              ·
                refine ⟨7352295648836357810416909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9803060865115143747222545 7352295648836357810416909)
                ·
                  refine ⟨2757110868313634178906341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7352295648836357810416909 2757110868313634178906341)
                  ·
                    refine ⟨516958287808806408544939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757110868313634178906341 516958287808806408544939)
                    ·
                      rfl

theorem cell23_3020318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3020318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020318 prefixEnd_3020318 := by exact prefixLift 3020318
  have htrace : WordTrace (prefixWord ++ tailWord_3020318) baseStart_3020318 baseEnd_3020318 := by
    simpa [prefixWord, tailWord_3020318, baseEnd_3020318] using wordTrace_append hprefix tailTrace_3020318
  have hstable : (prefixWord ++ tailWord_3020318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020318).length < 2 ^ (prefixWord ++ tailWord_3020318).sum := by decide
  have hdescent : baseEnd_3020318 < baseStart_3020318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020334 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_3020334 : Nat := 118140960795 + 3020334 * 2 ^ 59
def prefixEnd_3020334 : Nat := 4983230072969 + 3 ^ 40 * 3020334 * 2
def baseEnd_3020334 : Nat := 1550883079116891163034743

theorem tailTrace_3020334 : CollatzResearch.WordTrace tailWord_3020334 prefixEnd_3020334 1550883079116891163034743 := by
  unfold tailWord_3020334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13770078879981653103103507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73440420693235483216552037 13770078879981653103103507)
  ·
    refine ⟨20655118319972479654655261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13770078879981653103103507 20655118319972479654655261)
    ·
      refine ⟨7745669369989679870495723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20655118319972479654655261 7745669369989679870495723)
      ·
        refine ⟨11618504054984519805743585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7745669369989679870495723 11618504054984519805743585)
        ·
          refine ⟨8713878041238389854307689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11618504054984519805743585 8713878041238389854307689)
          ·
            refine ⟨6535408530928792390730767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8713878041238389854307689 6535408530928792390730767)
            ·
              refine ⟨9803112796393188586096151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6535408530928792390730767 9803112796393188586096151)
              ·
                refine ⟨14704669194589782879144227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9803112796393188586096151 14704669194589782879144227)
                ·
                  refine ⟨22057003791884674318716341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14704669194589782879144227 22057003791884674318716341)
                  ·
                    refine ⟨2067844105489188217379657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22057003791884674318716341 2067844105489188217379657)
                    ·
                      refine ⟨1550883079116891163034743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067844105489188217379657 1550883079116891163034743)
                      ·
                        rfl

theorem cell23_3020334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_3020334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020334 prefixEnd_3020334 := by exact prefixLift 3020334
  have htrace : WordTrace (prefixWord ++ tailWord_3020334) baseStart_3020334 baseEnd_3020334 := by
    simpa [prefixWord, tailWord_3020334, baseEnd_3020334] using wordTrace_append hprefix tailTrace_3020334
  have hstable : (prefixWord ++ tailWord_3020334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020334).length < 2 ^ (prefixWord ++ tailWord_3020334).sum := by decide
  have hdescent : baseEnd_3020334 < baseStart_3020334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020341 : List Nat := [1, 3, 3, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_3020341 : Nat := 118140960795 + 3020341 * 2 ^ 59
def prefixEnd_3020341 : Nat := 4983230072969 + 3 ^ 40 * 3020341 * 2
def baseEnd_3020341 : Nat := 1550886673481472635647211

theorem tailTrace_3020341 : CollatzResearch.WordTrace tailWord_3020341 prefixEnd_3020341 1550886673481472635647211 := by
  unfold tailWord_3020341
  simp only [CollatzResearch.WordTrace]
  refine ⟨110160886350827865020332877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73440590900551910013555251 110160886350827865020332877)
  ·
    refine ⟨41310332381560449382624829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110160886350827865020332877 41310332381560449382624829)
    ·
      refine ⟨15491374643085168518484311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41310332381560449382624829 15491374643085168518484311)
      ·
        refine ⟨23237061964627752777726467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15491374643085168518484311 23237061964627752777726467)
        ·
          refine ⟨34855592946941629166589701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23237061964627752777726467 34855592946941629166589701)
          ·
            refine ⟨6535423677551555468735569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34855592946941629166589701 6535423677551555468735569)
            ·
              refine ⟨4901567758163666601551677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6535423677551555468735569 4901567758163666601551677)
              ·
                refine ⟨1838087909311374975581879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4901567758163666601551677 1838087909311374975581879)
                ·
                  refine ⟨2757131863967062463372819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838087909311374975581879 2757131863967062463372819)
                  ·
                    refine ⟨4135697795950593695059229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2757131863967062463372819 4135697795950593695059229)
                    ·
                      refine ⟨1550886673481472635647211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4135697795950593695059229 1550886673481472635647211)
                      ·
                        rfl

theorem cell23_3020341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_3020341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020341 prefixEnd_3020341 := by exact prefixLift 3020341
  have htrace : WordTrace (prefixWord ++ tailWord_3020341) baseStart_3020341 baseEnd_3020341 := by
    simpa [prefixWord, tailWord_3020341, baseEnd_3020341] using wordTrace_append hprefix tailTrace_3020341
  have hstable : (prefixWord ++ tailWord_3020341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020341).length < 2 ^ (prefixWord ++ tailWord_3020341).sum := by decide
  have hdescent : baseEnd_3020341 < baseStart_3020341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020344 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 1, 5]
def baseStart_3020344 : Nat := 118140960795 + 3020344 * 2 ^ 59
def prefixEnd_3020344 : Nat := 4983230072969 + 3 ^ 40 * 3020344 * 2
def baseEnd_3020344 : Nat := 516962737974478707969899

theorem tailTrace_3020344 : CollatzResearch.WordTrace tailWord_3020344 prefixEnd_3020344 516962737974478707969899 := by
  unfold tailWord_3020344
  simp only [CollatzResearch.WordTrace]
  refine ⟨55080497884908498266346043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73440663846544664355128057 55080497884908498266346043)
  ·
    refine ⟨82620746827362747399519065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55080497884908498266346043 82620746827362747399519065)
    ·
      refine ⟨61965560120522060549639299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82620746827362747399519065 61965560120522060549639299)
      ·
        refine ⟨92948340180783090824458949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61965560120522060549639299 92948340180783090824458949)
        ·
          refine ⟨17427813783896829529586053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92948340180783090824458949 17427813783896829529586053)
          ·
            refine ⟨3267715084480655536797385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17427813783896829529586053 3267715084480655536797385)
            ·
              refine ⟨2450786313360491652598039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3267715084480655536797385 2450786313360491652598039)
              ·
                refine ⟨3676179470040737478897059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450786313360491652598039 3676179470040737478897059)
                ·
                  refine ⟨5514269205061106218345589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676179470040737478897059 5514269205061106218345589)
                  ·
                    refine ⟨516962737974478707969899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5514269205061106218345589 516962737974478707969899)
                    ·
                      rfl

theorem cell23_3020344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_3020344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020344 prefixEnd_3020344 := by exact prefixLift 3020344
  have htrace : WordTrace (prefixWord ++ tailWord_3020344) baseStart_3020344 baseEnd_3020344 := by
    simpa [prefixWord, tailWord_3020344, baseEnd_3020344] using wordTrace_append hprefix tailTrace_3020344
  have hstable : (prefixWord ++ tailWord_3020344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020344).length < 2 ^ (prefixWord ++ tailWord_3020344).sum := by decide
  have hdescent : baseEnd_3020344 < baseStart_3020344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020358 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3020358 : Nat := 118140960795 + 3020358 * 2 ^ 59
def prefixEnd_3020358 : Nat := 4983230072969 + 3 ^ 40 * 3020358 * 2
def baseEnd_3020358 : Nat := 1550895402652599069134633

theorem tailTrace_3020358 : CollatzResearch.WordTrace tailWord_3020358 prefixEnd_3020358 1550895402652599069134633 := by
  unfold tailWord_3020358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442547074742696153865679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73441004261177517949134485 3442547074742696153865679)
  ·
    refine ⟨5163820612114044230798519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3442547074742696153865679 5163820612114044230798519)
    ·
      refine ⟨7745730918171066346197779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5163820612114044230798519 7745730918171066346197779)
      ·
        refine ⟨11618596377256599519296669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7745730918171066346197779 11618596377256599519296669)
        ·
          refine ⟨4356973641471224819736251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11618596377256599519296669 4356973641471224819736251)
          ·
            refine ⟨6535460462206837229604377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356973641471224819736251 6535460462206837229604377)
            ·
              refine ⟨4901595346655127922203283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6535460462206837229604377 4901595346655127922203283)
              ·
                refine ⟨7352393019982691883304925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901595346655127922203283 7352393019982691883304925)
                ·
                  refine ⟨2757147382493509456239347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7352393019982691883304925 2757147382493509456239347)
                  ·
                    refine ⟨4135721073740264184359021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2757147382493509456239347 4135721073740264184359021)
                    ·
                      refine ⟨1550895402652599069134633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4135721073740264184359021 1550895402652599069134633)
                      ·
                        rfl

theorem cell23_3020358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3020358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020358 prefixEnd_3020358 := by exact prefixLift 3020358
  have htrace : WordTrace (prefixWord ++ tailWord_3020358) baseStart_3020358 baseEnd_3020358 := by
    simpa [prefixWord, tailWord_3020358, baseEnd_3020358] using wordTrace_append hprefix tailTrace_3020358
  have hstable : (prefixWord ++ tailWord_3020358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020358).length < 2 ^ (prefixWord ++ tailWord_3020358).sum := by decide
  have hdescent : baseEnd_3020358 < baseStart_3020358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020363 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 7]
def baseStart_3020363 : Nat := 118140960795 + 3020363 * 2 ^ 59
def prefixEnd_3020363 : Nat := 4983230072969 + 3 ^ 40 * 3020363 * 2
def baseEnd_3020363 : Nat := 1550897970055871549572109

theorem tailTrace_3020363 : CollatzResearch.WordTrace tailWord_3020363 prefixEnd_3020363 1550897970055871549572109 := by
  unfold tailWord_3020363
  simp only [CollatzResearch.WordTrace]
  refine ⟨110161688756748162777633743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73441125837832108518422495 110161688756748162777633743)
  ·
    refine ⟨165242533135122244166450615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110161688756748162777633743 165242533135122244166450615)
    ·
      refine ⟨247863799702683366249675923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165242533135122244166450615 247863799702683366249675923)
      ·
        refine ⟨371795699554025049374513885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247863799702683366249675923 371795699554025049374513885)
        ·
          refine ⟨139423387332759393515442707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371795699554025049374513885 139423387332759393515442707)
          ·
            refine ⟨209135080999139090273164061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139423387332759393515442707 209135080999139090273164061)
            ·
              refine ⟨78425655374677158852436523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209135080999139090273164061 78425655374677158852436523)
              ·
                refine ⟨117638483062015738278654785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78425655374677158852436523 117638483062015738278654785)
                ·
                  refine ⟨88228862296511803708991089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117638483062015738278654785 88228862296511803708991089)
                  ·
                    refine ⟨66171646722383852781743317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88228862296511803708991089 66171646722383852781743317)
                    ·
                      refine ⟨1550897970055871549572109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66171646722383852781743317 1550897970055871549572109)
                      ·
                        rfl

theorem cell23_3020363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_3020363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020363 prefixEnd_3020363 := by exact prefixLift 3020363
  have htrace : WordTrace (prefixWord ++ tailWord_3020363) baseStart_3020363 baseEnd_3020363 := by
    simpa [prefixWord, tailWord_3020363, baseEnd_3020363] using wordTrace_append hprefix tailTrace_3020363
  have hstable : (prefixWord ++ tailWord_3020363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020363).length < 2 ^ (prefixWord ++ tailWord_3020363).sum := by decide
  have hdescent : baseEnd_3020363 < baseStart_3020363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020364 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 3, 2, 2]
def baseStart_3020364 : Nat := 118140960795 + 3020364 * 2 ^ 59
def prefixEnd_3020364 : Nat := 4983230072969 + 3 ^ 40 * 3020364 * 2
def baseEnd_3020364 : Nat := 1550898483536526045659605

theorem tailTrace_3020364 : CollatzResearch.WordTrace tailWord_3020364 prefixEnd_3020364 1550898483536526045659605 := by
  unfold tailWord_3020364
  simp only [CollatzResearch.WordTrace]
  refine ⟨55080862614872269974210073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73441150153163026632280097 55080862614872269974210073)
  ·
    refine ⟨41310646961154202480657555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55080862614872269974210073 41310646961154202480657555)
    ·
      refine ⟨61965970441731303720986333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41310646961154202480657555 61965970441731303720986333)
      ·
        refine ⟨23237238915649238895369875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61965970441731303720986333 23237238915649238895369875)
        ·
          refine ⟨34855858373473858343054813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23237238915649238895369875 34855858373473858343054813)
          ·
            refine ⟨13070946890052696878645555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34855858373473858343054813 13070946890052696878645555)
            ·
              refine ⟨19606420335079045317968333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13070946890052696878645555 19606420335079045317968333)
              ·
                refine ⟨7352407625654641994238125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19606420335079045317968333 7352407625654641994238125)
                ·
                  refine ⟨2757152859620490747839297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7352407625654641994238125 2757152859620490747839297)
                  ·
                    refine ⟨2067864644715368060879473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2757152859620490747839297 2067864644715368060879473)
                    ·
                      refine ⟨1550898483536526045659605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067864644715368060879473 1550898483536526045659605)
                      ·
                        rfl

theorem cell23_3020364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_3020364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020364 prefixEnd_3020364 := by exact prefixLift 3020364
  have htrace : WordTrace (prefixWord ++ tailWord_3020364) baseStart_3020364 baseEnd_3020364 := by
    simpa [prefixWord, tailWord_3020364, baseEnd_3020364] using wordTrace_append hprefix tailTrace_3020364
  have hstable : (prefixWord ++ tailWord_3020364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020364).length < 2 ^ (prefixWord ++ tailWord_3020364).sum := by decide
  have hdescent : baseEnd_3020364 < baseStart_3020364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020387 : List Nat := [1, 1, 1, 5, 1, 5, 2, 7]
def baseStart_3020387 : Nat := 118140960795 + 3020387 * 2 ^ 59
def prefixEnd_3020387 : Nat := 4983230072969 + 3 ^ 40 * 3020387 * 2
def baseEnd_3020387 : Nat := 57441121984873313173037

theorem tailTrace_3020387 : CollatzResearch.WordTrace tailWord_3020387 prefixEnd_3020387 57441121984873313173037 := by
  unfold tailWord_3020387
  simp only [CollatzResearch.WordTrace]
  refine ⟨110162564108661214876507415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73441709405774143251004943 110162564108661214876507415)
  ·
    refine ⟨165243846162991822314761123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110162564108661214876507415 165243846162991822314761123)
    ·
      refine ⟨247865769244487733472141685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165243846162991822314761123 247865769244487733472141685)
      ·
        refine ⟨23237415866670725013013283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247865769244487733472141685 23237415866670725013013283)
        ·
          refine ⟨34856123800006087519519925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23237415866670725013013283 34856123800006087519519925)
          ·
            refine ⟨3267761606250570704954993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34856123800006087519519925 3267761606250570704954993)
            ·
              refine ⟨2450821204687928028716245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3267761606250570704954993 2450821204687928028716245)
              ·
                refine ⟨57441121984873313173037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2450821204687928028716245 57441121984873313173037)
                ·
                  rfl

theorem cell23_3020387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 7].length) (baseStart_3020387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020387 prefixEnd_3020387 := by exact prefixLift 3020387
  have htrace : WordTrace (prefixWord ++ tailWord_3020387) baseStart_3020387 baseEnd_3020387 := by
    simpa [prefixWord, tailWord_3020387, baseEnd_3020387] using wordTrace_append hprefix tailTrace_3020387
  have hstable : (prefixWord ++ tailWord_3020387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020387).length < 2 ^ (prefixWord ++ tailWord_3020387).sum := by decide
  have hdescent : baseEnd_3020387 < baseStart_3020387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020407 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 5, 3, 2]
def baseStart_3020407 : Nat := 118140960795 + 3020407 * 2 ^ 59
def prefixEnd_3020407 : Nat := 4983230072969 + 3 ^ 40 * 3020407 * 2
def baseEnd_3020407 : Nat := 1550920563204669377421907

theorem tailTrace_3020407 : CollatzResearch.WordTrace tailWord_3020407 prefixEnd_3020407 1550920563204669377421907 := by
  unfold tailWord_3020407
  simp only [CollatzResearch.WordTrace]
  refine ⟨110163293568588758292235475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73442195712392505528156983 110163293568588758292235475)
  ·
    refine ⟨165244940352883137438353213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110163293568588758292235475 165244940352883137438353213)
    ·
      refine ⟨61966852632331176539382455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165244940352883137438353213 61966852632331176539382455)
      ·
        refine ⟨92950278948496764809073683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61966852632331176539382455 92950278948496764809073683)
        ·
          refine ⟨139425418422745147213610525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92950278948496764809073683 139425418422745147213610525)
          ·
            refine ⟨52284531908529430205103947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139425418422745147213610525 52284531908529430205103947)
            ·
              refine ⟨78426797862794145307655921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52284531908529430205103947 78426797862794145307655921)
              ·
                refine ⟨58820098397095608980741941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78426797862794145307655921 58820098397095608980741941)
                ·
                  refine ⟨5514384224727713341944557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58820098397095608980741941 5514384224727713341944557)
                  ·
                    refine ⟨2067894084272892503229209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5514384224727713341944557 2067894084272892503229209)
                    ·
                      refine ⟨1550920563204669377421907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067894084272892503229209 1550920563204669377421907)
                      ·
                        rfl

theorem cell23_3020407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_3020407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020407 prefixEnd_3020407 := by exact prefixLift 3020407
  have htrace : WordTrace (prefixWord ++ tailWord_3020407) baseStart_3020407 baseEnd_3020407 := by
    simpa [prefixWord, tailWord_3020407, baseEnd_3020407] using wordTrace_append hprefix tailTrace_3020407
  have hstable : (prefixWord ++ tailWord_3020407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020407).length < 2 ^ (prefixWord ++ tailWord_3020407).sum := by decide
  have hdescent : baseEnd_3020407 < baseStart_3020407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020437 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_3020437 : Nat := 118140960795 + 3020437 * 2 ^ 59
def prefixEnd_3020437 : Nat := 4983230072969 + 3 ^ 40 * 3020437 * 2
def baseEnd_3020437 : Nat := 1550935967624304260046769

theorem tailTrace_3020437 : CollatzResearch.WordTrace tailWord_3020437 prefixEnd_3020437 1550935967624304260046769 := by
  unfold tailWord_3020437
  simp only [CollatzResearch.WordTrace]
  refine ⟨110164387758480073415827565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73442925172320048943885043 110164387758480073415827565)
  ·
    refine ⟨41311645409430027530935337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110164387758480073415827565 41311645409430027530935337)
    ·
      refine ⟨30983734057072520648201503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41311645409430027530935337 30983734057072520648201503)
      ·
        refine ⟨46475601085608780972302255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30983734057072520648201503 46475601085608780972302255)
        ·
          refine ⟨69713401628413171458453383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46475601085608780972302255 69713401628413171458453383)
          ·
            refine ⟨104570102442619757187680075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69713401628413171458453383 104570102442619757187680075)
            ·
              refine ⟨156855153663929635781520113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104570102442619757187680075 156855153663929635781520113)
              ·
                refine ⟨117641365247947226836140085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156855153663929635781520113 117641365247947226836140085)
                ·
                  refine ⟨11028877991995052515888133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117641365247947226836140085 11028877991995052515888133)
                  ·
                    refine ⟨2067914623499072346729025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11028877991995052515888133 2067914623499072346729025)
                    ·
                      refine ⟨1550935967624304260046769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067914623499072346729025 1550935967624304260046769)
                      ·
                        rfl

theorem cell23_3020437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_3020437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020437 prefixEnd_3020437 := by exact prefixLift 3020437
  have htrace : WordTrace (prefixWord ++ tailWord_3020437) baseStart_3020437 baseEnd_3020437 := by
    simpa [prefixWord, tailWord_3020437, baseEnd_3020437] using wordTrace_append hprefix tailTrace_3020437
  have hstable : (prefixWord ++ tailWord_3020437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020437).length < 2 ^ (prefixWord ++ tailWord_3020437).sum := by decide
  have hdescent : baseEnd_3020437 < baseStart_3020437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020471 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 2, 2, 2]
def baseStart_3020471 : Nat := 118140960795 + 3020471 * 2 ^ 59
def prefixEnd_3020471 : Nat := 4983230072969 + 3 ^ 40 * 3020471 * 2
def baseEnd_3020471 : Nat := 1550953425966557127021613

theorem tailTrace_3020471 : CollatzResearch.WordTrace tailWord_3020471 prefixEnd_3020471 1550953425966557127021613 := by
  unfold tailWord_3020471
  simp only [CollatzResearch.WordTrace]
  refine ⟨110165627840356897222565267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73443751893571264815043511 110165627840356897222565267)
  ·
    refine ⟨165248441760535345833847901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110165627840356897222565267 165248441760535345833847901)
    ·
      refine ⟨61968165660200754687692963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165248441760535345833847901 61968165660200754687692963)
      ·
        refine ⟨92952248490301132031539445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61968165660200754687692963 92952248490301132031539445)
        ·
          refine ⟨8714273295965731127956823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92952248490301132031539445 8714273295965731127956823)
          ·
            refine ⟨13071409943948596691935235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8714273295965731127956823 13071409943948596691935235)
            ·
              refine ⟨19607114915922895037902853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13071409943948596691935235 19607114915922895037902853)
              ·
                refine ⟨3676334046735542819606785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19607114915922895037902853 3676334046735542819606785)
                ·
                  refine ⟨2757250535051657114705089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676334046735542819606785 2757250535051657114705089)
                  ·
                    refine ⟨2067937901288742836028817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2757250535051657114705089 2067937901288742836028817)
                    ·
                      refine ⟨1550953425966557127021613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2067937901288742836028817 1550953425966557127021613)
                      ·
                        rfl

theorem cell23_3020471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_3020471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020471 prefixEnd_3020471 := by exact prefixLift 3020471
  have htrace : WordTrace (prefixWord ++ tailWord_3020471) baseStart_3020471 baseEnd_3020471 := by
    simpa [prefixWord, tailWord_3020471, baseEnd_3020471] using wordTrace_append hprefix tailTrace_3020471
  have hstable : (prefixWord ++ tailWord_3020471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020471).length < 2 ^ (prefixWord ++ tailWord_3020471).sum := by decide
  have hdescent : baseEnd_3020471 < baseStart_3020471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020487 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_3020487 : Nat := 118140960795 + 3020487 * 2 ^ 59
def prefixEnd_3020487 : Nat := 4983230072969 + 3 ^ 40 * 3020487 * 2
def baseEnd_3020487 : Nat := 1550961641657029064421539

theorem tailTrace_3020487 : CollatzResearch.WordTrace tailWord_3020487 prefixEnd_3020487 1550961641657029064421539 := by
  unfold tailWord_3020487
  simp only [CollatzResearch.WordTrace]
  refine ⟨110166211408298931955147715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73444140938865954636765143 110166211408298931955147715)
  ·
    refine ⟨165249317112448397932721573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110166211408298931955147715 165249317112448397932721573)
    ·
      refine ⟨30984246958584074612385295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165249317112448397932721573 30984246958584074612385295)
      ·
        refine ⟨46476370437876111918577943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30984246958584074612385295 46476370437876111918577943)
        ·
          refine ⟨69714555656814167877866915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46476370437876111918577943 69714555656814167877866915)
          ·
            refine ⟨104571833485221251816800373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69714555656814167877866915 104571833485221251816800373)
            ·
              refine ⟨9803609389239492357825035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104571833485221251816800373 9803609389239492357825035)
              ·
                refine ⟨14705414083859238536737553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9803609389239492357825035 14705414083859238536737553)
                ·
                  refine ⟨11029060562894428902553165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14705414083859238536737553 11029060562894428902553165)
                  ·
                    refine ⟨4135897711085410838457437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11029060562894428902553165 4135897711085410838457437)
                    ·
                      refine ⟨1550961641657029064421539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4135897711085410838457437 1550961641657029064421539)
                      ·
                        rfl

theorem cell23_3020487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_3020487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020487 prefixEnd_3020487 := by exact prefixLift 3020487
  have htrace : WordTrace (prefixWord ++ tailWord_3020487) baseStart_3020487 baseEnd_3020487 := by
    simpa [prefixWord, tailWord_3020487, baseEnd_3020487] using wordTrace_append hprefix tailTrace_3020487
  have hstable : (prefixWord ++ tailWord_3020487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020487).length < 2 ^ (prefixWord ++ tailWord_3020487).sum := by decide
  have hdescent : baseEnd_3020487 < baseStart_3020487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020527 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_3020527 : Nat := 118140960795 + 3020527 * 2 ^ 59
def prefixEnd_3020527 : Nat := 4983230072969 + 3 ^ 40 * 3020527 * 2
def baseEnd_3020527 : Nat := 1550982180883208907921355

theorem tailTrace_3020527 : CollatzResearch.WordTrace tailWord_3020527 prefixEnd_3020527 1550982180883208907921355 := by
  unfold tailWord_3020527
  simp only [CollatzResearch.WordTrace]
  refine ⟨110167670328154018786603835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73445113552102679191069223 110167670328154018786603835)
  ·
    refine ⟨165251505492231028179905753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110167670328154018786603835 165251505492231028179905753)
    ·
      refine ⟨123938629119173271134929315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165251505492231028179905753 123938629119173271134929315)
      ·
        refine ⟨185907943678759906702393973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123938629119173271134929315 185907943678759906702393973)
        ·
          refine ⟨17428869719883741253349435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185907943678759906702393973 17428869719883741253349435)
          ·
            refine ⟨26143304579825611880024153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17428869719883741253349435 26143304579825611880024153)
            ·
              refine ⟨19607478434869208910018115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26143304579825611880024153 19607478434869208910018115)
              ·
                refine ⟨29411217652303813365027173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19607478434869208910018115 29411217652303813365027173)
                ·
                  refine ⟨5514603309806965005942595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29411217652303813365027173 5514603309806965005942595)
                  ·
                    refine ⟨8271904964710447508913893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5514603309806965005942595 8271904964710447508913893)
                    ·
                      refine ⟨1550982180883208907921355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8271904964710447508913893 1550982180883208907921355)
                      ·
                        rfl

theorem cell23_3020527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_3020527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020527 prefixEnd_3020527 := by exact prefixLift 3020527
  have htrace : WordTrace (prefixWord ++ tailWord_3020527) baseStart_3020527 baseEnd_3020527 := by
    simpa [prefixWord, tailWord_3020527, baseEnd_3020527] using wordTrace_append hprefix tailTrace_3020527
  have hstable : (prefixWord ++ tailWord_3020527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020527).length < 2 ^ (prefixWord ++ tailWord_3020527).sum := by decide
  have hdescent : baseEnd_3020527 < baseStart_3020527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020547 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 3]
def baseStart_3020547 : Nat := 118140960795 + 3020547 * 2 ^ 59
def prefixEnd_3020547 : Nat := 4983230072969 + 3 ^ 40 * 3020547 * 2
def baseEnd_3020547 : Nat := 1550992450496298829671263

theorem tailTrace_3020547 : CollatzResearch.WordTrace tailWord_3020547 prefixEnd_3020547 1550992450496298829671263 := by
  unfold tailWord_3020547
  simp only [CollatzResearch.WordTrace]
  refine ⟨110168399788081562202331895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73445599858721041468221263 110168399788081562202331895)
  ·
    refine ⟨165252599682122343303497843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110168399788081562202331895 165252599682122343303497843)
    ·
      refine ⟨247878899523183514955246765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165252599682122343303497843 247878899523183514955246765)
      ·
        refine ⟨92954587321193818108217537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247878899523183514955246765 92954587321193818108217537)
        ·
          refine ⟨69715940490895363581163153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92954587321193818108217537 69715940490895363581163153)
          ·
            refine ⟨52286955368171522685872365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69715940490895363581163153 52286955368171522685872365)
            ·
              refine ⟨19607608263064321007202137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52286955368171522685872365 19607608263064321007202137)
              ·
                refine ⟨14705706197298240755401603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19607608263064321007202137 14705706197298240755401603)
                ·
                  refine ⟨22058559295947361133102405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14705706197298240755401603 22058559295947361133102405)
                  ·
                    refine ⟨4135979867990130212456701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22058559295947361133102405 4135979867990130212456701)
                    ·
                      refine ⟨1550992450496298829671263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4135979867990130212456701 1550992450496298829671263)
                      ·
                        rfl

theorem cell23_3020547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_3020547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020547 prefixEnd_3020547 := by exact prefixLift 3020547
  have htrace : WordTrace (prefixWord ++ tailWord_3020547) baseStart_3020547 baseEnd_3020547 := by
    simpa [prefixWord, tailWord_3020547, baseEnd_3020547] using wordTrace_append hprefix tailTrace_3020547
  have hstable : (prefixWord ++ tailWord_3020547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020547).length < 2 ^ (prefixWord ++ tailWord_3020547).sum := by decide
  have hdescent : baseEnd_3020547 < baseStart_3020547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020554 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_3020554 : Nat := 118140960795 + 3020554 * 2 ^ 59
def prefixEnd_3020554 : Nat := 4983230072969 + 3 ^ 40 * 3020554 * 2
def baseEnd_3020554 : Nat := 516998681620293434094577

theorem tailTrace_3020554 : CollatzResearch.WordTrace tailWord_3020554 prefixEnd_3020554 516998681620293434094577 := by
  unfold tailWord_3020554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27542163774764050599459179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73445770066037468265224477 27542163774764050599459179)
  ·
    refine ⟨41313245662146075899188769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27542163774764050599459179 41313245662146075899188769)
    ·
      refine ⟨30984934246609556924391577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41313245662146075899188769 30984934246609556924391577)
      ·
        refine ⟨23238700684957167693293683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30984934246609556924391577 23238700684957167693293683)
        ·
          refine ⟨34858051027435751539940525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23238700684957167693293683 34858051027435751539940525)
          ·
            refine ⟨13071769135288406827477697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34858051027435751539940525 13071769135288406827477697)
            ·
              refine ⟨9803826851466305120608273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13071769135288406827477697 9803826851466305120608273)
              ·
                refine ⟨7352870138599728840456205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9803826851466305120608273 7352870138599728840456205)
                ·
                  refine ⟨2757326301974898315171077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7352870138599728840456205 2757326301974898315171077)
                  ·
                    refine ⟨516998681620293434094577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757326301974898315171077 516998681620293434094577)
                    ·
                      rfl

theorem cell23_3020554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_3020554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020554 prefixEnd_3020554 := by exact prefixLift 3020554
  have htrace : WordTrace (prefixWord ++ tailWord_3020554) baseStart_3020554 baseEnd_3020554 := by
    simpa [prefixWord, tailWord_3020554, baseEnd_3020554] using wordTrace_append hprefix tailTrace_3020554
  have hstable : (prefixWord ++ tailWord_3020554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020554).length < 2 ^ (prefixWord ++ tailWord_3020554).sum := by decide
  have hdescent : baseEnd_3020554 < baseStart_3020554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020567 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 8]
def baseStart_3020567 : Nat := 118140960795 + 3020567 * 2 ^ 59
def prefixEnd_3020567 : Nat := 4983230072969 + 3 ^ 40 * 3020567 * 2
def baseEnd_3020567 : Nat := 172333635567709861269019

theorem tailTrace_3020567 : CollatzResearch.WordTrace tailWord_3020567 prefixEnd_3020567 172333635567709861269019 := by
  unfold tailWord_3020567
  simp only [CollatzResearch.WordTrace]
  refine ⟨110169129248009105618059955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73446086165339403745373303 110169129248009105618059955)
  ·
    refine ⟨165253693872013658427089933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110169129248009105618059955 165253693872013658427089933)
    ·
      refine ⟨61970135202005121910158725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165253693872013658427089933 61970135202005121910158725)
      ·
        refine ⟨11619400350375960358154761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61970135202005121910158725 11619400350375960358154761)
        ·
          refine ⟨8714550262781970268616071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11619400350375960358154761 8714550262781970268616071)
          ·
            refine ⟨13071825394172955402924107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8714550262781970268616071 13071825394172955402924107)
            ·
              refine ⟨19607738091259433104386161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13071825394172955402924107 19607738091259433104386161)
              ·
                refine ⟨14705803568444574828289621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19607738091259433104386161 14705803568444574828289621)
                ·
                  refine ⟨172333635567709861269019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14705803568444574828289621 172333635567709861269019)
                  ·
                    rfl

theorem cell23_3020567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 8].length) (baseStart_3020567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020567 prefixEnd_3020567 := by exact prefixLift 3020567
  have htrace : WordTrace (prefixWord ++ tailWord_3020567) baseStart_3020567 baseEnd_3020567 := by
    simpa [prefixWord, tailWord_3020567, baseEnd_3020567] using wordTrace_append hprefix tailTrace_3020567
  have hstable : (prefixWord ++ tailWord_3020567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020567).length < 2 ^ (prefixWord ++ tailWord_3020567).sum := by decide
  have hdescent : baseEnd_3020567 < baseStart_3020567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020588 : List Nat := [2, 2, 1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_3020588 : Nat := 118140960795 + 3020588 * 2 ^ 59
def prefixEnd_3020588 : Nat := 4983230072969 + 3 ^ 40 * 3020588 * 2
def baseEnd_3020588 : Nat := 517004501067711056419525

theorem tailTrace_3020588 : CollatzResearch.WordTrace tailWord_3020588 prefixEnd_3020588 517004501067711056419525 := by
  unfold tailWord_3020588
  simp only [CollatzResearch.WordTrace]
  refine ⟨55084947590466513102287209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73446596787288684136382945 55084947590466513102287209)
  ·
    refine ⟨41313710692849884826715407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55084947590466513102287209 41313710692849884826715407)
    ·
      refine ⟨61970566039274827240073111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41313710692849884826715407 61970566039274827240073111)
      ·
        refine ⟨92955849058912240860109667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61970566039274827240073111 92955849058912240860109667)
        ·
          refine ⟨139433773588368361290164501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92955849058912240860109667 139433773588368361290164501)
          ·
            refine ⟨6535958136954766935476461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139433773588368361290164501 6535958136954766935476461)
            ·
              refine ⟨2450984301358037600803673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6535958136954766935476461 2450984301358037600803673)
              ·
                refine ⟨1838238226018528200602755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2450984301358037600803673 1838238226018528200602755)
                ·
                  refine ⟨2757357339027792300904133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838238226018528200602755 2757357339027792300904133)
                  ·
                    refine ⟨517004501067711056419525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757357339027792300904133 517004501067711056419525)
                    ·
                      rfl

theorem cell23_3020588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_3020588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020588 prefixEnd_3020588 := by exact prefixLift 3020588
  have htrace : WordTrace (prefixWord ++ tailWord_3020588) baseStart_3020588 baseEnd_3020588 := by
    simpa [prefixWord, tailWord_3020588, baseEnd_3020588] using wordTrace_append hprefix tailTrace_3020588
  have hstable : (prefixWord ++ tailWord_3020588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020588).length < 2 ^ (prefixWord ++ tailWord_3020588).sum := by decide
  have hdescent : baseEnd_3020588 < baseStart_3020588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020601 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 6]
def baseStart_3020601 : Nat := 118140960795 + 3020601 * 2 ^ 59
def prefixEnd_3020601 : Nat := 4983230072969 + 3 ^ 40 * 3020601 * 2
def baseEnd_3020601 : Nat := 172335575383515735377335

theorem tailTrace_3020601 : CollatzResearch.WordTrace tailWord_3020601 prefixEnd_3020601 172335575383515735377335 := by
  unfold tailWord_3020601
  simp only [CollatzResearch.WordTrace]
  refine ⟨110170369329885929424797657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73446912886590619616531771 110170369329885929424797657)
  ·
    refine ⟨82627776997414447068598243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110170369329885929424797657 82627776997414447068598243)
    ·
      refine ⟨123941665496121670602897365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82627776997414447068598243 123941665496121670602897365)
      ·
        refine ⟨2904882785065351654755407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 123941665496121670602897365 2904882785065351654755407)
        ·
          refine ⟨4357324177598027482133111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2904882785065351654755407 4357324177598027482133111)
          ·
            refine ⟨6535986266397041223199667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357324177598027482133111 6535986266397041223199667)
            ·
              refine ⟨9803979399595561834799501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6535986266397041223199667 9803979399595561834799501)
              ·
                refine ⟨3676492274848335688049813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9803979399595561834799501 3676492274848335688049813)
                ·
                  refine ⟨172335575383515735377335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3676492274848335688049813 172335575383515735377335)
                  ·
                    rfl

theorem cell23_3020601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 6].length) (baseStart_3020601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020601 prefixEnd_3020601 := by exact prefixLift 3020601
  have htrace : WordTrace (prefixWord ++ tailWord_3020601) baseStart_3020601 baseEnd_3020601 := by
    simpa [prefixWord, tailWord_3020601, baseEnd_3020601] using wordTrace_append hprefix tailTrace_3020601
  have hstable : (prefixWord ++ tailWord_3020601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020601).length < 2 ^ (prefixWord ++ tailWord_3020601).sum := by decide
  have hdescent : baseEnd_3020601 < baseStart_3020601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020604 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_3020604 : Nat := 118140960795 + 3020604 * 2 ^ 59
def prefixEnd_3020604 : Nat := 4983230072969 + 3 ^ 40 * 3020604 * 2
def baseEnd_3020604 : Nat := 1551021718893605106658501

theorem tailTrace_3020604 : CollatzResearch.WordTrace tailWord_3020604 prefixEnd_3020604 1551021718893605106658501 := by
  unfold tailWord_3020604
  simp only [CollatzResearch.WordTrace]
  refine ⟨55085239374437530468578433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73446985832583373958104577 55085239374437530468578433)
  ·
    refine ⟨41313929530828147851433825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55085239374437530468578433 41313929530828147851433825)
    ·
      refine ⟨30985447148121110888575369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41313929530828147851433825 30985447148121110888575369)
      ·
        refine ⟨23239085361090833166431527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30985447148121110888575369 23239085361090833166431527)
        ·
          refine ⟨34858628041636249749647291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23239085361090833166431527 34858628041636249749647291)
          ·
            refine ⟨52287942062454374624470937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34858628041636249749647291 52287942062454374624470937)
            ·
              refine ⟨39215956546840780968353203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52287942062454374624470937 39215956546840780968353203)
              ·
                refine ⟨58823934820261171452529805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39215956546840780968353203 58823934820261171452529805)
                ·
                  refine ⟨22058975557597939294698677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58823934820261171452529805 22058975557597939294698677)
                  ·
                    refine ⟨2068028958524806808878001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22058975557597939294698677 2068028958524806808878001)
                    ·
                      refine ⟨1551021718893605106658501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068028958524806808878001 1551021718893605106658501)
                      ·
                        rfl

theorem cell23_3020604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_3020604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020604 prefixEnd_3020604 := by exact prefixLift 3020604
  have htrace : WordTrace (prefixWord ++ tailWord_3020604) baseStart_3020604 baseEnd_3020604 := by
    simpa [prefixWord, tailWord_3020604, baseEnd_3020604] using wordTrace_append hprefix tailTrace_3020604
  have hstable : (prefixWord ++ tailWord_3020604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020604).length < 2 ^ (prefixWord ++ tailWord_3020604).sum := by decide
  have hdescent : baseEnd_3020604 < baseStart_3020604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020651 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 3, 2, 2]
def baseStart_3020651 : Nat := 118140960795 + 3020651 * 2 ^ 59
def prefixEnd_3020651 : Nat := 4983230072969 + 3 ^ 40 * 3020651 * 2
def baseEnd_3020651 : Nat := 1551045852484366422770785

theorem tailTrace_3020651 : CollatzResearch.WordTrace tailWord_3020651 prefixEnd_3020651 1551045852484366422770785 := by
  unfold tailWord_3020651
  simp only [CollatzResearch.WordTrace]
  refine ⟨110172192979704787964117807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73448128653136525309411871 110172192979704787964117807)
  ·
    refine ⟨165258289469557181946176711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110172192979704787964117807 165258289469557181946176711)
    ·
      refine ⟨247887434204335772919265067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165258289469557181946176711 247887434204335772919265067)
      ·
        refine ⟨371831151306503659378897601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247887434204335772919265067 371831151306503659378897601)
        ·
          refine ⟨278873363479877744534173201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371831151306503659378897601 278873363479877744534173201)
          ·
            refine ⟨209155022609908308400629901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278873363479877744534173201 209155022609908308400629901)
            ·
              refine ⟨78433133478715615650236213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209155022609908308400629901 78433133478715615650236213)
              ·
                refine ⟨7353106263629588967209645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78433133478715615650236213 7353106263629588967209645)
                ·
                  refine ⟨2757414848861095862703617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7353106263629588967209645 2757414848861095862703617)
                  ·
                    refine ⟨2068061136645821897027713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2757414848861095862703617 2068061136645821897027713)
                    ·
                      refine ⟨1551045852484366422770785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068061136645821897027713 1551045852484366422770785)
                      ·
                        rfl

theorem cell23_3020651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 2, 2].length) (baseStart_3020651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020651 prefixEnd_3020651 := by exact prefixLift 3020651
  have htrace : WordTrace (prefixWord ++ tailWord_3020651) baseStart_3020651 baseEnd_3020651 := by
    simpa [prefixWord, tailWord_3020651, baseEnd_3020651] using wordTrace_append hprefix tailTrace_3020651
  have hstable : (prefixWord ++ tailWord_3020651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020651).length < 2 ^ (prefixWord ++ tailWord_3020651).sum := by decide
  have hdescent : baseEnd_3020651 < baseStart_3020651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020661 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3020661 : Nat := 118140960795 + 3020661 * 2 ^ 59
def prefixEnd_3020661 : Nat := 4983230072969 + 3 ^ 40 * 3020661 * 2
def baseEnd_3020661 : Nat := 517016995763637127881913

theorem tailTrace_3020661 : CollatzResearch.WordTrace tailWord_3020661 prefixEnd_3020661 517016995763637127881913 := by
  unfold tailWord_3020661
  simp only [CollatzResearch.WordTrace]
  refine ⟨110172557709668559671981837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73448371806445706447987891 110172557709668559671981837)
  ·
    refine ⟨41314709141125709876993189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110172557709668559671981837 41314709141125709876993189)
    ·
      refine ⟨7746507963961070601936223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41314709141125709876993189 7746507963961070601936223)
      ·
        refine ⟨11619761945941605902904335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7746507963961070601936223 11619761945941605902904335)
        ·
          refine ⟨17429642918912408854356503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11619761945941605902904335 17429642918912408854356503)
          ·
            refine ⟨26144464378368613281534755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17429642918912408854356503 26144464378368613281534755)
            ·
              refine ⟨39216696567552919922302133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26144464378368613281534755 39216696567552919922302133)
              ·
                refine ⟨3676565303208086242715825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39216696567552919922302133 3676565303208086242715825)
                ·
                  refine ⟨2757423977406064682036869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676565303208086242715825 2757423977406064682036869)
                  ·
                    refine ⟨517016995763637127881913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757423977406064682036869 517016995763637127881913)
                    ·
                      rfl

theorem cell23_3020661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3020661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020661 prefixEnd_3020661 := by exact prefixLift 3020661
  have htrace : WordTrace (prefixWord ++ tailWord_3020661) baseStart_3020661 baseEnd_3020661 := by
    simpa [prefixWord, tailWord_3020661, baseEnd_3020661] using wordTrace_append hprefix tailTrace_3020661
  have hstable : (prefixWord ++ tailWord_3020661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020661).length < 2 ^ (prefixWord ++ tailWord_3020661).sum := by decide
  have hdescent : baseEnd_3020661 < baseStart_3020661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020712 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3020712 : Nat := 118140960795 + 3020712 * 2 ^ 59
def prefixEnd_3020712 : Nat := 4983230072969 + 3 ^ 40 * 3020712 * 2
def baseEnd_3020712 : Nat := 517025724934763561369335

theorem tailTrace_3020712 : CollatzResearch.WordTrace tailWord_3020712 prefixEnd_3020712 517025724934763561369335 := by
  unfold tailWord_3020712
  simp only [CollatzResearch.WordTrace]
  refine ⟨55087208916241897691044195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73449611888322530254725593 55087208916241897691044195)
  ·
    refine ⟨82630813374362846536566293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55087208916241897691044195 82630813374362846536566293)
    ·
      refine ⟨3873319376923258431401545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82630813374362846536566293 3873319376923258431401545)
      ·
        refine ⟨2904989532692443823551159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3873319376923258431401545 2904989532692443823551159)
        ·
          refine ⟨4357484299038665735326739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2904989532692443823551159 4357484299038665735326739)
          ·
            refine ⟨6536226448557998602990109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357484299038665735326739 6536226448557998602990109)
            ·
              refine ⟨2451084918209249476121291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6536226448557998602990109 2451084918209249476121291)
              ·
                refine ⟨3676627377313874214181937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451084918209249476121291 3676627377313874214181937)
                ·
                  refine ⟨2757470532985405660636453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676627377313874214181937 2757470532985405660636453)
                  ·
                    refine ⟨517025724934763561369335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757470532985405660636453 517025724934763561369335)
                    ·
                      rfl

theorem cell23_3020712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3020712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020712 prefixEnd_3020712 := by exact prefixLift 3020712
  have htrace : WordTrace (prefixWord ++ tailWord_3020712) baseStart_3020712 baseEnd_3020712 := by
    simpa [prefixWord, tailWord_3020712, baseEnd_3020712] using wordTrace_append hprefix tailTrace_3020712
  have hstable : (prefixWord ++ tailWord_3020712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020712).length < 2 ^ (prefixWord ++ tailWord_3020712).sum := by decide
  have hdescent : baseEnd_3020712 < baseStart_3020712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020728 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 1, 3, 2]
def baseStart_3020728 : Nat := 118140960795 + 3020728 * 2 ^ 59
def prefixEnd_3020728 : Nat := 4983230072969 + 3 ^ 40 * 3020728 * 2
def baseEnd_3020728 : Nat := 1551085390494762621507931

theorem tailTrace_3020728 : CollatzResearch.WordTrace tailWord_3020728 prefixEnd_3020728 1551085390494762621507931 := by
  unfold tailWord_3020728
  simp only [CollatzResearch.WordTrace]
  refine ⟨55087500700212915057335419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73450000933617220076447225 55087500700212915057335419)
  ·
    refine ⟨82631251050319372586003129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55087500700212915057335419 82631251050319372586003129)
    ·
      refine ⟨61973438287739529439502347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82631251050319372586003129 61973438287739529439502347)
      ·
        refine ⟨92960157431609294159253521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61973438287739529439502347 92960157431609294159253521)
        ·
          refine ⟨69720118073706970619440141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92960157431609294159253521 69720118073706970619440141)
          ·
            refine ⟨26145044277640113982290053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69720118073706970619440141 26145044277640113982290053)
            ·
              refine ⟨4902195802057521371679385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26145044277640113982290053 4902195802057521371679385)
              ·
                refine ⟨3676646851543141028759539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4902195802057521371679385 3676646851543141028759539)
                ·
                  refine ⟨5514970277314711543139309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676646851543141028759539 5514970277314711543139309)
                  ·
                    refine ⟨2068113853993016828677241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5514970277314711543139309 2068113853993016828677241)
                    ·
                      refine ⟨1551085390494762621507931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068113853993016828677241 1551085390494762621507931)
                      ·
                        rfl

theorem cell23_3020728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_3020728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020728 prefixEnd_3020728 := by exact prefixLift 3020728
  have htrace : WordTrace (prefixWord ++ tailWord_3020728) baseStart_3020728 baseEnd_3020728 := by
    simpa [prefixWord, tailWord_3020728, baseEnd_3020728] using wordTrace_append hprefix tailTrace_3020728
  have hstable : (prefixWord ++ tailWord_3020728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020728).length < 2 ^ (prefixWord ++ tailWord_3020728).sum := by decide
  have hdescent : baseEnd_3020728 < baseStart_3020728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020744 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3020744 : Nat := 118140960795 + 3020744 * 2 ^ 59
def prefixEnd_3020744 : Nat := 4983230072969 + 3 ^ 40 * 3020744 * 2
def baseEnd_3020744 : Nat := 1551093606185234558907857

theorem tailTrace_3020744 : CollatzResearch.WordTrace tailWord_3020744 prefixEnd_3020744 1551093606185234558907857 := by
  unfold tailWord_3020744
  simp only [CollatzResearch.WordTrace]
  refine ⟨55087792484183932423626643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73450389978911909898168857 55087792484183932423626643)
  ·
    refine ⟨82631688726275898635439965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55087792484183932423626643 82631688726275898635439965)
    ·
      refine ⟨30986883272353461988289987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82631688726275898635439965 30986883272353461988289987)
      ·
        refine ⟨46480324908530192982434981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30986883272353461988289987 46480324908530192982434981)
        ·
          refine ⟨8715060920349411184206559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46480324908530192982434981 8715060920349411184206559)
          ·
            refine ⟨13072591380524116776309839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8715060920349411184206559 13072591380524116776309839)
            ·
              refine ⟨19608887070786175164464759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13072591380524116776309839 19608887070786175164464759)
              ·
                refine ⟨29413330606179262746697139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19608887070786175164464759 29413330606179262746697139)
                ·
                  refine ⟨44119995909268894120045709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29413330606179262746697139 44119995909268894120045709)
                  ·
                    refine ⟨16544998465975835295017141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44119995909268894120045709 16544998465975835295017141)
                    ·
                      refine ⟨1551093606185234558907857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16544998465975835295017141 1551093606185234558907857)
                      ·
                        rfl

theorem cell23_3020744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3020744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020744 prefixEnd_3020744 := by exact prefixLift 3020744
  have htrace : WordTrace (prefixWord ++ tailWord_3020744) baseStart_3020744 baseEnd_3020744 := by
    simpa [prefixWord, tailWord_3020744, baseEnd_3020744] using wordTrace_append hprefix tailTrace_3020744
  have hstable : (prefixWord ++ tailWord_3020744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020744).length < 2 ^ (prefixWord ++ tailWord_3020744).sum := by decide
  have hdescent : baseEnd_3020744 < baseStart_3020744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020844 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_3020844 : Nat := 118140960795 + 3020844 * 2 ^ 59
def prefixEnd_3020844 : Nat := 4983230072969 + 3 ^ 40 * 3020844 * 2
def baseEnd_3020844 : Nat := 1551144954250684167657397

theorem tailTrace_3020844 : CollatzResearch.WordTrace tailWord_3020844 prefixEnd_3020844 1551144954250684167657397 := by
  unfold tailWord_3020844
  simp only [CollatzResearch.WordTrace]
  refine ⟨55089616134002790962946793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73452821512003721283929057 55089616134002790962946793)
  ·
    refine ⟨41317212100502093222210095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55089616134002790962946793 41317212100502093222210095)
    ·
      refine ⟨61975818150753139833315143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41317212100502093222210095 61975818150753139833315143)
      ·
        refine ⟨92963727226129709749972715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61975818150753139833315143 92963727226129709749972715)
        ·
          refine ⟨139445590839194564624959073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92963727226129709749972715 139445590839194564624959073)
          ·
            refine ⟨104584193129395923468719305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139445590839194564624959073 104584193129395923468719305)
            ·
              refine ⟨78438144847046942601539479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104584193129395923468719305 78438144847046942601539479)
              ·
                refine ⟨117657217270570413902309219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78438144847046942601539479 117657217270570413902309219)
                ·
                  refine ⟨176485825905855620853463829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117657217270570413902309219 176485825905855620853463829)
                  ·
                    refine ⟨8272773089336982227506117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 176485825905855620853463829 8272773089336982227506117)
                    ·
                      refine ⟨1551144954250684167657397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8272773089336982227506117 1551144954250684167657397)
                      ·
                        rfl

theorem cell23_3020844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_3020844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020844 prefixEnd_3020844 := by exact prefixLift 3020844
  have htrace : WordTrace (prefixWord ++ tailWord_3020844) baseStart_3020844 baseEnd_3020844 := by
    simpa [prefixWord, tailWord_3020844, baseEnd_3020844] using wordTrace_append hprefix tailTrace_3020844
  have hstable : (prefixWord ++ tailWord_3020844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020844).length < 2 ^ (prefixWord ++ tailWord_3020844).sum := by decide
  have hdescent : baseEnd_3020844 < baseStart_3020844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020848 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 4]
def baseStart_3020848 : Nat := 118140960795 + 3020848 * 2 ^ 59
def prefixEnd_3020848 : Nat := 4983230072969 + 3 ^ 40 * 3020848 * 2
def baseEnd_3020848 : Nat := 1551147008173302152007379

theorem tailTrace_3020848 : CollatzResearch.WordTrace tailWord_3020848 prefixEnd_3020848 1551147008173302152007379 := by
  unfold tailWord_3020848
  simp only [CollatzResearch.WordTrace]
  refine ⟨55089689079995545304519599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73452918773327393739359465 55089689079995545304519599)
  ·
    refine ⟨82634533619993317956779399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55089689079995545304519599 82634533619993317956779399)
    ·
      refine ⟨123951800429989976935169099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82634533619993317956779399 123951800429989976935169099)
      ·
        refine ⟨185927700644984965402753649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123951800429989976935169099 185927700644984965402753649)
        ·
          refine ⟨139445775483738724052065237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185927700644984965402753649 139445775483738724052065237)
          ·
            refine ⟨3268260362900126344970279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 139445775483738724052065237 3268260362900126344970279)
            ·
              refine ⟨4902390544350189517455419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268260362900126344970279 4902390544350189517455419)
              ·
                refine ⟨7353585816525284276183129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4902390544350189517455419 7353585816525284276183129)
                ·
                  refine ⟨5515189362393963207137347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7353585816525284276183129 5515189362393963207137347)
                  ·
                    refine ⟨8272784043590944810706021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5515189362393963207137347 8272784043590944810706021)
                    ·
                      refine ⟨1551147008173302152007379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8272784043590944810706021 1551147008173302152007379)
                      ·
                        rfl

theorem cell23_3020848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 4].length) (baseStart_3020848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020848 prefixEnd_3020848 := by exact prefixLift 3020848
  have htrace : WordTrace (prefixWord ++ tailWord_3020848) baseStart_3020848 baseEnd_3020848 := by
    simpa [prefixWord, tailWord_3020848, baseEnd_3020848] using wordTrace_append hprefix tailTrace_3020848
  have hstable : (prefixWord ++ tailWord_3020848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020848).length < 2 ^ (prefixWord ++ tailWord_3020848).sum := by decide
  have hdescent : baseEnd_3020848 < baseStart_3020848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020888 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 6]
def baseStart_3020888 : Nat := 118140960795 + 3020888 * 2 ^ 59
def prefixEnd_3020888 : Nat := 4983230072969 + 3 ^ 40 * 3020888 * 2
def baseEnd_3020888 : Nat := 172351949711053555056355

theorem tailTrace_3020888 : CollatzResearch.WordTrace tailWord_3020888 prefixEnd_3020888 172351949711053555056355 := by
  unfold tailWord_3020888
  simp only [CollatzResearch.WordTrace]
  refine ⟨55090418539923088720247659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73453891386564118293663545 55090418539923088720247659)
  ·
    refine ⟨82635627809884633080371489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55090418539923088720247659 82635627809884633080371489)
    ·
      refine ⟨61976720857413474810278617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82635627809884633080371489 61976720857413474810278617)
      ·
        refine ⟨46482540643060106107708963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61976720857413474810278617 46482540643060106107708963)
        ·
          refine ⟨69723810964590159161563445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46482540643060106107708963 69723810964590159161563445)
          ·
            refine ⟨6536607277930327421396573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69723810964590159161563445 6536607277930327421396573)
            ·
              refine ⟨2451227729223872783023715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6536607277930327421396573 2451227729223872783023715)
              ·
                refine ⟨3676841593835809174535573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451227729223872783023715 3676841593835809174535573)
                ·
                  refine ⟨172351949711053555056355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3676841593835809174535573 172351949711053555056355)
                  ·
                    rfl

theorem cell23_3020888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 6].length) (baseStart_3020888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020888 prefixEnd_3020888 := by exact prefixLift 3020888
  have htrace : WordTrace (prefixWord ++ tailWord_3020888) baseStart_3020888 baseEnd_3020888 := by
    simpa [prefixWord, tailWord_3020888, baseEnd_3020888] using wordTrace_append hprefix tailTrace_3020888
  have hstable : (prefixWord ++ tailWord_3020888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020888).length < 2 ^ (prefixWord ++ tailWord_3020888).sum := by decide
  have hdescent : baseEnd_3020888 < baseStart_3020888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020908 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 1, 5, 2]
def baseStart_3020908 : Nat := 118140960795 + 3020908 * 2 ^ 59
def prefixEnd_3020908 : Nat := 4983230072969 + 3 ^ 40 * 3020908 * 2
def baseEnd_3020908 : Nat := 1551177817012571917257103

theorem tailTrace_3020908 : CollatzResearch.WordTrace tailWord_3020908 prefixEnd_3020908 1551177817012571917257103 := by
  unfold tailWord_3020908
  simp only [CollatzResearch.WordTrace]
  refine ⟨55090783269886860428111689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73454377693182480570815585 55090783269886860428111689)
  ·
    refine ⟨41318087452415145321083767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55090783269886860428111689 41318087452415145321083767)
    ·
      refine ⟨61977131178622717981625651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41318087452415145321083767 61977131178622717981625651)
      ·
        refine ⟨92965696767934076972438477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61977131178622717981625651 92965696767934076972438477)
        ·
          refine ⟨34862136287975278864664429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92965696767934076972438477 34862136287975278864664429)
          ·
            refine ⟨13073301107990729574249161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34862136287975278864664429 13073301107990729574249161)
            ·
              refine ⟨9804975830993047180686871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13073301107990729574249161 9804975830993047180686871)
              ·
                refine ⟨14707463746489570771030307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9804975830993047180686871 14707463746489570771030307)
                ·
                  refine ⟨22061195619734356156545461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14707463746489570771030307 22061195619734356156545461)
                  ·
                    refine ⟨2068237089350095889676137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22061195619734356156545461 2068237089350095889676137)
                    ·
                      refine ⟨1551177817012571917257103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068237089350095889676137 1551177817012571917257103)
                      ·
                        rfl

theorem cell23_3020908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_3020908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020908 prefixEnd_3020908 := by exact prefixLift 3020908
  have htrace : WordTrace (prefixWord ++ tailWord_3020908) baseStart_3020908 baseEnd_3020908 := by
    simpa [prefixWord, tailWord_3020908, baseEnd_3020908] using wordTrace_append hprefix tailTrace_3020908
  have hstable : (prefixWord ++ tailWord_3020908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020908).length < 2 ^ (prefixWord ++ tailWord_3020908).sum := by decide
  have hdescent : baseEnd_3020908 < baseStart_3020908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020925 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_3020925 : Nat := 118140960795 + 3020925 * 2 ^ 59
def prefixEnd_3020925 : Nat := 4983230072969 + 3 ^ 40 * 3020925 * 2
def baseEnd_3020925 : Nat := 1551186546183698350744525

theorem tailTrace_3020925 : CollatzResearch.WordTrace tailWord_3020925 prefixEnd_3020925 1551186546183698350744525 := by
  unfold tailWord_3020925
  simp only [CollatzResearch.WordTrace]
  refine ⟨110182186580712132759592229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73454791053808088506394819 110182186580712132759592229)
  ·
    refine ⟨20659159983883524892423543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110182186580712132759592229 20659159983883524892423543)
    ·
      refine ⟨30988739975825287338635315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20659159983883524892423543 30988739975825287338635315)
      ·
        refine ⟨46483109963737931007952973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30988739975825287338635315 46483109963737931007952973)
        ·
          refine ⟨17431166236401724127982365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46483109963737931007952973 17431166236401724127982365)
          ·
            refine ⟨6536687338650646547993387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17431166236401724127982365 6536687338650646547993387)
            ·
              refine ⟨9805031007975969821990081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536687338650646547993387 9805031007975969821990081)
              ·
                refine ⟨7353773255981977366492561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9805031007975969821990081 7353773255981977366492561)
                ·
                  refine ⟨5515329941986483024869421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7353773255981977366492561 5515329941986483024869421)
                  ·
                    refine ⟨2068248728244931134326033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5515329941986483024869421 2068248728244931134326033)
                    ·
                      refine ⟨1551186546183698350744525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068248728244931134326033 1551186546183698350744525)
                      ·
                        rfl

theorem cell23_3020925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_3020925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020925 prefixEnd_3020925 := by exact prefixLift 3020925
  have htrace : WordTrace (prefixWord ++ tailWord_3020925) baseStart_3020925 baseEnd_3020925 := by
    simpa [prefixWord, tailWord_3020925, baseEnd_3020925] using wordTrace_append hprefix tailTrace_3020925
  have hstable : (prefixWord ++ tailWord_3020925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020925).length < 2 ^ (prefixWord ++ tailWord_3020925).sum := by decide
  have hdescent : baseEnd_3020925 < baseStart_3020925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020952 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 1, 5]
def baseStart_3020952 : Nat := 118140960795 + 3020952 * 2 ^ 59
def prefixEnd_3020952 : Nat := 4983230072969 + 3 ^ 40 * 3020952 * 2
def baseEnd_3020952 : Nat := 517066803387123248368967

theorem tailTrace_3020952 : CollatzResearch.WordTrace tailWord_3020952 prefixEnd_3020952 517066803387123248368967 := by
  unfold tailWord_3020952
  simp only [CollatzResearch.WordTrace]
  refine ⟨55091585675807158185412555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73455447567742877580550073 55091585675807158185412555)
  ·
    refine ⟨82637378513710737278118833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55091585675807158185412555 82637378513710737278118833)
    ·
      refine ⟨61978033885283052958589125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82637378513710737278118833 61978033885283052958589125)
      ·
        refine ⟨11620881353490572429735461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61978033885283052958589125 11620881353490572429735461)
        ·
          refine ⟨2178915253779482330575399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11620881353490572429735461 2178915253779482330575399)
          ·
            refine ⟨3268372880669223495863099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178915253779482330575399 3268372880669223495863099)
            ·
              refine ⟨4902559321003835243794649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268372880669223495863099 4902559321003835243794649)
              ·
                refine ⟨3676919490752876432845987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4902559321003835243794649 3676919490752876432845987)
                ·
                  refine ⟨5515379236129314649268981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676919490752876432845987 5515379236129314649268981)
                  ·
                    refine ⟨517066803387123248368967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5515379236129314649268981 517066803387123248368967)
                    ·
                      rfl

theorem cell23_3020952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_3020952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020952 prefixEnd_3020952 := by exact prefixLift 3020952
  have htrace : WordTrace (prefixWord ++ tailWord_3020952) baseStart_3020952 baseEnd_3020952 := by
    simpa [prefixWord, tailWord_3020952, baseEnd_3020952] using wordTrace_append hprefix tailTrace_3020952
  have hstable : (prefixWord ++ tailWord_3020952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020952).length < 2 ^ (prefixWord ++ tailWord_3020952).sum := by decide
  have hdescent : baseEnd_3020952 < baseStart_3020952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3020961 : List Nat := [1, 2, 3, 3, 1, 2, 2, 9]
def baseStart_3020961 : Nat := 118140960795 + 3020961 * 2 ^ 59
def prefixEnd_3020961 : Nat := 4983230072969 + 3 ^ 40 * 3020961 * 2
def baseEnd_3020961 : Nat := 57452038203231859625717

theorem tailTrace_3020961 : CollatzResearch.WordTrace tailWord_3020961 prefixEnd_3020961 57452038203231859625717 := by
  unfold tailWord_3020961
  simp only [CollatzResearch.WordTrace]
  refine ⟨110183499608581710907902737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73455666405721140605268491 110183499608581710907902737)
  ·
    refine ⟨82637624706436283180927053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110183499608581710907902737 82637624706436283180927053)
    ·
      refine ⟨30989109264913606192847645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82637624706436283180927053 30989109264913606192847645)
      ·
        refine ⟨11620915974342602322317867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30989109264913606192847645 11620915974342602322317867)
        ·
          refine ⟨17431373961513903483476801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11620915974342602322317867 17431373961513903483476801)
          ·
            refine ⟨13073530471135427612607601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17431373961513903483476801 13073530471135427612607601)
            ·
              refine ⟨9805147853351570709455701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13073530471135427612607601 9805147853351570709455701)
              ·
                refine ⟨57452038203231859625717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9805147853351570709455701 57452038203231859625717)
                ·
                  rfl

theorem cell23_3020961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 9].length) (baseStart_3020961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3020961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3020961 prefixEnd_3020961 := by exact prefixLift 3020961
  have htrace : WordTrace (prefixWord ++ tailWord_3020961) baseStart_3020961 baseEnd_3020961 := by
    simpa [prefixWord, tailWord_3020961, baseEnd_3020961] using wordTrace_append hprefix tailTrace_3020961
  have hstable : (prefixWord ++ tailWord_3020961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3020961).length < 2 ^ (prefixWord ++ tailWord_3020961).sum := by decide
  have hdescent : baseEnd_3020961 < baseStart_3020961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3020961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021015 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 1, 3, 2]
def baseStart_3021015 : Nat := 118140960795 + 3021015 * 2 ^ 59
def prefixEnd_3021015 : Nat := 4983230072969 + 3 ^ 40 * 3021015 * 2
def baseEnd_3021015 : Nat := 1551232759442602998619111

theorem tailTrace_3021015 : CollatzResearch.WordTrace tailWord_3021015 prefixEnd_3021015 1551232759442602998619111 := by
  unfold tailWord_3021015
  simp only [CollatzResearch.WordTrace]
  refine ⟨110185469150386078130368499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73456979433590718753578999 110185469150386078130368499)
  ·
    refine ⟨165278203725579117195552749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110185469150386078130368499 165278203725579117195552749)
    ·
      refine ⟨61979326397092168948332281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165278203725579117195552749 61979326397092168948332281)
      ·
        refine ⟨46484494797819126711249211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61979326397092168948332281 46484494797819126711249211)
        ·
          refine ⟨69726742196728690066873817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46484494797819126711249211 69726742196728690066873817)
          ·
            refine ⟨52295056647546517550155363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69726742196728690066873817 52295056647546517550155363)
            ·
              refine ⟨78442584971319776325233045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52295056647546517550155363 78442584971319776325233045)
              ·
                refine ⟨3676996170530614515245299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78442584971319776325233045 3676996170530614515245299)
                ·
                  refine ⟨5515494255795921772867949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676996170530614515245299 5515494255795921772867949)
                  ·
                    refine ⟨2068310345923470664825481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5515494255795921772867949 2068310345923470664825481)
                    ·
                      refine ⟨1551232759442602998619111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068310345923470664825481 1551232759442602998619111)
                      ·
                        rfl

theorem cell23_3021015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_3021015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021015 prefixEnd_3021015 := by exact prefixLift 3021015
  have htrace : WordTrace (prefixWord ++ tailWord_3021015) baseStart_3021015 baseEnd_3021015 := by
    simpa [prefixWord, tailWord_3021015, baseEnd_3021015] using wordTrace_append hprefix tailTrace_3021015
  have hstable : (prefixWord ++ tailWord_3021015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021015).length < 2 ^ (prefixWord ++ tailWord_3021015).sum := by decide
  have hdescent : baseEnd_3021015 < baseStart_3021015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021026 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3021026 : Nat := 118140960795 + 3021026 * 2 ^ 59
def prefixEnd_3021026 : Nat := 4983230072969 + 3 ^ 40 * 3021026 * 2
def baseEnd_3021026 : Nat := 1551238407729802455581561

theorem tailTrace_3021026 : CollatzResearch.WordTrace tailWord_3021026 prefixEnd_3021026 1551238407729802455581561 := by
  unfold tailWord_3021026
  simp only [CollatzResearch.WordTrace]
  refine ⟨27546467588336556752254733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73457246902230818006012621 27546467588336556752254733)
  ·
    refine ⟨10329925345626208782095525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27546467588336556752254733 10329925345626208782095525)
    ·
      refine ⟨1936861002304914146642911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10329925345626208782095525 1936861002304914146642911)
      ·
        refine ⟨2905291503457371219964367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936861002304914146642911 2905291503457371219964367)
        ·
          refine ⟨4357937255186056829946551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905291503457371219964367 4357937255186056829946551)
          ·
            refine ⟨6536905882779085244919827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357937255186056829946551 6536905882779085244919827)
            ·
              refine ⟨9805358824168627867379741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536905882779085244919827 9805358824168627867379741)
              ·
                refine ⟨3677009559063235450267403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9805358824168627867379741 3677009559063235450267403)
                ·
                  refine ⟨5515514338594853175401105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677009559063235450267403 5515514338594853175401105)
                  ·
                    refine ⟨4136635753946139881550829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5515514338594853175401105 4136635753946139881550829)
                    ·
                      refine ⟨1551238407729802455581561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4136635753946139881550829 1551238407729802455581561)
                      ·
                        rfl

theorem cell23_3021026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3021026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021026 prefixEnd_3021026 := by exact prefixLift 3021026
  have htrace : WordTrace (prefixWord ++ tailWord_3021026) baseStart_3021026 baseEnd_3021026 := by
    simpa [prefixWord, tailWord_3021026, baseEnd_3021026] using wordTrace_append hprefix tailTrace_3021026
  have hstable : (prefixWord ++ tailWord_3021026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021026).length < 2 ^ (prefixWord ++ tailWord_3021026).sum := by decide
  have hdescent : baseEnd_3021026 < baseStart_3021026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021032 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_3021032 : Nat := 118140960795 + 3021032 * 2 ^ 59
def prefixEnd_3021032 : Nat := 4983230072969 + 3 ^ 40 * 3021032 * 2
def baseEnd_3021032 : Nat := 1551241488613729432106533

theorem tailTrace_3021032 : CollatzResearch.WordTrace tailWord_3021032 prefixEnd_3021032 1551241488613729432106533 := by
  unfold tailWord_3021032
  simp only [CollatzResearch.WordTrace]
  refine ⟨55093044595662245016868675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73457392794216326689158233 55093044595662245016868675)
  ·
    refine ⟨82639566893493367525303013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55093044595662245016868675 82639566893493367525303013)
    ·
      refine ⟨15494918792530006410994315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82639566893493367525303013 15494918792530006410994315)
      ·
        refine ⟨23242378188795009616491473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15494918792530006410994315 23242378188795009616491473)
        ·
          refine ⟨17431783641596257212368605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23242378188795009616491473 17431783641596257212368605)
          ·
            refine ⟨6536918865598596454638227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17431783641596257212368605 6536918865598596454638227)
            ·
              refine ⟨9805378298397894681957341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536918865598596454638227 9805378298397894681957341)
              ·
                refine ⟨3677016861899210505734003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9805378298397894681957341 3677016861899210505734003)
                ·
                  refine ⟨5515525292848815758601005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677016861899210505734003 5515525292848815758601005)
                  ·
                    refine ⟨2068321984818305909475377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5515525292848815758601005 2068321984818305909475377)
                    ·
                      refine ⟨1551241488613729432106533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068321984818305909475377 1551241488613729432106533)
                      ·
                        rfl

theorem cell23_3021032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_3021032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021032 prefixEnd_3021032 := by exact prefixLift 3021032
  have htrace : WordTrace (prefixWord ++ tailWord_3021032) baseStart_3021032 baseEnd_3021032 := by
    simpa [prefixWord, tailWord_3021032, baseEnd_3021032] using wordTrace_append hprefix tailTrace_3021032
  have hstable : (prefixWord ++ tailWord_3021032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021032).length < 2 ^ (prefixWord ++ tailWord_3021032).sum := by decide
  have hdescent : baseEnd_3021032 < baseStart_3021032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021155 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 3]
def baseStart_3021155 : Nat := 118140960795 + 3021155 * 2 ^ 59
def prefixEnd_3021155 : Nat := 4983230072969 + 3 ^ 40 * 3021155 * 2
def baseEnd_3021155 : Nat := 1551304646734232450868467

theorem tailTrace_3021155 : CollatzResearch.WordTrace tailWord_3021155 prefixEnd_3021155 1551304646734232450868467 := by
  unfold tailWord_3021155
  simp only [CollatzResearch.WordTrace]
  refine ⟨110190575369878882040464919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73460383579919254693643279 110190575369878882040464919)
  ·
    refine ⟨165285863054818323060697379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110190575369878882040464919 165285863054818323060697379)
    ·
      refine ⟨247928794582227484591046069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165285863054818323060697379 247928794582227484591046069)
      ·
        refine ⟨23243324492083826680410569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247928794582227484591046069 23243324492083826680410569)
        ·
          refine ⟨17432493369062870010307927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23243324492083826680410569 17432493369062870010307927)
          ·
            refine ⟨26148740053594305015461891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17432493369062870010307927 26148740053594305015461891)
            ·
              refine ⟨39223110080391457523192837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26148740053594305015461891 39223110080391457523192837)
              ·
                refine ⟨7354333140073398285598657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39223110080391457523192837 7354333140073398285598657)
                ·
                  refine ⟨5515749855055048714198993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7354333140073398285598657 5515749855055048714198993)
                  ·
                    refine ⟨4136812391291286535649245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5515749855055048714198993 4136812391291286535649245)
                    ·
                      refine ⟨1551304646734232450868467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4136812391291286535649245 1551304646734232450868467)
                      ·
                        rfl

theorem cell23_3021155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_3021155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021155 prefixEnd_3021155 := by exact prefixLift 3021155
  have htrace : WordTrace (prefixWord ++ tailWord_3021155) baseStart_3021155 baseEnd_3021155 := by
    simpa [prefixWord, tailWord_3021155, baseEnd_3021155] using wordTrace_append hprefix tailTrace_3021155
  have hstable : (prefixWord ++ tailWord_3021155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021155).length < 2 ^ (prefixWord ++ tailWord_3021155).sum := by decide
  have hdescent : baseEnd_3021155 < baseStart_3021155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021186 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3021186 : Nat := 118140960795 + 3021186 * 2 ^ 59
def prefixEnd_3021186 : Nat := 4983230072969 + 3 ^ 40 * 3021186 * 2
def baseEnd_3021186 : Nat := 1551320564634521829580825

theorem tailTrace_3021186 : CollatzResearch.WordTrace tailWord_3021186 prefixEnd_3021186 1551320564634521829580825 := by
  unfold tailWord_3021186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27547926508191643583710853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73461137355177716223228941 27547926508191643583710853)
  ·
    refine ⟨5165236220285933171945785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27547926508191643583710853 5165236220285933171945785)
    ·
      refine ⟨3873927165214449878959339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5165236220285933171945785 3873927165214449878959339)
      ·
        refine ⟨5810890747821674818439009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873927165214449878959339 5810890747821674818439009)
        ·
          refine ⟨4358168060866256113829257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5810890747821674818439009 4358168060866256113829257)
          ·
            refine ⟨3268626045649692085371943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4358168060866256113829257 3268626045649692085371943)
            ·
              refine ⟨4902939068474538128057915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268626045649692085371943 4902939068474538128057915)
              ·
                refine ⟨7354408602711807192086873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4902939068474538128057915 7354408602711807192086873)
                ·
                  refine ⟨5515806452033855394065155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7354408602711807192086873 5515806452033855394065155)
                  ·
                    refine ⟨8273709678050783091097733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5515806452033855394065155 8273709678050783091097733)
                    ·
                      refine ⟨1551320564634521829580825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8273709678050783091097733 1551320564634521829580825)
                      ·
                        rfl

theorem cell23_3021186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3021186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021186 prefixEnd_3021186 := by exact prefixLift 3021186
  have htrace : WordTrace (prefixWord ++ tailWord_3021186) baseStart_3021186 baseEnd_3021186 := by
    simpa [prefixWord, tailWord_3021186, baseEnd_3021186] using wordTrace_append hprefix tailTrace_3021186
  have hstable : (prefixWord ++ tailWord_3021186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021186).length < 2 ^ (prefixWord ++ tailWord_3021186).sum := by decide
  have hdescent : baseEnd_3021186 < baseStart_3021186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021219 : List Nat := [1, 1, 1, 4, 1, 4, 2, 4, 1, 1, 3]
def baseStart_3021219 : Nat := 118140960795 + 3021219 * 2 ^ 59
def prefixEnd_3021219 : Nat := 4983230072969 + 3 ^ 40 * 3021219 * 2
def baseEnd_3021219 : Nat := 1551337509496120200468173

theorem tailTrace_3021219 : CollatzResearch.WordTrace tailWord_3021219 prefixEnd_3021219 1551337509496120200468173 := by
  unfold tailWord_3021219
  simp only [CollatzResearch.WordTrace]
  refine ⟨110192909641647020970794711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73461939761098013980529807 110192909641647020970794711)
  ·
    refine ⟨165289364462470531456192067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110192909641647020970794711 165289364462470531456192067)
    ·
      refine ⟨247934046693705797184288101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165289364462470531456192067 247934046693705797184288101)
      ·
        refine ⟨46487633755069836972054019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247934046693705797184288101 46487633755069836972054019)
        ·
          refine ⟨69731450632604755458081029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46487633755069836972054019 69731450632604755458081029)
          ·
            refine ⟨13074646993613391648390193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69731450632604755458081029 13074646993613391648390193)
            ·
              refine ⟨9805985245210043736292645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13074646993613391648390193 9805985245210043736292645)
              ·
                refine ⟨1838622233476883200554871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9805985245210043736292645 1838622233476883200554871)
                ·
                  refine ⟨2757933350215324800832307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838622233476883200554871 2757933350215324800832307)
                  ·
                    refine ⟨4136900025322987201248461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2757933350215324800832307 4136900025322987201248461)
                    ·
                      refine ⟨1551337509496120200468173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4136900025322987201248461 1551337509496120200468173)
                      ·
                        rfl

theorem cell23_3021219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_3021219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021219 prefixEnd_3021219 := by exact prefixLift 3021219
  have htrace : WordTrace (prefixWord ++ tailWord_3021219) baseStart_3021219 baseEnd_3021219 := by
    simpa [prefixWord, tailWord_3021219, baseEnd_3021219] using wordTrace_append hprefix tailTrace_3021219
  have hstable : (prefixWord ++ tailWord_3021219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021219).length < 2 ^ (prefixWord ++ tailWord_3021219).sum := by decide
  have hdescent : baseEnd_3021219 < baseStart_3021219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021326 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_3021326 : Nat := 118140960795 + 3021326 * 2 ^ 59
def prefixEnd_3021326 : Nat := 4983230072969 + 3 ^ 40 * 3021326 * 2
def baseEnd_3021326 : Nat := 1551392451926151281830181

theorem tailTrace_3021326 : CollatzResearch.WordTrace tailWord_3021326 prefixEnd_3021326 1551392451926151281830181 := by
  unfold tailWord_3021326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13774601531532422280617479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73464541501506252163293221 13774601531532422280617479)
  ·
    refine ⟨20661902297298633420926219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13774601531532422280617479 20661902297298633420926219)
    ·
      refine ⟨30992853445947950131389329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20661902297298633420926219 30992853445947950131389329)
      ·
        refine ⟨23244640084460962598541997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30992853445947950131389329 23244640084460962598541997)
        ·
          refine ⟨8716740031672860974453249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23244640084460962598541997 8716740031672860974453249)
          ·
            refine ⟨6537555023754645730839937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8716740031672860974453249 6537555023754645730839937)
            ·
              refine ⟨4903166267815984298129953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6537555023754645730839937 4903166267815984298129953)
              ·
                refine ⟨3677374700861988223597465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4903166267815984298129953 3677374700861988223597465)
                ·
                  refine ⟨2758031025646491167698099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3677374700861988223597465 2758031025646491167698099)
                  ·
                    refine ⟨4137046538469736751547149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2758031025646491167698099 4137046538469736751547149)
                    ·
                      refine ⟨1551392451926151281830181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4137046538469736751547149 1551392451926151281830181)
                      ·
                        rfl

theorem cell23_3021326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_3021326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021326 prefixEnd_3021326 := by exact prefixLift 3021326
  have htrace : WordTrace (prefixWord ++ tailWord_3021326) baseStart_3021326 baseEnd_3021326 := by
    simpa [prefixWord, tailWord_3021326, baseEnd_3021326] using wordTrace_append hprefix tailTrace_3021326
  have hstable : (prefixWord ++ tailWord_3021326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021326).length < 2 ^ (prefixWord ++ tailWord_3021326).sum := by decide
  have hdescent : baseEnd_3021326 < baseStart_3021326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021366 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_3021366 : Nat := 118140960795 + 3021366 * 2 ^ 59
def prefixEnd_3021366 : Nat := 4983230072969 + 3 ^ 40 * 3021366 * 2
def baseEnd_3021366 : Nat := 1551412991152331125329997

theorem tailTrace_3021366 : CollatzResearch.WordTrace tailWord_3021366 prefixEnd_3021366 1551412991152331125329997 := by
  unfold tailWord_3021366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887391948257154067274747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73465514114742976717597301 6887391948257154067274747)
  ·
    refine ⟨10331087922385731100912121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6887391948257154067274747 10331087922385731100912121)
    ·
      refine ⟨7748315941789298325684091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10331087922385731100912121 7748315941789298325684091)
      ·
        refine ⟨11622473912683947488526137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7748315941789298325684091 11622473912683947488526137)
        ·
          refine ⟨8716855434512960616394603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11622473912683947488526137 8716855434512960616394603)
          ·
            refine ⟨13075283151769440924591905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8716855434512960616394603 13075283151769440924591905)
            ·
              refine ⟨9806462363827080693443929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13075283151769440924591905 9806462363827080693443929)
              ·
                refine ⟨7354846772870310520082947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9806462363827080693443929 7354846772870310520082947)
                ·
                  refine ⟨11032270159305465780124421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7354846772870310520082947 11032270159305465780124421)
                  ·
                    refine ⟨2068550654869774833773329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11032270159305465780124421 2068550654869774833773329)
                    ·
                      refine ⟨1551412991152331125329997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068550654869774833773329 1551412991152331125329997)
                      ·
                        rfl

theorem cell23_3021366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_3021366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021366 prefixEnd_3021366 := by exact prefixLift 3021366
  have htrace : WordTrace (prefixWord ++ tailWord_3021366) baseStart_3021366 baseEnd_3021366 := by
    simpa [prefixWord, tailWord_3021366, baseEnd_3021366] using wordTrace_append hprefix tailTrace_3021366
  have hstable : (prefixWord ++ tailWord_3021366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021366).length < 2 ^ (prefixWord ++ tailWord_3021366).sum := by decide
  have hdescent : baseEnd_3021366 < baseStart_3021366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021383 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_3021383 : Nat := 118140960795 + 3021383 * 2 ^ 59
def prefixEnd_3021383 : Nat := 4983230072969 + 3 ^ 40 * 3021383 * 2
def baseEnd_3021383 : Nat := 1551421720323457558817419

theorem tailTrace_3021383 : CollatzResearch.WordTrace tailWord_3021383 prefixEnd_3021383 1551421720323457558817419 := by
  unfold tailWord_3021383
  simp only [CollatzResearch.WordTrace]
  refine ⟨110198891213052876979764803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73465927475368584653176535 110198891213052876979764803)
  ·
    refine ⟨165298336819579315469647205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110198891213052876979764803 165298336819579315469647205)
    ·
      refine ⟨30993438153671121650558851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165298336819579315469647205 30993438153671121650558851)
      ·
        refine ⟨46490157230506682475838277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30993438153671121650558851 46490157230506682475838277)
        ·
          refine ⟨8716904480720002964219677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46490157230506682475838277 8716904480720002964219677)
          ·
            refine ⟨3268839180270001111582379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8716904480720002964219677 3268839180270001111582379)
            ·
              refine ⟨4903258770405001667373569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268839180270001111582379 4903258770405001667373569)
              ·
                refine ⟨3677444077803751250530177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4903258770405001667373569 3677444077803751250530177)
                ·
                  refine ⟨2758083058352813437897633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3677444077803751250530177 2758083058352813437897633)
                  ·
                    refine ⟨2068562293764610078423225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2758083058352813437897633 2068562293764610078423225)
                    ·
                      refine ⟨1551421720323457558817419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068562293764610078423225 1551421720323457558817419)
                      ·
                        rfl

theorem cell23_3021383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_3021383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021383 prefixEnd_3021383 := by exact prefixLift 3021383
  have htrace : WordTrace (prefixWord ++ tailWord_3021383) baseStart_3021383 baseEnd_3021383 := by
    simpa [prefixWord, tailWord_3021383, baseEnd_3021383] using wordTrace_append hprefix tailTrace_3021383
  have hstable : (prefixWord ++ tailWord_3021383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021383).length < 2 ^ (prefixWord ++ tailWord_3021383).sum := by decide
  have hdescent : baseEnd_3021383 < baseStart_3021383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021389 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 7]
def baseStart_3021389 : Nat := 118140960795 + 3021389 * 2 ^ 59
def prefixEnd_3021389 : Nat := 4983230072969 + 3 ^ 40 * 3021389 * 2
def baseEnd_3021389 : Nat := 172380533467487170593599

theorem tailTrace_3021389 : CollatzResearch.WordTrace tailWord_3021389 prefixEnd_3021389 172380533467487170593599 := by
  unfold tailWord_3021389
  simp only [CollatzResearch.WordTrace]
  refine ⟨110199110051031140004483221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73466073367354093336322147 110199110051031140004483221)
  ·
    refine ⟨5165583283642084687710151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110199110051031140004483221 5165583283642084687710151)
    ·
      refine ⟨7748374925463127031565227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5165583283642084687710151 7748374925463127031565227)
      ·
        refine ⟨11622562388194690547347841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7748374925463127031565227 11622562388194690547347841)
        ·
          refine ⟨8716921791146017910510881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11622562388194690547347841 8716921791146017910510881)
          ·
            refine ⟨6537691343359513432883161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8716921791146017910510881 6537691343359513432883161)
            ·
              refine ⟨4903268507519635074662371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6537691343359513432883161 4903268507519635074662371)
              ·
                refine ⟨7354902761279452611993557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903268507519635074662371 7354902761279452611993557)
                ·
                  refine ⟨172380533467487170593599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7354902761279452611993557 172380533467487170593599)
                  ·
                    rfl

theorem cell23_3021389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_3021389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021389 prefixEnd_3021389 := by exact prefixLift 3021389
  have htrace : WordTrace (prefixWord ++ tailWord_3021389) baseStart_3021389 baseEnd_3021389 := by
    simpa [prefixWord, tailWord_3021389, baseEnd_3021389] using wordTrace_append hprefix tailTrace_3021389
  have hstable : (prefixWord ++ tailWord_3021389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021389).length < 2 ^ (prefixWord ++ tailWord_3021389).sum := by decide
  have hdescent : baseEnd_3021389 < baseStart_3021389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021392 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 2, 5, 2]
def baseStart_3021392 : Nat := 118140960795 + 3021392 * 2 ^ 59
def prefixEnd_3021392 : Nat := 4983230072969 + 3 ^ 40 * 3021392 * 2
def baseEnd_3021392 : Nat := 1551426341649348023604877

theorem tailTrace_3021392 : CollatzResearch.WordTrace tailWord_3021392 prefixEnd_3021392 1551426341649348023604877 := by
  unfold tailWord_3021392
  simp only [CollatzResearch.WordTrace]
  refine ⟨55099609735010135758421215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73466146313346847677894953 55099609735010135758421215)
  ·
    refine ⟨82649414602515203637631823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55099609735010135758421215 82649414602515203637631823)
    ·
      refine ⟨123974121903772805456447735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82649414602515203637631823 123974121903772805456447735)
      ·
        refine ⟨185961182855659208184671603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123974121903772805456447735 185961182855659208184671603)
        ·
          refine ⟨278941774283488812277007405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185961182855659208184671603 278941774283488812277007405)
          ·
            refine ⟨104603165356308304603877777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278941774283488812277007405 104603165356308304603877777)
            ·
              refine ⟨78452374017231228452908333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104603165356308304603877777 78452374017231228452908333)
              ·
                refine ⟨29419640256461710669840625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78452374017231228452908333 29419640256461710669840625)
                ·
                  refine ⟨22064730192346283002380469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29419640256461710669840625 22064730192346283002380469)
                  ·
                    refine ⟨2068568455532464031473169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22064730192346283002380469 2068568455532464031473169)
                    ·
                      refine ⟨1551426341649348023604877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068568455532464031473169 1551426341649348023604877)
                      ·
                        rfl

theorem cell23_3021392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 5, 2].length) (baseStart_3021392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021392 prefixEnd_3021392 := by exact prefixLift 3021392
  have htrace : WordTrace (prefixWord ++ tailWord_3021392) baseStart_3021392 baseEnd_3021392 := by
    simpa [prefixWord, tailWord_3021392, baseEnd_3021392] using wordTrace_append hprefix tailTrace_3021392
  have hstable : (prefixWord ++ tailWord_3021392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021392).length < 2 ^ (prefixWord ++ tailWord_3021392).sum := by decide
  have hdescent : baseEnd_3021392 < baseStart_3021392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021415 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 1, 10]
def baseStart_3021415 : Nat := 118140960795 + 3021415 * 2 ^ 59
def prefixEnd_3021415 : Nat := 4983230072969 + 3 ^ 40 * 3021415 * 2
def baseEnd_3021415 : Nat := 517146050568133811205757

theorem tailTrace_3021415 : CollatzResearch.WordTrace tailWord_3021415 prefixEnd_3021415 517146050568133811205757 := by
  unfold tailWord_3021415
  simp only [CollatzResearch.WordTrace]
  refine ⟨110200058348936946444929699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73466705565957964296619799 110200058348936946444929699)
  ·
    refine ⟨165300087523405419667394549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110200058348936946444929699 165300087523405419667394549)
    ·
      refine ⟨15496883205319258093818239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165300087523405419667394549 15496883205319258093818239)
      ·
        refine ⟨23245324807978887140727359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15496883205319258093818239 23245324807978887140727359)
        ·
          refine ⟨34867987211968330711091039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23245324807978887140727359 34867987211968330711091039)
          ·
            refine ⟨52301980817952496066636559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34867987211968330711091039 52301980817952496066636559)
            ·
              refine ⟨78452971226928744099954839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52301980817952496066636559 78452971226928744099954839)
              ·
                refine ⟨117679456840393116149932259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78452971226928744099954839 117679456840393116149932259)
                ·
                  refine ⟨176519185260589674224898389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117679456840393116149932259 176519185260589674224898389)
                  ·
                    refine ⟨517146050568133811205757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 176519185260589674224898389 517146050568133811205757)
                    ·
                      rfl

theorem cell23_3021415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_3021415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021415 prefixEnd_3021415 := by exact prefixLift 3021415
  have htrace : WordTrace (prefixWord ++ tailWord_3021415) baseStart_3021415 baseEnd_3021415 := by
    simpa [prefixWord, tailWord_3021415, baseEnd_3021415] using wordTrace_append hprefix tailTrace_3021415
  have hstable : (prefixWord ++ tailWord_3021415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021415).length < 2 ^ (prefixWord ++ tailWord_3021415).sum := by decide
  have hdescent : baseEnd_3021415 < baseStart_3021415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021425 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_3021425 : Nat := 118140960795 + 3021425 * 2 ^ 59
def prefixEnd_3021425 : Nat := 4983230072969 + 3 ^ 40 * 3021425 * 2
def baseEnd_3021425 : Nat := 1551443286510946394492225

theorem tailTrace_3021425 : CollatzResearch.WordTrace tailWord_3021425 prefixEnd_3021425 1551443286510946394492225 := by
  unfold tailWord_3021425
  simp only [CollatzResearch.WordTrace]
  refine ⟨110200423078900718152793729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73466948719267145435195819 110200423078900718152793729)
  ·
    refine ⟨82650317309175538614595297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110200423078900718152793729 82650317309175538614595297)
    ·
      refine ⟨61987737981881653960946473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82650317309175538614595297 61987737981881653960946473)
      ·
        refine ⟨46490803486411240470709855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61987737981881653960946473 46490803486411240470709855)
        ·
          refine ⟨69736205229616860706064783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46490803486411240470709855 69736205229616860706064783)
          ·
            refine ⟨104604307844425291059097175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69736205229616860706064783 104604307844425291059097175)
            ·
              refine ⟨156906461766637936588645763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104604307844425291059097175 156906461766637936588645763)
              ·
                refine ⟨235359692649956904882968645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156906461766637936588645763 235359692649956904882968645)
                ·
                  refine ⟨44129942371866919665556621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235359692649956904882968645 44129942371866919665556621)
                  ·
                    refine ⟨16548728389450094874583733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44129942371866919665556621 16548728389450094874583733)
                    ·
                      refine ⟨1551443286510946394492225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16548728389450094874583733 1551443286510946394492225)
                      ·
                        rfl

theorem cell23_3021425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_3021425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021425 prefixEnd_3021425 := by exact prefixLift 3021425
  have htrace : WordTrace (prefixWord ++ tailWord_3021425) baseStart_3021425 baseEnd_3021425 := by
    simpa [prefixWord, tailWord_3021425, baseEnd_3021425] using wordTrace_append hprefix tailTrace_3021425
  have hstable : (prefixWord ++ tailWord_3021425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021425).length < 2 ^ (prefixWord ++ tailWord_3021425).sum := by decide
  have hdescent : baseEnd_3021425 < baseStart_3021425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021435 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 6]
def baseStart_3021435 : Nat := 118140960795 + 3021435 * 2 ^ 59
def prefixEnd_3021435 : Nat := 4983230072969 + 3 ^ 40 * 3021435 * 2
def baseEnd_3021435 : Nat := 1551448421317491355367179

theorem tailTrace_3021435 : CollatzResearch.WordTrace tailWord_3021435 prefixEnd_3021435 1551448421317491355367179 := by
  unfold tailWord_3021435
  simp only [CollatzResearch.WordTrace]
  refine ⟨110200787808864489860657759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73467191872576326573771839 110200787808864489860657759)
  ·
    refine ⟨165301181713296734790986639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110200787808864489860657759 165301181713296734790986639)
    ·
      refine ⟨247951772569945102186479959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165301181713296734790986639 247951772569945102186479959)
      ·
        refine ⟨371927658854917653279719939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247951772569945102186479959 371927658854917653279719939)
        ·
          refine ⟨557891488282376479919579909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371927658854917653279719939 557891488282376479919579909)
          ·
            refine ⟨104604654052945589984921233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 557891488282376479919579909 104604654052945589984921233)
            ·
              refine ⟨78453490539709192488690925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104604654052945589984921233 78453490539709192488690925)
              ·
                refine ⟨29420058952390947183259097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78453490539709192488690925 29420058952390947183259097)
                ·
                  refine ⟨22065044214293210387444323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29420058952390947183259097 22065044214293210387444323)
                  ·
                    refine ⟨33097566321439815581166485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22065044214293210387444323 33097566321439815581166485)
                    ·
                      refine ⟨1551448421317491355367179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33097566321439815581166485 1551448421317491355367179)
                      ·
                        rfl

theorem cell23_3021435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_3021435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021435 prefixEnd_3021435 := by exact prefixLift 3021435
  have htrace : WordTrace (prefixWord ++ tailWord_3021435) baseStart_3021435 baseEnd_3021435 := by
    simpa [prefixWord, tailWord_3021435, baseEnd_3021435] using wordTrace_append hprefix tailTrace_3021435
  have hstable : (prefixWord ++ tailWord_3021435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021435).length < 2 ^ (prefixWord ++ tailWord_3021435).sum := by decide
  have hdescent : baseEnd_3021435 < baseStart_3021435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021529 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 4]
def baseStart_3021529 : Nat := 118140960795 + 3021529 * 2 ^ 59
def prefixEnd_3021529 : Nat := 4983230072969 + 3 ^ 40 * 3021529 * 2
def baseEnd_3021529 : Nat := 1551496688499013987591747

theorem tailTrace_3021529 : CollatzResearch.WordTrace tailWord_3021529 prefixEnd_3021529 1551496688499013987591747 := by
  unfold tailWord_3021529
  simp only [CollatzResearch.WordTrace]
  refine ⟨110204216270523943914579641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73469477513682629276386427 110204216270523943914579641)
  ·
    refine ⟨82653162202892957935934731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110204216270523943914579641 82653162202892957935934731)
    ·
      refine ⟨123979743304339436903902097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82653162202892957935934731 123979743304339436903902097)
      ·
        refine ⟨92984807478254577677926573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123979743304339436903902097 92984807478254577677926573)
        ·
          refine ⟨34869302804345466629222465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92984807478254577677926573 34869302804345466629222465)
          ·
            refine ⟨26151977103259099971916849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34869302804345466629222465 26151977103259099971916849)
            ·
              refine ⟨19613982827444324978937637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26151977103259099971916849 19613982827444324978937637)
              ·
                refine ⟨3677621780145810933550807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19613982827444324978937637 3677621780145810933550807)
                ·
                  refine ⟨5516432670218716400326211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677621780145810933550807 5516432670218716400326211)
                  ·
                    refine ⟨8274649005328074600489317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5516432670218716400326211 8274649005328074600489317)
                    ·
                      refine ⟨1551496688499013987591747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8274649005328074600489317 1551496688499013987591747)
                      ·
                        rfl

theorem cell23_3021529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_3021529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021529 prefixEnd_3021529 := by exact prefixLift 3021529
  have htrace : WordTrace (prefixWord ++ tailWord_3021529) baseStart_3021529 baseEnd_3021529 := by
    simpa [prefixWord, tailWord_3021529, baseEnd_3021529] using wordTrace_append hprefix tailTrace_3021529
  have hstable : (prefixWord ++ tailWord_3021529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021529).length < 2 ^ (prefixWord ++ tailWord_3021529).sum := by decide
  have hdescent : baseEnd_3021529 < baseStart_3021529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021539 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 1, 6]
def baseStart_3021539 : Nat := 118140960795 + 3021539 * 2 ^ 59
def prefixEnd_3021539 : Nat := 4983230072969 + 3 ^ 40 * 3021539 * 2
def baseEnd_3021539 : Nat := 517167274435186316155567

theorem tailTrace_3021539 : CollatzResearch.WordTrace tailWord_3021539 prefixEnd_3021539 517167274435186316155567 := by
  unfold tailWord_3021539
  simp only [CollatzResearch.WordTrace]
  refine ⟨110204581000487715622443671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73469720666991810414962447 110204581000487715622443671)
  ·
    refine ⟨165306871500731573433665507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110204581000487715622443671 165306871500731573433665507)
    ·
      refine ⟨247960307251097360150498261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165306871500731573433665507 247960307251097360150498261)
      ·
        refine ⟨5811569701197594378527303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 247960307251097360150498261 5811569701197594378527303)
        ·
          refine ⟨8717354551796391567790955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811569701197594378527303 8717354551796391567790955)
          ·
            refine ⟨13076031827694587351686433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8717354551796391567790955 13076031827694587351686433)
            ·
              refine ⟨9807023870770940513764825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13076031827694587351686433 9807023870770940513764825)
              ·
                refine ⟨7355267903078205385323619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9807023870770940513764825 7355267903078205385323619)
                ·
                  refine ⟨11032901854617308077985429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7355267903078205385323619 11032901854617308077985429)
                  ·
                    refine ⟨517167274435186316155567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11032901854617308077985429 517167274435186316155567)
                    ·
                      rfl

theorem cell23_3021539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 6].length) (baseStart_3021539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021539 prefixEnd_3021539 := by exact prefixLift 3021539
  have htrace : WordTrace (prefixWord ++ tailWord_3021539) baseStart_3021539 baseEnd_3021539 := by
    simpa [prefixWord, tailWord_3021539, baseEnd_3021539] using wordTrace_append hprefix tailTrace_3021539
  have hstable : (prefixWord ++ tailWord_3021539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021539).length < 2 ^ (prefixWord ++ tailWord_3021539).sum := by decide
  have hdescent : baseEnd_3021539 < baseStart_3021539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021546 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_3021546 : Nat := 118140960795 + 3021546 * 2 ^ 59
def prefixEnd_3021546 : Nat := 4983230072969 + 3 ^ 40 * 3021546 * 2
def baseEnd_3021546 : Nat := 1551505417670140421079169

theorem tailTrace_3021546 : CollatzResearch.WordTrace tailWord_3021546 prefixEnd_3021546 1551505417670140421079169 := by
  unfold tailWord_3021546
  simp only [CollatzResearch.WordTrace]
  refine ⟨27551209077865588954487123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73469890874308237211965661 27551209077865588954487123)
  ·
    refine ⟨41326813616798383431730685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27551209077865588954487123 41326813616798383431730685)
    ·
      refine ⟨15497555106299393786899007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41326813616798383431730685 15497555106299393786899007)
      ·
        refine ⟨23246332659449090680348511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15497555106299393786899007 23246332659449090680348511)
        ·
          refine ⟨34869498989173636020522767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23246332659449090680348511 34869498989173636020522767)
          ·
            refine ⟨52304248483760454030784151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34869498989173636020522767 52304248483760454030784151)
            ·
              refine ⟨78456372725640681046176227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52304248483760454030784151 78456372725640681046176227)
              ·
                refine ⟨117684559088461021569264341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78456372725640681046176227 117684559088461021569264341)
                ·
                  refine ⟨2758231853635805193029633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 117684559088461021569264341 2758231853635805193029633)
                  ·
                    refine ⟨2068673890226853894772225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2758231853635805193029633 2068673890226853894772225)
                    ·
                      refine ⟨1551505417670140421079169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068673890226853894772225 1551505417670140421079169)
                      ·
                        rfl

theorem cell23_3021546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_3021546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021546 prefixEnd_3021546 := by exact prefixLift 3021546
  have htrace : WordTrace (prefixWord ++ tailWord_3021546) baseStart_3021546 baseEnd_3021546 := by
    simpa [prefixWord, tailWord_3021546, baseEnd_3021546] using wordTrace_append hprefix tailTrace_3021546
  have hstable : (prefixWord ++ tailWord_3021546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021546).length < 2 ^ (prefixWord ++ tailWord_3021546).sum := by decide
  have hdescent : baseEnd_3021546 < baseStart_3021546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021549 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3021549 : Nat := 118140960795 + 3021549 * 2 ^ 59
def prefixEnd_3021549 : Nat := 4983230072969 + 3 ^ 40 * 3021549 * 2
def baseEnd_3021549 : Nat := 1551506958112103909341655

theorem tailTrace_3021549 : CollatzResearch.WordTrace tailWord_3021549 prefixEnd_3021549 1551506958112103909341655 := by
  unfold tailWord_3021549
  simp only [CollatzResearch.WordTrace]
  refine ⟨110204945730451487330307701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73469963820300991553538467 110204945730451487330307701)
  ·
    refine ⟨10331713662229826937216347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110204945730451487330307701 10331713662229826937216347)
    ·
      refine ⟨15497570493344740405824521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10331713662229826937216347 15497570493344740405824521)
      ·
        refine ⟨11623177870008555304368391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15497570493344740405824521 11623177870008555304368391)
        ·
          refine ⟨17434766805012832956552587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11623177870008555304368391 17434766805012832956552587)
          ·
            refine ⟨26152150207519249434828881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17434766805012832956552587 26152150207519249434828881)
            ·
              refine ⟨19614112655639437076121661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26152150207519249434828881 19614112655639437076121661)
              ·
                refine ⟨7355292245864788903545623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19614112655639437076121661 7355292245864788903545623)
                ·
                  refine ⟨11032938368797183355318435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7355292245864788903545623 11032938368797183355318435)
                  ·
                    refine ⟨16549407553195775032977653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11032938368797183355318435 16549407553195775032977653)
                    ·
                      refine ⟨1551506958112103909341655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16549407553195775032977653 1551506958112103909341655)
                      ·
                        rfl

theorem cell23_3021549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3021549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021549 prefixEnd_3021549 := by exact prefixLift 3021549
  have htrace : WordTrace (prefixWord ++ tailWord_3021549) baseStart_3021549 baseEnd_3021549 := by
    simpa [prefixWord, tailWord_3021549, baseEnd_3021549] using wordTrace_append hprefix tailTrace_3021549
  have hstable : (prefixWord ++ tailWord_3021549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021549).length < 2 ^ (prefixWord ++ tailWord_3021549).sum := by decide
  have hdescent : baseEnd_3021549 < baseStart_3021549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021557 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3021557 : Nat := 118140960795 + 3021557 * 2 ^ 59
def prefixEnd_3021557 : Nat := 4983230072969 + 3 ^ 40 * 3021557 * 2
def baseEnd_3021557 : Nat := 1551511065957339878041619

theorem tailTrace_3021557 : CollatzResearch.WordTrace tailWord_3021557 prefixEnd_3021557 1551511065957339878041619 := by
  unfold tailWord_3021557
  simp only [CollatzResearch.WordTrace]
  refine ⟨110205237514422504696598925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73470158342948336464399283 110205237514422504696598925)
  ·
    refine ⟨41326964067908439261224597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110205237514422504696598925 41326964067908439261224597)
    ·
      refine ⟨1937201440683208090369903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41326964067908439261224597 1937201440683208090369903)
      ·
        refine ⟨2905802161024812135554855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937201440683208090369903 2905802161024812135554855)
        ·
          refine ⟨4358703241537218203332283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905802161024812135554855 4358703241537218203332283)
          ·
            refine ⟨6538054862305827304998425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358703241537218203332283 6538054862305827304998425)
            ·
              refine ⟨4903541146729370478748819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6538054862305827304998425 4903541146729370478748819)
              ·
                refine ⟨7355311720094055718123229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903541146729370478748819 7355311720094055718123229)
                ·
                  refine ⟨2758241895035270894296211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7355311720094055718123229 2758241895035270894296211)
                  ·
                    refine ⟨4137362842552906341444317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2758241895035270894296211 4137362842552906341444317)
                    ·
                      refine ⟨1551511065957339878041619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4137362842552906341444317 1551511065957339878041619)
                      ·
                        rfl

theorem cell23_3021557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3021557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021557 prefixEnd_3021557 := by exact prefixLift 3021557
  have htrace : WordTrace (prefixWord ++ tailWord_3021557) baseStart_3021557 baseEnd_3021557 := by
    simpa [prefixWord, tailWord_3021557, baseEnd_3021557] using wordTrace_append hprefix tailTrace_3021557
  have hstable : (prefixWord ++ tailWord_3021557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021557).length < 2 ^ (prefixWord ++ tailWord_3021557).sum := by decide
  have hdescent : baseEnd_3021557 < baseStart_3021557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021566 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3021566 : Nat := 118140960795 + 3021566 * 2 ^ 59
def prefixEnd_3021566 : Nat := 4983230072969 + 3 ^ 40 * 3021566 * 2
def baseEnd_3021566 : Nat := 1551515687283230342829077

theorem tailTrace_3021566 : CollatzResearch.WordTrace tailWord_3021566 prefixEnd_3021566 1551515687283230342829077 := by
  unfold tailWord_3021566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775695721423737404209569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73470377180926599489117701 13775695721423737404209569)
  ·
    refine ⟨10331771791067803053157177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13775695721423737404209569 10331771791067803053157177)
    ·
      refine ⟨7748828843300852289867883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10331771791067803053157177 7748828843300852289867883)
      ·
        refine ⟨11623243264951278434801825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7748828843300852289867883 11623243264951278434801825)
        ·
          refine ⟨8717432448713458826101369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11623243264951278434801825 8717432448713458826101369)
          ·
            refine ⟨6538074336535094119576027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8717432448713458826101369 6538074336535094119576027)
            ·
              refine ⟨9807111504802641179364041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538074336535094119576027 9807111504802641179364041)
              ·
                refine ⟨7355333628601980884523031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9807111504802641179364041 7355333628601980884523031)
                ·
                  refine ⟨11033000442902971326784547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7355333628601980884523031 11033000442902971326784547)
                  ·
                    refine ⟨16549500664354456990176821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11033000442902971326784547 16549500664354456990176821)
                    ·
                      refine ⟨1551515687283230342829077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16549500664354456990176821 1551515687283230342829077)
                      ·
                        rfl

theorem cell23_3021566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3021566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021566 prefixEnd_3021566 := by exact prefixLift 3021566
  have htrace : WordTrace (prefixWord ++ tailWord_3021566) baseStart_3021566 baseEnd_3021566 := by
    simpa [prefixWord, tailWord_3021566, baseEnd_3021566] using wordTrace_append hprefix tailTrace_3021566
  have hstable : (prefixWord ++ tailWord_3021566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021566).length < 2 ^ (prefixWord ++ tailWord_3021566).sum := by decide
  have hdescent : baseEnd_3021566 < baseStart_3021566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021576 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_3021576 : Nat := 118140960795 + 3021576 * 2 ^ 59
def prefixEnd_3021576 : Nat := 4983230072969 + 3 ^ 40 * 3021576 * 2
def baseEnd_3021576 : Nat := 1551520822089775303704031

theorem tailTrace_3021576 : CollatzResearch.WordTrace tailWord_3021576 prefixEnd_3021576 1551520822089775303704031 := by
  unfold tailWord_3021576
  simp only [CollatzResearch.WordTrace]
  refine ⟨55102965250676835470770291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73470620334235780627693721 55102965250676835470770291)
  ·
    refine ⟨82654447876015253206155437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55102965250676835470770291 82654447876015253206155437)
    ·
      refine ⟨30995417953505719952308289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82654447876015253206155437 30995417953505719952308289)
      ·
        refine ⟨23246563465129289964231217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30995417953505719952308289 23246563465129289964231217)
        ·
          refine ⟨17434922598846967473173413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23246563465129289964231217 17434922598846967473173413)
          ·
            refine ⟨3269047987283806401220015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17434922598846967473173413 3269047987283806401220015)
            ·
              refine ⟨4903571980925709601830023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269047987283806401220015 4903571980925709601830023)
              ·
                refine ⟨7355357971388564402745035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903571980925709601830023 7355357971388564402745035)
                ·
                  refine ⟨11033036957082846604117553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7355357971388564402745035 11033036957082846604117553)
                  ·
                    refine ⟨8274777717812134953088165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11033036957082846604117553 8274777717812134953088165)
                    ·
                      refine ⟨1551520822089775303704031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8274777717812134953088165 1551520822089775303704031)
                      ·
                        rfl

theorem cell23_3021576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_3021576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021576 prefixEnd_3021576 := by exact prefixLift 3021576
  have htrace : WordTrace (prefixWord ++ tailWord_3021576) baseStart_3021576 baseEnd_3021576 := by
    simpa [prefixWord, tailWord_3021576, baseEnd_3021576] using wordTrace_append hprefix tailTrace_3021576
  have hstable : (prefixWord ++ tailWord_3021576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021576).length < 2 ^ (prefixWord ++ tailWord_3021576).sum := by decide
  have hdescent : baseEnd_3021576 < baseStart_3021576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021586 : List Nat := [3, 2, 4, 1, 2, 1, 1, 9]
def baseStart_3021586 : Nat := 118140960795 + 3021586 * 2 ^ 59
def prefixEnd_3021586 : Nat := 4983230072969 + 3 ^ 40 * 3021586 * 2
def baseEnd_3021586 : Nat := 57463924329493343132555

theorem tailTrace_3021586 : CollatzResearch.WordTrace tailWord_3021586 prefixEnd_3021586 57463924329493343132555 := by
  unfold tailWord_3021586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27551573807829360662351153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73470863487544961766269741 27551573807829360662351153)
  ·
    refine ⟨20663680355872020496763365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27551573807829360662351153 20663680355872020496763365)
    ·
      refine ⟨3874440066726003843143131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20663680355872020496763365 3874440066726003843143131)
      ·
        refine ⟨5811660100089005764714697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874440066726003843143131 5811660100089005764714697)
        ·
          refine ⟨4358745075066754323536023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5811660100089005764714697 4358745075066754323536023)
          ·
            refine ⟨6538117612600131485304035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358745075066754323536023 6538117612600131485304035)
            ·
              refine ⟨9807176418900197227956053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538117612600131485304035 9807176418900197227956053)
              ·
                refine ⟨57463924329493343132555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9807176418900197227956053 57463924329493343132555)
                ·
                  rfl

theorem cell23_3021586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 9].length) (baseStart_3021586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021586 prefixEnd_3021586 := by exact prefixLift 3021586
  have htrace : WordTrace (prefixWord ++ tailWord_3021586) baseStart_3021586 baseEnd_3021586 := by
    simpa [prefixWord, tailWord_3021586, baseEnd_3021586] using wordTrace_append hprefix tailTrace_3021586
  have hstable : (prefixWord ++ tailWord_3021586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021586).length < 2 ^ (prefixWord ++ tailWord_3021586).sum := by decide
  have hdescent : baseEnd_3021586 < baseStart_3021586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021596 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_3021596 : Nat := 118140960795 + 3021596 * 2 ^ 59
def prefixEnd_3021596 : Nat := 4983230072969 + 3 ^ 40 * 3021596 * 2
def baseEnd_3021596 : Nat := 1551531091702865225453939

theorem tailTrace_3021596 : CollatzResearch.WordTrace tailWord_3021596 prefixEnd_3021596 1551531091702865225453939 := by
  unfold tailWord_3021596
  simp only [CollatzResearch.WordTrace]
  refine ⟨55103329980640607178634321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73471106640854142904845761 55103329980640607178634321)
  ·
    refine ⟨41327497485480455383975741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55103329980640607178634321 41327497485480455383975741)
    ·
      refine ⟨15497811557055170768990903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41327497485480455383975741 15497811557055170768990903)
      ·
        refine ⟨23246717335582756153486355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15497811557055170768990903 23246717335582756153486355)
        ·
          refine ⟨34870076003374134230229533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23246717335582756153486355 34870076003374134230229533)
          ·
            refine ⟨13076278501265300336336075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34870076003374134230229533 13076278501265300336336075)
            ·
              refine ⟨19614417751897950504504113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13076278501265300336336075 19614417751897950504504113)
              ·
                refine ⟨14710813313923462878378085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19614417751897950504504113 14710813313923462878378085)
                ·
                  refine ⟨2758277496360649289695891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14710813313923462878378085 2758277496360649289695891)
                  ·
                    refine ⟨4137416244540973934543837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2758277496360649289695891 4137416244540973934543837)
                    ·
                      refine ⟨1551531091702865225453939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4137416244540973934543837 1551531091702865225453939)
                      ·
                        rfl

theorem cell23_3021596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_3021596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021596 prefixEnd_3021596 := by exact prefixLift 3021596
  have htrace : WordTrace (prefixWord ++ tailWord_3021596) baseStart_3021596 baseEnd_3021596 := by
    simpa [prefixWord, tailWord_3021596, baseEnd_3021596] using wordTrace_append hprefix tailTrace_3021596
  have hstable : (prefixWord ++ tailWord_3021596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021596).length < 2 ^ (prefixWord ++ tailWord_3021596).sum := by decide
  have hdescent : baseEnd_3021596 < baseStart_3021596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021614 : List Nat := [4, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3021614 : Nat := 118140960795 + 3021614 * 2 ^ 59
def prefixEnd_3021614 : Nat := 4983230072969 + 3 ^ 40 * 3021614 * 2
def baseEnd_3021614 : Nat := 1551540334354646155028857

theorem tailTrace_3021614 : CollatzResearch.WordTrace tailWord_3021614 prefixEnd_3021614 1551540334354646155028857 := by
  unfold tailWord_3021614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775914559402000428927987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73471544316810668954282597 13775914559402000428927987)
  ·
    refine ⟨20663871839103000643391981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13775914559402000428927987 20663871839103000643391981)
    ·
      refine ⟨7748951939663625241271993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20663871839103000643391981 7748951939663625241271993)
      ·
        refine ⟨5811713954747718930953995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7748951939663625241271993 5811713954747718930953995)
        ·
          refine ⟨8717570932121578396430993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811713954747718930953995 8717570932121578396430993)
          ·
            refine ⟨6538178199091183797323245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8717570932121578396430993 6538178199091183797323245)
            ·
              refine ⟨2451816824659193923996217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6538178199091183797323245 2451816824659193923996217)
              ·
                refine ⟨1838862618494395442997163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451816824659193923996217 1838862618494395442997163)
                ·
                  refine ⟨2758293927741593164495745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838862618494395442997163 2758293927741593164495745)
                  ·
                    refine ⟨2068720445806194873371809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2758293927741593164495745 2068720445806194873371809)
                    ·
                      refine ⟨1551540334354646155028857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068720445806194873371809 1551540334354646155028857)
                      ·
                        rfl

theorem cell23_3021614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3021614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021614 prefixEnd_3021614 := by exact prefixLift 3021614
  have htrace : WordTrace (prefixWord ++ tailWord_3021614) baseStart_3021614 baseEnd_3021614 := by
    simpa [prefixWord, tailWord_3021614, baseEnd_3021614] using wordTrace_append hprefix tailTrace_3021614
  have hstable : (prefixWord ++ tailWord_3021614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021614).length < 2 ^ (prefixWord ++ tailWord_3021614).sum := by decide
  have hdescent : baseEnd_3021614 < baseStart_3021614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021630 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3021630 : Nat := 118140960795 + 3021630 * 2 ^ 59
def prefixEnd_3021630 : Nat := 4983230072969 + 3 ^ 40 * 3021630 * 2
def baseEnd_3021630 : Nat := 1551548550045118092428783

theorem tailTrace_3021630 : CollatzResearch.WordTrace tailWord_3021630 prefixEnd_3021630 1551548550045118092428783 := by
  unfold tailWord_3021630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775987505394754770500793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73471933362105358776004229 13775987505394754770500793)
  ·
    refine ⟨10331990629046066077875595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13775987505394754770500793 10331990629046066077875595)
    ·
      refine ⟨15497985943569099116813393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10331990629046066077875595 15497985943569099116813393)
      ·
        refine ⟨11623489457676824337610045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15497985943569099116813393 11623489457676824337610045)
        ·
          refine ⟨4358808546628809126603767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11623489457676824337610045 4358808546628809126603767)
          ·
            refine ⟨6538212819943213689905651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358808546628809126603767 6538212819943213689905651)
            ·
              refine ⟨9807319229914820534858477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538212819943213689905651 9807319229914820534858477)
              ·
                refine ⟨3677744711218057700571929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9807319229914820534858477 3677744711218057700571929)
                ·
                  refine ⟨2758308533413543275428947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3677744711218057700571929 2758308533413543275428947)
                  ·
                    refine ⟨4137462800120314913143421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2758308533413543275428947 4137462800120314913143421)
                    ·
                      refine ⟨1551548550045118092428783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4137462800120314913143421 1551548550045118092428783)
                      ·
                        rfl

theorem cell23_3021630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3021630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021630 prefixEnd_3021630 := by exact prefixLift 3021630
  have htrace : WordTrace (prefixWord ++ tailWord_3021630) baseStart_3021630 baseEnd_3021630 := by
    simpa [prefixWord, tailWord_3021630, baseEnd_3021630] using wordTrace_append hprefix tailTrace_3021630
  have hstable : (prefixWord ++ tailWord_3021630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021630).length < 2 ^ (prefixWord ++ tailWord_3021630).sum := by decide
  have hdescent : baseEnd_3021630 < baseStart_3021630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021632 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_3021632 : Nat := 118140960795 + 3021632 * 2 ^ 59
def prefixEnd_3021632 : Nat := 4983230072969 + 3 ^ 40 * 3021632 * 2
def baseEnd_3021632 : Nat := 1551549577006427084603773

theorem tailTrace_3021632 : CollatzResearch.WordTrace tailWord_3021632 prefixEnd_3021632 1551549577006427084603773 := by
  unfold tailWord_3021632
  simp only [CollatzResearch.WordTrace]
  refine ⟨55103986494575396252789575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73471981992767195003719433 55103986494575396252789575)
  ·
    refine ⟨82655979741863094379184363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55103986494575396252789575 82655979741863094379184363)
    ·
      refine ⟨123983969612794641568776545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82655979741863094379184363 123983969612794641568776545)
      ·
        refine ⟨92987977209595981176582409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123983969612794641568776545 92987977209595981176582409)
        ·
          refine ⟨69740982907196985882436807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92987977209595981176582409 69740982907196985882436807)
          ·
            refine ⟨104611474360795478823655211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69740982907196985882436807 104611474360795478823655211)
            ·
              refine ⟨156917211541193218235482817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104611474360795478823655211 156917211541193218235482817)
              ·
                refine ⟨117687908655894913676612113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156917211541193218235482817 117687908655894913676612113)
                ·
                  refine ⟨88265931491921185257459085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117687908655894913676612113 88265931491921185257459085)
                  ·
                    refine ⟨33099724309470444471547157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88265931491921185257459085 33099724309470444471547157)
                    ·
                      refine ⟨1551549577006427084603773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33099724309470444471547157 1551549577006427084603773)
                      ·
                        rfl

theorem cell23_3021632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_3021632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021632 prefixEnd_3021632 := by exact prefixLift 3021632
  have htrace : WordTrace (prefixWord ++ tailWord_3021632) baseStart_3021632 baseEnd_3021632 := by
    simpa [prefixWord, tailWord_3021632, baseEnd_3021632] using wordTrace_append hprefix tailTrace_3021632
  have hstable : (prefixWord ++ tailWord_3021632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021632).length < 2 ^ (prefixWord ++ tailWord_3021632).sum := by decide
  have hdescent : baseEnd_3021632 < baseStart_3021632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021676 : List Nat := [2, 2, 1, 1, 4, 1, 3, 4, 5]
def baseStart_3021676 : Nat := 118140960795 + 3021676 * 2 ^ 59
def prefixEnd_3021676 : Nat := 4983230072969 + 3 ^ 40 * 3021676 * 2
def baseEnd_3021676 : Nat := 172396907795024990272619

theorem tailTrace_3021676 : CollatzResearch.WordTrace tailWord_3021676 prefixEnd_3021676 172396907795024990272619 := by
  unfold tailWord_3021676
  simp only [CollatzResearch.WordTrace]
  refine ⟨55104788900495694010090441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73473051867327592013453921 55104788900495694010090441)
  ·
    refine ⟨41328591675371770507567831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55104788900495694010090441 41328591675371770507567831)
    ·
      refine ⟨61992887513057655761351747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41328591675371770507567831 61992887513057655761351747)
      ·
        refine ⟨92989331269586483642027621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61992887513057655761351747 92989331269586483642027621)
        ·
          refine ⟨17435499613047465682880179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92989331269586483642027621 17435499613047465682880179)
          ·
            refine ⟨26153249419571198524320269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17435499613047465682880179 26153249419571198524320269)
            ·
              refine ⟨9807468532339199446620101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26153249419571198524320269 9807468532339199446620101)
              ·
                refine ⟨1838900349813599896241269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9807468532339199446620101 1838900349813599896241269)
                ·
                  refine ⟨172396907795024990272619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1838900349813599896241269 172396907795024990272619)
                  ·
                    rfl

theorem cell23_3021676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_3021676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021676 prefixEnd_3021676 := by exact prefixLift 3021676
  have htrace : WordTrace (prefixWord ++ tailWord_3021676) baseStart_3021676 baseEnd_3021676 := by
    simpa [prefixWord, tailWord_3021676, baseEnd_3021676] using wordTrace_append hprefix tailTrace_3021676
  have hstable : (prefixWord ++ tailWord_3021676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021676).length < 2 ^ (prefixWord ++ tailWord_3021676).sum := by decide
  have hdescent : baseEnd_3021676 < baseStart_3021676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021706 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_3021706 : Nat := 118140960795 + 3021706 * 2 ^ 59
def prefixEnd_3021706 : Nat := 4983230072969 + 3 ^ 40 * 3021706 * 2
def baseEnd_3021706 : Nat := 517195858191619931692811

theorem tailTrace_3021706 : CollatzResearch.WordTrace tailWord_3021706 prefixEnd_3021706 517195858191619931692811 := by
  unfold tailWord_3021706
  simp only [CollatzResearch.WordTrace]
  refine ⟨27552667997720675785943243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73473781327255135429181981 27552667997720675785943243)
  ·
    refine ⟨41329001996581013678914865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27552667997720675785943243 41329001996581013678914865)
    ·
      refine ⟨30996751497435760259186149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41329001996581013678914865 30996751497435760259186149)
      ·
        refine ⟨5811890905769205048597403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30996751497435760259186149 5811890905769205048597403)
        ·
          refine ⟨8717836358653807572896105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811890905769205048597403 8717836358653807572896105)
          ·
            refine ⟨6538377268990355679672079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8717836358653807572896105 6538377268990355679672079)
            ·
              refine ⟨9807565903485533519508119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538377268990355679672079 9807565903485533519508119)
              ·
                refine ⟨14711348855228300279262179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9807565903485533519508119 14711348855228300279262179)
                ·
                  refine ⟨22067023282842450418893269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14711348855228300279262179 22067023282842450418893269)
                  ·
                    refine ⟨517195858191619931692811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22067023282842450418893269 517195858191619931692811)
                    ·
                      rfl

theorem cell23_3021706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_3021706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021706 prefixEnd_3021706 := by exact prefixLift 3021706
  have htrace : WordTrace (prefixWord ++ tailWord_3021706) baseStart_3021706 baseEnd_3021706 := by
    simpa [prefixWord, tailWord_3021706, baseEnd_3021706] using wordTrace_append hprefix tailTrace_3021706
  have hstable : (prefixWord ++ tailWord_3021706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021706).length < 2 ^ (prefixWord ++ tailWord_3021706).sum := by decide
  have hdescent : baseEnd_3021706 < baseStart_3021706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021820 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_3021820 : Nat := 118140960795 + 3021820 * 2 ^ 59
def prefixEnd_3021820 : Nat := 4983230072969 + 3 ^ 40 * 3021820 * 2
def baseEnd_3021820 : Nat := 1551646111369472349052909

theorem tailTrace_3021820 : CollatzResearch.WordTrace tailWord_3021820 prefixEnd_3021820 1551646111369472349052909 := by
  unfold tailWord_3021820
  simp only [CollatzResearch.WordTrace]
  refine ⟨55107414956234850306711457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73476553274979800408948609 55107414956234850306711457)
  ·
    refine ⟨41330561217176137730033593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55107414956234850306711457 41330561217176137730033593)
    ·
      refine ⟨30997920912882103297525195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41330561217176137730033593 30997920912882103297525195)
      ·
        refine ⟨46496881369323154946287793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30997920912882103297525195 46496881369323154946287793)
        ·
          refine ⟨34872661026992366209715845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46496881369323154946287793 34872661026992366209715845)
          ·
            refine ⟨6538623942561068664321721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34872661026992366209715845 6538623942561068664321721)
            ·
              refine ⟨4903967956920801498241291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6538623942561068664321721 4903967956920801498241291)
              ·
                refine ⟨7355951935381202247361937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903967956920801498241291 7355951935381202247361937)
                ·
                  refine ⟨5516963951535901685521453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7355951935381202247361937 5516963951535901685521453)
                  ·
                    refine ⟨2068861481825963132070545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5516963951535901685521453 2068861481825963132070545)
                    ·
                      refine ⟨1551646111369472349052909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068861481825963132070545 1551646111369472349052909)
                      ·
                        rfl

theorem cell23_3021820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_3021820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021820 prefixEnd_3021820 := by exact prefixLift 3021820
  have htrace : WordTrace (prefixWord ++ tailWord_3021820) baseStart_3021820 baseEnd_3021820 := by
    simpa [prefixWord, tailWord_3021820, baseEnd_3021820] using wordTrace_append hprefix tailTrace_3021820
  have hstable : (prefixWord ++ tailWord_3021820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021820).length < 2 ^ (prefixWord ++ tailWord_3021820).sum := by decide
  have hdescent : baseEnd_3021820 < baseStart_3021820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021850 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2]
def baseStart_3021850 : Nat := 118140960795 + 3021850 * 2 ^ 59
def prefixEnd_3021850 : Nat := 4983230072969 + 3 ^ 40 * 3021850 * 2
def baseEnd_3021850 : Nat := 1551661515789107231677771

theorem tailTrace_3021850 : CollatzResearch.WordTrace tailWord_3021850 prefixEnd_3021850 1551661515789107231677771 := by
  unfold tailWord_3021850
  simp only [CollatzResearch.WordTrace]
  refine ⟨27553981025590253934253751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73477282734907343824676669 27553981025590253934253751)
  ·
    refine ⟨41330971538385380901380627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27553981025590253934253751 41330971538385380901380627)
    ·
      refine ⟨61996457307578071352070941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41330971538385380901380627 61996457307578071352070941)
      ·
        refine ⟨23248671490341776757026603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61996457307578071352070941 23248671490341776757026603)
        ·
          refine ⟨34873007235512665135539905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23248671490341776757026603 34873007235512665135539905)
          ·
            refine ⟨26154755426634498851654929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34873007235512665135539905 26154755426634498851654929)
            ·
              refine ⟨19616066569975874138741197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26154755426634498851654929 19616066569975874138741197)
              ·
                refine ⟨7356024963740952802027949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19616066569975874138741197 7356024963740952802027949)
                ·
                  refine ⟨2758509361402857300760481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7356024963740952802027949 2758509361402857300760481)
                  ·
                    refine ⟨2068882021052142975570361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2758509361402857300760481 2068882021052142975570361)
                    ·
                      refine ⟨1551661515789107231677771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068882021052142975570361 1551661515789107231677771)
                      ·
                        rfl

theorem cell23_3021850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_3021850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021850 prefixEnd_3021850 := by exact prefixLift 3021850
  have htrace : WordTrace (prefixWord ++ tailWord_3021850) baseStart_3021850 baseEnd_3021850 := by
    simpa [prefixWord, tailWord_3021850, baseEnd_3021850] using wordTrace_append hprefix tailTrace_3021850
  have hstable : (prefixWord ++ tailWord_3021850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021850).length < 2 ^ (prefixWord ++ tailWord_3021850).sum := by decide
  have hdescent : baseEnd_3021850 < baseStart_3021850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021860 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_3021860 : Nat := 118140960795 + 3021860 * 2 ^ 59
def prefixEnd_3021860 : Nat := 4983230072969 + 3 ^ 40 * 3021860 * 2
def baseEnd_3021860 : Nat := 517222216865217397517575

theorem tailTrace_3021860 : CollatzResearch.WordTrace tailWord_3021860 prefixEnd_3021860 517222216865217397517575 := by
  unfold tailWord_3021860
  simp only [CollatzResearch.WordTrace]
  refine ⟨55108144416162393722439517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73477525888216524963252689 55108144416162393722439517)
  ·
    refine ⟨20665554156060897645914819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55108144416162393722439517 20665554156060897645914819)
    ·
      refine ⟨30998331234091346468872229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20665554156060897645914819 30998331234091346468872229)
      ·
        refine ⟨5812187106392127462913543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30998331234091346468872229 5812187106392127462913543)
        ·
          refine ⟨8718280659588191194370315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5812187106392127462913543 8718280659588191194370315)
          ·
            refine ⟨13077420989382286791555473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8718280659588191194370315 13077420989382286791555473)
            ·
              refine ⟨9808065742036715093666605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13077420989382286791555473 9808065742036715093666605)
              ·
                refine ⟨3678024653263768160124977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9808065742036715093666605 3678024653263768160124977)
                ·
                  refine ⟨2758518489947826120093733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3678024653263768160124977 2758518489947826120093733)
                  ·
                    refine ⟨517222216865217397517575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2758518489947826120093733 517222216865217397517575)
                    ·
                      rfl

theorem cell23_3021860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_3021860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021860 prefixEnd_3021860 := by exact prefixLift 3021860
  have htrace : WordTrace (prefixWord ++ tailWord_3021860) baseStart_3021860 baseEnd_3021860 := by
    simpa [prefixWord, tailWord_3021860, baseEnd_3021860] using wordTrace_append hprefix tailTrace_3021860
  have hstable : (prefixWord ++ tailWord_3021860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021860).length < 2 ^ (prefixWord ++ tailWord_3021860).sum := by decide
  have hdescent : baseEnd_3021860 < baseStart_3021860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021870 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3021870 : Nat := 118140960795 + 3021870 * 2 ^ 59
def prefixEnd_3021870 : Nat := 4983230072969 + 3 ^ 40 * 3021870 * 2
def baseEnd_3021870 : Nat := 1551671785402197153427679

theorem tailTrace_3021870 : CollatzResearch.WordTrace tailWord_3021870 prefixEnd_3021870 1551671785402197153427679 := by
  unfold tailWord_3021870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13777081695286069894092883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73477769041525706101828709 13777081695286069894092883)
  ·
    refine ⟨20665622542929104841139325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13777081695286069894092883 20665622542929104841139325)
    ·
      refine ⟨7749608453598414315427247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20665622542929104841139325 7749608453598414315427247)
      ·
        refine ⟨11624412680397621473140871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7749608453598414315427247 11624412680397621473140871)
        ·
          refine ⟨17436619020596432209711307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11624412680397621473140871 17436619020596432209711307)
          ·
            refine ⟨26154928530894648314566961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17436619020596432209711307 26154928530894648314566961)
            ·
              refine ⟨19616196398170986235925221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26154928530894648314566961 19616196398170986235925221)
              ·
                refine ⟨3678036824657059919235979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19616196398170986235925221 3678036824657059919235979)
                ·
                  refine ⟨5517055236985589878853969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678036824657059919235979 5517055236985589878853969)
                  ·
                    refine ⟨4137791427739192409140477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5517055236985589878853969 4137791427739192409140477)
                    ·
                      refine ⟨1551671785402197153427679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4137791427739192409140477 1551671785402197153427679)
                      ·
                        rfl

theorem cell23_3021870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3021870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021870 prefixEnd_3021870 := by exact prefixLift 3021870
  have htrace : WordTrace (prefixWord ++ tailWord_3021870) baseStart_3021870 baseEnd_3021870 := by
    simpa [prefixWord, tailWord_3021870, baseEnd_3021870] using wordTrace_append hprefix tailTrace_3021870
  have hstable : (prefixWord ++ tailWord_3021870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021870).length < 2 ^ (prefixWord ++ tailWord_3021870).sum := by decide
  have hdescent : baseEnd_3021870 < baseStart_3021870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021884 : List Nat := [2, 2, 2, 2, 2, 3, 2, 3, 1, 2, 2]
def baseStart_3021884 : Nat := 118140960795 + 3021884 * 2 ^ 59
def prefixEnd_3021884 : Nat := 4983230072969 + 3 ^ 40 * 3021884 * 2
def baseEnd_3021884 : Nat := 1551678974131360098652615

theorem tailTrace_3021884 : CollatzResearch.WordTrace tailWord_3021884 prefixEnd_3021884 1551678974131360098652615 := by
  unfold tailWord_3021884
  simp only [CollatzResearch.WordTrace]
  refine ⟨55108582092118919771876353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73478109456158559695835137 55108582092118919771876353)
  ·
    refine ⟨41331436569089189828907265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55108582092118919771876353 41331436569089189828907265)
    ·
      refine ⟨30998577426816892371680449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41331436569089189828907265 30998577426816892371680449)
      ·
        refine ⟨23248933070112669278760337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30998577426816892371680449 23248933070112669278760337)
        ·
          refine ⟨17436699802584501959070253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23248933070112669278760337 17436699802584501959070253)
          ·
            refine ⟨6538762425969188234651345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17436699802584501959070253 6538762425969188234651345)
            ·
              refine ⟨4904071819476891175988509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6538762425969188234651345 4904071819476891175988509)
              ·
                refine ⟨1839026932303834190995691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4904071819476891175988509 1839026932303834190995691)
                ·
                  refine ⟨2758540398455751286493537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839026932303834190995691 2758540398455751286493537)
                  ·
                    refine ⟨2068905298841813464870153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2758540398455751286493537 2068905298841813464870153)
                    ·
                      refine ⟨1551678974131360098652615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068905298841813464870153 1551678974131360098652615)
                      ·
                        rfl

theorem cell23_3021884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_3021884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021884 prefixEnd_3021884 := by exact prefixLift 3021884
  have htrace : WordTrace (prefixWord ++ tailWord_3021884) baseStart_3021884 baseEnd_3021884 := by
    simpa [prefixWord, tailWord_3021884, baseEnd_3021884] using wordTrace_append hprefix tailTrace_3021884
  have hstable : (prefixWord ++ tailWord_3021884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021884).length < 2 ^ (prefixWord ++ tailWord_3021884).sum := by decide
  have hdescent : baseEnd_3021884 < baseStart_3021884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021894 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3021894 : Nat := 118140960795 + 3021894 * 2 ^ 59
def prefixEnd_3021894 : Nat := 4983230072969 + 3 ^ 40 * 3021894 * 2
def baseEnd_3021894 : Nat := 517228036312635019842523

theorem tailTrace_3021894 : CollatzResearch.WordTrace tailWord_3021894 prefixEnd_3021894 517228036312635019842523 := by
  unfold tailWord_3021894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3444297778568800351613023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73478352609467740834411157 3444297778568800351613023)
  ·
    refine ⟨5166446667853200527419535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3444297778568800351613023 5166446667853200527419535)
    ·
      refine ⟨7749670001779800791129303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5166446667853200527419535 7749670001779800791129303)
      ·
        refine ⟨11624505002669701186693955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7749670001779800791129303 11624505002669701186693955)
        ·
          refine ⟨17436757504004551780040933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11624505002669701186693955 17436757504004551780040933)
          ·
            refine ⟨3269392032000853458757675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17436757504004551780040933 3269392032000853458757675)
            ·
              refine ⟨4904088048001280188136513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269392032000853458757675 4904088048001280188136513)
              ·
                refine ⟨3678066036000960141102385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4904088048001280188136513 3678066036000960141102385)
                ·
                  refine ⟨2758549527000720105826789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3678066036000960141102385 2758549527000720105826789)
                  ·
                    refine ⟨517228036312635019842523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2758549527000720105826789 517228036312635019842523)
                    ·
                      rfl

theorem cell23_3021894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3021894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021894 prefixEnd_3021894 := by exact prefixLift 3021894
  have htrace : WordTrace (prefixWord ++ tailWord_3021894) baseStart_3021894 baseEnd_3021894 := by
    simpa [prefixWord, tailWord_3021894, baseEnd_3021894] using wordTrace_append hprefix tailTrace_3021894
  have hstable : (prefixWord ++ tailWord_3021894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021894).length < 2 ^ (prefixWord ++ tailWord_3021894).sum := by decide
  have hdescent : baseEnd_3021894 < baseStart_3021894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021927 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_3021927 : Nat := 118140960795 + 3021927 * 2 ^ 59
def prefixEnd_3021927 : Nat := 4983230072969 + 3 ^ 40 * 3021927 * 2
def baseEnd_3021927 : Nat := 1551701053799503430414917

theorem tailTrace_3021927 : CollatzResearch.WordTrace tailWord_3021927 prefixEnd_3021927 1551701053799503430414917 := by
  unfold tailWord_3021927
  simp only [CollatzResearch.WordTrace]
  refine ⟨110218732523082057887568035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73479155015388038591712023 110218732523082057887568035)
  ·
    refine ⟨165328098784623086831352053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110218732523082057887568035 165328098784623086831352053)
    ·
      refine ⟨15499509261058414390439255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165328098784623086831352053 15499509261058414390439255)
      ·
        refine ⟨23249263891587621585658883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15499509261058414390439255 23249263891587621585658883)
        ·
          refine ⟨34873895837381432378488325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23249263891587621585658883 34873895837381432378488325)
          ·
            refine ⟨6538855469509018570966561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34873895837381432378488325 6538855469509018570966561)
            ·
              refine ⟨4904141602131763928224921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6538855469509018570966561 4904141602131763928224921)
              ·
                refine ⟨3678106201598822946168691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4904141602131763928224921 3678106201598822946168691)
                ·
                  refine ⟨5517159302398234419253037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678106201598822946168691 5517159302398234419253037)
                  ·
                    refine ⟨2068934738399337907219889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5517159302398234419253037 2068934738399337907219889)
                    ·
                      refine ⟨1551701053799503430414917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068934738399337907219889 1551701053799503430414917)
                      ·
                        rfl

theorem cell23_3021927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_3021927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021927 prefixEnd_3021927 := by exact prefixLift 3021927
  have htrace : WordTrace (prefixWord ++ tailWord_3021927) baseStart_3021927 baseEnd_3021927 := by
    simpa [prefixWord, tailWord_3021927, baseEnd_3021927] using wordTrace_append hprefix tailTrace_3021927
  have hstable : (prefixWord ++ tailWord_3021927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021927).length < 2 ^ (prefixWord ++ tailWord_3021927).sum := by decide
  have hdescent : baseEnd_3021927 < baseStart_3021927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3021963 : List Nat := [1, 1, 1, 1, 4, 1, 1, 8, 5]
def baseStart_3021963 : Nat := 118140960795 + 3021963 * 2 ^ 59
def prefixEnd_3021963 : Nat := 4983230072969 + 3 ^ 40 * 3021963 * 2
def baseEnd_3021963 : Nat := 172413282122562809951639

theorem tailTrace_3021963 : CollatzResearch.WordTrace tailWord_3021963 prefixEnd_3021963 172413282122562809951639 := by
  unfold tailWord_3021963
  simp only [CollatzResearch.WordTrace]
  refine ⟨110220045550951636035878543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73480030367301090690585695 110220045550951636035878543)
  ·
    refine ⟨165330068326427454053817815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110220045550951636035878543 165330068326427454053817815)
    ·
      refine ⟨247995102489641181080726723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165330068326427454053817815 247995102489641181080726723)
      ·
        refine ⟨371992653734461771621090085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247995102489641181080726723 371992653734461771621090085)
        ·
          refine ⟨69748622575211582178954391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371992653734461771621090085 69748622575211582178954391)
          ·
            refine ⟨104622933862817373268431587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69748622575211582178954391 104622933862817373268431587)
            ·
              refine ⟨156934400794226059902647381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104622933862817373268431587 156934400794226059902647381)
              ·
                refine ⟨1839075009307336639484149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 156934400794226059902647381 1839075009307336639484149)
                ·
                  refine ⟨172413282122562809951639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1839075009307336639484149 172413282122562809951639)
                  ·
                    rfl

theorem cell23_3021963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 5].length) (baseStart_3021963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3021963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3021963 prefixEnd_3021963 := by exact prefixLift 3021963
  have htrace : WordTrace (prefixWord ++ tailWord_3021963) baseStart_3021963 baseEnd_3021963 := by
    simpa [prefixWord, tailWord_3021963, baseEnd_3021963] using wordTrace_append hprefix tailTrace_3021963
  have hstable : (prefixWord ++ tailWord_3021963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3021963).length < 2 ^ (prefixWord ++ tailWord_3021963).sum := by decide
  have hdescent : baseEnd_3021963 < baseStart_3021963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3021963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022014 : List Nat := [4, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_3022014 : Nat := 118140960795 + 3022014 * 2 ^ 59
def prefixEnd_3022014 : Nat := 4983230072969 + 3 ^ 40 * 3022014 * 2
def baseEnd_3022014 : Nat := 172416191846271621114113

theorem tailTrace_3022014 : CollatzResearch.WordTrace tailWord_3022014 prefixEnd_3022014 172416191846271621114113 := by
  unfold tailWord_3022014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13777738209220858968248137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73481270449177914497323397 13777738209220858968248137)
  ·
    refine ⟨10333303656915644226186103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13777738209220858968248137 10333303656915644226186103)
    ·
      refine ⟨15499955485373466339279155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10333303656915644226186103 15499955485373466339279155)
      ·
        refine ⟨23249933228060199508918733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15499955485373466339279155 23249933228060199508918733)
        ·
          refine ⟨8718724960522574815844525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23249933228060199508918733 8718724960522574815844525)
          ·
            refine ⟨3269521860195965555941697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8718724960522574815844525 3269521860195965555941697)
            ·
              refine ⟨2452141395146974166956273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3269521860195965555941697 2452141395146974166956273)
              ·
                refine ⟨1839106046360230625217205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452141395146974166956273 1839106046360230625217205)
                ·
                  refine ⟨172416191846271621114113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1839106046360230625217205 172416191846271621114113)
                  ·
                    rfl

theorem cell23_3022014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_3022014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022014 prefixEnd_3022014 := by exact prefixLift 3022014
  have htrace : WordTrace (prefixWord ++ tailWord_3022014) baseStart_3022014 baseEnd_3022014 := by
    simpa [prefixWord, tailWord_3022014, baseEnd_3022014] using wordTrace_append hprefix tailTrace_3022014
  have hstable : (prefixWord ++ tailWord_3022014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022014).length < 2 ^ (prefixWord ++ tailWord_3022014).sum := by decide
  have hdescent : baseEnd_3022014 < baseStart_3022014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022017 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3022017 : Nat := 118140960795 + 3022017 * 2 ^ 59
def prefixEnd_3022017 : Nat := 4983230072969 + 3 ^ 40 * 3022017 * 2
def baseEnd_3022017 : Nat := 1551747267058408078289503

theorem tailTrace_3022017 : CollatzResearch.WordTrace tailWord_3022017 prefixEnd_3022017 1551747267058408078289503 := by
  unfold tailWord_3022017
  simp only [CollatzResearch.WordTrace]
  refine ⟨110222015092756003258344305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73481343395170668838896203 110222015092756003258344305)
  ·
    refine ⟨82666511319567002443758229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110222015092756003258344305 82666511319567002443758229)
    ·
      refine ⟨3874992718104703239551167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82666511319567002443758229 3874992718104703239551167)
      ·
        refine ⟨5812489077157054859326751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874992718104703239551167 5812489077157054859326751)
        ·
          refine ⟨8718733615735582288990127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5812489077157054859326751 8718733615735582288990127)
          ·
            refine ⟨13078100423603373433485191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8718733615735582288990127 13078100423603373433485191)
            ·
              refine ⟨19617150635405060150227787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13078100423603373433485191 19617150635405060150227787)
              ·
                refine ⟨29425725953107590225341681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19617150635405060150227787 29425725953107590225341681)
                ·
                  refine ⟨22069294464830692669006261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29425725953107590225341681 22069294464830692669006261)
                  ·
                    refine ⟨2068996356077877437719337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22069294464830692669006261 2068996356077877437719337)
                    ·
                      refine ⟨1551747267058408078289503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2068996356077877437719337 1551747267058408078289503)
                      ·
                        rfl

theorem cell23_3022017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3022017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022017 prefixEnd_3022017 := by exact prefixLift 3022017
  have htrace : WordTrace (prefixWord ++ tailWord_3022017) baseStart_3022017 baseEnd_3022017 := by
    simpa [prefixWord, tailWord_3022017, baseEnd_3022017] using wordTrace_append hprefix tailTrace_3022017
  have hstable : (prefixWord ++ tailWord_3022017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022017).length < 2 ^ (prefixWord ++ tailWord_3022017).sum := by decide
  have hdescent : baseEnd_3022017 < baseStart_3022017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022023 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 7, 4]
def baseStart_3022023 : Nat := 118140960795 + 3022023 * 2 ^ 59
def prefixEnd_3022023 : Nat := 4983230072969 + 3 ^ 40 * 3022023 * 2
def baseEnd_3022023 : Nat := 517250115980778351604825

theorem tailTrace_3022023 : CollatzResearch.WordTrace tailWord_3022023 prefixEnd_3022023 517250115980778351604825 := by
  unfold tailWord_3022023
  simp only [CollatzResearch.WordTrace]
  refine ⟨110222233930734266283062723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73481489287156177522041815 110222233930734266283062723)
  ·
    refine ⟨165333350896101399424594085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110222233930734266283062723 165333350896101399424594085)
    ·
      refine ⟨31000003293019012392111391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165333350896101399424594085 31000003293019012392111391)
      ·
        refine ⟨46500004939528518588167087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31000003293019012392111391 46500004939528518588167087)
        ·
          refine ⟨69750007409292777882250631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46500004939528518588167087 69750007409292777882250631)
          ·
            refine ⟨104625011113939166823375947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69750007409292777882250631 104625011113939166823375947)
            ·
              refine ⟨156937516670908750235063921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104625011113939166823375947 156937516670908750235063921)
              ·
                refine ⟨117703137503181562676297941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156937516670908750235063921 117703137503181562676297941)
                ·
                  refine ⟨2758667285230817875225733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 117703137503181562676297941 2758667285230817875225733)
                  ·
                    refine ⟨517250115980778351604825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2758667285230817875225733 517250115980778351604825)
                    ·
                      rfl

theorem cell23_3022023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_3022023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022023 prefixEnd_3022023 := by exact prefixLift 3022023
  have htrace : WordTrace (prefixWord ++ tailWord_3022023) baseStart_3022023 baseEnd_3022023 := by
    simpa [prefixWord, tailWord_3022023, baseEnd_3022023] using wordTrace_append hprefix tailTrace_3022023
  have hstable : (prefixWord ++ tailWord_3022023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022023).length < 2 ^ (prefixWord ++ tailWord_3022023).sum := by decide
  have hdescent : baseEnd_3022023 < baseStart_3022023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022033 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_3022033 : Nat := 118140960795 + 3022033 * 2 ^ 59
def prefixEnd_3022033 : Nat := 4983230072969 + 3 ^ 40 * 3022033 * 2
def baseEnd_3022033 : Nat := 1551755482748880015689429

theorem tailTrace_3022033 : CollatzResearch.WordTrace tailWord_3022033 prefixEnd_3022033 1551755482748880015689429 := by
  unfold tailWord_3022033
  simp only [CollatzResearch.WordTrace]
  refine ⟨110222598660698037990926753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73481732440465358660617835 110222598660698037990926753)
  ·
    refine ⟨82666948995523528493195065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110222598660698037990926753 82666948995523528493195065)
    ·
      refine ⟨62000211746642646369896299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82666948995523528493195065 62000211746642646369896299)
      ·
        refine ⟨93000317619963969554844449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62000211746642646369896299 93000317619963969554844449)
        ·
          refine ⟨69750238214972977166133337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93000317619963969554844449 69750238214972977166133337)
          ·
            refine ⟨52312678661229732874600003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69750238214972977166133337 52312678661229732874600003)
            ·
              refine ⟨78469017991844599311900005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52312678661229732874600003 78469017991844599311900005)
              ·
                refine ⟨14712940873470862370981251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78469017991844599311900005 14712940873470862370981251)
                ·
                  refine ⟨22069411310206293556471877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14712940873470862370981251 22069411310206293556471877)
                  ·
                    refine ⟨4138014620663680041838477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22069411310206293556471877 4138014620663680041838477)
                    ·
                      refine ⟨1551755482748880015689429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4138014620663680041838477 1551755482748880015689429)
                      ·
                        rfl

theorem cell23_3022033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_3022033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022033 prefixEnd_3022033 := by exact prefixLift 3022033
  have htrace : WordTrace (prefixWord ++ tailWord_3022033) baseStart_3022033 baseEnd_3022033 := by
    simpa [prefixWord, tailWord_3022033, baseEnd_3022033] using wordTrace_append hprefix tailTrace_3022033
  have hstable : (prefixWord ++ tailWord_3022033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022033).length < 2 ^ (prefixWord ++ tailWord_3022033).sum := by decide
  have hdescent : baseEnd_3022033 < baseStart_3022033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022113 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 3, 6]
def baseStart_3022113 : Nat := 118140960795 + 3022113 * 2 ^ 59
def prefixEnd_3022113 : Nat := 4983230072969 + 3 ^ 40 * 3022113 * 2
def baseEnd_3022113 : Nat := 517265520400413234229687

theorem tailTrace_3022113 : CollatzResearch.WordTrace tailWord_3022113 prefixEnd_3022113 517265520400413234229687 := by
  unfold tailWord_3022113
  simp only [CollatzResearch.WordTrace]
  refine ⟨110225516500408211653838993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73483677666938807769225995 110225516500408211653838993)
  ·
    refine ⟨82669137375306158740379245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110225516500408211653838993 82669137375306158740379245)
    ·
      refine ⟨31000926515739809527642217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82669137375306158740379245 31000926515739809527642217)
      ·
        refine ⟨23250694886804857145731663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31000926515739809527642217 23250694886804857145731663)
        ·
          refine ⟨34876042330207285718597495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23250694886804857145731663 34876042330207285718597495)
          ·
            refine ⟨52314063495310928577896243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34876042330207285718597495 52314063495310928577896243)
            ·
              refine ⟨78471095242966392866844365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52314063495310928577896243 78471095242966392866844365)
              ·
                refine ⟨29426660716112397325066637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78471095242966392866844365 29426660716112397325066637)
                ·
                  refine ⟨11034997768542148996899989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29426660716112397325066637 11034997768542148996899989)
                  ·
                    refine ⟨517265520400413234229687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11034997768542148996899989 517265520400413234229687)
                    ·
                      rfl

theorem cell23_3022113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_3022113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022113 prefixEnd_3022113 := by exact prefixLift 3022113
  have htrace : WordTrace (prefixWord ++ tailWord_3022113) baseStart_3022113 baseEnd_3022113 := by
    simpa [prefixWord, tailWord_3022113, baseEnd_3022113] using wordTrace_append hprefix tailTrace_3022113
  have hstable : (prefixWord ++ tailWord_3022113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022113).length < 2 ^ (prefixWord ++ tailWord_3022113).sum := by decide
  have hdescent : baseEnd_3022113 < baseStart_3022113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022131 : List Nat := [1, 1, 1, 2, 5, 3, 3, 2, 1, 1, 3]
def baseStart_3022131 : Nat := 118140960795 + 3022131 * 2 ^ 59
def prefixEnd_3022131 : Nat := 4983230072969 + 3 ^ 40 * 3022131 * 2
def baseEnd_3022131 : Nat := 1551805803853020632263979

theorem tailTrace_3022131 : CollatzResearch.WordTrace tailWord_3022131 prefixEnd_3022131 1551805803853020632263979 := by
  unfold tailWord_3022131
  simp only [CollatzResearch.WordTrace]
  refine ⟨110226173014343000727994247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73484115342895333818662831 110226173014343000727994247)
  ·
    refine ⟨165339259521514501091991371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110226173014343000727994247 165339259521514501091991371)
    ·
      refine ⟨248008889282271751637987057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165339259521514501091991371 248008889282271751637987057)
      ·
        refine ⟨186006666961703813728490293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248008889282271751637987057 186006666961703813728490293)
        ·
          refine ⟨17438125027659732537045965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186006666961703813728490293 17438125027659732537045965)
          ·
            refine ⟨6539296885372399701392237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17438125027659732537045965 6539296885372399701392237)
            ·
              refine ⟨2452236332014649888022089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6539296885372399701392237 2452236332014649888022089)
              ·
                refine ⟨1839177249010987416016567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452236332014649888022089 1839177249010987416016567)
                ·
                  refine ⟨2758765873516481124024851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839177249010987416016567 2758765873516481124024851)
                  ·
                    refine ⟨4138148810274721686037277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2758765873516481124024851 4138148810274721686037277)
                    ·
                      refine ⟨1551805803853020632263979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4138148810274721686037277 1551805803853020632263979)
                      ·
                        rfl

theorem cell23_3022131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 1, 3].length) (baseStart_3022131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022131 prefixEnd_3022131 := by exact prefixLift 3022131
  have htrace : WordTrace (prefixWord ++ tailWord_3022131) baseStart_3022131 baseEnd_3022131 := by
    simpa [prefixWord, tailWord_3022131, baseEnd_3022131] using wordTrace_append hprefix tailTrace_3022131
  have hstable : (prefixWord ++ tailWord_3022131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022131).length < 2 ^ (prefixWord ++ tailWord_3022131).sum := by decide
  have hdescent : baseEnd_3022131 < baseStart_3022131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022140 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_3022140 : Nat := 118140960795 + 3022140 * 2 ^ 59
def prefixEnd_3022140 : Nat := 4983230072969 + 3 ^ 40 * 3022140 * 2
def baseEnd_3022140 : Nat := 1551810425178911097051437

theorem tailTrace_3022140 : CollatzResearch.WordTrace tailWord_3022140 prefixEnd_3022140 1551810425178911097051437 := by
  unfold tailWord_3022140
  simp only [CollatzResearch.WordTrace]
  refine ⟨55113250635655197632535937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73484334180873596843381249 55113250635655197632535937)
  ·
    refine ⟨41334937976741398224401953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55113250635655197632535937 41334937976741398224401953)
    ·
      refine ⟨31001203482556048668301465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41334937976741398224401953 31001203482556048668301465)
      ·
        refine ⟨23250902611917036501226099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31001203482556048668301465 23250902611917036501226099)
        ·
          refine ⟨34876353917875554751839149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23250902611917036501226099 34876353917875554751839149)
          ·
            refine ⟨13078632719203333031939681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34876353917875554751839149 13078632719203333031939681)
            ·
              refine ⟨9808974539402499773954761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13078632719203333031939681 9808974539402499773954761)
              ·
                refine ⟨7356730904551874830466071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9808974539402499773954761 7356730904551874830466071)
                ·
                  refine ⟨11035096356827812245699107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7356730904551874830466071 11035096356827812245699107)
                  ·
                    refine ⟨16552644535241718368548661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11035096356827812245699107 16552644535241718368548661)
                    ·
                      refine ⟨1551810425178911097051437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16552644535241718368548661 1551810425178911097051437)
                      ·
                        rfl

theorem cell23_3022140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_3022140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022140 prefixEnd_3022140 := by exact prefixLift 3022140
  have htrace : WordTrace (prefixWord ++ tailWord_3022140) baseStart_3022140 baseEnd_3022140 := by
    simpa [prefixWord, tailWord_3022140, baseEnd_3022140] using wordTrace_append hprefix tailTrace_3022140
  have hstable : (prefixWord ++ tailWord_3022140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022140).length < 2 ^ (prefixWord ++ tailWord_3022140).sum := by decide
  have hdescent : baseEnd_3022140 < baseStart_3022140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022143 : List Nat := [1, 1, 2, 2, 4, 2, 1, 10]
def baseStart_3022143 : Nat := 118140960795 + 3022143 * 2 ^ 59
def prefixEnd_3022143 : Nat := 4983230072969 + 3 ^ 40 * 3022143 * 2
def baseEnd_3022143 : Nat := 57474517245217577233849

theorem tailTrace_3022143 : CollatzResearch.WordTrace tailWord_3022143 prefixEnd_3022143 57474517245217577233849 := by
  unfold tailWord_3022143
  simp only [CollatzResearch.WordTrace]
  refine ⟨110226610690299526777431083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73484407126866351184954055 110226610690299526777431083)
  ·
    refine ⟨165339916035449290166146625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110226610690299526777431083 165339916035449290166146625)
    ·
      refine ⟨124004937026586967624609969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165339916035449290166146625 124004937026586967624609969)
      ·
        refine ⟨93003702769940225718457477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124004937026586967624609969 93003702769940225718457477)
        ·
          refine ⟨17438194269363792322210777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93003702769940225718457477 17438194269363792322210777)
          ·
            refine ⟨13078645702022844241658083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17438194269363792322210777 13078645702022844241658083)
            ·
              refine ⟨19617968553034266362487125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13078645702022844241658083 19617968553034266362487125)
              ·
                refine ⟨57474517245217577233849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19617968553034266362487125 57474517245217577233849)
                ·
                  rfl

theorem cell23_3022143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 10].length) (baseStart_3022143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022143 prefixEnd_3022143 := by exact prefixLift 3022143
  have htrace : WordTrace (prefixWord ++ tailWord_3022143) baseStart_3022143 baseEnd_3022143 := by
    simpa [prefixWord, tailWord_3022143, baseEnd_3022143] using wordTrace_append hprefix tailTrace_3022143
  have hstable : (prefixWord ++ tailWord_3022143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022143).length < 2 ^ (prefixWord ++ tailWord_3022143).sum := by decide
  have hdescent : baseEnd_3022143 < baseStart_3022143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022170 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_3022170 : Nat := 118140960795 + 3022170 * 2 ^ 59
def prefixEnd_3022170 : Nat := 4983230072969 + 3 ^ 40 * 3022170 * 2
def baseEnd_3022170 : Nat := 1551825829598545979676299

theorem tailTrace_3022170 : CollatzResearch.WordTrace tailWord_3022170 prefixEnd_3022170 1551825829598545979676299 := by
  unfold tailWord_3022170
  simp only [CollatzResearch.WordTrace]
  refine ⟨27556898865300427597165991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73485063640801140259109309 27556898865300427597165991)
  ·
    refine ⟨41335348297950641395748987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27556898865300427597165991 41335348297950641395748987)
    ·
      refine ⟨62003022446925962093623481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41335348297950641395748987 62003022446925962093623481)
      ·
        refine ⟨46502266835194471570217611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62003022446925962093623481 46502266835194471570217611)
        ·
          refine ⟨69753400252791707355326417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46502266835194471570217611 69753400252791707355326417)
          ·
            refine ⟨52315050189593780516494813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69753400252791707355326417 52315050189593780516494813)
            ·
              refine ⟨19618143821097667693685555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52315050189593780516494813 19618143821097667693685555)
              ·
                refine ⟨29427215731646501540528333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19618143821097667693685555 29427215731646501540528333)
                ·
                  refine ⟨11035205899367438077698125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29427215731646501540528333 11035205899367438077698125)
                  ·
                    refine ⟨4138202212262789279136797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11035205899367438077698125 4138202212262789279136797)
                    ·
                      refine ⟨1551825829598545979676299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4138202212262789279136797 1551825829598545979676299)
                      ·
                        rfl

theorem cell23_3022170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_3022170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022170 prefixEnd_3022170 := by exact prefixLift 3022170
  have htrace : WordTrace (prefixWord ++ tailWord_3022170) baseStart_3022170 baseEnd_3022170 := by
    simpa [prefixWord, tailWord_3022170, baseEnd_3022170] using wordTrace_append hprefix tailTrace_3022170
  have hstable : (prefixWord ++ tailWord_3022170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022170).length < 2 ^ (prefixWord ++ tailWord_3022170).sum := by decide
  have hdescent : baseEnd_3022170 < baseStart_3022170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022188 : List Nat := [2, 2, 1, 1, 5, 1, 4, 2, 1, 2, 2]
def baseStart_3022188 : Nat := 118140960795 + 3022188 * 2 ^ 59
def prefixEnd_3022188 : Nat := 4983230072969 + 3 ^ 40 * 3022188 * 2
def baseEnd_3022188 : Nat := 1551835072250326909251217

theorem tailTrace_3022188 : CollatzResearch.WordTrace tailWord_3022188 prefixEnd_3022188 1551835072250326909251217 := by
  unfold tailWord_3022188
  simp only [CollatzResearch.WordTrace]
  refine ⟨55114125987568249731409609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73485501316757666308546145 55114125987568249731409609)
  ·
    refine ⟨41335594490676187298557207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55114125987568249731409609 41335594490676187298557207)
    ·
      refine ⟨62003391736014280947835811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41335594490676187298557207 62003391736014280947835811)
      ·
        refine ⟨93005087604021421421753717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62003391736014280947835811 93005087604021421421753717)
        ·
          refine ⟨8719226962877008258289411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93005087604021421421753717 8719226962877008258289411)
          ·
            refine ⟨13078840444315512387434117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8719226962877008258289411 13078840444315512387434117)
            ·
              refine ⟨2452282583309158572643897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13078840444315512387434117 2452282583309158572643897)
              ·
                refine ⟨1839211937481868929482923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452282583309158572643897 1839211937481868929482923)
                ·
                  refine ⟨2758817906222803394224385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839211937481868929482923 2758817906222803394224385)
                  ·
                    refine ⟨2069113429667102545668289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2758817906222803394224385 2069113429667102545668289)
                    ·
                      refine ⟨1551835072250326909251217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069113429667102545668289 1551835072250326909251217)
                      ·
                        rfl

theorem cell23_3022188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 2, 2].length) (baseStart_3022188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022188 prefixEnd_3022188 := by exact prefixLift 3022188
  have htrace : WordTrace (prefixWord ++ tailWord_3022188) baseStart_3022188 baseEnd_3022188 := by
    simpa [prefixWord, tailWord_3022188, baseEnd_3022188] using wordTrace_append hprefix tailTrace_3022188
  have hstable : (prefixWord ++ tailWord_3022188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022188).length < 2 ^ (prefixWord ++ tailWord_3022188).sum := by decide
  have hdescent : baseEnd_3022188 < baseStart_3022188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022240 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3022240 : Nat := 118140960795 + 3022240 * 2 ^ 59
def prefixEnd_3022240 : Nat := 4983230072969 + 3 ^ 40 * 3022240 * 2
def baseEnd_3022240 : Nat := 1551861773244360705800977

theorem tailTrace_3022240 : CollatzResearch.WordTrace tailWord_3022240 prefixEnd_3022240 1551861773244360705800977 := by
  unfold tailWord_3022240
  simp only [CollatzResearch.WordTrace]
  refine ⟨55115074285474056171856087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73486765713965408229141449 55115074285474056171856087)
  ·
    refine ⟨82672611428211084257784131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55115074285474056171856087 82672611428211084257784131)
    ·
      refine ⟨124008917142316626386676197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82672611428211084257784131 124008917142316626386676197)
      ·
        refine ⟨23251671964184367447501787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124008917142316626386676197 23251671964184367447501787)
        ·
          refine ⟨34877507946276551171252681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23251671964184367447501787 34877507946276551171252681)
          ·
            refine ⟨26158130959707413378439511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34877507946276551171252681 26158130959707413378439511)
            ·
              refine ⟨39237196439561120067659267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26158130959707413378439511 39237196439561120067659267)
              ·
                refine ⟨58855794659341680101488901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39237196439561120067659267 58855794659341680101488901)
                ·
                  refine ⟨11035461498626565019029169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58855794659341680101488901 11035461498626565019029169)
                  ·
                    refine ⟨8276596123969923764271877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11035461498626565019029169 8276596123969923764271877)
                    ·
                      refine ⟨1551861773244360705800977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8276596123969923764271877 1551861773244360705800977)
                      ·
                        rfl

theorem cell23_3022240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3022240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022240 prefixEnd_3022240 := by exact prefixLift 3022240
  have htrace : WordTrace (prefixWord ++ tailWord_3022240) baseStart_3022240 baseEnd_3022240 := by
    simpa [prefixWord, tailWord_3022240, baseEnd_3022240] using wordTrace_append hprefix tailTrace_3022240
  have hstable : (prefixWord ++ tailWord_3022240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022240).length < 2 ^ (prefixWord ++ tailWord_3022240).sum := by decide
  have hdescent : baseEnd_3022240 < baseStart_3022240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022261 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_3022261 : Nat := 118140960795 + 3022261 * 2 ^ 59
def prefixEnd_3022261 : Nat := 4983230072969 + 3 ^ 40 * 3022261 * 2
def baseEnd_3022261 : Nat := 1551872556338105123638381

theorem tailTrace_3022261 : CollatzResearch.WordTrace tailWord_3022261 prefixEnd_3022261 1551872556338105123638381 := by
  unfold tailWord_3022261
  simp only [CollatzResearch.WordTrace]
  refine ⟨110230914503872032930226637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73487276335914688620151091 110230914503872032930226637)
  ·
    refine ⟨41336592938952012348834989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110230914503872032930226637 41336592938952012348834989)
    ·
      refine ⟨15501222352107004630813121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41336592938952012348834989 15501222352107004630813121)
      ·
        refine ⟨11625916764080253473109841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15501222352107004630813121 11625916764080253473109841)
        ·
          refine ⟨8719437573060190104832381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11625916764080253473109841 8719437573060190104832381)
          ·
            refine ⟨3269789089897571289312143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8719437573060190104832381 3269789089897571289312143)
            ·
              refine ⟨4904683634846356933968215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269789089897571289312143 4904683634846356933968215)
              ·
                refine ⟨7357025452269535400952323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4904683634846356933968215 7357025452269535400952323)
                ·
                  refine ⟨11035538178404303101428485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7357025452269535400952323 11035538178404303101428485)
                  ·
                    refine ⟨2069163408450806831517841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11035538178404303101428485 2069163408450806831517841)
                    ·
                      refine ⟨1551872556338105123638381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2069163408450806831517841 1551872556338105123638381)
                      ·
                        rfl

theorem cell23_3022261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_3022261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022261 prefixEnd_3022261 := by exact prefixLift 3022261
  have htrace : WordTrace (prefixWord ++ tailWord_3022261) baseStart_3022261 baseEnd_3022261 := by
    simpa [prefixWord, tailWord_3022261, baseEnd_3022261] using wordTrace_append hprefix tailTrace_3022261
  have hstable : (prefixWord ++ tailWord_3022261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022261).length < 2 ^ (prefixWord ++ tailWord_3022261).sum := by decide
  have hdescent : baseEnd_3022261 < baseStart_3022261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022280 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 1, 7]
def baseStart_3022280 : Nat := 118140960795 + 3022280 * 2 ^ 59
def prefixEnd_3022280 : Nat := 4983230072969 + 3 ^ 40 * 3022280 * 2
def baseEnd_3022280 : Nat := 517294104156846849766931

theorem tailTrace_3022280 : CollatzResearch.WordTrace tailWord_3022280 prefixEnd_3022280 517294104156846849766931 := by
  unfold tailWord_3022280
  simp only [CollatzResearch.WordTrace]
  refine ⟨55115803745401599587584147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73487738327202132783445529 55115803745401599587584147)
  ·
    refine ⟨82673705618102399381376221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55115803745401599587584147 82673705618102399381376221)
    ·
      refine ⟨31002639606788399768016083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82673705618102399381376221 31002639606788399768016083)
      ·
        refine ⟨46503959410182599652024125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31002639606788399768016083 46503959410182599652024125)
        ·
          refine ⟨17438984778818474869509047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46503959410182599652024125 17438984778818474869509047)
          ·
            refine ⟨26158477168227712304263571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17438984778818474869509047 26158477168227712304263571)
            ·
              refine ⟨39237715752341568456395357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26158477168227712304263571 39237715752341568456395357)
              ·
                refine ⟨14714143407128088171148259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39237715752341568456395357 14714143407128088171148259)
                ·
                  refine ⟨22071215110692132256722389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14714143407128088171148259 22071215110692132256722389)
                  ·
                    refine ⟨517294104156846849766931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22071215110692132256722389 517294104156846849766931)
                    ·
                      rfl

theorem cell23_3022280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_3022280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022280 prefixEnd_3022280 := by exact prefixLift 3022280
  have htrace : WordTrace (prefixWord ++ tailWord_3022280) baseStart_3022280 baseEnd_3022280 := by
    simpa [prefixWord, tailWord_3022280, baseEnd_3022280] using wordTrace_append hprefix tailTrace_3022280
  have hstable : (prefixWord ++ tailWord_3022280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022280).length < 2 ^ (prefixWord ++ tailWord_3022280).sum := by decide
  have hdescent : baseEnd_3022280 < baseStart_3022280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022284 : List Nat := [2, 2, 1, 4, 2, 1, 3, 3, 5]
def baseStart_3022284 : Nat := 118140960795 + 3022284 * 2 ^ 59
def prefixEnd_3022284 : Nat := 4983230072969 + 3 ^ 40 * 3022284 * 2
def baseEnd_3022284 : Nat := 172431596265906503738975

theorem tailTrace_3022284 : CollatzResearch.WordTrace tailWord_3022284 prefixEnd_3022284 172431596265906503738975 := by
  unfold tailWord_3022284
  simp only [CollatzResearch.WordTrace]
  refine ⟨55115876691394353929156953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73487835588525805238875937 55115876691394353929156953)
  ·
    refine ⟨41336907518545765446867715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55115876691394353929156953 41336907518545765446867715)
    ·
      refine ⟨62005361277818648170301573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41336907518545765446867715 62005361277818648170301573)
      ·
        refine ⟨11626005239590996531931545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62005361277818648170301573 11626005239590996531931545)
        ·
          refine ⟨8719503929693247398948659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11626005239590996531931545 8719503929693247398948659)
          ·
            refine ⟨13079255894539871098422989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8719503929693247398948659 13079255894539871098422989)
            ·
              refine ⟨4904720960452451661908621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13079255894539871098422989 4904720960452451661908621)
              ·
                refine ⟨1839270360169669373215733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4904720960452451661908621 1839270360169669373215733)
                ·
                  refine ⟨172431596265906503738975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1839270360169669373215733 172431596265906503738975)
                  ·
                    rfl

theorem cell23_3022284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_3022284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022284 prefixEnd_3022284 := by exact prefixLift 3022284
  have htrace : WordTrace (prefixWord ++ tailWord_3022284) baseStart_3022284 baseEnd_3022284 := by
    simpa [prefixWord, tailWord_3022284, baseEnd_3022284] using wordTrace_append hprefix tailTrace_3022284
  have hstable : (prefixWord ++ tailWord_3022284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022284).length < 2 ^ (prefixWord ++ tailWord_3022284).sum := by decide
  have hdescent : baseEnd_3022284 < baseStart_3022284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022297 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 2, 5]
def baseStart_3022297 : Nat := 118140960795 + 3022297 * 2 ^ 59
def prefixEnd_3022297 : Nat := 4983230072969 + 3 ^ 40 * 3022297 * 2
def baseEnd_3022297 : Nat := 517297013880555660929405

theorem tailTrace_3022297 : CollatzResearch.WordTrace tailWord_3022297 prefixEnd_3022297 517297013880555660929405 := by
  unfold tailWord_3022297
  simp only [CollatzResearch.WordTrace]
  refine ⟨110232227531741611078537145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73488151687827740719024763 110232227531741611078537145)
  ·
    refine ⟨82674170648806208308902859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110232227531741611078537145 82674170648806208308902859)
    ·
      refine ⟨124011255973209312463354289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82674170648806208308902859 124011255973209312463354289)
      ·
        refine ⟨93008441979906984347515717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124011255973209312463354289 93008441979906984347515717)
        ·
          refine ⟨17439082871232559565159197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93008441979906984347515717 17439082871232559565159197)
          ·
            refine ⟨6539656076712209836934699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17439082871232559565159197 6539656076712209836934699)
            ·
              refine ⟨9809484115068314755402049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6539656076712209836934699 9809484115068314755402049)
              ·
                refine ⟨7357113086301236066551537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9809484115068314755402049 7357113086301236066551537)
                ·
                  refine ⟨5517834814725927049913653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7357113086301236066551537 5517834814725927049913653)
                  ·
                    refine ⟨517297013880555660929405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5517834814725927049913653 517297013880555660929405)
                    ·
                      rfl

theorem cell23_3022297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_3022297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022297 prefixEnd_3022297 := by exact prefixLift 3022297
  have htrace : WordTrace (prefixWord ++ tailWord_3022297) baseStart_3022297 baseEnd_3022297 := by
    simpa [prefixWord, tailWord_3022297, baseEnd_3022297] using wordTrace_append hprefix tailTrace_3022297
  have hstable : (prefixWord ++ tailWord_3022297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022297).length < 2 ^ (prefixWord ++ tailWord_3022297).sum := by decide
  have hdescent : baseEnd_3022297 < baseStart_3022297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022301 : List Nat := [1, 4, 3, 1, 1, 3, 3, 2, 5]
def baseStart_3022301 : Nat := 118140960795 + 3022301 * 2 ^ 59
def prefixEnd_3022301 : Nat := 4983230072969 + 3 ^ 40 * 3022301 * 2
def baseEnd_3022301 : Nat := 172432566173809440793133

theorem tailTrace_3022301 : CollatzResearch.WordTrace tailWord_3022301 prefixEnd_3022301 172432566173809440793133 := by
  unfold tailWord_3022301
  simp only [CollatzResearch.WordTrace]
  refine ⟨110232373423727119761682757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73488248949151413174455171 110232373423727119761682757)
  ·
    refine ⟨20668570016948834955315517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110232373423727119761682757 20668570016948834955315517)
    ·
      refine ⟨7750713756355813108243319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20668570016948834955315517 7750713756355813108243319)
      ·
        refine ⟨11626070634533719662364979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7750713756355813108243319 11626070634533719662364979)
        ·
          refine ⟨17439105951800579493547469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11626070634533719662364979 17439105951800579493547469)
          ·
            refine ⟨6539664731925217310080301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17439105951800579493547469 6539664731925217310080301)
            ·
              refine ⟨2452374274471956491280113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6539664731925217310080301 2452374274471956491280113)
              ·
                refine ⟨1839280705853967368460085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452374274471956491280113 1839280705853967368460085)
                ·
                  refine ⟨172432566173809440793133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1839280705853967368460085 172432566173809440793133)
                  ·
                    rfl

theorem cell23_3022301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_3022301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022301 prefixEnd_3022301 := by exact prefixLift 3022301
  have htrace : WordTrace (prefixWord ++ tailWord_3022301) baseStart_3022301 baseEnd_3022301 := by
    simpa [prefixWord, tailWord_3022301, baseEnd_3022301] using wordTrace_append hprefix tailTrace_3022301
  have hstable : (prefixWord ++ tailWord_3022301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022301).length < 2 ^ (prefixWord ++ tailWord_3022301).sum := by decide
  have hdescent : baseEnd_3022301 < baseStart_3022301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022307 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3022307 : Nat := 118140960795 + 3022307 * 2 ^ 59
def prefixEnd_3022307 : Nat := 4983230072969 + 3 ^ 40 * 3022307 * 2
def baseEnd_3022307 : Nat := 1551896176448211943663169

theorem tailTrace_3022307 : CollatzResearch.WordTrace tailWord_3022307 prefixEnd_3022307 1551896176448211943663169 := by
  unfold tailWord_3022307
  simp only [CollatzResearch.WordTrace]
  refine ⟨110232592261705382786401175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73488394841136921857600783 110232592261705382786401175)
  ·
    refine ⟨165348888392558074179601763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110232592261705382786401175 165348888392558074179601763)
    ·
      refine ⟨248023332588837111269402645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165348888392558074179601763 248023332588837111269402645)
      ·
        refine ⟨11626093715101739590753249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 248023332588837111269402645 11626093715101739590753249)
        ·
          refine ⟨8719570286326304693064937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11626093715101739590753249 8719570286326304693064937)
          ·
            refine ⟨6539677714744728519798703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8719570286326304693064937 6539677714744728519798703)
            ·
              refine ⟨9809516572117092779698055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6539677714744728519798703 9809516572117092779698055)
              ·
                refine ⟨14714274858175639169547083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9809516572117092779698055 14714274858175639169547083)
                ·
                  refine ⟨22071412287263458754320625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14714274858175639169547083 22071412287263458754320625)
                  ·
                    refine ⟨16553559215447594065740469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22071412287263458754320625 16553559215447594065740469)
                    ·
                      refine ⟨1551896176448211943663169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16553559215447594065740469 1551896176448211943663169)
                      ·
                        rfl

theorem cell23_3022307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3022307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022307 prefixEnd_3022307 := by exact prefixLift 3022307
  have htrace : WordTrace (prefixWord ++ tailWord_3022307) baseStart_3022307 baseEnd_3022307 := by
    simpa [prefixWord, tailWord_3022307, baseEnd_3022307] using wordTrace_append hprefix tailTrace_3022307
  have hstable : (prefixWord ++ tailWord_3022307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022307).length < 2 ^ (prefixWord ++ tailWord_3022307).sum := by decide
  have hdescent : baseEnd_3022307 < baseStart_3022307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022357 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 6]
def baseStart_3022357 : Nat := 118140960795 + 3022357 * 2 ^ 59
def prefixEnd_3022357 : Nat := 4983230072969 + 3 ^ 40 * 3022357 * 2
def baseEnd_3022357 : Nat := 172435761164548527559771

theorem tailTrace_3022357 : CollatzResearch.WordTrace tailWord_3022357 prefixEnd_3022357 172435761164548527559771 := by
  unfold tailWord_3022357
  simp only [CollatzResearch.WordTrace]
  refine ⟨110234415911524241325721325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73489610607682827550480883 110234415911524241325721325)
  ·
    refine ⟨41337905966821590497145497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110234415911524241325721325 41337905966821590497145497)
    ·
      refine ⟨31003429475116192872859123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41337905966821590497145497 31003429475116192872859123)
      ·
        refine ⟨46505144212674289309288685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31003429475116192872859123 46505144212674289309288685)
        ·
          refine ⟨17439429079752858490983257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46505144212674289309288685 17439429079752858490983257)
          ·
            refine ⟨13079571809814643868237443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17439429079752858490983257 13079571809814643868237443)
            ·
              refine ⟨19619357714721965802356165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13079571809814643868237443 19619357714721965802356165)
              ·
                refine ⟨3678629571510368587941781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19619357714721965802356165 3678629571510368587941781)
                ·
                  refine ⟨172435761164548527559771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3678629571510368587941781 172435761164548527559771)
                  ·
                    rfl

theorem cell23_3022357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_3022357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022357 prefixEnd_3022357 := by exact prefixLift 3022357
  have htrace : WordTrace (prefixWord ++ tailWord_3022357) baseStart_3022357 baseEnd_3022357 := by
    simpa [prefixWord, tailWord_3022357, baseEnd_3022357] using wordTrace_append hprefix tailTrace_3022357
  have hstable : (prefixWord ++ tailWord_3022357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022357).length < 2 ^ (prefixWord ++ tailWord_3022357).sum := by decide
  have hdescent : baseEnd_3022357 < baseStart_3022357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3022387 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 3, 5]
def baseStart_3022387 : Nat := 118140960795 + 3022387 * 2 ^ 59
def prefixEnd_3022387 : Nat := 4983230072969 + 3 ^ 40 * 3022387 * 2
def baseEnd_3022387 : Nat := 517312418300190543554267

theorem tailTrace_3022387 : CollatzResearch.WordTrace tailWord_3022387 prefixEnd_3022387 517312418300190543554267 := by
  unfold tailWord_3022387
  simp only [CollatzResearch.WordTrace]
  refine ⟨110235510101415556449313415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73490340067610370966208943 110235510101415556449313415)
  ·
    refine ⟨165353265152123334673970123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110235510101415556449313415 165353265152123334673970123)
    ·
      refine ⟨248029897728185002010955185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165353265152123334673970123 248029897728185002010955185)
      ·
        refine ⟨186022423296138751508216389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248029897728185002010955185 186022423296138751508216389)
        ·
          refine ⟨34879204368026015907790573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186022423296138751508216389 34879204368026015907790573)
          ·
            refine ⟨13079701638009755965421465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34879204368026015907790573 13079701638009755965421465)
            ·
              refine ⟨9809776228507316974066099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13079701638009755965421465 9809776228507316974066099)
              ·
                refine ⟨14714664342760975461099149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9809776228507316974066099 14714664342760975461099149)
                ·
                  refine ⟨5517999128535365797912181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14714664342760975461099149 5517999128535365797912181)
                  ·
                    refine ⟨517312418300190543554267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5517999128535365797912181 517312418300190543554267)
                    ·
                      rfl

theorem cell23_3022387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 5].length) (baseStart_3022387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3022387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3022387 prefixEnd_3022387 := by exact prefixLift 3022387
  have htrace : WordTrace (prefixWord ++ tailWord_3022387) baseStart_3022387 baseEnd_3022387 := by
    simpa [prefixWord, tailWord_3022387, baseEnd_3022387] using wordTrace_append hprefix tailTrace_3022387
  have hstable : (prefixWord ++ tailWord_3022387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3022387).length < 2 ^ (prefixWord ++ tailWord_3022387).sum := by decide
  have hdescent : baseEnd_3022387 < baseStart_3022387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3022387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
