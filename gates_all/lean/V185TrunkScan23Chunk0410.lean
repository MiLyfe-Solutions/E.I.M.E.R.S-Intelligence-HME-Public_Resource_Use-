import V185TrunkScan23Chunk0409

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2424026 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_2424026 : Nat := 118140960795 + 2424026 * 2 ^ 59
def prefixEnd_2424026 : Nat := 4983230072969 + 3 ^ 40 * 2424026 * 2
def baseEnd_2424026 : Nat := 1244690456995638220827113

theorem tailTrace_2424026 : CollatzResearch.WordTrace tailWord_2424026 prefixEnd_2424026 1244690456995638220827113 := by
  unfold tailWord_2424026
  simp only [CollatzResearch.WordTrace]
  refine ⟨22102872879043816881606983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58940994344116845017618621 22102872879043816881606983)
  ·
    refine ⟨33154309318565725322410475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22102872879043816881606983 33154309318565725322410475)
    ·
      refine ⟨49731463977848587983615713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33154309318565725322410475 49731463977848587983615713)
      ·
        refine ⟨37298597983386440987711785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49731463977848587983615713 37298597983386440987711785)
        ·
          refine ⟨27973948487539830740783839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37298597983386440987711785 27973948487539830740783839)
          ·
            refine ⟨41960922731309746111175759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27973948487539830740783839 41960922731309746111175759)
            ·
              refine ⟨62941384096964619166763639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41960922731309746111175759 62941384096964619166763639)
              ·
                refine ⟨94412076145446928750145459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62941384096964619166763639 94412076145446928750145459)
                ·
                  refine ⟨141618114218170393125218189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94412076145446928750145459 141618114218170393125218189)
                  ·
                    refine ⟨53106792831813897421956821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141618114218170393125218189 53106792831813897421956821)
                    ·
                      refine ⟨1244690456995638220827113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53106792831813897421956821 1244690456995638220827113)
                      ·
                        rfl

theorem cell23_2424026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_2424026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424026 prefixEnd_2424026 := by exact prefixLift 2424026
  have htrace : WordTrace (prefixWord ++ tailWord_2424026) baseStart_2424026 baseEnd_2424026 := by
    simpa [prefixWord, tailWord_2424026, baseEnd_2424026] using wordTrace_append hprefix tailTrace_2424026
  have hstable : (prefixWord ++ tailWord_2424026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424026).length < 2 ^ (prefixWord ++ tailWord_2424026).sum := by decide
  have hdescent : baseEnd_2424026 < baseStart_2424026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424033 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 3, 5]
def baseStart_2424033 : Nat := 118140960795 + 2424033 * 2 ^ 59
def prefixEnd_2424033 : Nat := 4983230072969 + 3 ^ 40 * 2424033 * 2
def baseEnd_2424033 : Nat := 414898017120073231146527

theorem tailTrace_2424033 : CollatzResearch.WordTrace tailWord_2424033 prefixEnd_2424033 414898017120073231146527 := by
  unfold tailWord_2424033
  simp only [CollatzResearch.WordTrace]
  refine ⟨88411746827149907721932753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58941164551433271814621835 88411746827149907721932753)
  ·
    refine ⟨66308810120362430791449565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88411746827149907721932753 66308810120362430791449565)
    ·
      refine ⟨24865803795135911546793587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66308810120362430791449565 24865803795135911546793587)
      ·
        refine ⟨37298705692703867320190381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24865803795135911546793587 37298705692703867320190381)
        ·
          refine ⟨13987014634763950245071393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37298705692703867320190381 13987014634763950245071393)
          ·
            refine ⟨10490260976072962683803545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13987014634763950245071393 10490260976072962683803545)
            ·
              refine ⟨7867695732054722012852659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10490260976072962683803545 7867695732054722012852659)
              ·
                refine ⟨11801543598082083019278989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7867695732054722012852659 11801543598082083019278989)
                ·
                  refine ⟨4425578849280781132229621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11801543598082083019278989 4425578849280781132229621)
                  ·
                    refine ⟨414898017120073231146527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4425578849280781132229621 414898017120073231146527)
                    ·
                      rfl

theorem cell23_2424033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_2424033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424033 prefixEnd_2424033 := by exact prefixLift 2424033
  have htrace : WordTrace (prefixWord ++ tailWord_2424033) baseStart_2424033 baseEnd_2424033 := by
    simpa [prefixWord, tailWord_2424033, baseEnd_2424033] using wordTrace_append hprefix tailTrace_2424033
  have hstable : (prefixWord ++ tailWord_2424033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424033).length < 2 ^ (prefixWord ++ tailWord_2424033).sum := by decide
  have hdescent : baseEnd_2424033 < baseStart_2424033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424040 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_2424040 : Nat := 118140960795 + 2424040 * 2 ^ 59
def prefixEnd_2424040 : Nat := 4983230072969 + 3 ^ 40 * 2424040 * 2
def baseEnd_2424040 : Nat := 1244697645724801166052049

theorem tailTrace_2424040 : CollatzResearch.WordTrace tailWord_2424040 prefixEnd_2424040 1244697645724801166052049 := by
  unfold tailWord_2424040
  simp only [CollatzResearch.WordTrace]
  refine ⟨44206001069062273958718787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58941334758749698611625049 44206001069062273958718787)
  ·
    refine ⟨66309001603593410938078181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44206001069062273958718787 66309001603593410938078181)
    ·
      refine ⟨12432937800673764550889659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66309001603593410938078181 12432937800673764550889659)
      ·
        refine ⟨18649406701010646826334489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12432937800673764550889659 18649406701010646826334489)
        ·
          refine ⟨13987055025757985119750867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18649406701010646826334489 13987055025757985119750867)
          ·
            refine ⟨20980582538636977679626301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13987055025757985119750867 20980582538636977679626301)
            ·
              refine ⟨7867718451988866629859863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20980582538636977679626301 7867718451988866629859863)
              ·
                refine ⟨11801577677983299944789795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7867718451988866629859863 11801577677983299944789795)
                ·
                  refine ⟨17702366516974949917184693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11801577677983299944789795 17702366516974949917184693)
                  ·
                    refine ⟨1659596860966401554736065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17702366516974949917184693 1659596860966401554736065)
                    ·
                      refine ⟨1244697645724801166052049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1659596860966401554736065 1244697645724801166052049)
                      ·
                        rfl

theorem cell23_2424040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_2424040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424040 prefixEnd_2424040 := by exact prefixLift 2424040
  have htrace : WordTrace (prefixWord ++ tailWord_2424040) baseStart_2424040 baseEnd_2424040 := by
    simpa [prefixWord, tailWord_2424040, baseEnd_2424040] using wordTrace_append hprefix tailTrace_2424040
  have hstable : (prefixWord ++ tailWord_2424040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424040).length < 2 ^ (prefixWord ++ tailWord_2424040).sum := by decide
  have hdescent : baseEnd_2424040 < baseStart_2424040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424073 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_2424073 : Nat := 118140960795 + 2424073 * 2 ^ 59
def prefixEnd_2424073 : Nat := 4983230072969 + 3 ^ 40 * 2424073 * 2
def baseEnd_2424073 : Nat := 1244714590586399536939397

theorem tailTrace_2424073 : CollatzResearch.WordTrace tailWord_2424073 prefixEnd_2424073 1244714590586399536939397 := by
  unfold tailWord_2424073
  simp only [CollatzResearch.WordTrace]
  refine ⟨88413205747004994553388873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58942137164669996368925915 88413205747004994553388873)
  ·
    refine ⟨66309904310253745915041655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88413205747004994553388873 66309904310253745915041655)
    ·
      refine ⟨99464856465380618872562483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66309904310253745915041655 99464856465380618872562483)
      ·
        refine ⟨149197284698070928308843725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99464856465380618872562483 149197284698070928308843725)
        ·
          refine ⟨55948981761776598115816397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149197284698070928308843725 55948981761776598115816397)
          ·
            refine ⟨20980868160666224293431149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55948981761776598115816397 20980868160666224293431149)
            ·
              refine ⟨7867825560249834110036681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20980868160666224293431149 7867825560249834110036681)
              ·
                refine ⟨5900869170187375582527511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7867825560249834110036681 5900869170187375582527511)
                ·
                  refine ⟨8851303755281063373791267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5900869170187375582527511 8851303755281063373791267)
                  ·
                    refine ⟨13276955632921595060686901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8851303755281063373791267 13276955632921595060686901)
                    ·
                      refine ⟨1244714590586399536939397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13276955632921595060686901 1244714590586399536939397)
                      ·
                        rfl

theorem cell23_2424073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_2424073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424073 prefixEnd_2424073 := by exact prefixLift 2424073
  have htrace : WordTrace (prefixWord ++ tailWord_2424073) baseStart_2424073 baseEnd_2424073 := by
    simpa [prefixWord, tailWord_2424073, baseEnd_2424073] using wordTrace_append hprefix tailTrace_2424073
  have hstable : (prefixWord ++ tailWord_2424073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424073).length < 2 ^ (prefixWord ++ tailWord_2424073).sum := by decide
  have hdescent : baseEnd_2424073 < baseStart_2424073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424087 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 3, 2, 2]
def baseStart_2424087 : Nat := 118140960795 + 2424087 * 2 ^ 59
def prefixEnd_2424087 : Nat := 4983230072969 + 3 ^ 40 * 2424087 * 2
def baseEnd_2424087 : Nat := 1244721779315562482164333

theorem tailTrace_2424087 : CollatzResearch.WordTrace tailWord_2424087 prefixEnd_2424087 1244721779315562482164333 := by
  unfold tailWord_2424087
  simp only [CollatzResearch.WordTrace]
  refine ⟨88413716368954274944398515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58942477579302849962932343 88413716368954274944398515)
  ·
    refine ⟨132620574553431412416597773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88413716368954274944398515 132620574553431412416597773)
    ·
      refine ⟨49732715457536779656224165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132620574553431412416597773 49732715457536779656224165)
      ·
        refine ⟨9324884148288146185542031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49732715457536779656224165 9324884148288146185542031)
        ·
          refine ⟨13987326222432219278313047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9324884148288146185542031 13987326222432219278313047)
          ·
            refine ⟨20980989333648328917469571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13987326222432219278313047 20980989333648328917469571)
            ·
              refine ⟨31471484000472493376204357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20980989333648328917469571 31471484000472493376204357)
              ·
                refine ⟨5900903250088592508038317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31471484000472493376204357 5900903250088592508038317)
                ·
                  refine ⟨2212838718783222190514369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5900903250088592508038317 2212838718783222190514369)
                  ·
                    refine ⟨1659629039087416642885777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2212838718783222190514369 1659629039087416642885777)
                    ·
                      refine ⟨1244721779315562482164333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1659629039087416642885777 1244721779315562482164333)
                      ·
                        rfl

theorem cell23_2424087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_2424087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424087 prefixEnd_2424087 := by exact prefixLift 2424087
  have htrace : WordTrace (prefixWord ++ tailWord_2424087) baseStart_2424087 baseEnd_2424087 := by
    simpa [prefixWord, tailWord_2424087, baseEnd_2424087] using wordTrace_append hprefix tailTrace_2424087
  have hstable : (prefixWord ++ tailWord_2424087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424087).length < 2 ^ (prefixWord ++ tailWord_2424087).sum := by decide
  have hdescent : baseEnd_2424087 < baseStart_2424087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424098 : List Nat := [3, 3, 1, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_2424098 : Nat := 118140960795 + 2424098 * 2 ^ 59
def prefixEnd_2424098 : Nat := 4983230072969 + 3 ^ 40 * 2424098 * 2
def baseEnd_2424098 : Nat := 1244727427602761939126783

theorem tailTrace_2424098 : CollatzResearch.WordTrace tailWord_2424098 prefixEnd_2424098 1244727427602761939126783 := by
  unfold tailWord_2424098
  simp only [CollatzResearch.WordTrace]
  refine ⟨22103529392978605955762237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58942745047942949215365965 22103529392978605955762237)
  ·
    refine ⟨8288823522366977233410839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22103529392978605955762237 8288823522366977233410839)
    ·
      refine ⟨12433235283550465850116259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8288823522366977233410839 12433235283550465850116259)
      ·
        refine ⟨18649852925325698775174389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12433235283550465850116259 18649852925325698775174389)
        ·
          refine ⟨1748423711749284260172599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18649852925325698775174389 1748423711749284260172599)
          ·
            refine ⟨2622635567623926390258899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748423711749284260172599 2622635567623926390258899)
            ·
              refine ⟨3933953351435889585388349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622635567623926390258899 3933953351435889585388349)
              ·
                refine ⟨1475232506788458594520631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3933953351435889585388349 1475232506788458594520631)
                ·
                  refine ⟨2212848760182687891780947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1475232506788458594520631 2212848760182687891780947)
                  ·
                    refine ⟨3319273140274031837671421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2212848760182687891780947 3319273140274031837671421)
                    ·
                      refine ⟨1244727427602761939126783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3319273140274031837671421 1244727427602761939126783)
                      ·
                        rfl

theorem cell23_2424098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_2424098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424098 prefixEnd_2424098 := by exact prefixLift 2424098
  have htrace : WordTrace (prefixWord ++ tailWord_2424098) baseStart_2424098 baseEnd_2424098 := by
    simpa [prefixWord, tailWord_2424098, baseEnd_2424098] using wordTrace_append hprefix tailTrace_2424098
  have hstable : (prefixWord ++ tailWord_2424098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424098).length < 2 ^ (prefixWord ++ tailWord_2424098).sum := by decide
  have hdescent : baseEnd_2424098 < baseStart_2424098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424121 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2424121 : Nat := 118140960795 + 2424121 * 2 ^ 59
def prefixEnd_2424121 : Nat := 4983230072969 + 3 ^ 40 * 2424121 * 2
def baseEnd_2424121 : Nat := 1244739237657815349139177

theorem tailTrace_2424121 : CollatzResearch.WordTrace tailWord_2424121 prefixEnd_2424121 1244739237657815349139177 := by
  unfold tailWord_2424121
  simp only [CollatzResearch.WordTrace]
  refine ⟨88414956450831098751136217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58943304300554065834090811 88414956450831098751136217)
  ·
    refine ⟨66311217338123324063352163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88414956450831098751136217 66311217338123324063352163)
    ·
      refine ⟨99466826007184986095028245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66311217338123324063352163 99466826007184986095028245)
      ·
        refine ⟨4662507469086796223204449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99466826007184986095028245 4662507469086796223204449)
        ·
          refine ⟨3496880601815097167403337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4662507469086796223204449 3496880601815097167403337)
          ·
            refine ⟨2622660451361322875552503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3496880601815097167403337 2622660451361322875552503)
            ·
              refine ⟨3933990677041984313328755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622660451361322875552503 3933990677041984313328755)
              ·
                refine ⟨5900986015562976469993133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933990677041984313328755 5900986015562976469993133)
                ·
                  refine ⟨2212869755836116176247425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5900986015562976469993133 2212869755836116176247425)
                  ·
                    refine ⟨1659652316877087132185569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2212869755836116176247425 1659652316877087132185569)
                    ·
                      refine ⟨1244739237657815349139177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1659652316877087132185569 1244739237657815349139177)
                      ·
                        rfl

theorem cell23_2424121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2424121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424121 prefixEnd_2424121 := by exact prefixLift 2424121
  have htrace : WordTrace (prefixWord ++ tailWord_2424121) baseStart_2424121 baseEnd_2424121 := by
    simpa [prefixWord, tailWord_2424121, baseEnd_2424121] using wordTrace_append hprefix tailTrace_2424121
  have hstable : (prefixWord ++ tailWord_2424121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424121).length < 2 ^ (prefixWord ++ tailWord_2424121).sum := by decide
  have hdescent : baseEnd_2424121 < baseStart_2424121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424177 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 4, 2, 2]
def baseStart_2424177 : Nat := 118140960795 + 2424177 * 2 ^ 59
def prefixEnd_2424177 : Nat := 4983230072969 + 3 ^ 40 * 2424177 * 2
def baseEnd_2424177 : Nat := 1244767992574467130038919

theorem tailTrace_2424177 : CollatzResearch.WordTrace tailWord_2424177 prefixEnd_2424177 1244767992574467130038919 := by
  unfold tailWord_2424177
  simp only [CollatzResearch.WordTrace]
  refine ⟨88416998938628220315174785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58944665959085480210116523 88416998938628220315174785)
  ·
    refine ⟨66312749203971165236381089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88416998938628220315174785 66312749203971165236381089)
    ·
      refine ⟨49734561902978373927285817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66312749203971165236381089 49734561902978373927285817)
      ·
        refine ⟨37300921427233780445464363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49734561902978373927285817 37300921427233780445464363)
        ·
          refine ⟨55951382140850670668196545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37300921427233780445464363 55951382140850670668196545)
          ·
            refine ⟨41963536605638003001147409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55951382140850670668196545 41963536605638003001147409)
            ·
              refine ⟨31472652454228502250860557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41963536605638003001147409 31472652454228502250860557)
              ·
                refine ⟨11802244670335688344072709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31472652454228502250860557 11802244670335688344072709)
                ·
                  refine ⟨2212920875687941564513633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11802244670335688344072709 2212920875687941564513633)
                  ·
                    refine ⟨1659690656765956173385225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2212920875687941564513633 1659690656765956173385225)
                    ·
                      refine ⟨1244767992574467130038919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1659690656765956173385225 1244767992574467130038919)
                      ·
                        rfl

theorem cell23_2424177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_2424177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424177 prefixEnd_2424177 := by exact prefixLift 2424177
  have htrace : WordTrace (prefixWord ++ tailWord_2424177) baseStart_2424177 baseEnd_2424177 := by
    simpa [prefixWord, tailWord_2424177, baseEnd_2424177] using wordTrace_append hprefix tailTrace_2424177
  have hstable : (prefixWord ++ tailWord_2424177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424177).length < 2 ^ (prefixWord ++ tailWord_2424177).sum := by decide
  have hdescent : baseEnd_2424177 < baseStart_2424177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424183 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 7]
def baseStart_2424183 : Nat := 118140960795 + 2424183 * 2 ^ 59
def prefixEnd_2424183 : Nat := 4983230072969 + 3 ^ 40 * 2424183 * 2
def baseEnd_2424183 : Nat := 138307897050932678507099

theorem tailTrace_2424183 : CollatzResearch.WordTrace tailWord_2424183 prefixEnd_2424183 138307897050932678507099 := by
  unfold tailWord_2424183
  simp only [CollatzResearch.WordTrace]
  refine ⟨88417217776606483339893203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58944811851070988893262135 88417217776606483339893203)
  ·
    refine ⟨132625826664909725009839805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88417217776606483339893203 132625826664909725009839805)
    ·
      refine ⟨49734684999341146878689927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132625826664909725009839805 49734684999341146878689927)
      ·
        refine ⟨74602027499011720318034891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49734684999341146878689927 74602027499011720318034891)
        ·
          refine ⟨111903041248517580477052337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74602027499011720318034891 111903041248517580477052337)
          ·
            refine ⟨83927280936388185357789253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111903041248517580477052337 83927280936388185357789253)
            ·
              refine ⟨15736365175572784754585485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83927280936388185357789253 15736365175572784754585485)
              ·
                refine ⟨5901136940839794282969557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15736365175572784754585485 5901136940839794282969557)
                ·
                  refine ⟨138307897050932678507099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5901136940839794282969557 138307897050932678507099)
                  ·
                    rfl

theorem cell23_2424183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 7].length) (baseStart_2424183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424183 prefixEnd_2424183 := by exact prefixLift 2424183
  have htrace : WordTrace (prefixWord ++ tailWord_2424183) baseStart_2424183 baseEnd_2424183 := by
    simpa [prefixWord, tailWord_2424183, baseEnd_2424183] using wordTrace_append hprefix tailTrace_2424183
  have hstable : (prefixWord ++ tailWord_2424183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424183).length < 2 ^ (prefixWord ++ tailWord_2424183).sum := by decide
  have hdescent : baseEnd_2424183 < baseStart_2424183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424200 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 7]
def baseStart_2424200 : Nat := 118140960795 + 2424200 * 2 ^ 59
def prefixEnd_2424200 : Nat := 4983230072969 + 3 ^ 40 * 2424200 * 2
def baseEnd_2424200 : Nat := 138308866958835615561257

theorem tailTrace_2424200 : CollatzResearch.WordTrace tailWord_2424200 prefixEnd_2424200 138308866958835615561257 := by
  unfold tailWord_2424200
  simp only [CollatzResearch.WordTrace]
  refine ⟨44208918908772447621631027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58945225211696596828841369 44208918908772447621631027)
  ·
    refine ⟨66313378363158671432446541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44208918908772447621631027 66313378363158671432446541)
    ·
      refine ⟨24867516886184501787167453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66313378363158671432446541 24867516886184501787167453)
      ·
        refine ⟨9325318832319188170187795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24867516886184501787167453 9325318832319188170187795)
        ·
          refine ⟨13987978248478782255281693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9325318832319188170187795 13987978248478782255281693)
          ·
            refine ⟨5245491843179543345730635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13987978248478782255281693 5245491843179543345730635)
            ·
              refine ⟨7868237764769315018595953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5245491843179543345730635 7868237764769315018595953)
              ·
                refine ⟨5901178323576986263946965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7868237764769315018595953 5901178323576986263946965)
                ·
                  refine ⟨138308866958835615561257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5901178323576986263946965 138308866958835615561257)
                  ·
                    rfl

theorem cell23_2424200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 7].length) (baseStart_2424200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424200 prefixEnd_2424200 := by exact prefixLift 2424200
  have htrace : WordTrace (prefixWord ++ tailWord_2424200) baseStart_2424200 baseEnd_2424200 := by
    simpa [prefixWord, tailWord_2424200, baseEnd_2424200] using wordTrace_append hprefix tailTrace_2424200
  have hstable : (prefixWord ++ tailWord_2424200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424200).length < 2 ^ (prefixWord ++ tailWord_2424200).sum := by decide
  have hdescent : baseEnd_2424200 < baseStart_2424200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424217 : List Nat := [1, 2, 1, 2, 1, 6, 2, 3, 5]
def baseStart_2424217 : Nat := 118140960795 + 2424217 * 2 ^ 59
def prefixEnd_2424217 : Nat := 4983230072969 + 3 ^ 40 * 2424217 * 2
def baseEnd_2424217 : Nat := 138309836866738552615415

theorem tailTrace_2424217 : CollatzResearch.WordTrace tailWord_2424217 prefixEnd_2424217 138309836866738552615415 := by
  unfold tailWord_2424217
  simp only [CollatzResearch.WordTrace]
  refine ⟨88418457858483307146630905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58945638572322204764420603 88418457858483307146630905)
  ·
    refine ⟨66313843393862480359973179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88418457858483307146630905 66313843393862480359973179)
    ·
      refine ⟨99470765090793720539959769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66313843393862480359973179 99470765090793720539959769)
      ·
        refine ⟨74603073818095290404969827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99470765090793720539959769 74603073818095290404969827)
        ·
          refine ⟨111904610727142935607454741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74603073818095290404969827 111904610727142935607454741)
          ·
            refine ⟨5245528627834825106599441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111904610727142935607454741 5245528627834825106599441)
            ·
              refine ⟨3934146470876118829949581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5245528627834825106599441 3934146470876118829949581)
              ·
                refine ⟨1475304926578544561231093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3934146470876118829949581 1475304926578544561231093)
                ·
                  refine ⟨138309836866738552615415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1475304926578544561231093 138309836866738552615415)
                  ·
                    rfl

theorem cell23_2424217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 5].length) (baseStart_2424217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424217 prefixEnd_2424217 := by exact prefixLift 2424217
  have htrace : WordTrace (prefixWord ++ tailWord_2424217) baseStart_2424217 baseEnd_2424217 := by
    simpa [prefixWord, tailWord_2424217, baseEnd_2424217] using wordTrace_append hprefix tailTrace_2424217
  have hstable : (prefixWord ++ tailWord_2424217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424217).length < 2 ^ (prefixWord ++ tailWord_2424217).sum := by decide
  have hdescent : baseEnd_2424217 < baseStart_2424217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424283 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 9]
def baseStart_2424283 : Nat := 118140960795 + 2424283 * 2 ^ 59
def prefixEnd_2424283 : Nat := 4983230072969 + 3 ^ 40 * 2424283 * 2
def baseEnd_2424283 : Nat := 1244822421523843715313431

theorem tailTrace_2424283 : CollatzResearch.WordTrace tailWord_2424283 prefixEnd_2424283 1244822421523843715313431 := by
  unfold tailWord_2424283
  simp only [CollatzResearch.WordTrace]
  refine ⟨88420865076244200418533503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58947243384162800279022335 88420865076244200418533503)
  ·
    refine ⟨132631297614366300627800255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88420865076244200418533503 132631297614366300627800255)
    ·
      refine ⟨198946946421549450941700383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132631297614366300627800255 198946946421549450941700383)
      ·
        refine ⟨298420419632324176412550575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198946946421549450941700383 298420419632324176412550575)
        ·
          refine ⟨447630629448486264618825863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298420419632324176412550575 447630629448486264618825863)
          ·
            refine ⟨671445944172729396928238795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447630629448486264618825863 671445944172729396928238795)
            ·
              refine ⟨1007168916259094095392358193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671445944172729396928238795 1007168916259094095392358193)
              ·
                refine ⟨755376687194320571544268645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007168916259094095392358193 755376687194320571544268645)
                ·
                  refine ⟨141633128848935107164550371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 755376687194320571544268645 141633128848935107164550371)
                  ·
                    refine ⟨212449693273402660746825557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141633128848935107164550371 212449693273402660746825557)
                    ·
                      refine ⟨1244822421523843715313431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 212449693273402660746825557 1244822421523843715313431)
                      ·
                        rfl

theorem cell23_2424283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_2424283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424283 prefixEnd_2424283 := by exact prefixLift 2424283
  have htrace : WordTrace (prefixWord ++ tailWord_2424283) baseStart_2424283 baseEnd_2424283 := by
    simpa [prefixWord, tailWord_2424283, baseEnd_2424283] using wordTrace_append hprefix tailTrace_2424283
  have hstable : (prefixWord ++ tailWord_2424283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424283).length < 2 ^ (prefixWord ++ tailWord_2424283).sum := by decide
  have hdescent : baseEnd_2424283 < baseStart_2424283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424287 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 3]
def baseStart_2424287 : Nat := 118140960795 + 2424287 * 2 ^ 59
def prefixEnd_2424287 : Nat := 4983230072969 + 3 ^ 40 * 2424287 * 2
def baseEnd_2424287 : Nat := 1244824475446461699663413

theorem tailTrace_2424287 : CollatzResearch.WordTrace tailWord_2424287 prefixEnd_2424287 1244824475446461699663413 := by
  unfold tailWord_2424287
  simp only [CollatzResearch.WordTrace]
  refine ⟨88421010968229709101679115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58947340645486472734452743 88421010968229709101679115)
  ·
    refine ⟨132631516452344563652518673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88421010968229709101679115 132631516452344563652518673)
    ·
      refine ⟨99473637339258422739389005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132631516452344563652518673 99473637339258422739389005)
      ·
        refine ⟨37302614002221908527270877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99473637339258422739389005 37302614002221908527270877)
        ·
          refine ⟨13988480250833215697726579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37302614002221908527270877 13988480250833215697726579)
          ·
            refine ⟨20982720376249823546589869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13988480250833215697726579 20982720376249823546589869)
            ·
              refine ⟨7868520141093683829971201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20982720376249823546589869 7868520141093683829971201)
              ·
                refine ⟨5901390105820262872478401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7868520141093683829971201 5901390105820262872478401)
                ·
                  refine ⟨4426042579365197154358801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5901390105820262872478401 4426042579365197154358801)
                  ·
                    refine ⟨3319531934523897865769101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4426042579365197154358801 3319531934523897865769101)
                    ·
                      refine ⟨1244824475446461699663413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3319531934523897865769101 1244824475446461699663413)
                      ·
                        rfl

theorem cell23_2424287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_2424287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424287 prefixEnd_2424287 := by exact prefixLift 2424287
  have htrace : WordTrace (prefixWord ++ tailWord_2424287) baseStart_2424287 baseEnd_2424287 := by
    simpa [prefixWord, tailWord_2424287, baseEnd_2424287] using wordTrace_append hprefix tailTrace_2424287
  have hstable : (prefixWord ++ tailWord_2424287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424287).length < 2 ^ (prefixWord ++ tailWord_2424287).sum := by decide
  have hdescent : baseEnd_2424287 < baseStart_2424287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424300 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_2424300 : Nat := 118140960795 + 2424300 * 2 ^ 59
def prefixEnd_2424300 : Nat := 4983230072969 + 3 ^ 40 * 2424300 * 2
def baseEnd_2424300 : Nat := 1244831150694970148800853

theorem tailTrace_2424300 : CollatzResearch.WordTrace tailWord_2424300 prefixEnd_2424300 1244831150694970148800853 := by
  unfold tailWord_2424300
  simp only [CollatzResearch.WordTrace]
  refine ⟨44210742558591306160951177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58947656744788408214601569 44210742558591306160951177)
  ·
    refine ⟨33158056918943479620713383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44210742558591306160951177 33158056918943479620713383)
    ·
      refine ⟨49737085378415219431070075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33158056918943479620713383 49737085378415219431070075)
      ·
        refine ⟨74605628067622829146605113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49737085378415219431070075 74605628067622829146605113)
        ·
          refine ⟨55954221050717121859953835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74605628067622829146605113 55954221050717121859953835)
          ·
            refine ⟨83931331576075682789930753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55954221050717121859953835 83931331576075682789930753)
            ·
              refine ⟨62948498682056762092448065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83931331576075682789930753 62948498682056762092448065)
              ·
                refine ⟨47211374011542571569336049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62948498682056762092448065 47211374011542571569336049)
                ·
                  refine ⟨35408530508656928677002037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47211374011542571569336049 35408530508656928677002037)
                  ·
                    refine ⟨3319549735186587063468941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35408530508656928677002037 3319549735186587063468941)
                    ·
                      refine ⟨1244831150694970148800853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3319549735186587063468941 1244831150694970148800853)
                      ·
                        rfl

theorem cell23_2424300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_2424300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424300 prefixEnd_2424300 := by exact prefixLift 2424300
  have htrace : WordTrace (prefixWord ++ tailWord_2424300) baseStart_2424300 baseEnd_2424300 := by
    simpa [prefixWord, tailWord_2424300, baseEnd_2424300] using wordTrace_append hprefix tailTrace_2424300
  have hstable : (prefixWord ++ tailWord_2424300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424300).length < 2 ^ (prefixWord ++ tailWord_2424300).sum := by decide
  have hdescent : baseEnd_2424300 < baseStart_2424300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424357 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 2, 6, 2]
def baseStart_2424357 : Nat := 118140960795 + 2424357 * 2 ^ 59
def prefixEnd_2424357 : Nat := 4983230072969 + 3 ^ 40 * 2424357 * 2
def baseEnd_2424357 : Nat := 1244860419092276425788091

theorem tailTrace_2424357 : CollatzResearch.WordTrace tailWord_2424357 prefixEnd_2424357 1244860419092276425788091 := by
  unfold tailWord_2424357
  simp only [CollatzResearch.WordTrace]
  refine ⟨88423564077976111056727325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58949042718650740704484883 88423564077976111056727325)
  ·
    refine ⟨33158836529241041646272747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88423564077976111056727325 33158836529241041646272747)
    ·
      refine ⟨49738254793861562469409121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33158836529241041646272747 49738254793861562469409121)
      ·
        refine ⟨37303691095396171852056841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49738254793861562469409121 37303691095396171852056841)
        ·
          refine ⟨27977768321547128889042631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37303691095396171852056841 27977768321547128889042631)
          ·
            refine ⟨41966652482320693333563947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27977768321547128889042631 41966652482320693333563947)
            ·
              refine ⟨62949978723481040000345921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41966652482320693333563947 62949978723481040000345921)
              ·
                refine ⟨47212484042610780000259441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62949978723481040000345921 47212484042610780000259441)
                ·
                  refine ⟨35409363031958085000194581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47212484042610780000259441 35409363031958085000194581)
                  ·
                    refine ⟨1659813892123035234384121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35409363031958085000194581 1659813892123035234384121)
                    ·
                      refine ⟨1244860419092276425788091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1659813892123035234384121 1244860419092276425788091)
                      ·
                        rfl

theorem cell23_2424357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_2424357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424357 prefixEnd_2424357 := by exact prefixLift 2424357
  have htrace : WordTrace (prefixWord ++ tailWord_2424357) baseStart_2424357 baseEnd_2424357 := by
    simpa [prefixWord, tailWord_2424357, baseEnd_2424357] using wordTrace_append hprefix tailTrace_2424357
  have hstable : (prefixWord ++ tailWord_2424357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424357).length < 2 ^ (prefixWord ++ tailWord_2424357).sum := by decide
  have hdescent : baseEnd_2424357 < baseStart_2424357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424394 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_2424394 : Nat := 118140960795 + 2424394 * 2 ^ 59
def prefixEnd_2424394 : Nat := 4983230072969 + 3 ^ 40 * 2424394 * 2
def baseEnd_2424394 : Nat := 1244879417876492781025421

theorem tailTrace_2424394 : CollatzResearch.WordTrace tailWord_2424394 prefixEnd_2424394 1244879417876492781025421 := by
  unfold tailWord_2424394
  simp only [CollatzResearch.WordTrace]
  refine ⟨22106228394710516593956059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58949942385894710917216157 22106228394710516593956059)
  ·
    refine ⟨33159342592065774890934089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22106228394710516593956059 33159342592065774890934089)
    ·
      refine ⟨24869506944049331168200567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33159342592065774890934089 24869506944049331168200567)
      ·
        refine ⟨37304260416073996752300851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24869506944049331168200567 37304260416073996752300851)
        ·
          refine ⟨55956390624110995128451277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37304260416073996752300851 55956390624110995128451277)
          ·
            refine ⟨20983646484041623173169229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55956390624110995128451277 20983646484041623173169229)
            ·
              refine ⟨7868867431515608689938461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20983646484041623173169229 7868867431515608689938461)
              ·
                refine ⟨2950825286818353258726923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7868867431515608689938461 2950825286818353258726923)
                ·
                  refine ⟨4426237930227529888090385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950825286818353258726923 4426237930227529888090385)
                  ·
                    refine ⟨3319678447670647416067789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4426237930227529888090385 3319678447670647416067789)
                    ·
                      refine ⟨1244879417876492781025421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3319678447670647416067789 1244879417876492781025421)
                      ·
                        rfl

theorem cell23_2424394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_2424394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424394 prefixEnd_2424394 := by exact prefixLift 2424394
  have htrace : WordTrace (prefixWord ++ tailWord_2424394) baseStart_2424394 baseEnd_2424394 := by
    simpa [prefixWord, tailWord_2424394, baseEnd_2424394] using wordTrace_append hprefix tailTrace_2424394
  have hstable : (prefixWord ++ tailWord_2424394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424394).length < 2 ^ (prefixWord ++ tailWord_2424394).sum := by decide
  have hdescent : baseEnd_2424394 < baseStart_2424394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424410 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_2424410 : Nat := 118140960795 + 2424410 * 2 ^ 59
def prefixEnd_2424410 : Nat := 4983230072969 + 3 ^ 40 * 2424410 * 2
def baseEnd_2424410 : Nat := 414962544522321572808449

theorem tailTrace_2424410 : CollatzResearch.WordTrace tailWord_2424410 prefixEnd_2424410 414962544522321572808449 := by
  unfold tailWord_2424410
  simp only [CollatzResearch.WordTrace]
  refine ⟨22106374286696025277101671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58950331431189400738937789 22106374286696025277101671)
  ·
    refine ⟨33159561430044037915652507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22106374286696025277101671 33159561430044037915652507)
    ·
      refine ⟨49739342145066056873478761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33159561430044037915652507 49739342145066056873478761)
      ·
        refine ⟨37304506608799542655109071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49739342145066056873478761 37304506608799542655109071)
        ·
          refine ⟨55956759913199313982663607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37304506608799542655109071 55956759913199313982663607)
          ·
            refine ⟨83935139869798970973995411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55956759913199313982663607 83935139869798970973995411)
            ·
              refine ⟨125902709804698456460993117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83935139869798970973995411 125902709804698456460993117)
              ·
                refine ⟨47213516176761921172872419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125902709804698456460993117 47213516176761921172872419)
                ·
                  refine ⟨70820274265142881759308629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47213516176761921172872419 70820274265142881759308629)
                  ·
                    refine ⟨414962544522321572808449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 70820274265142881759308629 414962544522321572808449)
                    ·
                      rfl

theorem cell23_2424410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_2424410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424410 prefixEnd_2424410 := by exact prefixLift 2424410
  have htrace : WordTrace (prefixWord ++ tailWord_2424410) baseStart_2424410 baseEnd_2424410 := by
    simpa [prefixWord, tailWord_2424410, baseEnd_2424410] using wordTrace_append hprefix tailTrace_2424410
  have hstable : (prefixWord ++ tailWord_2424410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424410).length < 2 ^ (prefixWord ++ tailWord_2424410).sum := by decide
  have hdescent : baseEnd_2424410 < baseStart_2424410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424477 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_2424477 : Nat := 118140960795 + 2424477 * 2 ^ 59
def prefixEnd_2424477 : Nat := 4983230072969 + 3 ^ 40 * 2424477 * 2
def baseEnd_2424477 : Nat := 1244922036770815956287539

theorem tailTrace_2424477 : CollatzResearch.WordTrace tailWord_2424477 prefixEnd_2424477 1244922036770815956287539 := by
  unfold tailWord_2424477
  simp only [CollatzResearch.WordTrace]
  refine ⟨88427940837541371551095685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58951960558360914367397123 88427940837541371551095685)
  ·
    refine ⟨16580238907039007165830441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88427940837541371551095685 16580238907039007165830441)
    ·
      refine ⟨12435179180279255374372831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16580238907039007165830441 12435179180279255374372831)
      ·
        refine ⟨18652768770418883061559247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12435179180279255374372831 18652768770418883061559247)
        ·
          refine ⟨27979153155628324592338871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18652768770418883061559247 27979153155628324592338871)
          ·
            refine ⟨41968729733442486888508307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27979153155628324592338871 41968729733442486888508307)
            ·
              refine ⟨62953094600163730332762461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41968729733442486888508307 62953094600163730332762461)
              ·
                refine ⟨23607410475061398874785923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62953094600163730332762461 23607410475061398874785923)
                ·
                  refine ⟨35411115712592098312178885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23607410475061398874785923 35411115712592098312178885)
                  ·
                    refine ⟨6639584196111018433533541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35411115712592098312178885 6639584196111018433533541)
                    ·
                      refine ⟨1244922036770815956287539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6639584196111018433533541 1244922036770815956287539)
                      ·
                        rfl

theorem cell23_2424477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_2424477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424477 prefixEnd_2424477 := by exact prefixLift 2424477
  have htrace : WordTrace (prefixWord ++ tailWord_2424477) baseStart_2424477 baseEnd_2424477 := by
    simpa [prefixWord, tailWord_2424477, baseEnd_2424477] using wordTrace_append hprefix tailTrace_2424477
  have hstable : (prefixWord ++ tailWord_2424477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424477).length < 2 ^ (prefixWord ++ tailWord_2424477).sum := by decide
  have hdescent : baseEnd_2424477 < baseStart_2424477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424502 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_2424502 : Nat := 118140960795 + 2424502 * 2 ^ 59
def prefixEnd_2424502 : Nat := 4983230072969 + 3 ^ 40 * 2424502 * 2
def baseEnd_2424502 : Nat := 1244934873787178358474925

theorem tailTrace_2424502 : CollatzResearch.WordTrace tailWord_2424502 prefixEnd_2424502 1244934873787178358474925 := by
  unfold tailWord_2424502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526803291403175051297235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58952568441633867213837173 5526803291403175051297235)
  ·
    refine ⟨8290204937104762576945853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5526803291403175051297235 8290204937104762576945853)
    ·
      refine ⟨3108826851414285966354695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8290204937104762576945853 3108826851414285966354695)
      ·
        refine ⟨4663240277121428949532043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108826851414285966354695 4663240277121428949532043)
        ·
          refine ⟨6994860415682143424298065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4663240277121428949532043 6994860415682143424298065)
          ·
            refine ⟨5246145311761607568223549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6994860415682143424298065 5246145311761607568223549)
            ·
              refine ⟨1967304491910602838083831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5246145311761607568223549 1967304491910602838083831)
              ·
                refine ⟨2950956737865904257125747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967304491910602838083831 2950956737865904257125747)
                ·
                  refine ⟨4426435106798856385688621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950956737865904257125747 4426435106798856385688621)
                  ·
                    refine ⟨1659913165049571144633233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4426435106798856385688621 1659913165049571144633233)
                    ·
                      refine ⟨1244934873787178358474925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1659913165049571144633233 1244934873787178358474925)
                      ·
                        rfl

theorem cell23_2424502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_2424502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424502 prefixEnd_2424502 := by exact prefixLift 2424502
  have htrace : WordTrace (prefixWord ++ tailWord_2424502) baseStart_2424502 baseEnd_2424502 := by
    simpa [prefixWord, tailWord_2424502, baseEnd_2424502] using wordTrace_append hprefix tailTrace_2424502
  have hstable : (prefixWord ++ tailWord_2424502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424502).length < 2 ^ (prefixWord ++ tailWord_2424502).sum := by decide
  have hdescent : baseEnd_2424502 < baseStart_2424502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424518 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2424518 : Nat := 118140960795 + 2424518 * 2 ^ 59
def prefixEnd_2424518 : Nat := 4983230072969 + 3 ^ 40 * 2424518 * 2
def baseEnd_2424518 : Nat := 1244943089477650295874851

theorem tailTrace_2424518 : CollatzResearch.WordTrace tailWord_2424518 prefixEnd_2424518 1244943089477650295874851 := by
  unfold tailWord_2424518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2763419882199776111041819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58952957486928557035558805 2763419882199776111041819)
  ·
    refine ⟨4145129823299664166562729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2763419882199776111041819 4145129823299664166562729)
    ·
      refine ⟨3108847367474748124922047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4145129823299664166562729 3108847367474748124922047)
      ·
        refine ⟨4663271051212122187383071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108847367474748124922047 4663271051212122187383071)
        ·
          refine ⟨6994906576818183281074607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4663271051212122187383071 6994906576818183281074607)
          ·
            refine ⟨10492359865227274921611911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6994906576818183281074607 10492359865227274921611911)
            ·
              refine ⟨15738539797840912382417867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10492359865227274921611911 15738539797840912382417867)
              ·
                refine ⟨23607809696761368573626801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15738539797840912382417867 23607809696761368573626801)
                ·
                  refine ⟨17705857272571026430220101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23607809696761368573626801 17705857272571026430220101)
                  ·
                    refine ⟨3319848238607067455666269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17705857272571026430220101 3319848238607067455666269)
                    ·
                      refine ⟨1244943089477650295874851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3319848238607067455666269 1244943089477650295874851)
                      ·
                        rfl

theorem cell23_2424518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2424518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424518 prefixEnd_2424518 := by exact prefixLift 2424518
  have htrace : WordTrace (prefixWord ++ tailWord_2424518) baseStart_2424518 baseEnd_2424518 := by
    simpa [prefixWord, tailWord_2424518, baseEnd_2424518] using wordTrace_append hprefix tailTrace_2424518
  have hstable : (prefixWord ++ tailWord_2424518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424518).length < 2 ^ (prefixWord ++ tailWord_2424518).sum := by decide
  have hdescent : baseEnd_2424518 < baseStart_2424518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424551 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 1, 7]
def baseStart_2424551 : Nat := 118140960795 + 2424551 * 2 ^ 59
def prefixEnd_2424551 : Nat := 4983230072969 + 3 ^ 40 * 2424551 * 2
def baseEnd_2424551 : Nat := 414986678113082888920733

theorem tailTrace_2424551 : CollatzResearch.WordTrace tailWord_2424551 prefixEnd_2424551 414986678113082888920733 := by
  unfold tailWord_2424551
  simp only [CollatzResearch.WordTrace]
  refine ⟨88430639839273282189289507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58953759892848854792859671 88430639839273282189289507)
  ·
    refine ⟨132645959758909923283934261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88430639839273282189289507 132645959758909923283934261)
    ·
      refine ⟨12435558727397805307868837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132645959758909923283934261 12435558727397805307868837)
      ·
        refine ⟨2331667261387088495225407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12435558727397805307868837 2331667261387088495225407)
        ·
          refine ⟨3497500892080632742838111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2331667261387088495225407 3497500892080632742838111)
          ·
            refine ⟨5246251338120949114257167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497500892080632742838111 5246251338120949114257167)
            ·
              refine ⟨7869377007181423671385751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5246251338120949114257167 7869377007181423671385751)
              ·
                refine ⟨11804065510772135507078627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7869377007181423671385751 11804065510772135507078627)
                ·
                  refine ⟨17706098266158203260617941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11804065510772135507078627 17706098266158203260617941)
                  ·
                    refine ⟨414986678113082888920733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17706098266158203260617941 414986678113082888920733)
                    ·
                      rfl

theorem cell23_2424551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_2424551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424551 prefixEnd_2424551 := by exact prefixLift 2424551
  have htrace : WordTrace (prefixWord ++ tailWord_2424551) baseStart_2424551 baseEnd_2424551 := by
    simpa [prefixWord, tailWord_2424551, baseEnd_2424551] using wordTrace_append hprefix tailTrace_2424551
  have hstable : (prefixWord ++ tailWord_2424551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424551).length < 2 ^ (prefixWord ++ tailWord_2424551).sum := by decide
  have hdescent : baseEnd_2424551 < baseStart_2424551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424567 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_2424567 : Nat := 118140960795 + 2424567 * 2 ^ 59
def prefixEnd_2424567 : Nat := 4983230072969 + 3 ^ 40 * 2424567 * 2
def baseEnd_2424567 : Nat := 1244968250029720604162125

theorem tailTrace_2424567 : CollatzResearch.WordTrace tailWord_2424567 prefixEnd_2424567 1244968250029720604162125 := by
  unfold tailWord_2424567
  simp only [CollatzResearch.WordTrace]
  refine ⟨88431223407215316921871955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58954148938143544614581303 88431223407215316921871955)
  ·
    refine ⟨132646835110822975382807933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88431223407215316921871955 132646835110822975382807933)
    ·
      refine ⟨49742563166558615768552975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132646835110822975382807933 49742563166558615768552975)
      ·
        refine ⟨74613844749837923652829463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49742563166558615768552975 74613844749837923652829463)
        ·
          refine ⟨111920767124756885479244195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74613844749837923652829463 111920767124756885479244195)
          ·
            refine ⟨167881150687135328218866293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111920767124756885479244195 167881150687135328218866293)
            ·
              refine ⟨15738857876918937020518715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167881150687135328218866293 15738857876918937020518715)
              ·
                refine ⟨23608286815378405530778073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15738857876918937020518715 23608286815378405530778073)
                ·
                  refine ⟨17706215111533804148083555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23608286815378405530778073 17706215111533804148083555)
                  ·
                    refine ⟨26559322667300706222125333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17706215111533804148083555 26559322667300706222125333)
                    ·
                      refine ⟨1244968250029720604162125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26559322667300706222125333 1244968250029720604162125)
                      ·
                        rfl

theorem cell23_2424567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_2424567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424567 prefixEnd_2424567 := by exact prefixLift 2424567
  have htrace : WordTrace (prefixWord ++ tailWord_2424567) baseStart_2424567 baseEnd_2424567 := by
    simpa [prefixWord, tailWord_2424567, baseEnd_2424567] using wordTrace_append hprefix tailTrace_2424567
  have hstable : (prefixWord ++ tailWord_2424567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424567).length < 2 ^ (prefixWord ++ tailWord_2424567).sum := by decide
  have hdescent : baseEnd_2424567 < baseStart_2424567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424604 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_2424604 : Nat := 118140960795 + 2424604 * 2 ^ 59
def prefixEnd_2424604 : Nat := 4983230072969 + 3 ^ 40 * 2424604 * 2
def baseEnd_2424604 : Nat := 1244987248813936959399455

theorem tailTrace_2424604 : CollatzResearch.WordTrace tailWord_2424604 prefixEnd_2424604 1244987248813936959399455 := by
  unfold tailWord_2424604
  simp only [CollatzResearch.WordTrace]
  refine ⟨44216286454040636120484433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58955048605387514827312577 44216286454040636120484433)
  ·
    refine ⟨33162214840530477090363325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44216286454040636120484433 33162214840530477090363325)
    ·
      refine ⟨12435830565198928908886247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33162214840530477090363325 12435830565198928908886247)
      ·
        refine ⟨18653745847798393363329371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12435830565198928908886247 18653745847798393363329371)
        ·
          refine ⟨27980618771697590044994057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18653745847798393363329371 27980618771697590044994057)
          ·
            refine ⟨20985464078773192533745543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27980618771697590044994057 20985464078773192533745543)
            ·
              refine ⟨31478196118159788800618315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20985464078773192533745543 31478196118159788800618315)
              ·
                refine ⟨47217294177239683200927473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31478196118159788800618315 47217294177239683200927473)
                ·
                  refine ⟨35412970632929762400695605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47217294177239683200927473 35412970632929762400695605)
                  ·
                    refine ⟨3319965996837165225065213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35412970632929762400695605 3319965996837165225065213)
                    ·
                      refine ⟨1244987248813936959399455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3319965996837165225065213 1244987248813936959399455)
                      ·
                        rfl

theorem cell23_2424604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_2424604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424604 prefixEnd_2424604 := by exact prefixLift 2424604
  have htrace : WordTrace (prefixWord ++ tailWord_2424604) baseStart_2424604 baseEnd_2424604 := by
    simpa [prefixWord, tailWord_2424604, baseEnd_2424604] using wordTrace_append hprefix tailTrace_2424604
  have hstable : (prefixWord ++ tailWord_2424604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424604).length < 2 ^ (prefixWord ++ tailWord_2424604).sum := by decide
  have hdescent : baseEnd_2424604 < baseStart_2424604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424617 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_2424617 : Nat := 118140960795 + 2424617 * 2 ^ 59
def prefixEnd_2424617 : Nat := 4983230072969 + 3 ^ 40 * 2424617 * 2
def baseEnd_2424617 : Nat := 1244993924062445408536895

theorem tailTrace_2424617 : CollatzResearch.WordTrace tailWord_2424617 prefixEnd_2424617 1244993924062445408536895 := by
  unfold tailWord_2424617
  simp only [CollatzResearch.WordTrace]
  refine ⟨88433047057034175461192105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58955364704689450307461403 88433047057034175461192105)
  ·
    refine ⟨66324785292775631595894079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88433047057034175461192105 66324785292775631595894079)
    ·
      refine ⟨99487177939163447393841119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66324785292775631595894079 99487177939163447393841119)
      ·
        refine ⟨149230766908745171090761679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99487177939163447393841119 149230766908745171090761679)
        ·
          refine ⟨223846150363117756636142519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149230766908745171090761679 223846150363117756636142519)
          ·
            refine ⟨335769225544676634954213779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223846150363117756636142519 335769225544676634954213779)
            ·
              refine ⟨503653838317014952431320669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335769225544676634954213779 503653838317014952431320669)
              ·
                refine ⟨188870189368880607161745251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503653838317014952431320669 188870189368880607161745251)
                ·
                  refine ⟨283305284053320910742617877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188870189368880607161745251 283305284053320910742617877)
                  ·
                    refine ⟨13279935189999417691060213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 283305284053320910742617877 13279935189999417691060213)
                    ·
                      refine ⟨1244993924062445408536895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13279935189999417691060213 1244993924062445408536895)
                      ·
                        rfl

theorem cell23_2424617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_2424617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424617 prefixEnd_2424617 := by exact prefixLift 2424617
  have htrace : WordTrace (prefixWord ++ tailWord_2424617) baseStart_2424617 baseEnd_2424617 := by
    simpa [prefixWord, tailWord_2424617, baseEnd_2424617] using wordTrace_append hprefix tailTrace_2424617
  have hstable : (prefixWord ++ tailWord_2424617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424617).length < 2 ^ (prefixWord ++ tailWord_2424617).sum := by decide
  have hdescent : baseEnd_2424617 < baseStart_2424617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424658 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_2424658 : Nat := 118140960795 + 2424658 * 2 ^ 59
def prefixEnd_2424658 : Nat := 4983230072969 + 3 ^ 40 * 2424658 * 2
def baseEnd_2424658 : Nat := 415004992256426582708069

theorem tailTrace_2424658 : CollatzResearch.WordTrace tailWord_2424658 prefixEnd_2424658 415004992256426582708069 := by
  unfold tailWord_2424658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22108635612471409865858657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58956361633257092975623085 22108635612471409865858657)
  ·
    refine ⟨16581476709353557399393993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22108635612471409865858657 16581476709353557399393993)
    ·
      refine ⟨12436107532015168049545495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16581476709353557399393993 12436107532015168049545495)
      ·
        refine ⟨18654161298022752074318243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12436107532015168049545495 18654161298022752074318243)
        ·
          refine ⟨27981241947034128111477365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18654161298022752074318243 27981241947034128111477365)
          ·
            refine ⟨2623241432534449510451003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27981241947034128111477365 2623241432534449510451003)
            ·
              refine ⟨3934862148801674265676505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623241432534449510451003 3934862148801674265676505)
              ·
                refine ⟨2951146611601255699257379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3934862148801674265676505 2951146611601255699257379)
                ·
                  refine ⟨4426719917401883548886069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951146611601255699257379 4426719917401883548886069)
                  ·
                    refine ⟨415004992256426582708069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4426719917401883548886069 415004992256426582708069)
                    ·
                      rfl

theorem cell23_2424658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_2424658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424658 prefixEnd_2424658 := by exact prefixLift 2424658
  have htrace : WordTrace (prefixWord ++ tailWord_2424658) baseStart_2424658 baseEnd_2424658 := by
    simpa [prefixWord, tailWord_2424658, baseEnd_2424658] using wordTrace_append hprefix tailTrace_2424658
  have hstable : (prefixWord ++ tailWord_2424658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424658).length < 2 ^ (prefixWord ++ tailWord_2424658).sum := by decide
  have hdescent : baseEnd_2424658 < baseStart_2424658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424661 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2424661 : Nat := 118140960795 + 2424661 * 2 ^ 59
def prefixEnd_2424661 : Nat := 4983230072969 + 3 ^ 40 * 2424661 * 2
def baseEnd_2424661 : Nat := 1245016517211243236386693

theorem tailTrace_2424661 : CollatzResearch.WordTrace tailWord_2424661 prefixEnd_2424661 1245016517211243236386693 := by
  unfold tailWord_2424661
  simp only [CollatzResearch.WordTrace]
  refine ⟨88434651868874770975793837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58956434579249847317195891 88434651868874770975793837)
  ·
    refine ⟨33162994450828039115922689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88434651868874770975793837 33162994450828039115922689)
    ·
      refine ⟨24872245838121029336942017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33162994450828039115922689 24872245838121029336942017)
      ·
        refine ⟨18654184378590772002706513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24872245838121029336942017 18654184378590772002706513)
        ·
          refine ⟨13990638283943079002029885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18654184378590772002706513 13990638283943079002029885)
          ·
            refine ⟨5246489356478654625761207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13990638283943079002029885 5246489356478654625761207)
            ·
              refine ⟨7869734034717981938641811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5246489356478654625761207 7869734034717981938641811)
              ·
                refine ⟨11804601052076972907962717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7869734034717981938641811 11804601052076972907962717)
                ·
                  refine ⟨4426725394528864840486019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11804601052076972907962717 4426725394528864840486019)
                  ·
                    refine ⟨6640088091793297260729029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4426725394528864840486019 6640088091793297260729029)
                    ·
                      refine ⟨1245016517211243236386693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6640088091793297260729029 1245016517211243236386693)
                      ·
                        rfl

theorem cell23_2424661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2424661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424661 prefixEnd_2424661 := by exact prefixLift 2424661
  have htrace : WordTrace (prefixWord ++ tailWord_2424661) baseStart_2424661 baseEnd_2424661 := by
    simpa [prefixWord, tailWord_2424661, baseEnd_2424661] using wordTrace_append hprefix tailTrace_2424661
  have hstable : (prefixWord ++ tailWord_2424661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424661).length < 2 ^ (prefixWord ++ tailWord_2424661).sum := by decide
  have hdescent : baseEnd_2424661 < baseStart_2424661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424681 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 3]
def baseStart_2424681 : Nat := 118140960795 + 2424681 * 2 ^ 59
def prefixEnd_2424681 : Nat := 4983230072969 + 3 ^ 40 * 2424681 * 2
def baseEnd_2424681 : Nat := 1245026786824333158136601

theorem tailTrace_2424681 : CollatzResearch.WordTrace tailWord_2424681 prefixEnd_2424681 1245026786824333158136601 := by
  unfold tailWord_2424681
  simp only [CollatzResearch.WordTrace]
  refine ⟨88435381328802314391521897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58956920885868209594347931 88435381328802314391521897)
  ·
    refine ⟨66326535996601735793641423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88435381328802314391521897 66326535996601735793641423)
    ·
      refine ⟨99489803994902603690462135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66326535996601735793641423 99489803994902603690462135)
      ·
        refine ⟨149234705992353905535693203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99489803994902603690462135 149234705992353905535693203)
        ·
          refine ⟨223852058988530858303539805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149234705992353905535693203 223852058988530858303539805)
          ·
            refine ⟨83944522120699071863827427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223852058988530858303539805 83944522120699071863827427)
            ·
              refine ⟨125916783181048607795741141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83944522120699071863827427 125916783181048607795741141)
              ·
                refine ⟨2951174605805826745212683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125916783181048607795741141 2951174605805826745212683)
                ·
                  refine ⟨4426761908708740117819025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951174605805826745212683 4426761908708740117819025)
                  ·
                    refine ⟨3320071431531555088364269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4426761908708740117819025 3320071431531555088364269)
                    ·
                      refine ⟨1245026786824333158136601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3320071431531555088364269 1245026786824333158136601)
                      ·
                        rfl

theorem cell23_2424681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 3].length) (baseStart_2424681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424681 prefixEnd_2424681 := by exact prefixLift 2424681
  have htrace : WordTrace (prefixWord ++ tailWord_2424681) baseStart_2424681 baseEnd_2424681 := by
    simpa [prefixWord, tailWord_2424681, baseEnd_2424681] using wordTrace_append hprefix tailTrace_2424681
  have hstable : (prefixWord ++ tailWord_2424681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424681).length < 2 ^ (prefixWord ++ tailWord_2424681).sum := by decide
  have hdescent : baseEnd_2424681 < baseStart_2424681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424726 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2424726 : Nat := 118140960795 + 2424726 * 2 ^ 59
def prefixEnd_2424726 : Nat := 4983230072969 + 3 ^ 40 * 2424726 * 2
def baseEnd_2424726 : Nat := 415016631151261827357965

theorem tailTrace_2424726 : CollatzResearch.WordTrace tailWord_2424726 prefixEnd_2424726 415016631151261827357965 := by
  unfold tailWord_2424726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527313913352455442306877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58958015075759524717940021 5527313913352455442306877)
  ·
    refine ⟨2072742717507170790865079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5527313913352455442306877 2072742717507170790865079)
    ·
      refine ⟨3109114076260756186297619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2072742717507170790865079 3109114076260756186297619)
      ·
        refine ⟨4663671114391134279446429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109114076260756186297619 4663671114391134279446429)
        ·
          refine ⟨1748876667896675354792411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4663671114391134279446429 1748876667896675354792411)
          ·
            refine ⟨2623315001845013032188617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748876667896675354792411 2623315001845013032188617)
            ·
              refine ⟨1967486251383759774141463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2623315001845013032188617 1967486251383759774141463)
              ·
                refine ⟨2951229377075639661212195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967486251383759774141463 2951229377075639661212195)
                ·
                  refine ⟨4426844065613459491818293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951229377075639661212195 4426844065613459491818293)
                  ·
                    refine ⟨415016631151261827357965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4426844065613459491818293 415016631151261827357965)
                    ·
                      rfl

theorem cell23_2424726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2424726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424726 prefixEnd_2424726 := by exact prefixLift 2424726
  have htrace : WordTrace (prefixWord ++ tailWord_2424726) baseStart_2424726 baseEnd_2424726 := by
    simpa [prefixWord, tailWord_2424726, baseEnd_2424726] using wordTrace_append hprefix tailTrace_2424726
  have hstable : (prefixWord ++ tailWord_2424726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424726).length < 2 ^ (prefixWord ++ tailWord_2424726).sum := by decide
  have hdescent : baseEnd_2424726 < baseStart_2424726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424732 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2424732 : Nat := 118140960795 + 2424732 * 2 ^ 59
def prefixEnd_2424732 : Nat := 4983230072969 + 3 ^ 40 * 2424732 * 2
def baseEnd_2424732 : Nat := 1245052974337712458598867

theorem tailTrace_2424732 : CollatzResearch.WordTrace tailWord_2424732 prefixEnd_2424732 1245052974337712458598867 := by
  unfold tailWord_2424732
  simp only [CollatzResearch.WordTrace]
  refine ⟨44218620725808775050814225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58958160967745033401085633 44218620725808775050814225)
  ·
    refine ⟨33163965544356581288110669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44218620725808775050814225 33163965544356581288110669)
    ·
      refine ⟨12436487079133717983041501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33163965544356581288110669 12436487079133717983041501)
      ·
        refine ⟨4663682654675144243640563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12436487079133717983041501 4663682654675144243640563)
        ·
          refine ⟨6995523982012716365460845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4663682654675144243640563 6995523982012716365460845)
          ·
            refine ⟨2623321493254768637047817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6995523982012716365460845 2623321493254768637047817)
            ·
              refine ⟨1967491119941076477785863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2623321493254768637047817 1967491119941076477785863)
              ·
                refine ⟨2951236679911614716678795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967491119941076477785863 2951236679911614716678795)
                ·
                  refine ⟨4426855019867422075018193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951236679911614716678795 4426855019867422075018193)
                  ·
                    refine ⟨3320141264900566556263645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4426855019867422075018193 3320141264900566556263645)
                    ·
                      refine ⟨1245052974337712458598867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3320141264900566556263645 1245052974337712458598867)
                      ·
                        rfl

theorem cell23_2424732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2424732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424732 prefixEnd_2424732 := by exact prefixLift 2424732
  have htrace : WordTrace (prefixWord ++ tailWord_2424732) baseStart_2424732 baseEnd_2424732 := by
    simpa [prefixWord, tailWord_2424732, baseEnd_2424732] using wordTrace_append hprefix tailTrace_2424732
  have hstable : (prefixWord ++ tailWord_2424732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424732).length < 2 ^ (prefixWord ++ tailWord_2424732).sum := by decide
  have hdescent : baseEnd_2424732 < baseStart_2424732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424801 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_2424801 : Nat := 118140960795 + 2424801 * 2 ^ 59
def prefixEnd_2424801 : Nat := 4983230072969 + 3 ^ 40 * 2424801 * 2
def baseEnd_2424801 : Nat := 1245088404502872688636049

theorem tailTrace_2424801 : CollatzResearch.WordTrace tailWord_2424801 prefixEnd_2424801 1245088404502872688636049 := by
  unfold tailWord_2424801
  simp only [CollatzResearch.WordTrace]
  refine ⟨88439758088367574885890257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58959838725578383257260171 88439758088367574885890257)
  ·
    refine ⟨66329818566275681164417693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88439758088367574885890257 66329818566275681164417693)
    ·
      refine ⟨24873681962353380436656635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66329818566275681164417693 24873681962353380436656635)
      ·
        refine ⟨37310522943530070654984953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24873681962353380436656635 37310522943530070654984953)
        ·
          refine ⟨27982892207647552991238715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37310522943530070654984953 27982892207647552991238715)
          ·
            refine ⟨41974338311471329486858073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27982892207647552991238715 41974338311471329486858073)
            ·
              refine ⟨31480753733603497115143555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41974338311471329486858073 31480753733603497115143555)
              ·
                refine ⟨47221130600405245672715333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31480753733603497115143555 47221130600405245672715333)
                ·
                  refine ⟨8853961987575983563634125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47221130600405245672715333 8853961987575983563634125)
                  ·
                    refine ⟨3320235745340993836362797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8853961987575983563634125 3320235745340993836362797)
                    ·
                      refine ⟨1245088404502872688636049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3320235745340993836362797 1245088404502872688636049)
                      ·
                        rfl

theorem cell23_2424801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_2424801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424801 prefixEnd_2424801 := by exact prefixLift 2424801
  have htrace : WordTrace (prefixWord ++ tailWord_2424801) baseStart_2424801 baseEnd_2424801 := by
    simpa [prefixWord, tailWord_2424801, baseEnd_2424801] using wordTrace_append hprefix tailTrace_2424801
  have hstable : (prefixWord ++ tailWord_2424801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424801).length < 2 ^ (prefixWord ++ tailWord_2424801).sum := by decide
  have hdescent : baseEnd_2424801 < baseStart_2424801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424858 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_2424858 : Nat := 118140960795 + 2424858 * 2 ^ 59
def prefixEnd_2424858 : Nat := 4983230072969 + 3 ^ 40 * 2424858 * 2
def baseEnd_2424858 : Nat := 1245117672900178965623287

theorem tailTrace_2424858 : CollatzResearch.WordTrace tailWord_2424858 prefixEnd_2424858 1245117672900178965623287 := by
  unfold tailWord_2424858
  simp only [CollatzResearch.WordTrace]
  refine ⟨22110459262290268405178807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58961224699440715747143485 22110459262290268405178807)
  ·
    refine ⟨33165688893435402607768211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22110459262290268405178807 33165688893435402607768211)
    ·
      refine ⟨49748533340153103911652317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33165688893435402607768211 49748533340153103911652317)
      ·
        refine ⟨18655700002557413966869619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49748533340153103911652317 18655700002557413966869619)
        ·
          refine ⟨27983550003836120950304429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18655700002557413966869619 27983550003836120950304429)
          ·
            refine ⟨10493831251438545356364161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27983550003836120950304429 10493831251438545356364161)
            ·
              refine ⟨7870373438578909017273121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10493831251438545356364161 7870373438578909017273121)
              ·
                refine ⟨5902780078934181762954841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7870373438578909017273121 5902780078934181762954841)
                ·
                  refine ⟨4427085059200636322216131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5902780078934181762954841 4427085059200636322216131)
                  ·
                    refine ⟨6640627588800954483324197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4427085059200636322216131 6640627588800954483324197)
                    ·
                      refine ⟨1245117672900178965623287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6640627588800954483324197 1245117672900178965623287)
                      ·
                        rfl

theorem cell23_2424858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_2424858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424858 prefixEnd_2424858 := by exact prefixLift 2424858
  have htrace : WordTrace (prefixWord ++ tailWord_2424858) baseStart_2424858 baseEnd_2424858 := by
    simpa [prefixWord, tailWord_2424858, baseEnd_2424858] using wordTrace_append hprefix tailTrace_2424858
  have hstable : (prefixWord ++ tailWord_2424858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424858).length < 2 ^ (prefixWord ++ tailWord_2424858).sum := by decide
  have hdescent : baseEnd_2424858 < baseStart_2424858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424891 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 3]
def baseStart_2424891 : Nat := 118140960795 + 2424891 * 2 ^ 59
def prefixEnd_2424891 : Nat := 4983230072969 + 3 ^ 40 * 2424891 * 2
def baseEnd_2424891 : Nat := 1245134617761777336510635

theorem tailTrace_2424891 : CollatzResearch.WordTrace tailWord_2424891 prefixEnd_2424891 1245134617761777336510635 := by
  unfold tailWord_2424891
  simp only [CollatzResearch.WordTrace]
  refine ⟨88443040658041520256666527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58962027105361013504444351 88443040658041520256666527)
  ·
    refine ⟨132664560987062280384999791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88443040658041520256666527 132664560987062280384999791)
    ·
      refine ⟨198996841480593420577499687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132664560987062280384999791 198996841480593420577499687)
      ·
        refine ⟨298495262220890130866249531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198996841480593420577499687 298495262220890130866249531)
        ·
          refine ⟨447742893331335196299374297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298495262220890130866249531 447742893331335196299374297)
          ·
            refine ⟨335807169998501397224530723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447742893331335196299374297 335807169998501397224530723)
            ·
              refine ⟨503710754997752095836796085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335807169998501397224530723 503710754997752095836796085)
              ·
                refine ⟨47222883281039258984699633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 503710754997752095836796085 47222883281039258984699633)
                ·
                  refine ⟨35417162460779444238524725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47222883281039258984699633 35417162460779444238524725)
                  ·
                    refine ⟨3320358980698072897361693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35417162460779444238524725 3320358980698072897361693)
                    ·
                      refine ⟨1245134617761777336510635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3320358980698072897361693 1245134617761777336510635)
                      ·
                        rfl

theorem cell23_2424891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 3].length) (baseStart_2424891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424891 prefixEnd_2424891 := by exact prefixLift 2424891
  have htrace : WordTrace (prefixWord ++ tailWord_2424891) baseStart_2424891 baseEnd_2424891 := by
    simpa [prefixWord, tailWord_2424891, baseEnd_2424891] using wordTrace_append hprefix tailTrace_2424891
  have hstable : (prefixWord ++ tailWord_2424891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424891).length < 2 ^ (prefixWord ++ tailWord_2424891).sum := by decide
  have hdescent : baseEnd_2424891 < baseStart_2424891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424965 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 4]
def baseStart_2424965 : Nat := 118140960795 + 2424965 * 2 ^ 59
def prefixEnd_2424965 : Nat := 4983230072969 + 3 ^ 40 * 2424965 * 2
def baseEnd_2424965 : Nat := 1245172615330210046985295

theorem tailTrace_2424965 : CollatzResearch.WordTrace tailWord_2424965 prefixEnd_2424965 1245172615330210046985295 := by
  unfold tailWord_2424965
  simp only [CollatzResearch.WordTrace]
  refine ⟨88445739659773430894860349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58963826439848953929906899 88445739659773430894860349)
  ·
    refine ⟨33167152372415036585572631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88445739659773430894860349 33167152372415036585572631)
    ·
      refine ⟨49750728558622554878358947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33167152372415036585572631 49750728558622554878358947)
      ·
        refine ⟨74626092837933832317538421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49750728558622554878358947 74626092837933832317538421)
        ·
          refine ⟨6996196203556296779769227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74626092837933832317538421 6996196203556296779769227)
          ·
            refine ⟨10494294305334445169653841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996196203556296779769227 10494294305334445169653841)
            ·
              refine ⟨7870720729000833877240381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10494294305334445169653841 7870720729000833877240381)
              ·
                refine ⟨2951520273375312703965143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7870720729000833877240381 2951520273375312703965143)
                ·
                  refine ⟨4427280410062969055947715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951520273375312703965143 4427280410062969055947715)
                  ·
                    refine ⟨6640920615094453583921573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4427280410062969055947715 6640920615094453583921573)
                    ·
                      refine ⟨1245172615330210046985295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6640920615094453583921573 1245172615330210046985295)
                      ·
                        rfl

theorem cell23_2424965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_2424965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424965 prefixEnd_2424965 := by exact prefixLift 2424965
  have htrace : WordTrace (prefixWord ++ tailWord_2424965) baseStart_2424965 baseEnd_2424965 := by
    simpa [prefixWord, tailWord_2424965, baseEnd_2424965] using wordTrace_append hprefix tailTrace_2424965
  have hstable : (prefixWord ++ tailWord_2424965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424965).length < 2 ^ (prefixWord ++ tailWord_2424965).sum := by decide
  have hdescent : baseEnd_2424965 < baseStart_2424965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424978 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2424978 : Nat := 118140960795 + 2424978 * 2 ^ 59
def prefixEnd_2424978 : Nat := 4983230072969 + 3 ^ 40 * 2424978 * 2
def baseEnd_2424978 : Nat := 1245179290578718496122735

theorem tailTrace_2424978 : CollatzResearch.WordTrace tailWord_2424978 prefixEnd_2424978 1245179290578718496122735 := by
  unfold tailWord_2424978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22111553452181583528770897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58964142539150889410055725 22111553452181583528770897)
  ·
    refine ⟨16583665089136187646578173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22111553452181583528770897 16583665089136187646578173)
    ·
      refine ⟨6218874408426070367466815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16583665089136187646578173 6218874408426070367466815)
      ·
        refine ⟨9328311612639105551200223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6218874408426070367466815 9328311612639105551200223)
        ·
          refine ⟨13992467418958658326800335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9328311612639105551200223 13992467418958658326800335)
          ·
            refine ⟨20988701128437987490200503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13992467418958658326800335 20988701128437987490200503)
            ·
              refine ⟨31483051692656981235300755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20988701128437987490200503 31483051692656981235300755)
              ·
                refine ⟨47224577538985471852951133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31483051692656981235300755 47224577538985471852951133)
                ·
                  refine ⟨17709216577119551944856675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47224577538985471852951133 17709216577119551944856675)
                  ·
                    refine ⟨26563824865679327917285013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17709216577119551944856675 26563824865679327917285013)
                    ·
                      refine ⟨1245179290578718496122735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26563824865679327917285013 1245179290578718496122735)
                      ·
                        rfl

theorem cell23_2424978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2424978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424978 prefixEnd_2424978 := by exact prefixLift 2424978
  have htrace : WordTrace (prefixWord ++ tailWord_2424978) baseStart_2424978 baseEnd_2424978 := by
    simpa [prefixWord, tailWord_2424978, baseEnd_2424978] using wordTrace_append hprefix tailTrace_2424978
  have hstable : (prefixWord ++ tailWord_2424978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424978).length < 2 ^ (prefixWord ++ tailWord_2424978).sum := by decide
  have hdescent : baseEnd_2424978 < baseStart_2424978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424988 : List Nat := [2, 2, 3, 2, 1, 1, 4, 8]
def baseStart_2424988 : Nat := 118140960795 + 2424988 * 2 ^ 59
def prefixEnd_2424988 : Nat := 4983230072969 + 3 ^ 40 * 2424988 * 2
def baseEnd_2424988 : Nat := 46117941680935683592507

theorem tailTrace_2424988 : CollatzResearch.WordTrace tailWord_2424988 prefixEnd_2424988 46117941680935683592507 := by
  unfold tailWord_2424988
  simp only [CollatzResearch.WordTrace]
  refine ⟨44223289269345052911473809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58964385692460070548631745 44223289269345052911473809)
  ·
    refine ⟨33167466952008789683605357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44223289269345052911473809 33167466952008789683605357)
    ·
      refine ⟨12437800107003296131352009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33167466952008789683605357 12437800107003296131352009)
      ·
        refine ⟨9328350080252472098514007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12437800107003296131352009 9328350080252472098514007)
        ·
          refine ⟨13992525120378708147771011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9328350080252472098514007 13992525120378708147771011)
          ·
            refine ⟨20988787680568062221656517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13992525120378708147771011 20988787680568062221656517)
            ·
              refine ⟨3935397690106511666560597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20988787680568062221656517 3935397690106511666560597)
              ·
                refine ⟨46117941680935683592507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3935397690106511666560597 46117941680935683592507)
                ·
                  rfl

theorem cell23_2424988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 8].length) (baseStart_2424988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424988 prefixEnd_2424988 := by exact prefixLift 2424988
  have htrace : WordTrace (prefixWord ++ tailWord_2424988) baseStart_2424988 baseEnd_2424988 := by
    simpa [prefixWord, tailWord_2424988, baseEnd_2424988] using wordTrace_append hprefix tailTrace_2424988
  have hstable : (prefixWord ++ tailWord_2424988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424988).length < 2 ^ (prefixWord ++ tailWord_2424988).sum := by decide
  have hdescent : baseEnd_2424988 < baseStart_2424988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424992 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 2, 4]
def baseStart_2424992 : Nat := 118140960795 + 2424992 * 2 ^ 59
def prefixEnd_2424992 : Nat := 4983230072969 + 3 ^ 40 * 2424992 * 2
def baseEnd_2424992 : Nat := 415062159769293813782557

theorem tailTrace_2424992 : CollatzResearch.WordTrace tailWord_2424992 prefixEnd_2424992 415062159769293813782557 := by
  unfold tailWord_2424992
  simp only [CollatzResearch.WordTrace]
  refine ⟨44223362215337807253046615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58964482953783743004062153 44223362215337807253046615)
  ·
    refine ⟨66335043323006710879569923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44223362215337807253046615 66335043323006710879569923)
    ·
      refine ⟨99502564984510066319354885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66335043323006710879569923 99502564984510066319354885)
      ·
        refine ⟨18656730934595637434879041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99502564984510066319354885 18656730934595637434879041)
        ·
          refine ⟨13992548200946728076159281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18656730934595637434879041 13992548200946728076159281)
          ·
            refine ⟨10494411150710046057119461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13992548200946728076159281 10494411150710046057119461)
            ·
              refine ⟨1967702090758133635709899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10494411150710046057119461 1967702090758133635709899)
              ·
                refine ⟨2951553136137200453564849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967702090758133635709899 2951553136137200453564849)
                ·
                  refine ⟨2213664852102900340173637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2951553136137200453564849 2213664852102900340173637)
                  ·
                    refine ⟨415062159769293813782557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2213664852102900340173637 415062159769293813782557)
                    ·
                      rfl

theorem cell23_2424992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 4].length) (baseStart_2424992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424992 prefixEnd_2424992 := by exact prefixLift 2424992
  have htrace : WordTrace (prefixWord ++ tailWord_2424992) baseStart_2424992 baseEnd_2424992 := by
    simpa [prefixWord, tailWord_2424992, baseEnd_2424992] using wordTrace_append hprefix tailTrace_2424992
  have hstable : (prefixWord ++ tailWord_2424992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424992).length < 2 ^ (prefixWord ++ tailWord_2424992).sum := by decide
  have hdescent : baseEnd_2424992 < baseStart_2424992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424999 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2424999 : Nat := 118140960795 + 2424999 * 2 ^ 59
def prefixEnd_2424999 : Nat := 4983230072969 + 3 ^ 40 * 2424999 * 2
def baseEnd_2424999 : Nat := 1245190073672462913960139

theorem tailTrace_2424999 : CollatzResearch.WordTrace tailWord_2424999 prefixEnd_2424999 1245190073672462913960139 := by
  unfold tailWord_2424999
  simp only [CollatzResearch.WordTrace]
  refine ⟨88446979741650254701598051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58964653161100169801065367 88446979741650254701598051)
  ·
    refine ⟨132670469612475382052397077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88446979741650254701598051 132670469612475382052397077)
    ·
      refine ⟨6218928263084783533706113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132670469612475382052397077 6218928263084783533706113)
      ·
        refine ⟨4664196197313587650279585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6218928263084783533706113 4664196197313587650279585)
        ·
          refine ⟨3498147147985190737709689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4664196197313587650279585 3498147147985190737709689)
          ·
            refine ⟨2623610360988893053282267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3498147147985190737709689 2623610360988893053282267)
            ·
              refine ⟨3935415541483339579923401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623610360988893053282267 3935415541483339579923401)
              ·
                refine ⟨2951561656112504684942551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3935415541483339579923401 2951561656112504684942551)
                ·
                  refine ⟨4427342484168757027413827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951561656112504684942551 4427342484168757027413827)
                  ·
                    refine ⟨6641013726253135541120741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4427342484168757027413827 6641013726253135541120741)
                    ·
                      refine ⟨1245190073672462913960139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6641013726253135541120741 1245190073672462913960139)
                      ·
                        rfl

theorem cell23_2424999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2424999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2424999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2424999 prefixEnd_2424999 := by exact prefixLift 2424999
  have htrace : WordTrace (prefixWord ++ tailWord_2424999) baseStart_2424999 baseEnd_2424999 := by
    simpa [prefixWord, tailWord_2424999, baseEnd_2424999] using wordTrace_append hprefix tailTrace_2424999
  have hstable : (prefixWord ++ tailWord_2424999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424999).length < 2 ^ (prefixWord ++ tailWord_2424999).sum := by decide
  have hdescent : baseEnd_2424999 < baseStart_2424999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425015 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_2425015 : Nat := 118140960795 + 2425015 * 2 ^ 59
def prefixEnd_2425015 : Nat := 4983230072969 + 3 ^ 40 * 2425015 * 2
def baseEnd_2425015 : Nat := 1245198289362934851360065

theorem tailTrace_2425015 : CollatzResearch.WordTrace tailWord_2425015 prefixEnd_2425015 1245198289362934851360065 := by
  unfold tailWord_2425015
  simp only [CollatzResearch.WordTrace]
  refine ⟨88447563309592289434180499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58965042206394859622786999 88447563309592289434180499)
  ·
    refine ⟨132671344964388434151270749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88447563309592289434180499 132671344964388434151270749)
    ·
      refine ⟨49751754361645662806726531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132671344964388434151270749 49751754361645662806726531)
      ·
        refine ⟨74627631542468494210089797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49751754361645662806726531 74627631542468494210089797)
        ·
          refine ⟨13992680914212842664391837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74627631542468494210089797 13992680914212842664391837)
          ·
            refine ⟨5247255342829815999146939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13992680914212842664391837 5247255342829815999146939)
            ·
              refine ⟨7870883014244723998720409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5247255342829815999146939 7870883014244723998720409)
              ·
                refine ⟨5903162260683542999040307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7870883014244723998720409 5903162260683542999040307)
                ·
                  refine ⟨8854743391025314498560461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5903162260683542999040307 8854743391025314498560461)
                  ·
                    refine ⟨3320528771634492936960173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8854743391025314498560461 3320528771634492936960173)
                    ·
                      refine ⟨1245198289362934851360065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3320528771634492936960173 1245198289362934851360065)
                      ·
                        rfl

theorem cell23_2425015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_2425015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425015 prefixEnd_2425015 := by exact prefixLift 2425015
  have htrace : WordTrace (prefixWord ++ tailWord_2425015) baseStart_2425015 baseEnd_2425015 := by
    simpa [prefixWord, tailWord_2425015, baseEnd_2425015] using wordTrace_append hprefix tailTrace_2425015
  have hstable : (prefixWord ++ tailWord_2425015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425015).length < 2 ^ (prefixWord ++ tailWord_2425015).sum := by decide
  have hdescent : baseEnd_2425015 < baseStart_2425015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425026 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2425026 : Nat := 118140960795 + 2425026 * 2 ^ 59
def prefixEnd_2425026 : Nat := 4983230072969 + 3 ^ 40 * 2425026 * 2
def baseEnd_2425026 : Nat := 415067979216711436107505

theorem tailTrace_2425026 : CollatzResearch.WordTrace tailWord_2425026 prefixEnd_2425026 415067979216711436107505 := by
  unfold tailWord_2425026
  simp only [CollatzResearch.WordTrace]
  refine ⟨22111991128138109578207733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58965309675034958875220621 22111991128138109578207733)
  ·
    refine ⟨2072999168262947772956975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22111991128138109578207733 2072999168262947772956975)
    ·
      refine ⟨3109498752394421659435463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2072999168262947772956975 3109498752394421659435463)
      ·
        refine ⟨4664248128591632489153195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109498752394421659435463 4664248128591632489153195)
        ·
          refine ⟨6996372192887448733729793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664248128591632489153195 6996372192887448733729793)
          ·
            refine ⟨5247279144665586550297345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6996372192887448733729793 5247279144665586550297345)
            ·
              refine ⟨3935459358499189912723009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5247279144665586550297345 3935459358499189912723009)
              ·
                refine ⟨2951594518874392434542257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3935459358499189912723009 2951594518874392434542257)
                ·
                  refine ⟨2213695889155794325906693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2951594518874392434542257 2213695889155794325906693)
                  ·
                    refine ⟨415067979216711436107505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2213695889155794325906693 415067979216711436107505)
                    ·
                      rfl

theorem cell23_2425026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2425026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425026 prefixEnd_2425026 := by exact prefixLift 2425026
  have htrace : WordTrace (prefixWord ++ tailWord_2425026) baseStart_2425026 baseEnd_2425026 := by
    simpa [prefixWord, tailWord_2425026, baseEnd_2425026] using wordTrace_append hprefix tailTrace_2425026
  have hstable : (prefixWord ++ tailWord_2425026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425026).length < 2 ^ (prefixWord ++ tailWord_2425026).sum := by decide
  have hdescent : baseEnd_2425026 < baseStart_2425026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425042 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_2425042 : Nat := 118140960795 + 2425042 * 2 ^ 59
def prefixEnd_2425042 : Nat := 4983230072969 + 3 ^ 40 * 2425042 * 2
def baseEnd_2425042 : Nat := 1245212153340606245722441

theorem tailTrace_2425042 : CollatzResearch.WordTrace tailWord_2425042 prefixEnd_2425042 1245212153340606245722441 := by
  unfold tailWord_2425042
  simp only [CollatzResearch.WordTrace]
  refine ⟨22112137020123618261353345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58965698720329648696942253 22112137020123618261353345)
  ·
    refine ⟨16584102765092713696015009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22112137020123618261353345 16584102765092713696015009)
    ·
      refine ⟨12438077073819535272011257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16584102765092713696015009 12438077073819535272011257)
      ·
        refine ⟨9328557805364651454008443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12438077073819535272011257 9328557805364651454008443)
        ·
          refine ⟨13992836708046977181012665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9328557805364651454008443 13992836708046977181012665)
          ·
            refine ⟨10494627531035232885759499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13992836708046977181012665 10494627531035232885759499)
            ·
              refine ⟨15741941296552849328639249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10494627531035232885759499 15741941296552849328639249)
              ·
                refine ⟨11806455972414636996479437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15741941296552849328639249 11806455972414636996479437)
                ·
                  refine ⟨4427420989655488873679789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11806455972414636996479437 4427420989655488873679789)
                  ·
                    refine ⟨1660282871120808327629921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4427420989655488873679789 1660282871120808327629921)
                    ·
                      refine ⟨1245212153340606245722441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1660282871120808327629921 1245212153340606245722441)
                      ·
                        rfl

theorem cell23_2425042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_2425042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425042 prefixEnd_2425042 := by exact prefixLift 2425042
  have htrace : WordTrace (prefixWord ++ tailWord_2425042) baseStart_2425042 baseEnd_2425042 := by
    simpa [prefixWord, tailWord_2425042, baseEnd_2425042] using wordTrace_append hprefix tailTrace_2425042
  have hstable : (prefixWord ++ tailWord_2425042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425042).length < 2 ^ (prefixWord ++ tailWord_2425042).sum := by decide
  have hdescent : baseEnd_2425042 < baseStart_2425042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425048 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 1, 8]
def baseStart_2425048 : Nat := 118140960795 + 2425048 * 2 ^ 59
def prefixEnd_2425048 : Nat := 4983230072969 + 3 ^ 40 * 2425048 * 2
def baseEnd_2425048 : Nat := 415071744741511074082471

theorem tailTrace_2425048 : CollatzResearch.WordTrace tailWord_2425048 prefixEnd_2425048 415071744741511074082471 := by
  unfold tailWord_2425048
  simp only [CollatzResearch.WordTrace]
  refine ⟨44224383459236368035065899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58965844612315157380087865 44224383459236368035065899)
  ·
    refine ⟨66336575188854552052598849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44224383459236368035065899 66336575188854552052598849)
    ·
      refine ⟨49752431391640914039449137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66336575188854552052598849 49752431391640914039449137)
      ·
        refine ⟨37314323543730685529586853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49752431391640914039449137 37314323543730685529586853)
        ·
          refine ⟨6996435664449503536797535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37314323543730685529586853 6996435664449503536797535)
          ·
            refine ⟨10494653496674255305196303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996435664449503536797535 10494653496674255305196303)
            ·
              refine ⟨15741980245011382957794455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10494653496674255305196303 15741980245011382957794455)
              ·
                refine ⟨23612970367517074436691683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15741980245011382957794455 23612970367517074436691683)
                ·
                  refine ⟨35419455551275611655037525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23612970367517074436691683 35419455551275611655037525)
                  ·
                    refine ⟨415071744741511074082471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35419455551275611655037525 415071744741511074082471)
                    ·
                      rfl

theorem cell23_2425048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_2425048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425048 prefixEnd_2425048 := by exact prefixLift 2425048
  have htrace : WordTrace (prefixWord ++ tailWord_2425048) baseStart_2425048 baseEnd_2425048 := by
    simpa [prefixWord, tailWord_2425048, baseEnd_2425048] using wordTrace_append hprefix tailTrace_2425048
  have hstable : (prefixWord ++ tailWord_2425048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425048).length < 2 ^ (prefixWord ++ tailWord_2425048).sum := by decide
  have hdescent : baseEnd_2425048 < baseStart_2425048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425068 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_2425068 : Nat := 118140960795 + 2425068 * 2 ^ 59
def prefixEnd_2425068 : Nat := 4983230072969 + 3 ^ 40 * 2425068 * 2
def baseEnd_2425068 : Nat := 1245225503837623143997321

theorem tailTrace_2425068 : CollatzResearch.WordTrace tailWord_2425068 prefixEnd_2425068 1245225503837623143997321 := by
  unfold tailWord_2425068
  simp only [CollatzResearch.WordTrace]
  refine ⟨44224748189200139742929929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58966330918933519657239905 44224748189200139742929929)
  ·
    refine ⟨33168561141900104807197447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44224748189200139742929929 33168561141900104807197447)
    ·
      refine ⟨49752841712850157210796171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33168561141900104807197447 49752841712850157210796171)
      ·
        refine ⟨74629262569275235816194257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49752841712850157210796171 74629262569275235816194257)
        ·
          refine ⟨55971946926956426862145693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74629262569275235816194257 55971946926956426862145693)
          ·
            refine ⟨20989480097608660073304635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55971946926956426862145693 20989480097608660073304635)
            ·
              refine ⟨31484220146412990109956953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20989480097608660073304635 31484220146412990109956953)
              ·
                refine ⟨23613165109809742582467715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31484220146412990109956953 23613165109809742582467715)
                ·
                  refine ⟨35419747664714613873701573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23613165109809742582467715 35419747664714613873701573)
                  ·
                    refine ⟨6641202687133990101319045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35419747664714613873701573 6641202687133990101319045)
                    ·
                      refine ⟨1245225503837623143997321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6641202687133990101319045 1245225503837623143997321)
                      ·
                        rfl

theorem cell23_2425068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_2425068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425068 prefixEnd_2425068 := by exact prefixLift 2425068
  have htrace : WordTrace (prefixWord ++ tailWord_2425068) baseStart_2425068 baseEnd_2425068 := by
    simpa [prefixWord, tailWord_2425068, baseEnd_2425068] using wordTrace_append hprefix tailTrace_2425068
  have hstable : (prefixWord ++ tailWord_2425068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425068).length < 2 ^ (prefixWord ++ tailWord_2425068).sum := by decide
  have hdescent : baseEnd_2425068 < baseStart_2425068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425105 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_2425105 : Nat := 118140960795 + 2425105 * 2 ^ 59
def prefixEnd_2425105 : Nat := 4983230072969 + 3 ^ 40 * 2425105 * 2
def baseEnd_2425105 : Nat := 1245244502621839499234651

theorem tailTrace_2425105 : CollatzResearch.WordTrace tailWord_2425105 prefixEnd_2425105 1245244502621839499234651 := by
  unfold tailWord_2425105
  simp only [CollatzResearch.WordTrace]
  refine ⟨88450845879266234804956769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58967230586177489869971179 88450845879266234804956769)
  ·
    refine ⟨66338134409449676103717577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88450845879266234804956769 66338134409449676103717577)
    ·
      refine ⟨49753600807087257077788183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66338134409449676103717577 49753600807087257077788183)
      ·
        refine ⟨74630401210630885616682275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49753600807087257077788183 74630401210630885616682275)
        ·
          refine ⟨111945601815946328425023413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74630401210630885616682275 111945601815946328425023413)
          ·
            refine ⟨10494900170244968289845945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111945601815946328425023413 10494900170244968289845945)
            ·
              refine ⟨7871175127683726217384459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10494900170244968289845945 7871175127683726217384459)
              ·
                refine ⟨11806762691525589326076689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7871175127683726217384459 11806762691525589326076689)
                ·
                  refine ⟨8855072018644191994557517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11806762691525589326076689 8855072018644191994557517)
                  ·
                    refine ⟨3320652006991571997959069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8855072018644191994557517 3320652006991571997959069)
                    ·
                      refine ⟨1245244502621839499234651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3320652006991571997959069 1245244502621839499234651)
                      ·
                        rfl

theorem cell23_2425105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_2425105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425105 prefixEnd_2425105 := by exact prefixLift 2425105
  have htrace : WordTrace (prefixWord ++ tailWord_2425105) baseStart_2425105 baseEnd_2425105 := by
    simpa [prefixWord, tailWord_2425105, baseEnd_2425105] using wordTrace_append hprefix tailTrace_2425105
  have hstable : (prefixWord ++ tailWord_2425105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425105).length < 2 ^ (prefixWord ++ tailWord_2425105).sum := by decide
  have hdescent : baseEnd_2425105 < baseStart_2425105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425115 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 2, 5, 2]
def baseStart_2425115 : Nat := 118140960795 + 2425115 * 2 ^ 59
def prefixEnd_2425115 : Nat := 4983230072969 + 3 ^ 40 * 2425115 * 2
def baseEnd_2425115 : Nat := 1245249637428384460109605

theorem tailTrace_2425115 : CollatzResearch.WordTrace tailWord_2425115 prefixEnd_2425115 1245249637428384460109605 := by
  unfold tailWord_2425115
  simp only [CollatzResearch.WordTrace]
  refine ⟨88451210609230006512820799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58967473739486671008547199 88451210609230006512820799)
  ·
    refine ⟨132676815913845009769231199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88451210609230006512820799 132676815913845009769231199)
    ·
      refine ⟨199015223870767514653846799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132676815913845009769231199 199015223870767514653846799)
      ·
        refine ⟨298522835806151271980770199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199015223870767514653846799 298522835806151271980770199)
        ·
          refine ⟨447784253709226907971155299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298522835806151271980770199 447784253709226907971155299)
          ·
            refine ⟨671676380563840361956732949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447784253709226907971155299 671676380563840361956732949)
            ·
              refine ⟨31484830338930016966721857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 671676380563840361956732949 31484830338930016966721857)
              ·
                refine ⟨23613622754197512725041393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31484830338930016966721857 23613622754197512725041393)
                ·
                  refine ⟨17710217065648134543781045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23613622754197512725041393 17710217065648134543781045)
                  ·
                    refine ⟨1660332849904512613479473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17710217065648134543781045 1660332849904512613479473)
                    ·
                      refine ⟨1245249637428384460109605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1660332849904512613479473 1245249637428384460109605)
                      ·
                        rfl

theorem cell23_2425115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 5, 2].length) (baseStart_2425115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425115 prefixEnd_2425115 := by exact prefixLift 2425115
  have htrace : WordTrace (prefixWord ++ tailWord_2425115) baseStart_2425115 baseEnd_2425115 := by
    simpa [prefixWord, tailWord_2425115, baseEnd_2425115] using wordTrace_append hprefix tailTrace_2425115
  have hstable : (prefixWord ++ tailWord_2425115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425115).length < 2 ^ (prefixWord ++ tailWord_2425115).sum := by decide
  have hdescent : baseEnd_2425115 < baseStart_2425115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425202 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 6]
def baseStart_2425202 : Nat := 118140960795 + 2425202 * 2 ^ 59
def prefixEnd_2425202 : Nat := 4983230072969 + 3 ^ 40 * 2425202 * 2
def baseEnd_2425202 : Nat := 138366034471702846635745

theorem tailTrace_2425202 : CollatzResearch.WordTrace tailWord_2425202 prefixEnd_2425202 138366034471702846635745 := by
  unfold tailWord_2425202
  simp only [CollatzResearch.WordTrace]
  refine ⟨22113595939978705092809465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58969589173276546914158573 22113595939978705092809465)
  ·
    refine ⟨16585196954984028819607099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22113595939978705092809465 16585196954984028819607099)
    ·
      refine ⟨24877795432476043229410649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16585196954984028819607099 24877795432476043229410649)
      ·
        refine ⟨18658346574357032422057987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24877795432476043229410649 18658346574357032422057987)
        ·
          refine ⟨27987519861535548633086981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18658346574357032422057987 27987519861535548633086981)
          ·
            refine ⟨5247659974037915368703809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27987519861535548633086981 5247659974037915368703809)
            ·
              refine ⟨3935744980528436526527857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5247659974037915368703809 3935744980528436526527857)
              ·
                refine ⟨2951808735396327394895893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3935744980528436526527857 2951808735396327394895893)
                ·
                  refine ⟨138366034471702846635745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2951808735396327394895893 138366034471702846635745)
                  ·
                    rfl

theorem cell23_2425202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_2425202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425202 prefixEnd_2425202 := by exact prefixLift 2425202
  have htrace : WordTrace (prefixWord ++ tailWord_2425202) baseStart_2425202 baseEnd_2425202 := by
    simpa [prefixWord, tailWord_2425202, baseEnd_2425202] using wordTrace_append hprefix tailTrace_2425202
  have hstable : (prefixWord ++ tailWord_2425202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425202).length < 2 ^ (prefixWord ++ tailWord_2425202).sum := by decide
  have hdescent : baseEnd_2425202 < baseStart_2425202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425239 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 2, 3, 2]
def baseStart_2425239 : Nat := 118140960795 + 2425239 * 2 ^ 59
def prefixEnd_2425239 : Nat := 4983230072969 + 3 ^ 40 * 2425239 * 2
def baseEnd_2425239 : Nat := 1245313309029541974959035

theorem tailTrace_2425239 : CollatzResearch.WordTrace tailWord_2425239 prefixEnd_2425239 1245313309029541974959035 := by
  unfold tailWord_2425239
  simp only [CollatzResearch.WordTrace]
  refine ⟨88455733260780775690334771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58970488840520517126889847 88455733260780775690334771)
  ·
    refine ⟨132683599891171163535502157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88455733260780775690334771 132683599891171163535502157)
    ·
      refine ⟨49756349959189186325813309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132683599891171163535502157 49756349959189186325813309)
      ·
        refine ⟨18658631234695944872179991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49756349959189186325813309 18658631234695944872179991)
        ·
          refine ⟨27987946852043917308269987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18658631234695944872179991 27987946852043917308269987)
          ·
            refine ⟨41981920278065875962404981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27987946852043917308269987 41981920278065875962404981)
            ·
              refine ⟨3935805026068675871475467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41981920278065875962404981 3935805026068675871475467)
              ·
                refine ⟨5903707539103013807213201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935805026068675871475467 5903707539103013807213201)
                ·
                  refine ⟨4427780654327260355409901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5903707539103013807213201 4427780654327260355409901)
                  ·
                    refine ⟨1660417745372722633278713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4427780654327260355409901 1660417745372722633278713)
                    ·
                      refine ⟨1245313309029541974959035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1660417745372722633278713 1245313309029541974959035)
                      ·
                        rfl

theorem cell23_2425239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_2425239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425239 prefixEnd_2425239 := by exact prefixLift 2425239
  have htrace : WordTrace (prefixWord ++ tailWord_2425239) baseStart_2425239 baseEnd_2425239 := by
    simpa [prefixWord, tailWord_2425239, baseEnd_2425239] using wordTrace_append hprefix tailTrace_2425239
  have hstable : (prefixWord ++ tailWord_2425239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425239).length < 2 ^ (prefixWord ++ tailWord_2425239).sum := by decide
  have hdescent : baseEnd_2425239 < baseStart_2425239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425292 : List Nat := [2, 2, 1, 4, 3, 1, 1, 9]
def baseStart_2425292 : Nat := 118140960795 + 2425292 * 2 ^ 59
def prefixEnd_2425292 : Nat := 4983230072969 + 3 ^ 40 * 2425292 * 2
def baseEnd_2425292 : Nat := 46123723092749269170233

theorem tailTrace_2425292 : CollatzResearch.WordTrace tailWord_2425292 prefixEnd_2425292 46123723092749269170233 := by
  unfold tailWord_2425292
  simp only [CollatzResearch.WordTrace]
  refine ⟨44228833164794382871007065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58971777553059177161342753 44228833164794382871007065)
  ·
    refine ⟨33171624873595787153255299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44228833164794382871007065 33171624873595787153255299)
    ·
      refine ⟨49757437310393680729882949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33171624873595787153255299 49757437310393680729882949)
      ·
        refine ⟨9329519495698815136853053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49757437310393680729882949 9329519495698815136853053)
        ·
          refine ⟨3498569810887055676319895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9329519495698815136853053 3498569810887055676319895)
          ·
            refine ⟨5247854716330583514479843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3498569810887055676319895 5247854716330583514479843)
            ·
              refine ⟨7871782074495875271719765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5247854716330583514479843 7871782074495875271719765)
              ·
                refine ⟨46123723092749269170233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7871782074495875271719765 46123723092749269170233)
                ·
                  rfl

theorem cell23_2425292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 9].length) (baseStart_2425292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425292 prefixEnd_2425292 := by exact prefixLift 2425292
  have htrace : WordTrace (prefixWord ++ tailWord_2425292) baseStart_2425292 baseEnd_2425292 := by
    simpa [prefixWord, tailWord_2425292, baseEnd_2425292] using wordTrace_append hprefix tailTrace_2425292
  have hstable : (prefixWord ++ tailWord_2425292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425292).length < 2 ^ (prefixWord ++ tailWord_2425292).sum := by decide
  have hdescent : baseEnd_2425292 < baseStart_2425292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425319 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2425319 : Nat := 118140960795 + 2425319 * 2 ^ 59
def prefixEnd_2425319 : Nat := 4983230072969 + 3 ^ 40 * 2425319 * 2
def baseEnd_2425319 : Nat := 1245354387481901661958667

theorem tailTrace_2425319 : CollatzResearch.WordTrace tailWord_2425319 prefixEnd_2425319 1245354387481901661958667 := by
  unfold tailWord_2425319
  simp only [CollatzResearch.WordTrace]
  refine ⟨88458651100490949353247011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58972434066993966235498007 88458651100490949353247011)
  ·
    refine ⟨132687976650736424029870517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88458651100490949353247011 132687976650736424029870517)
    ·
      refine ⟨12439497811006539752800361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132687976650736424029870517 12439497811006539752800361)
      ·
        refine ⟨9329623358254904814600271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12439497811006539752800361 9329623358254904814600271)
        ·
          refine ⟨13994435037382357221900407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9329623358254904814600271 13994435037382357221900407)
          ·
            refine ⟨20991652556073535832850611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13994435037382357221900407 20991652556073535832850611)
            ·
              refine ⟨31487478834110303749275917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20991652556073535832850611 31487478834110303749275917)
              ·
                refine ⟨11807804562791363905978469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31487478834110303749275917 11807804562791363905978469)
                ·
                  refine ⟨2213963355523380732370963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11807804562791363905978469 2213963355523380732370963)
                  ·
                    refine ⟨3320945033285071098556445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2213963355523380732370963 3320945033285071098556445)
                    ·
                      refine ⟨1245354387481901661958667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3320945033285071098556445 1245354387481901661958667)
                      ·
                        rfl

theorem cell23_2425319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2425319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425319 prefixEnd_2425319 := by exact prefixLift 2425319
  have htrace : WordTrace (prefixWord ++ tailWord_2425319) baseStart_2425319 baseEnd_2425319 := by
    simpa [prefixWord, tailWord_2425319, baseEnd_2425319] using wordTrace_append hprefix tailTrace_2425319
  have hstable : (prefixWord ++ tailWord_2425319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425319).length < 2 ^ (prefixWord ++ tailWord_2425319).sum := by decide
  have hdescent : baseEnd_2425319 < baseStart_2425319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425320 : List Nat := [2, 1, 4, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_2425320 : Nat := 118140960795 + 2425320 * 2 ^ 59
def prefixEnd_2425320 : Nat := 4983230072969 + 3 ^ 40 * 2425320 * 2
def baseEnd_2425320 : Nat := 1245354900962556158046163

theorem tailTrace_2425320 : CollatzResearch.WordTrace tailWord_2425320 prefixEnd_2425320 1245354900962556158046163 := by
  unfold tailWord_2425320
  simp only [CollatzResearch.WordTrace]
  refine ⟨44229343786743663262016707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58972458382324884349355609 44229343786743663262016707)
  ·
    refine ⟨66344015680115494893025061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44229343786743663262016707 66344015680115494893025061)
    ·
      refine ⟨12439502940021655292442199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66344015680115494893025061 12439502940021655292442199)
      ·
        refine ⟨18659254410032482938663299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12439502940021655292442199 18659254410032482938663299)
        ·
          refine ⟨27988881615048724407994949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18659254410032482938663299 27988881615048724407994949)
          ·
            refine ⟨5247915302821635826499053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27988881615048724407994949 5247915302821635826499053)
            ·
              refine ⟨1967968238558113434937145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5247915302821635826499053 1967968238558113434937145)
              ·
                refine ⟨1475976178918585076202859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1967968238558113434937145 1475976178918585076202859)
                ·
                  refine ⟨2213964268377877614304289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1475976178918585076202859 2213964268377877614304289)
                  ·
                    refine ⟨1660473201283408210728217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2213964268377877614304289 1660473201283408210728217)
                    ·
                      refine ⟨1245354900962556158046163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1660473201283408210728217 1245354900962556158046163)
                      ·
                        rfl

theorem cell23_2425320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_2425320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425320 prefixEnd_2425320 := by exact prefixLift 2425320
  have htrace : WordTrace (prefixWord ++ tailWord_2425320) baseStart_2425320 baseEnd_2425320 := by
    simpa [prefixWord, tailWord_2425320, baseEnd_2425320] using wordTrace_append hprefix tailTrace_2425320
  have hstable : (prefixWord ++ tailWord_2425320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425320).length < 2 ^ (prefixWord ++ tailWord_2425320).sum := by decide
  have hdescent : baseEnd_2425320 < baseStart_2425320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425329 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 3, 3, 2]
def baseStart_2425329 : Nat := 118140960795 + 2425329 * 2 ^ 59
def prefixEnd_2425329 : Nat := 4983230072969 + 3 ^ 40 * 2425329 * 2
def baseEnd_2425329 : Nat := 1245359522288446622833621

theorem tailTrace_2425329 : CollatzResearch.WordTrace tailWord_2425329 prefixEnd_2425329 1245359522288446622833621 := by
  unfold tailWord_2425329
  simp only [CollatzResearch.WordTrace]
  refine ⟨88459015830454721061111041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58972677220303147374074027 88459015830454721061111041)
  ·
    refine ⟨66344261872841040795833281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88459015830454721061111041 66344261872841040795833281)
    ·
      refine ⟨49758196404630780596874961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66344261872841040795833281 49758196404630780596874961)
      ·
        refine ⟨37318647303473085447656221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49758196404630780596874961 37318647303473085447656221)
        ·
          refine ⟨13994492738802407042871083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37318647303473085447656221 13994492738802407042871083)
          ·
            refine ⟨20991739108203610564306625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13994492738802407042871083 20991739108203610564306625)
            ·
              refine ⟨15743804331152707923229969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20991739108203610564306625 15743804331152707923229969)
              ·
                refine ⟨11807853248364530942422477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15743804331152707923229969 11807853248364530942422477)
                ·
                  refine ⟨4427944968136699103408429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11807853248364530942422477 4427944968136699103408429)
                  ·
                    refine ⟨1660479363051262163778161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4427944968136699103408429 1660479363051262163778161)
                    ·
                      refine ⟨1245359522288446622833621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1660479363051262163778161 1245359522288446622833621)
                      ·
                        rfl

theorem cell23_2425329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_2425329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425329 prefixEnd_2425329 := by exact prefixLift 2425329
  have htrace : WordTrace (prefixWord ++ tailWord_2425329) baseStart_2425329 baseEnd_2425329 := by
    simpa [prefixWord, tailWord_2425329, baseEnd_2425329] using wordTrace_append hprefix tailTrace_2425329
  have hstable : (prefixWord ++ tailWord_2425329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425329).length < 2 ^ (prefixWord ++ tailWord_2425329).sum := by decide
  have hdescent : baseEnd_2425329 < baseStart_2425329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425330 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_2425330 : Nat := 118140960795 + 2425330 * 2 ^ 59
def prefixEnd_2425330 : Nat := 4983230072969 + 3 ^ 40 * 2425330 * 2
def baseEnd_2425330 : Nat := 415120011923033706307039

theorem tailTrace_2425330 : CollatzResearch.WordTrace tailWord_2425330 prefixEnd_2425330 415120011923033706307039 := by
  unfold tailWord_2425330
  simp only [CollatzResearch.WordTrace]
  refine ⟨22114763075862774557974361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58972701535634065487931629 22114763075862774557974361)
  ·
    refine ⟨16586072306897080918480771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22114763075862774557974361 16586072306897080918480771)
    ·
      refine ⟨24879108460345621377721157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16586072306897080918480771 24879108460345621377721157)
      ·
        refine ⟨4664832836314804008322717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24879108460345621377721157 4664832836314804008322717)
        ·
          refine ⟨1749312313618051503121019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4664832836314804008322717 1749312313618051503121019)
          ·
            refine ⟨2623968470427077254681529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749312313618051503121019 2623968470427077254681529)
            ·
              refine ⟨1967976352820307941011147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2623968470427077254681529 1967976352820307941011147)
              ·
                refine ⟨2951964529230461911516721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967976352820307941011147 2951964529230461911516721)
                ·
                  refine ⟨2213973396922846433637541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2951964529230461911516721 2213973396922846433637541)
                  ·
                    refine ⟨415120011923033706307039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2213973396922846433637541 415120011923033706307039)
                    ·
                      rfl

theorem cell23_2425330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_2425330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425330 prefixEnd_2425330 := by exact prefixLift 2425330
  have htrace : WordTrace (prefixWord ++ tailWord_2425330) baseStart_2425330 baseEnd_2425330 := by
    simpa [prefixWord, tailWord_2425330, baseEnd_2425330] using wordTrace_append hprefix tailTrace_2425330
  have hstable : (prefixWord ++ tailWord_2425330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425330).length < 2 ^ (prefixWord ++ tailWord_2425330).sum := by decide
  have hdescent : baseEnd_2425330 < baseStart_2425330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425335 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 6, 6]
def baseStart_2425335 : Nat := 118140960795 + 2425335 * 2 ^ 59
def prefixEnd_2425335 : Nat := 4983230072969 + 3 ^ 40 * 2425335 * 2
def baseEnd_2425335 : Nat := 415120867724124533119531

theorem tailTrace_2425335 : CollatzResearch.WordTrace tailWord_2425335 prefixEnd_2425335 415120867724124533119531 := by
  unfold tailWord_2425335
  simp only [CollatzResearch.WordTrace]
  refine ⟨88459234668432984085829459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58972823112288656057219639 88459234668432984085829459)
  ·
    refine ⟨132688852002649476128744189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88459234668432984085829459 132688852002649476128744189)
    ·
      refine ⟨49758319500993553548279071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132688852002649476128744189 49758319500993553548279071)
      ·
        refine ⟨74637479251490330322418607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49758319500993553548279071 74637479251490330322418607)
        ·
          refine ⟨111956218877235495483627911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74637479251490330322418607 111956218877235495483627911)
          ·
            refine ⟨167934328315853243225441867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111956218877235495483627911 167934328315853243225441867)
            ·
              refine ⟨251901492473779864838162801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167934328315853243225441867 251901492473779864838162801)
              ·
                refine ⟨188926119355334898628622101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251901492473779864838162801 188926119355334898628622101)
                ·
                  refine ⟨8855911844781323373216661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188926119355334898628622101 8855911844781323373216661)
                  ·
                    refine ⟨415120867724124533119531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8855911844781323373216661 415120867724124533119531)
                    ·
                      rfl

theorem cell23_2425335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_2425335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425335 prefixEnd_2425335 := by exact prefixLift 2425335
  have htrace : WordTrace (prefixWord ++ tailWord_2425335) baseStart_2425335 baseEnd_2425335 := by
    simpa [prefixWord, tailWord_2425335, baseEnd_2425335] using wordTrace_append hprefix tailTrace_2425335
  have hstable : (prefixWord ++ tailWord_2425335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425335).length < 2 ^ (prefixWord ++ tailWord_2425335).sum := by decide
  have hdescent : baseEnd_2425335 < baseStart_2425335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425392 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 3]
def baseStart_2425392 : Nat := 118140960795 + 2425392 * 2 ^ 59
def prefixEnd_2425392 : Nat := 4983230072969 + 3 ^ 40 * 2425392 * 2
def baseEnd_2425392 : Nat := 1245391871569679876345831

theorem tailTrace_2425392 : CollatzResearch.WordTrace tailWord_2425392 prefixEnd_2425392 1245391871569679876345831 := by
  unfold tailWord_2425392
  simp only [CollatzResearch.WordTrace]
  refine ⟨44230656814613241410327215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58974209086150988547102953 44230656814613241410327215)
  ·
    refine ⟨66345985221919862115490823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44230656814613241410327215 66345985221919862115490823)
    ·
      refine ⟨99518977832879793173236235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66345985221919862115490823 99518977832879793173236235)
      ·
        refine ⟨149278466749319689759854353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99518977832879793173236235 149278466749319689759854353)
        ·
          refine ⟨111958850061989767319890765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149278466749319689759854353 111958850061989767319890765)
          ·
            refine ⟨41984568773246162744959037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111958850061989767319890765 41984568773246162744959037)
            ·
              refine ⟨15744213289967311029359639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41984568773246162744959037 15744213289967311029359639)
              ·
                refine ⟨23616319934950966544039459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15744213289967311029359639 23616319934950966544039459)
                ·
                  refine ⟨35424479902426449816059189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23616319934950966544039459 35424479902426449816059189)
                  ·
                    refine ⟨3321044990852479670255549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35424479902426449816059189 3321044990852479670255549)
                    ·
                      refine ⟨1245391871569679876345831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3321044990852479670255549 1245391871569679876345831)
                      ·
                        rfl

theorem cell23_2425392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_2425392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425392 prefixEnd_2425392 := by exact prefixLift 2425392
  have htrace : WordTrace (prefixWord ++ tailWord_2425392) baseStart_2425392 baseEnd_2425392 := by
    simpa [prefixWord, tailWord_2425392, baseEnd_2425392] using wordTrace_append hprefix tailTrace_2425392
  have hstable : (prefixWord ++ tailWord_2425392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425392).length < 2 ^ (prefixWord ++ tailWord_2425392).sum := by decide
  have hdescent : baseEnd_2425392 < baseStart_2425392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425422 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2425422 : Nat := 118140960795 + 2425422 * 2 ^ 59
def prefixEnd_2425422 : Nat := 4983230072969 + 3 ^ 40 * 2425422 * 2
def baseEnd_2425422 : Nat := 1245407275989314758970693

theorem tailTrace_2425422 : CollatzResearch.WordTrace tailWord_2425422 prefixEnd_2425422 1245407275989314758970693 := by
  unfold tailWord_2425422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11057800977389724743030815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58974938546078531962831013 11057800977389724743030815)
  ·
    refine ⟨16586701466084587114546223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11057800977389724743030815 16586701466084587114546223)
    ·
      refine ⟨24880052199126880671819335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16586701466084587114546223 24880052199126880671819335)
      ·
        refine ⟨37320078298690321007729003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24880052199126880671819335 37320078298690321007729003)
        ·
          refine ⟨55980117448035481511593505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37320078298690321007729003 55980117448035481511593505)
          ·
            refine ⟨41985088086026611133695129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55980117448035481511593505 41985088086026611133695129)
            ·
              refine ⟨31488816064519958350271347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41985088086026611133695129 31488816064519958350271347)
              ·
                refine ⟨47233224096779937525407021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31488816064519958350271347 47233224096779937525407021)
                ·
                  refine ⟨17712459036292476572027633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47233224096779937525407021 17712459036292476572027633)
                  ·
                    refine ⟨13284344277219357429020725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17712459036292476572027633 13284344277219357429020725)
                    ·
                      refine ⟨1245407275989314758970693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13284344277219357429020725 1245407275989314758970693)
                      ·
                        rfl

theorem cell23_2425422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2425422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425422 prefixEnd_2425422 := by exact prefixLift 2425422
  have htrace : WordTrace (prefixWord ++ tailWord_2425422) baseStart_2425422 baseEnd_2425422 := by
    simpa [prefixWord, tailWord_2425422, baseEnd_2425422] using wordTrace_append hprefix tailTrace_2425422
  have hstable : (prefixWord ++ tailWord_2425422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425422).length < 2 ^ (prefixWord ++ tailWord_2425422).sum := by decide
  have hdescent : baseEnd_2425422 < baseStart_2425422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425472 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 8]
def baseStart_2425472 : Nat := 118140960795 + 2425472 * 2 ^ 59
def prefixEnd_2425472 : Nat := 4983230072969 + 3 ^ 40 * 2425472 * 2
def baseEnd_2425472 : Nat := 138381438891337729260607

theorem tailTrace_2425472 : CollatzResearch.WordTrace tailWord_2425472 prefixEnd_2425472 138381438891337729260607 := by
  unfold tailWord_2425472
  simp only [CollatzResearch.WordTrace]
  refine ⟨44232115734468328241783335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58976154312624437655711113 44232115734468328241783335)
  ·
    refine ⟨66348173601702492362675003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44232115734468328241783335 66348173601702492362675003)
    ·
      refine ⟨99522260402553738544012505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66348173601702492362675003 99522260402553738544012505)
      ·
        refine ⟨74641695301915303908009379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99522260402553738544012505 74641695301915303908009379)
        ·
          refine ⟨111962542952872955862014069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74641695301915303908009379 111962542952872955862014069)
          ·
            refine ⟨10496488401831839612063819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111962542952872955862014069 10496488401831839612063819)
            ·
              refine ⟨15744732602747759418095729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10496488401831839612063819 15744732602747759418095729)
              ·
                refine ⟨11808549452060819563571797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15744732602747759418095729 11808549452060819563571797)
                ·
                  refine ⟨138381438891337729260607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11808549452060819563571797 138381438891337729260607)
                  ·
                    rfl

theorem cell23_2425472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 8].length) (baseStart_2425472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425472 prefixEnd_2425472 := by exact prefixLift 2425472
  have htrace : WordTrace (prefixWord ++ tailWord_2425472) baseStart_2425472 baseEnd_2425472 := by
    simpa [prefixWord, tailWord_2425472, baseEnd_2425472] using wordTrace_append hprefix tailTrace_2425472
  have hstable : (prefixWord ++ tailWord_2425472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425472).length < 2 ^ (prefixWord ++ tailWord_2425472).sum := by decide
  have hdescent : baseEnd_2425472 < baseStart_2425472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425486 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2425486 : Nat := 118140960795 + 2425486 * 2 ^ 59
def prefixEnd_2425486 : Nat := 4983230072969 + 3 ^ 40 * 2425486 * 2
def baseEnd_2425486 : Nat := 1245440138751202508570399

theorem tailTrace_2425486 : CollatzResearch.WordTrace tailWord_2425486 prefixEnd_2425486 1245440138751202508570399 := by
  unfold tailWord_2425486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11058092761360742109322039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58976494727257291249717541 11058092761360742109322039)
  ·
    refine ⟨16587139142041113163983059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11058092761360742109322039 16587139142041113163983059)
    ·
      refine ⟨24880708713061669745974589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16587139142041113163983059 24880708713061669745974589)
      ·
        refine ⟨9330265767398126154740471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24880708713061669745974589 9330265767398126154740471)
        ·
          refine ⟨13995398651097189232110707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9330265767398126154740471 13995398651097189232110707)
          ·
            refine ⟨20993097976645783848166061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13995398651097189232110707 20993097976645783848166061)
            ·
              refine ⟨7872411741242168943062273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20993097976645783848166061 7872411741242168943062273)
              ·
                refine ⟨5904308805931626707296705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7872411741242168943062273 5904308805931626707296705)
                ·
                  refine ⟨4428231604448720030472529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5904308805931626707296705 4428231604448720030472529)
                  ·
                    refine ⟨3321173703336540022854397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4428231604448720030472529 3321173703336540022854397)
                    ·
                      refine ⟨1245440138751202508570399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3321173703336540022854397 1245440138751202508570399)
                      ·
                        rfl

theorem cell23_2425486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2425486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425486 prefixEnd_2425486 := by exact prefixLift 2425486
  have htrace : WordTrace (prefixWord ++ tailWord_2425486) baseStart_2425486 baseEnd_2425486 := by
    simpa [prefixWord, tailWord_2425486, baseEnd_2425486] using wordTrace_append hprefix tailTrace_2425486
  have hstable : (prefixWord ++ tailWord_2425486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425486).length < 2 ^ (prefixWord ++ tailWord_2425486).sum := by decide
  have hdescent : baseEnd_2425486 < baseStart_2425486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425519 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 3, 5]
def baseStart_2425519 : Nat := 118140960795 + 2425519 * 2 ^ 59
def prefixEnd_2425519 : Nat := 4983230072969 + 3 ^ 40 * 2425519 * 2
def baseEnd_2425519 : Nat := 415152361204266959819249

theorem tailTrace_2425519 : CollatzResearch.WordTrace tailWord_2425519 prefixEnd_2425519 415152361204266959819249 := by
  unfold tailWord_2425519
  simp only [CollatzResearch.WordTrace]
  refine ⟨88465945699766383510527611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58977297133177589007018407 88465945699766383510527611)
  ·
    refine ⟨132698918549649575265791417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88465945699766383510527611 132698918549649575265791417)
    ·
      refine ⟨99524188912237181449343563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132698918549649575265791417 99524188912237181449343563)
      ·
        refine ⟨149286283368355772174015345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99524188912237181449343563 149286283368355772174015345)
        ·
          refine ⟨111964712526266829130511509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149286283368355772174015345 111964712526266829130511509)
          ·
            refine ⟨5248345899668757615492727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111964712526266829130511509 5248345899668757615492727)
            ·
              refine ⟨7872518849503136423239091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248345899668757615492727 7872518849503136423239091)
              ·
                refine ⟨11808778274254704634858637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7872518849503136423239091 11808778274254704634858637)
                ·
                  refine ⟨4428291852845514238071989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11808778274254704634858637 4428291852845514238071989)
                  ·
                    refine ⟨415152361204266959819249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4428291852845514238071989 415152361204266959819249)
                    ·
                      rfl

theorem cell23_2425519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_2425519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425519 prefixEnd_2425519 := by exact prefixLift 2425519
  have htrace : WordTrace (prefixWord ++ tailWord_2425519) baseStart_2425519 baseEnd_2425519 := by
    simpa [prefixWord, tailWord_2425519, baseEnd_2425519] using wordTrace_append hprefix tailTrace_2425519
  have hstable : (prefixWord ++ tailWord_2425519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425519).length < 2 ^ (prefixWord ++ tailWord_2425519).sum := by decide
  have hdescent : baseEnd_2425519 < baseStart_2425519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425550 : List Nat := [4, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3]
def baseStart_2425550 : Nat := 118140960795 + 2425550 * 2 ^ 59
def prefixEnd_2425550 : Nat := 4983230072969 + 3 ^ 40 * 2425550 * 2
def baseEnd_2425550 : Nat := 1245473001513090258170105

theorem tailTrace_2425550 : CollatzResearch.WordTrace tailWord_2425550 prefixEnd_2425550 1245473001513090258170105 := by
  unfold tailWord_2425550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11058384545331759475613263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58978050908436050536604069 11058384545331759475613263)
  ·
    refine ⟨16587576817997639213419895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11058384545331759475613263 16587576817997639213419895)
    ·
      refine ⟨24881365226996458820129843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16587576817997639213419895 24881365226996458820129843)
      ·
        refine ⟨37322047840494688230194765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24881365226996458820129843 37322047840494688230194765)
        ·
          refine ⟨13995767940185508086323037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37322047840494688230194765 13995767940185508086323037)
          ·
            refine ⟨5248412977569565532371139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13995767940185508086323037 5248412977569565532371139)
            ·
              refine ⟨7872619466354348298556709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248412977569565532371139 7872619466354348298556709)
              ·
                refine ⟨1476116149941440305979383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7872619466354348298556709 1476116149941440305979383)
                ·
                  refine ⟨2214174224912160458969075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476116149941440305979383 2214174224912160458969075)
                  ·
                    refine ⟨3321261337368240688453613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2214174224912160458969075 3321261337368240688453613)
                    ·
                      refine ⟨1245473001513090258170105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3321261337368240688453613 1245473001513090258170105)
                      ·
                        rfl

theorem cell23_2425550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_2425550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425550 prefixEnd_2425550 := by exact prefixLift 2425550
  have htrace : WordTrace (prefixWord ++ tailWord_2425550) baseStart_2425550 baseEnd_2425550 := by
    simpa [prefixWord, tailWord_2425550, baseEnd_2425550] using wordTrace_append hprefix tailTrace_2425550
  have hstable : (prefixWord ++ tailWord_2425550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425550).length < 2 ^ (prefixWord ++ tailWord_2425550).sum := by decide
  have hdescent : baseEnd_2425550 < baseStart_2425550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425573 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 5, 2, 2]
def baseStart_2425573 : Nat := 118140960795 + 2425573 * 2 ^ 59
def prefixEnd_2425573 : Nat := 4983230072969 + 3 ^ 40 * 2425573 * 2
def baseEnd_2425573 : Nat := 1245484811568143668182499

theorem tailTrace_2425573 : CollatzResearch.WordTrace tailWord_2425573 prefixEnd_2425573 1245484811568143668182499 := by
  unfold tailWord_2425573
  simp only [CollatzResearch.WordTrace]
  refine ⟨88467915241570750732993373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58978610161047167155328915 88467915241570750732993373)
  ·
    refine ⟨33175468215589031524872515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88467915241570750732993373 33175468215589031524872515)
    ·
      refine ⟨49763202323383547287308773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33175468215589031524872515 49763202323383547287308773)
      ·
        refine ⟨9330600435634415116370395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49763202323383547287308773 9330600435634415116370395)
        ·
          refine ⟨13995900653451622674555593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9330600435634415116370395 13995900653451622674555593)
          ·
            refine ⟨10496925490088717005916695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13995900653451622674555593 10496925490088717005916695)
            ·
              refine ⟨15745388235133075508875043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10496925490088717005916695 15745388235133075508875043)
              ·
                refine ⟨23618082352699613263312565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15745388235133075508875043 23618082352699613263312565)
                ·
                  refine ⟨2214195220565588743435553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23618082352699613263312565 2214195220565588743435553)
                  ·
                    refine ⟨1660646415424191557576665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2214195220565588743435553 1660646415424191557576665)
                    ·
                      refine ⟨1245484811568143668182499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1660646415424191557576665 1245484811568143668182499)
                      ·
                        rfl

theorem cell23_2425573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_2425573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425573 prefixEnd_2425573 := by exact prefixLift 2425573
  have htrace : WordTrace (prefixWord ++ tailWord_2425573) baseStart_2425573 baseEnd_2425573 := by
    simpa [prefixWord, tailWord_2425573, baseEnd_2425573] using wordTrace_append hprefix tailTrace_2425573
  have hstable : (prefixWord ++ tailWord_2425573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425573).length < 2 ^ (prefixWord ++ tailWord_2425573).sum := by decide
  have hdescent : baseEnd_2425573 < baseStart_2425573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425586 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2425586 : Nat := 118140960795 + 2425586 * 2 ^ 59
def prefixEnd_2425586 : Nat := 4983230072969 + 3 ^ 40 * 2425586 * 2
def baseEnd_2425586 : Nat := 1245491486816652117319939

theorem tailTrace_2425586 : CollatzResearch.WordTrace tailWord_2425586 prefixEnd_2425586 1245491486816652117319939 := by
  unfold tailWord_2425586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22117097347630913488304153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58978926260349102635477741 22117097347630913488304153)
  ·
    refine ⟨16587823010723185116228115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22117097347630913488304153 16587823010723185116228115)
    ·
      refine ⟨24881734516084777674342173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16587823010723185116228115 24881734516084777674342173)
      ·
        refine ⟨9330650443531791627878315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24881734516084777674342173 9330650443531791627878315)
        ·
          refine ⟨13995975665297687441817473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9330650443531791627878315 13995975665297687441817473)
          ·
            refine ⟨10496981748973265581363105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13995975665297687441817473 10496981748973265581363105)
            ·
              refine ⟨7872736311729949186022329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10496981748973265581363105 7872736311729949186022329)
              ·
                refine ⟨5904552233797461889516747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7872736311729949186022329 5904552233797461889516747)
                ·
                  refine ⟨8856828350696192834275121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5904552233797461889516747 8856828350696192834275121)
                  ·
                    refine ⟨6642621263022144625706341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8856828350696192834275121 6642621263022144625706341)
                    ·
                      refine ⟨1245491486816652117319939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6642621263022144625706341 1245491486816652117319939)
                      ·
                        rfl

theorem cell23_2425586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2425586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425586 prefixEnd_2425586 := by exact prefixLift 2425586
  have htrace : WordTrace (prefixWord ++ tailWord_2425586) baseStart_2425586 baseEnd_2425586 := by
    simpa [prefixWord, tailWord_2425586, baseEnd_2425586] using wordTrace_append hprefix tailTrace_2425586
  have hstable : (prefixWord ++ tailWord_2425586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425586).length < 2 ^ (prefixWord ++ tailWord_2425586).sum := by decide
  have hdescent : baseEnd_2425586 < baseStart_2425586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425607 : List Nat := [1, 1, 4, 4, 1, 1, 2, 4, 1, 2, 2]
def baseStart_2425607 : Nat := 118140960795 + 2425607 * 2 ^ 59
def prefixEnd_2425607 : Nat := 4983230072969 + 3 ^ 40 * 2425607 * 2
def baseEnd_2425607 : Nat := 1245502269910396535157343

theorem tailTrace_2425607 : CollatzResearch.WordTrace tailWord_2425607 prefixEnd_2425607 1245502269910396535157343 := by
  unfold tailWord_2425607
  simp only [CollatzResearch.WordTrace]
  refine ⟨88469155323447574539731075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58979436882298383026487383 88469155323447574539731075)
  ·
    refine ⟨132703732985171361809596613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88469155323447574539731075 132703732985171361809596613)
    ·
      refine ⟨24881949934719630339299365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132703732985171361809596613 24881949934719630339299365)
      ·
        refine ⟨4665365612759930688618631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24881949934719630339299365 4665365612759930688618631)
        ·
          refine ⟨6998048419139896032927947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4665365612759930688618631 6998048419139896032927947)
          ·
            refine ⟨10497072628709844049391921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6998048419139896032927947 10497072628709844049391921)
            ·
              refine ⟨7872804471532383037043941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10497072628709844049391921 7872804471532383037043941)
              ·
                refine ⟨1476150838412321819445739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7872804471532383037043941 1476150838412321819445739)
                ·
                  refine ⟨2214226257618482729168609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476150838412321819445739 2214226257618482729168609)
                  ·
                    refine ⟨1660669693213862046876457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2214226257618482729168609 1660669693213862046876457)
                    ·
                      refine ⟨1245502269910396535157343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1660669693213862046876457 1245502269910396535157343)
                      ·
                        rfl

theorem cell23_2425607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_2425607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425607 prefixEnd_2425607 := by exact prefixLift 2425607
  have htrace : WordTrace (prefixWord ++ tailWord_2425607) baseStart_2425607 baseEnd_2425607 := by
    simpa [prefixWord, tailWord_2425607, baseEnd_2425607] using wordTrace_append hprefix tailTrace_2425607
  have hstable : (prefixWord ++ tailWord_2425607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425607).length < 2 ^ (prefixWord ++ tailWord_2425607).sum := by decide
  have hdescent : baseEnd_2425607 < baseStart_2425607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425669 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 7]
def baseStart_2425669 : Nat := 118140960795 + 2425669 * 2 ^ 59
def prefixEnd_2425669 : Nat := 4983230072969 + 3 ^ 40 * 2425669 * 2
def baseEnd_2425669 : Nat := 138392678412330588064673

theorem tailTrace_2425669 : CollatzResearch.WordTrace tailWord_2425669 prefixEnd_2425669 138392678412330588064673 := by
  unfold tailWord_2425669
  simp only [CollatzResearch.WordTrace]
  refine ⟨88471416649222959128488061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58980944432815306085658707 88471416649222959128488061)
  ·
    refine ⟨33176781243458609673183023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88471416649222959128488061 33176781243458609673183023)
    ·
      refine ⟨49765171865187914509774535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33176781243458609673183023 49765171865187914509774535)
      ·
        refine ⟨74647757797781871764661803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49765171865187914509774535 74647757797781871764661803)
        ·
          refine ⟨111971636696672807646992705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74647757797781871764661803 111971636696672807646992705)
          ·
            refine ⟨83978727522504605735244529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111971636696672807646992705 83978727522504605735244529)
            ·
              refine ⟨62984045641878454301433397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83978727522504605735244529 62984045641878454301433397)
              ·
                refine ⟨5904754278926105090759381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62984045641878454301433397 5904754278926105090759381)
                ·
                  refine ⟨138392678412330588064673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5904754278926105090759381 138392678412330588064673)
                  ·
                    rfl

theorem cell23_2425669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_2425669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425669 prefixEnd_2425669 := by exact prefixLift 2425669
  have htrace : WordTrace (prefixWord ++ tailWord_2425669) baseStart_2425669 baseEnd_2425669 := by
    simpa [prefixWord, tailWord_2425669, baseEnd_2425669] using wordTrace_append hprefix tailTrace_2425669
  have hstable : (prefixWord ++ tailWord_2425669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425669).length < 2 ^ (prefixWord ++ tailWord_2425669).sum := by decide
  have hdescent : baseEnd_2425669 < baseStart_2425669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425684 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_2425684 : Nat := 118140960795 + 2425684 * 2 ^ 59
def prefixEnd_2425684 : Nat := 4983230072969 + 3 ^ 40 * 2425684 * 2
def baseEnd_2425684 : Nat := 1245541807920792733894489

theorem tailTrace_2425684 : CollatzResearch.WordTrace tailWord_2425684 prefixEnd_2425684 1245541807920792733894489 := by
  unfold tailWord_2425684
  simp only [CollatzResearch.WordTrace]
  refine ⟨44235981872084308345142053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58981309162779077793522737 44235981872084308345142053)
  ·
    refine ⟨8294246601015807814714135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44235981872084308345142053 8294246601015807814714135)
    ·
      refine ⟨12441369901523711722071203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8294246601015807814714135 12441369901523711722071203)
      ·
        refine ⟨18662054852285567583106805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12441369901523711722071203 18662054852285567583106805)
        ·
          refine ⟨1749567642401771960916263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18662054852285567583106805 1749567642401771960916263)
          ·
            refine ⟨2624351463602657941374395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749567642401771960916263 2624351463602657941374395)
            ·
              refine ⟨3936527195403986912061593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2624351463602657941374395 3936527195403986912061593)
              ·
                refine ⟨2952395396552990184046195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3936527195403986912061593 2952395396552990184046195)
                ·
                  refine ⟨4428593094829485276069293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952395396552990184046195 4428593094829485276069293)
                  ·
                    refine ⟨1660722410561056978525985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4428593094829485276069293 1660722410561056978525985)
                    ·
                      refine ⟨1245541807920792733894489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1660722410561056978525985 1245541807920792733894489)
                      ·
                        rfl

theorem cell23_2425684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_2425684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425684 prefixEnd_2425684 := by exact prefixLift 2425684
  have htrace : WordTrace (prefixWord ++ tailWord_2425684) baseStart_2425684 baseEnd_2425684 := by
    simpa [prefixWord, tailWord_2425684, baseEnd_2425684] using wordTrace_append hprefix tailTrace_2425684
  have hstable : (prefixWord ++ tailWord_2425684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425684).length < 2 ^ (prefixWord ++ tailWord_2425684).sum := by decide
  have hdescent : baseEnd_2425684 < baseStart_2425684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425814 : List Nat := [5, 2, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_2425814 : Nat := 118140960795 + 2425814 * 2 ^ 59
def prefixEnd_2425814 : Nat := 4983230072969 + 3 ^ 40 * 2425814 * 2
def baseEnd_2425814 : Nat := 415202853468625741756297

theorem tailTrace_2425814 : CollatzResearch.WordTrace tailWord_2425814 prefixEnd_2425814 415202853468625741756297 := by
  unfold tailWord_2425814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5529794077106103055782281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58984470155798432595010997 5529794077106103055782281)
  ·
    refine ⟨4147345557829577291836711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5529794077106103055782281 4147345557829577291836711)
    ·
      refine ⟨6221018336744365937755067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4147345557829577291836711 6221018336744365937755067)
      ·
        refine ⟨9331527505116548906632601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6221018336744365937755067 9331527505116548906632601)
        ·
          refine ⟨6998645628837411679974451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9331527505116548906632601 6998645628837411679974451)
          ·
            refine ⟨10497968443256117519961677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6998645628837411679974451 10497968443256117519961677)
            ·
              refine ⟨3936738166221044069985629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10497968443256117519961677 3936738166221044069985629)
              ·
                refine ⟨1476276812332891526244611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3936738166221044069985629 1476276812332891526244611)
                ·
                  refine ⟨2214415218499337289366917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476276812332891526244611 2214415218499337289366917)
                  ·
                    refine ⟨415202853468625741756297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2214415218499337289366917 415202853468625741756297)
                    ·
                      rfl

theorem cell23_2425814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_2425814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425814 prefixEnd_2425814 := by exact prefixLift 2425814
  have htrace : WordTrace (prefixWord ++ tailWord_2425814) baseStart_2425814 baseEnd_2425814 := by
    simpa [prefixWord, tailWord_2425814, baseEnd_2425814] using wordTrace_append hprefix tailTrace_2425814
  have hstable : (prefixWord ++ tailWord_2425814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425814).length < 2 ^ (prefixWord ++ tailWord_2425814).sum := by decide
  have hdescent : baseEnd_2425814 < baseStart_2425814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425877 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_2425877 : Nat := 118140960795 + 2425877 * 2 ^ 59
def prefixEnd_2425877 : Nat := 4983230072969 + 3 ^ 40 * 2425877 * 2
def baseEnd_2425877 : Nat := 1245640909687110478781101

theorem tailTrace_2425877 : CollatzResearch.WordTrace tailWord_2425877 prefixEnd_2425877 1245640909687110478781101 := by
  unfold tailWord_2425877
  simp only [CollatzResearch.WordTrace]
  refine ⟨88479003032469410652059885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58986002021646273768039923 88479003032469410652059885)
  ·
    refine ⟨33179626137176028994522457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88479003032469410652059885 33179626137176028994522457)
    ·
      refine ⟨24884719602882021745891843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33179626137176028994522457 24884719602882021745891843)
      ·
        refine ⟨37327079404323032618837765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24884719602882021745891843 37327079404323032618837765)
        ·
          refine ⟨6998827388310568616032081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37327079404323032618837765 6998827388310568616032081)
          ·
            refine ⟨5249120541232926462024061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6998827388310568616032081 5249120541232926462024061)
            ·
              refine ⟨1968420202962347423259023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5249120541232926462024061 1968420202962347423259023)
              ·
                refine ⟨2952630304443521134888535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968420202962347423259023 2952630304443521134888535)
                ·
                  refine ⟨4428945456665281702332803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952630304443521134888535 4428945456665281702332803)
                  ·
                    refine ⟨6643418184997922553499205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4428945456665281702332803 6643418184997922553499205)
                    ·
                      refine ⟨1245640909687110478781101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6643418184997922553499205 1245640909687110478781101)
                      ·
                        rfl

theorem cell23_2425877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_2425877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425877 prefixEnd_2425877 := by exact prefixLift 2425877
  have htrace : WordTrace (prefixWord ++ tailWord_2425877) baseStart_2425877 baseEnd_2425877 := by
    simpa [prefixWord, tailWord_2425877, baseEnd_2425877] using wordTrace_append hprefix tailTrace_2425877
  have hstable : (prefixWord ++ tailWord_2425877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425877).length < 2 ^ (prefixWord ++ tailWord_2425877).sum := by decide
  have hdescent : baseEnd_2425877 < baseStart_2425877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425880 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2425880 : Nat := 118140960795 + 2425880 * 2 ^ 59
def prefixEnd_2425880 : Nat := 4983230072969 + 3 ^ 40 * 2425880 * 2
def baseEnd_2425880 : Nat := 1245642450129073967043587

theorem tailTrace_2425880 : CollatzResearch.WordTrace tailWord_2425880 prefixEnd_2425880 1245642450129073967043587 := by
  unfold tailWord_2425880
  simp only [CollatzResearch.WordTrace]
  refine ⟨44239556225729271082209547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58986074967639028109612729 44239556225729271082209547)
  ·
    refine ⟨66359334338593906623314321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44239556225729271082209547 66359334338593906623314321)
    ·
      refine ⟨49769500753945429967485741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66359334338593906623314321 49769500753945429967485741)
      ·
        refine ⟨18663562782729536237807153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49769500753945429967485741 18663562782729536237807153)
        ·
          refine ⟨13997672087047152178355365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18663562782729536237807153 13997672087047152178355365)
          ·
            refine ⟨2624563516321341033441631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13997672087047152178355365 2624563516321341033441631)
            ·
              refine ⟨3936845274482011550162447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2624563516321341033441631 3936845274482011550162447)
              ·
                refine ⟨5905267911723017325243671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936845274482011550162447 5905267911723017325243671)
                ·
                  refine ⟨8857901867584525987865507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5905267911723017325243671 8857901867584525987865507)
                  ·
                    refine ⟨13286852801376788981798261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8857901867584525987865507 13286852801376788981798261)
                    ·
                      refine ⟨1245642450129073967043587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13286852801376788981798261 1245642450129073967043587)
                      ·
                        rfl

theorem cell23_2425880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2425880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425880 prefixEnd_2425880 := by exact prefixLift 2425880
  have htrace : WordTrace (prefixWord ++ tailWord_2425880) baseStart_2425880 baseEnd_2425880 := by
    simpa [prefixWord, tailWord_2425880, baseEnd_2425880] using wordTrace_append hprefix tailTrace_2425880
  have hstable : (prefixWord ++ tailWord_2425880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425880).length < 2 ^ (prefixWord ++ tailWord_2425880).sum := by decide
  have hdescent : baseEnd_2425880 < baseStart_2425880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425888 : List Nat := [2, 1, 1, 7, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2425888 : Nat := 118140960795 + 2425888 * 2 ^ 59
def prefixEnd_2425888 : Nat := 4983230072969 + 3 ^ 40 * 2425888 * 2
def baseEnd_2425888 : Nat := 1245646557974309935743551

theorem tailTrace_2425888 : CollatzResearch.WordTrace tailWord_2425888 prefixEnd_2425888 1245646557974309935743551 := by
  unfold tailWord_2425888
  simp only [CollatzResearch.WordTrace]
  refine ⟨44239702117714779765355159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58986269490286373020473545 44239702117714779765355159)
  ·
    refine ⟨66359553176572169648032739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44239702117714779765355159 66359553176572169648032739)
    ·
      refine ⟨99539329764858254472049109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66359553176572169648032739 99539329764858254472049109)
      ·
        refine ⟨2332953041363865339188651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 99539329764858254472049109 2332953041363865339188651)
        ·
          refine ⟨3499429562045798008782977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332953041363865339188651 3499429562045798008782977)
          ·
            refine ⟨2624572171534348506587233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3499429562045798008782977 2624572171534348506587233)
            ·
              refine ⟨1968429128650761379940425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2624572171534348506587233 1968429128650761379940425)
              ·
                refine ⟨1476321846488071034955319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1968429128650761379940425 1476321846488071034955319)
                ·
                  refine ⟨2214482769732106552432979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476321846488071034955319 2214482769732106552432979)
                  ·
                    refine ⟨3321724154598159828649469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2214482769732106552432979 3321724154598159828649469)
                    ·
                      refine ⟨1245646557974309935743551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3321724154598159828649469 1245646557974309935743551)
                      ·
                        rfl

theorem cell23_2425888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2425888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425888 prefixEnd_2425888 := by exact prefixLift 2425888
  have htrace : WordTrace (prefixWord ++ tailWord_2425888) baseStart_2425888 baseEnd_2425888 := by
    simpa [prefixWord, tailWord_2425888, baseEnd_2425888] using wordTrace_append hprefix tailTrace_2425888
  have hstable : (prefixWord ++ tailWord_2425888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425888).length < 2 ^ (prefixWord ++ tailWord_2425888).sum := by decide
  have hdescent : baseEnd_2425888 < baseStart_2425888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425893 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_2425893 : Nat := 118140960795 + 2425893 * 2 ^ 59
def prefixEnd_2425893 : Nat := 4983230072969 + 3 ^ 40 * 2425893 * 2
def baseEnd_2425893 : Nat := 1245649125377582416181027

theorem tailTrace_2425893 : CollatzResearch.WordTrace tailWord_2425893 prefixEnd_2425893 1245649125377582416181027 := by
  unfold tailWord_2425893
  simp only [CollatzResearch.WordTrace]
  refine ⟨88479586600411445384642333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58986391066940963589761555 88479586600411445384642333)
  ·
    refine ⟨33179844975154292019240875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88479586600411445384642333 33179844975154292019240875)
    ·
      refine ⟨49769767462731438028861313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33179844975154292019240875 49769767462731438028861313)
      ·
        refine ⟨37327325597048578521645985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49769767462731438028861313 37327325597048578521645985)
        ·
          refine ⟨27995494197786433891234489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37327325597048578521645985 27995494197786433891234489)
          ·
            refine ⟨20996620648339825418425867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27995494197786433891234489 20996620648339825418425867)
            ·
              refine ⟨31494930972509738127638801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20996620648339825418425867 31494930972509738127638801)
              ·
                refine ⟨23621198229382303595729101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31494930972509738127638801 23621198229382303595729101)
                ·
                  refine ⟨8857949336018363848398413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23621198229382303595729101 8857949336018363848398413)
                  ·
                    refine ⟨3321731001006886443149405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8857949336018363848398413 3321731001006886443149405)
                    ·
                      refine ⟨1245649125377582416181027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3321731001006886443149405 1245649125377582416181027)
                      ·
                        rfl

theorem cell23_2425893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_2425893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425893 prefixEnd_2425893 := by exact prefixLift 2425893
  have htrace : WordTrace (prefixWord ++ tailWord_2425893) baseStart_2425893 baseEnd_2425893 := by
    simpa [prefixWord, tailWord_2425893, baseEnd_2425893] using wordTrace_append hprefix tailTrace_2425893
  have hstable : (prefixWord ++ tailWord_2425893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425893).length < 2 ^ (prefixWord ++ tailWord_2425893).sum := by decide
  have hdescent : baseEnd_2425893 < baseStart_2425893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425920 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 3, 3, 2]
def baseStart_2425920 : Nat := 118140960795 + 2425920 * 2 ^ 59
def prefixEnd_2425920 : Nat := 4983230072969 + 3 ^ 40 * 2425920 * 2
def baseEnd_2425920 : Nat := 1245662989355253810543403

theorem tailTrace_2425920 : CollatzResearch.WordTrace tailWord_2425920 prefixEnd_2425920 1245662989355253810543403 := by
  unfold tailWord_2425920
  simp only [CollatzResearch.WordTrace]
  refine ⟨44240285685656814497937607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58987047580875752663916809 44240285685656814497937607)
  ·
    refine ⟨66360428528485221746906411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44240285685656814497937607 66360428528485221746906411)
    ·
      refine ⟨99540642792727832620359617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66360428528485221746906411 99540642792727832620359617)
      ·
        refine ⟨74655482094545874465269713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99540642792727832620359617 74655482094545874465269713)
        ·
          refine ⟨55991611570909405848952285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74655482094545874465269713 55991611570909405848952285)
          ·
            refine ⟨20996854339091027193357107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55991611570909405848952285 20996854339091027193357107)
            ·
              refine ⟨31495281508636540790035661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20996854339091027193357107 31495281508636540790035661)
              ·
                refine ⟨11810730565738702796263373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31495281508636540790035661 11810730565738702796263373)
                ·
                  refine ⟨4429023962152013548598765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11810730565738702796263373 4429023962152013548598765)
                  ·
                    refine ⟨1660883985807005080724537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4429023962152013548598765 1660883985807005080724537)
                    ·
                      refine ⟨1245662989355253810543403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1660883985807005080724537 1245662989355253810543403)
                      ·
                        rfl

theorem cell23_2425920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_2425920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425920 prefixEnd_2425920 := by exact prefixLift 2425920
  have htrace : WordTrace (prefixWord ++ tailWord_2425920) baseStart_2425920 baseEnd_2425920 := by
    simpa [prefixWord, tailWord_2425920, baseEnd_2425920] using wordTrace_append hprefix tailTrace_2425920
  have hstable : (prefixWord ++ tailWord_2425920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425920).length < 2 ^ (prefixWord ++ tailWord_2425920).sum := by decide
  have hdescent : baseEnd_2425920 < baseStart_2425920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2425953 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_2425953 : Nat := 118140960795 + 2425953 * 2 ^ 59
def prefixEnd_2425953 : Nat := 4983230072969 + 3 ^ 40 * 2425953 * 2
def baseEnd_2425953 : Nat := 1245679934216852181430751

theorem tailTrace_2425953 : CollatzResearch.WordTrace tailWord_2425953 prefixEnd_2425953 1245679934216852181430751 := by
  unfold tailWord_2425953
  simp only [CollatzResearch.WordTrace]
  refine ⟨88481774980194075631826513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58987849986796050421217675 88481774980194075631826513)
  ·
    refine ⟨66361331235145556723869885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88481774980194075631826513 66361331235145556723869885)
    ·
      refine ⟨24885499213179583771451207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66361331235145556723869885 24885499213179583771451207)
      ·
        refine ⟨37328248819769375657176811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24885499213179583771451207 37328248819769375657176811)
        ·
          refine ⟨55992373229654063485765217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37328248819769375657176811 55992373229654063485765217)
          ·
            refine ⟨41994279922240547614323913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55992373229654063485765217 41994279922240547614323913)
            ·
              refine ⟨31495709941680410710742935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41994279922240547614323913 31495709941680410710742935)
              ·
                refine ⟨47243564912520616066114403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31495709941680410710742935 47243564912520616066114403)
                ·
                  refine ⟨70865347368780924099171605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47243564912520616066114403 70865347368780924099171605)
                  ·
                    refine ⟨3321813157911605817148669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70865347368780924099171605 3321813157911605817148669)
                    ·
                      refine ⟨1245679934216852181430751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3321813157911605817148669 1245679934216852181430751)
                      ·
                        rfl

theorem cell23_2425953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_2425953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2425953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2425953 prefixEnd_2425953 := by exact prefixLift 2425953
  have htrace : WordTrace (prefixWord ++ tailWord_2425953) baseStart_2425953 baseEnd_2425953 := by
    simpa [prefixWord, tailWord_2425953, baseEnd_2425953] using wordTrace_append hprefix tailTrace_2425953
  have hstable : (prefixWord ++ tailWord_2425953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2425953).length < 2 ^ (prefixWord ++ tailWord_2425953).sum := by decide
  have hdescent : baseEnd_2425953 < baseStart_2425953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2425953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426003 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 4, 5]
def baseStart_2426003 : Nat := 118140960795 + 2426003 * 2 ^ 59
def prefixEnd_2426003 : Nat := 4983230072969 + 3 ^ 40 * 2426003 * 2
def baseEnd_2426003 : Nat := 415235202749858995268507

theorem tailTrace_2426003 : CollatzResearch.WordTrace tailWord_2426003 prefixEnd_2426003 415235202749858995268507 := by
  unfold tailWord_2426003
  simp only [CollatzResearch.WordTrace]
  refine ⟨88483598630012934171146663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58989065753341956114097775 88483598630012934171146663)
  ·
    refine ⟨132725397945019401256719995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88483598630012934171146663 132725397945019401256719995)
    ·
      refine ⟨199088096917529101885079993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132725397945019401256719995 199088096917529101885079993)
      ·
        refine ⟨149316072688146826413809995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199088096917529101885079993 149316072688146826413809995)
        ·
          refine ⟨223974109032220239620714993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149316072688146826413809995 223974109032220239620714993)
          ·
            refine ⟨167980581774165179715536245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223974109032220239620714993 167980581774165179715536245)
            ·
              refine ⟨15748179541327985598331523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167980581774165179715536245 15748179541327985598331523)
              ·
                refine ⟨23622269311991978397497285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15748179541327985598331523 23622269311991978397497285)
                ·
                  refine ⟨4429175495998495949530741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23622269311991978397497285 4429175495998495949530741)
                  ·
                    refine ⟨415235202749858995268507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4429175495998495949530741 415235202749858995268507)
                    ·
                      rfl

theorem cell23_2426003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 5].length) (baseStart_2426003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426003 prefixEnd_2426003 := by exact prefixLift 2426003
  have htrace : WordTrace (prefixWord ++ tailWord_2426003) baseStart_2426003 baseEnd_2426003 := by
    simpa [prefixWord, tailWord_2426003, baseEnd_2426003] using wordTrace_append hprefix tailTrace_2426003
  have hstable : (prefixWord ++ tailWord_2426003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426003).length < 2 ^ (prefixWord ++ tailWord_2426003).sum := by decide
  have hdescent : baseEnd_2426003 < baseStart_2426003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426040 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 3, 6, 2]
def baseStart_2426040 : Nat := 118140960795 + 2426040 * 2 ^ 59
def prefixEnd_2426040 : Nat := 4983230072969 + 3 ^ 40 * 2426040 * 2
def baseEnd_2426040 : Nat := 1245724607033793341042851

theorem tailTrace_2426040 : CollatzResearch.WordTrace tailWord_2426040 prefixEnd_2426040 1245724607033793341042851 := by
  unfold tailWord_2426040
  simp only [CollatzResearch.WordTrace]
  refine ⟨44242474065439444745121787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58989965420585926326829049 44242474065439444745121787)
  ·
    refine ⟨66363711098159167117682681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44242474065439444745121787 66363711098159167117682681)
    ·
      refine ⟨49772783323619375338262011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66363711098159167117682681 49772783323619375338262011)
      ·
        refine ⟨74659174985429063007393017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49772783323619375338262011 74659174985429063007393017)
        ·
          refine ⟨55994381239071797255544763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74659174985429063007393017 55994381239071797255544763)
          ·
            refine ⟨83991571858607695883317145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55994381239071797255544763 83991571858607695883317145)
            ·
              refine ⟨62993678893955771912487859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83991571858607695883317145 62993678893955771912487859)
              ·
                refine ⟨94490518340933657868731789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62993678893955771912487859 94490518340933657868731789)
                ·
                  refine ⟨35433944377850121700774421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94490518340933657868731789 35433944377850121700774421)
                  ·
                    refine ⟨1660966142711724454723801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35433944377850121700774421 1660966142711724454723801)
                    ·
                      refine ⟨1245724607033793341042851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1660966142711724454723801 1245724607033793341042851)
                      ·
                        rfl

theorem cell23_2426040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_2426040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426040 prefixEnd_2426040 := by exact prefixLift 2426040
  have htrace : WordTrace (prefixWord ++ tailWord_2426040) baseStart_2426040 baseEnd_2426040 := by
    simpa [prefixWord, tailWord_2426040, baseEnd_2426040] using wordTrace_append hprefix tailTrace_2426040
  have hstable : (prefixWord ++ tailWord_2426040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426040).length < 2 ^ (prefixWord ++ tailWord_2426040).sum := by decide
  have hdescent : baseEnd_2426040 < baseStart_2426040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426053 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_2426053 : Nat := 118140960795 + 2426053 * 2 ^ 59
def prefixEnd_2426053 : Nat := 4983230072969 + 3 ^ 40 * 2426053 * 2
def baseEnd_2426053 : Nat := 1245731282282301790180291

theorem tailTrace_2426053 : CollatzResearch.WordTrace tailWord_2426053 prefixEnd_2426053 1245731282282301790180291 := by
  unfold tailWord_2426053
  simp only [CollatzResearch.WordTrace]
  refine ⟨88485422279831792710466813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58990281519887861806977875 88485422279831792710466813)
  ·
    refine ⟨33182033354936922266425055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88485422279831792710466813 33182033354936922266425055)
    ·
      refine ⟨49773050032405383399637583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33182033354936922266425055 49773050032405383399637583)
      ·
        refine ⟨74659575048608075099456375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49773050032405383399637583 74659575048608075099456375)
        ·
          refine ⟨111989362572912112649184563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74659575048608075099456375 111989362572912112649184563)
          ·
            refine ⟨167984043859368168973776845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111989362572912112649184563 167984043859368168973776845)
            ·
              refine ⟨62994016447263063365166317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167984043859368168973776845 62994016447263063365166317)
              ·
                refine ⟨23622756167723648761937369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62994016447263063365166317 23622756167723648761937369)
                ·
                  refine ⟨17717067125792736571453027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23622756167723648761937369 17717067125792736571453027)
                  ·
                    refine ⟨26575600688689104857179541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17717067125792736571453027 26575600688689104857179541)
                    ·
                      refine ⟨1245731282282301790180291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26575600688689104857179541 1245731282282301790180291)
                      ·
                        rfl

theorem cell23_2426053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_2426053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426053 prefixEnd_2426053 := by exact prefixLift 2426053
  have htrace : WordTrace (prefixWord ++ tailWord_2426053) baseStart_2426053 baseEnd_2426053 := by
    simpa [prefixWord, tailWord_2426053, baseEnd_2426053] using wordTrace_append hprefix tailTrace_2426053
  have hstable : (prefixWord ++ tailWord_2426053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426053).length < 2 ^ (prefixWord ++ tailWord_2426053).sum := by decide
  have hdescent : baseEnd_2426053 < baseStart_2426053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426067 : List Nat := [1, 1, 1, 2, 1, 1, 1, 10, 1, 4]
def baseStart_2426067 : Nat := 118140960795 + 2426067 * 2 ^ 59
def prefixEnd_2426067 : Nat := 4983230072969 + 3 ^ 40 * 2426067 * 2
def baseEnd_2426067 : Nat := 415246157003821578468409

theorem tailTrace_2426067 : CollatzResearch.WordTrace tailWord_2426067 prefixEnd_2426067 415246157003821578468409 := by
  unfold tailWord_2426067
  simp only [CollatzResearch.WordTrace]
  refine ⟨88485932901781073101476455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58990621934520715400984303 88485932901781073101476455)
  ·
    refine ⟨132728899352671609652214683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88485932901781073101476455 132728899352671609652214683)
    ·
      refine ⟨199093349029007414478322025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132728899352671609652214683 199093349029007414478322025)
      ·
        refine ⟨149320011771755560858741519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199093349029007414478322025 149320011771755560858741519)
        ·
          refine ⟨223980017657633341288112279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149320011771755560858741519 223980017657633341288112279)
          ·
            refine ⟨335970026486450011932168419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223980017657633341288112279 335970026486450011932168419)
            ·
              refine ⟨503955039729675017898252629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335970026486450011932168419 503955039729675017898252629)
              ·
                refine ⟨1476430780458032278998787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 503955039729675017898252629 1476430780458032278998787)
                ·
                  refine ⟨2214646170687048418498181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476430780458032278998787 2214646170687048418498181)
                  ·
                    refine ⟨415246157003821578468409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2214646170687048418498181 415246157003821578468409)
                    ·
                      rfl

theorem cell23_2426067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 4].length) (baseStart_2426067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426067 prefixEnd_2426067 := by exact prefixLift 2426067
  have htrace : WordTrace (prefixWord ++ tailWord_2426067) baseStart_2426067 baseEnd_2426067 := by
    simpa [prefixWord, tailWord_2426067, baseEnd_2426067] using wordTrace_append hprefix tailTrace_2426067
  have hstable : (prefixWord ++ tailWord_2426067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426067).length < 2 ^ (prefixWord ++ tailWord_2426067).sum := by decide
  have hdescent : baseEnd_2426067 < baseStart_2426067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426080 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 6]
def baseStart_2426080 : Nat := 118140960795 + 2426080 * 2 ^ 59
def prefixEnd_2426080 : Nat := 4983230072969 + 3 ^ 40 * 2426080 * 2
def baseEnd_2426080 : Nat := 138416127362219242726963

theorem tailTrace_2426080 : CollatzResearch.WordTrace tailWord_2426080 prefixEnd_2426080 138416127362219242726963 := by
  unfold tailWord_2426080
  simp only [CollatzResearch.WordTrace]
  refine ⟨44243203525366988160849847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58990938033822650881133129 44243203525366988160849847)
  ·
    refine ⟨66364805288050482241274771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44243203525366988160849847 66364805288050482241274771)
    ·
      refine ⟨99547207932075723361912157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66364805288050482241274771 99547207932075723361912157)
      ·
        refine ⟨37330202974528396260717059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99547207932075723361912157 37330202974528396260717059)
        ·
          refine ⟨55995304461792594391075589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37330202974528396260717059 55995304461792594391075589)
          ·
            refine ⟨10499119586586111448326673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55995304461792594391075589 10499119586586111448326673)
            ·
              refine ⟨7874339689939583586245005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10499119586586111448326673 7874339689939583586245005)
              ·
                refine ⟨2952877383727343844841877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7874339689939583586245005 2952877383727343844841877)
                ·
                  refine ⟨138416127362219242726963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2952877383727343844841877 138416127362219242726963)
                  ·
                    rfl

theorem cell23_2426080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 6].length) (baseStart_2426080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426080 prefixEnd_2426080 := by exact prefixLift 2426080
  have htrace : WordTrace (prefixWord ++ tailWord_2426080) baseStart_2426080 baseEnd_2426080 := by
    simpa [prefixWord, tailWord_2426080, baseEnd_2426080] using wordTrace_append hprefix tailTrace_2426080
  have hstable : (prefixWord ++ tailWord_2426080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426080).length < 2 ^ (prefixWord ++ tailWord_2426080).sum := by decide
  have hdescent : baseEnd_2426080 < baseStart_2426080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426103 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_2426103 : Nat := 118140960795 + 2426103 * 2 ^ 59
def prefixEnd_2426103 : Nat := 4983230072969 + 3 ^ 40 * 2426103 * 2
def baseEnd_2426103 : Nat := 1245756956315026594555061

theorem tailTrace_2426103 : CollatzResearch.WordTrace tailWord_2426103 prefixEnd_2426103 1245756956315026594555061 := by
  unfold tailWord_2426103
  simp only [CollatzResearch.WordTrace]
  refine ⟨88487245929650651249786963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58991497286433767499857975 88487245929650651249786963)
  ·
    refine ⟨132730868894475976874680445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88487245929650651249786963 132730868894475976874680445)
    ·
      refine ⟨49774075835428491328005167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132730868894475976874680445 49774075835428491328005167)
      ·
        refine ⟨74661113753142736992007751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49774075835428491328005167 74661113753142736992007751)
        ·
          refine ⟨111991670629714105488011627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74661113753142736992007751 111991670629714105488011627)
          ·
            refine ⟨167987505944571158232017441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111991670629714105488011627 167987505944571158232017441)
            ·
              refine ⟨125990629458428368674013081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167987505944571158232017441 125990629458428368674013081)
              ·
                refine ⟨94492972093821276505509811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125990629458428368674013081 94492972093821276505509811)
                ·
                  refine ⟨141739458140731914758264717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94492972093821276505509811 141739458140731914758264717)
                  ·
                    refine ⟨53152296802774468034349269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141739458140731914758264717 53152296802774468034349269)
                    ·
                      refine ⟨1245756956315026594555061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53152296802774468034349269 1245756956315026594555061)
                      ·
                        rfl

theorem cell23_2426103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_2426103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426103 prefixEnd_2426103 := by exact prefixLift 2426103
  have htrace : WordTrace (prefixWord ++ tailWord_2426103) baseStart_2426103 baseEnd_2426103 := by
    simpa [prefixWord, tailWord_2426103, baseEnd_2426103] using wordTrace_append hprefix tailTrace_2426103
  have hstable : (prefixWord ++ tailWord_2426103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426103).length < 2 ^ (prefixWord ++ tailWord_2426103).sum := by decide
  have hdescent : baseEnd_2426103 < baseStart_2426103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426117 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 4, 3, 2]
def baseStart_2426117 : Nat := 118140960795 + 2426117 * 2 ^ 59
def prefixEnd_2426117 : Nat := 4983230072969 + 3 ^ 40 * 2426117 * 2
def baseEnd_2426117 : Nat := 1245764145044189539779997

theorem tailTrace_2426117 : CollatzResearch.WordTrace tailWord_2426117 prefixEnd_2426117 1245764145044189539779997 := by
  unfold tailWord_2426117
  simp only [CollatzResearch.WordTrace]
  refine ⟨88487756551599931640796605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58991837701066621093864403 88487756551599931640796605)
  ·
    refine ⟨33182908706849974365298727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88487756551599931640796605 33182908706849974365298727)
    ·
      refine ⟨49774363060274961547948091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33182908706849974365298727 49774363060274961547948091)
      ·
        refine ⟨74661544590412442321922137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49774363060274961547948091 74661544590412442321922137)
        ·
          refine ⟨55996158442809331741441603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74661544590412442321922137 55996158442809331741441603)
          ·
            refine ⟨83994237664213997612162405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55996158442809331741441603 83994237664213997612162405)
            ·
              refine ⟨15748919562040124552280451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83994237664213997612162405 15748919562040124552280451)
              ·
                refine ⟨23623379343060186828420677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15748919562040124552280451 23623379343060186828420677)
                ·
                  refine ⟨4429383626823785030328877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23623379343060186828420677 4429383626823785030328877)
                  ·
                    refine ⟨1661018860058919386373329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4429383626823785030328877 1661018860058919386373329)
                    ·
                      refine ⟨1245764145044189539779997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661018860058919386373329 1245764145044189539779997)
                      ·
                        rfl

theorem cell23_2426117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_2426117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426117 prefixEnd_2426117 := by exact prefixLift 2426117
  have htrace : WordTrace (prefixWord ++ tailWord_2426117) baseStart_2426117 baseEnd_2426117 := by
    simpa [prefixWord, tailWord_2426117, baseEnd_2426117] using wordTrace_append hprefix tailTrace_2426117
  have hstable : (prefixWord ++ tailWord_2426117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426117).length < 2 ^ (prefixWord ++ tailWord_2426117).sum := by decide
  have hdescent : baseEnd_2426117 < baseStart_2426117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426124 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 3, 1, 3]
def baseStart_2426124 : Nat := 118140960795 + 2426124 * 2 ^ 59
def prefixEnd_2426124 : Nat := 4983230072969 + 3 ^ 40 * 2426124 * 2
def baseEnd_2426124 : Nat := 1245767739408771012392465

theorem tailTrace_2426124 : CollatzResearch.WordTrace tailWord_2426124 prefixEnd_2426124 1245767739408771012392465 := by
  unfold tailWord_2426124
  simp only [CollatzResearch.WordTrace]
  refine ⟨44244005931287285918150713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58992007908383047890867617 44244005931287285918150713)
  ·
    refine ⟨33183004448465464438613035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44244005931287285918150713 33183004448465464438613035)
    ·
      refine ⟨49774506672698196657919553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33183004448465464438613035 49774506672698196657919553)
      ·
        refine ⟨37330880004523647493439665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49774506672698196657919553 37330880004523647493439665)
        ·
          refine ⟨27998160003392735620079749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37330880004523647493439665 27998160003392735620079749)
          ·
            refine ⟨5249655000636137928764953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27998160003392735620079749 5249655000636137928764953)
            ·
              refine ⟨3937241250477103446573715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5249655000636137928764953 3937241250477103446573715)
              ·
                refine ⟨5905861875715655169860573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3937241250477103446573715 5905861875715655169860573)
                ·
                  refine ⟨2214698203393370688697715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5905861875715655169860573 2214698203393370688697715)
                  ·
                    refine ⟨3322047305090056033046573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2214698203393370688697715 3322047305090056033046573)
                    ·
                      refine ⟨1245767739408771012392465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3322047305090056033046573 1245767739408771012392465)
                      ·
                        rfl

theorem cell23_2426124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_2426124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426124 prefixEnd_2426124 := by exact prefixLift 2426124
  have htrace : WordTrace (prefixWord ++ tailWord_2426124) baseStart_2426124 baseEnd_2426124 := by
    simpa [prefixWord, tailWord_2426124, baseEnd_2426124] using wordTrace_append hprefix tailTrace_2426124
  have hstable : (prefixWord ++ tailWord_2426124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426124).length < 2 ^ (prefixWord ++ tailWord_2426124).sum := by decide
  have hdescent : baseEnd_2426124 < baseStart_2426124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426144 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 1, 5]
def baseStart_2426144 : Nat := 118140960795 + 2426144 * 2 ^ 59
def prefixEnd_2426144 : Nat := 4983230072969 + 3 ^ 40 * 2426144 * 2
def baseEnd_2426144 : Nat := 415259336340620311380791

theorem tailTrace_2426144 : CollatzResearch.WordTrace tailWord_2426144 prefixEnd_2426144 415259336340620311380791 := by
  unfold tailWord_2426144
  simp only [CollatzResearch.WordTrace]
  refine ⟨44244370661251057626014743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58992494215001410168019657 44244370661251057626014743)
  ·
    refine ⟨66366555991876586439022115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44244370661251057626014743 66366555991876586439022115)
    ·
      refine ⟨99549833987814879658533173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66366555991876586439022115 99549833987814879658533173)
      ·
        refine ⟨9332796936357644967987485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99549833987814879658533173 9332796936357644967987485)
        ·
          refine ⟨3499798851134116862995307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9332796936357644967987485 3499798851134116862995307)
          ·
            refine ⟨5249698276701175294492961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499798851134116862995307 5249698276701175294492961)
            ·
              refine ⟨3937273707525881470869721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5249698276701175294492961 3937273707525881470869721)
              ·
                refine ⟨2952955280644411103152291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3937273707525881470869721 2952955280644411103152291)
                ·
                  refine ⟨4429432920966616654728437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952955280644411103152291 4429432920966616654728437)
                  ·
                    refine ⟨415259336340620311380791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4429432920966616654728437 415259336340620311380791)
                    ·
                      rfl

theorem cell23_2426144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 5].length) (baseStart_2426144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426144 prefixEnd_2426144 := by exact prefixLift 2426144
  have htrace : WordTrace (prefixWord ++ tailWord_2426144) baseStart_2426144 baseEnd_2426144 := by
    simpa [prefixWord, tailWord_2426144, baseEnd_2426144] using wordTrace_append hprefix tailTrace_2426144
  have hstable : (prefixWord ++ tailWord_2426144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426144).length < 2 ^ (prefixWord ++ tailWord_2426144).sum := by decide
  have hdescent : baseEnd_2426144 < baseStart_2426144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426147 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 4]
def baseStart_2426147 : Nat := 118140960795 + 2426147 * 2 ^ 59
def prefixEnd_2426147 : Nat := 4983230072969 + 3 ^ 40 * 2426147 * 2
def baseEnd_2426147 : Nat := 1245779549463824422404859

theorem tailTrace_2426147 : CollatzResearch.WordTrace tailWord_2426147 prefixEnd_2426147 1245779549463824422404859 := by
  unfold tailWord_2426147
  simp only [CollatzResearch.WordTrace]
  refine ⟨88488850741491246764388695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58992567160994164509592463 88488850741491246764388695)
  ·
    refine ⟨132733276112236870146583043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88488850741491246764388695 132733276112236870146583043)
    ·
      refine ⟨199099914168355305219874565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132733276112236870146583043 199099914168355305219874565)
      ·
        refine ⟨37331233906566619728726481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199099914168355305219874565 37331233906566619728726481)
        ·
          refine ⟨27998425429924964796544861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37331233906566619728726481 27998425429924964796544861)
          ·
            refine ⟨10499409536221861798704323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27998425429924964796544861 10499409536221861798704323)
            ·
              refine ⟨15749114304332792698056485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10499409536221861798704323 15749114304332792698056485)
              ·
                refine ⟨2952958932062398630885591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15749114304332792698056485 2952958932062398630885591)
                ·
                  refine ⟨4429438398093597946328387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952958932062398630885591 4429438398093597946328387)
                  ·
                    refine ⟨6644157597140396919492581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4429438398093597946328387 6644157597140396919492581)
                    ·
                      refine ⟨1245779549463824422404859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6644157597140396919492581 1245779549463824422404859)
                      ·
                        rfl

theorem cell23_2426147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_2426147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426147 prefixEnd_2426147 := by exact prefixLift 2426147
  have htrace : WordTrace (prefixWord ++ tailWord_2426147) baseStart_2426147 baseEnd_2426147 := by
    simpa [prefixWord, tailWord_2426147, baseEnd_2426147] using wordTrace_append hprefix tailTrace_2426147
  have hstable : (prefixWord ++ tailWord_2426147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426147).length < 2 ^ (prefixWord ++ tailWord_2426147).sum := by decide
  have hdescent : baseEnd_2426147 < baseStart_2426147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426160 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_2426160 : Nat := 118140960795 + 2426160 * 2 ^ 59
def prefixEnd_2426160 : Nat := 4983230072969 + 3 ^ 40 * 2426160 * 2
def baseEnd_2426160 : Nat := 1245786224712332871542299

theorem tailTrace_2426160 : CollatzResearch.WordTrace tailWord_2426160 prefixEnd_2426160 1245786224712332871542299 := by
  unfold tailWord_2426160
  simp only [CollatzResearch.WordTrace]
  refine ⟨44244662445222074992305967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58992883260296099989741289 44244662445222074992305967)
  ·
    refine ⟨66366993667833112488458951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44244662445222074992305967 66366993667833112488458951)
    ·
      refine ⟨99550490501749668732688427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66366993667833112488458951 99550490501749668732688427)
      ·
        refine ⟨149325735752624503099032641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99550490501749668732688427 149325735752624503099032641)
        ·
          refine ⟨111994301814468377324274481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149325735752624503099032641 111994301814468377324274481)
          ·
            refine ⟨83995726360851282993205861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111994301814468377324274481 83995726360851282993205861)
            ·
              refine ⟨15749198692659615561226099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83995726360851282993205861 15749198692659615561226099)
              ·
                refine ⟨23623798038989423341839149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15749198692659615561226099 23623798038989423341839149)
                ·
                  refine ⟨8858924264621033753189681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23623798038989423341839149 8858924264621033753189681)
                  ·
                    refine ⟨6644193198465775314892261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8858924264621033753189681 6644193198465775314892261)
                    ·
                      refine ⟨1245786224712332871542299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6644193198465775314892261 1245786224712332871542299)
                      ·
                        rfl

theorem cell23_2426160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_2426160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426160 prefixEnd_2426160 := by exact prefixLift 2426160
  have htrace : WordTrace (prefixWord ++ tailWord_2426160) baseStart_2426160 baseEnd_2426160 := by
    simpa [prefixWord, tailWord_2426160, baseEnd_2426160] using wordTrace_append hprefix tailTrace_2426160
  have hstable : (prefixWord ++ tailWord_2426160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426160).length < 2 ^ (prefixWord ++ tailWord_2426160).sum := by decide
  have hdescent : baseEnd_2426160 < baseStart_2426160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426164 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2426164 : Nat := 118140960795 + 2426164 * 2 ^ 59
def prefixEnd_2426164 : Nat := 4983230072969 + 3 ^ 40 * 2426164 * 2
def baseEnd_2426164 : Nat := 1245788278634950855892281

theorem tailTrace_2426164 : CollatzResearch.WordTrace tailWord_2426164 prefixEnd_2426164 1245788278634950855892281 := by
  unfold tailWord_2426164
  simp only [CollatzResearch.WordTrace]
  refine ⟨44244735391214829333878773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58992980521619772445171697 44244735391214829333878773)
  ·
    refine ⟨4147943942926390250051135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44244735391214829333878773 4147943942926390250051135)
    ·
      refine ⟨6221915914389585375076703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4147943942926390250051135 6221915914389585375076703)
      ·
        refine ⟨9332873871584378062615055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6221915914389585375076703 9332873871584378062615055)
        ·
          refine ⟨13999310807376567093922583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9332873871584378062615055 13999310807376567093922583)
          ·
            refine ⟨20998966211064850640883875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13999310807376567093922583 20998966211064850640883875)
            ·
              refine ⟨31498449316597275961325813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20998966211064850640883875 31498449316597275961325813)
              ·
                refine ⟨2952979623430994621374295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31498449316597275961325813 2952979623430994621374295)
                ·
                  refine ⟨4429469435146491932061443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952979623430994621374295 4429469435146491932061443)
                  ·
                    refine ⟨6644204152719737898092165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4429469435146491932061443 6644204152719737898092165)
                    ·
                      refine ⟨1245788278634950855892281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6644204152719737898092165 1245788278634950855892281)
                      ·
                        rfl

theorem cell23_2426164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2426164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426164 prefixEnd_2426164 := by exact prefixLift 2426164
  have htrace : WordTrace (prefixWord ++ tailWord_2426164) baseStart_2426164 baseEnd_2426164 := by
    simpa [prefixWord, tailWord_2426164, baseEnd_2426164] using wordTrace_append hprefix tailTrace_2426164
  have hstable : (prefixWord ++ tailWord_2426164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426164).length < 2 ^ (prefixWord ++ tailWord_2426164).sum := by decide
  have hdescent : baseEnd_2426164 < baseStart_2426164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426174 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_2426174 : Nat := 118140960795 + 2426174 * 2 ^ 59
def prefixEnd_2426174 : Nat := 4983230072969 + 3 ^ 40 * 2426174 * 2
def baseEnd_2426174 : Nat := 415264471147165272255745

theorem tailTrace_2426174 : CollatzResearch.WordTrace tailWord_2426174 prefixEnd_2426174 415264471147165272255745 := by
  unfold tailWord_2426174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11061229439049178796952697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58993223674928953583747717 11061229439049178796952697)
  ·
    refine ⟨8295922079286884097714523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11061229439049178796952697 8295922079286884097714523)
    ·
      refine ⟨12443883118930326146571785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8295922079286884097714523 12443883118930326146571785)
      ·
        refine ⟨9332912339197744609928839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12443883118930326146571785 9332912339197744609928839)
        ·
          refine ⟨13999368508796616914893259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9332912339197744609928839 13999368508796616914893259)
          ·
            refine ⟨20999052763194925372339889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13999368508796616914893259 20999052763194925372339889)
            ·
              refine ⟨15749289572396194029254917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20999052763194925372339889 15749289572396194029254917)
              ·
                refine ⟨2952991794824286380485297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15749289572396194029254917 2952991794824286380485297)
                ·
                  refine ⟨2214743846118214785363973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2952991794824286380485297 2214743846118214785363973)
                  ·
                    refine ⟨415264471147165272255745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2214743846118214785363973 415264471147165272255745)
                    ·
                      rfl

theorem cell23_2426174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_2426174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426174 prefixEnd_2426174 := by exact prefixLift 2426174
  have htrace : WordTrace (prefixWord ++ tailWord_2426174) baseStart_2426174 baseEnd_2426174 := by
    simpa [prefixWord, tailWord_2426174, baseEnd_2426174] using wordTrace_append hprefix tailTrace_2426174
  have hstable : (prefixWord ++ tailWord_2426174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426174).length < 2 ^ (prefixWord ++ tailWord_2426174).sum := by decide
  have hdescent : baseEnd_2426174 < baseStart_2426174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426177 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2426177 : Nat := 118140960795 + 2426177 * 2 ^ 59
def prefixEnd_2426177 : Nat := 4983230072969 + 3 ^ 40 * 2426177 * 2
def baseEnd_2426177 : Nat := 1245794953883459305029721

theorem tailTrace_2426177 : CollatzResearch.WordTrace tailWord_2426177 prefixEnd_2426177 1245794953883459305029721 := by
  unfold tailWord_2426177
  simp only [CollatzResearch.WordTrace]
  refine ⟨88489944931382561887980785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58993296620921707925320523 88489944931382561887980785)
  ·
    refine ⟨66367458698536921415985589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88489944931382561887980785 66367458698536921415985589)
    ·
      refine ⟨6221949252987836382748649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66367458698536921415985589 6221949252987836382748649)
      ·
        refine ⟨4666461939740877287061487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6221949252987836382748649 4666461939740877287061487)
        ·
          refine ⟨6999692909611315930592231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4666461939740877287061487 6999692909611315930592231)
          ·
            refine ⟨10499539364416973895888347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6999692909611315930592231 10499539364416973895888347)
            ·
              refine ⟨15749309046625460843832521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10499539364416973895888347 15749309046625460843832521)
              ·
                refine ⟨11811981784969095632874391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15749309046625460843832521 11811981784969095632874391)
                ·
                  refine ⟨17717972677453643449311587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11811981784969095632874391 17717972677453643449311587)
                  ·
                    refine ⟨26576959016180465173967381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17717972677453643449311587 26576959016180465173967381)
                    ·
                      refine ⟨1245794953883459305029721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26576959016180465173967381 1245794953883459305029721)
                      ·
                        rfl

theorem cell23_2426177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2426177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426177 prefixEnd_2426177 := by exact prefixLift 2426177
  have htrace : WordTrace (prefixWord ++ tailWord_2426177) baseStart_2426177 baseEnd_2426177 := by
    simpa [prefixWord, tailWord_2426177, baseEnd_2426177] using wordTrace_append hprefix tailTrace_2426177
  have hstable : (prefixWord ++ tailWord_2426177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426177).length < 2 ^ (prefixWord ++ tailWord_2426177).sum := by decide
  have hdescent : baseEnd_2426177 < baseStart_2426177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426181 : List Nat := [1, 3, 1, 1, 1, 2, 1, 8, 1, 2, 2]
def baseStart_2426181 : Nat := 118140960795 + 2426181 * 2 ^ 59
def prefixEnd_2426181 : Nat := 4983230072969 + 3 ^ 40 * 2426181 * 2
def baseEnd_2426181 : Nat := 1245797007806077289379703

theorem tailTrace_2426181 : CollatzResearch.WordTrace tailWord_2426181 prefixEnd_2426181 1245797007806077289379703 := by
  unfold tailWord_2426181
  simp only [CollatzResearch.WordTrace]
  refine ⟨88490090823368070571126397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58993393882245380380750931 88490090823368070571126397)
  ·
    refine ⟨33183784058763026464172399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88490090823368070571126397 33183784058763026464172399)
    ·
      refine ⟨49775676088144539696258599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33183784058763026464172399 49775676088144539696258599)
      ·
        refine ⟨74663514132216809544387899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49775676088144539696258599 74663514132216809544387899)
        ·
          refine ⟨111995271198325214316581849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74663514132216809544387899 111995271198325214316581849)
          ·
            refine ⟨83996453398743910737436387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111995271198325214316581849 83996453398743910737436387)
            ·
              refine ⟨125994680098115866106154581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83996453398743910737436387 125994680098115866106154581)
              ·
                refine ⟨1476500157399795305931499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 125994680098115866106154581 1476500157399795305931499)
                ·
                  refine ⟨2214750236099692958897249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476500157399795305931499 2214750236099692958897249)
                  ·
                    refine ⟨1661062677074769719172937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2214750236099692958897249 1661062677074769719172937)
                    ·
                      refine ⟨1245797007806077289379703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661062677074769719172937 1245797007806077289379703)
                      ·
                        rfl

theorem cell23_2426181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 2, 2].length) (baseStart_2426181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426181 prefixEnd_2426181 := by exact prefixLift 2426181
  have htrace : WordTrace (prefixWord ++ tailWord_2426181) baseStart_2426181 baseEnd_2426181 := by
    simpa [prefixWord, tailWord_2426181, baseEnd_2426181] using wordTrace_append hprefix tailTrace_2426181
  have hstable : (prefixWord ++ tailWord_2426181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426181).length < 2 ^ (prefixWord ++ tailWord_2426181).sum := by decide
  have hdescent : baseEnd_2426181 < baseStart_2426181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426190 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2426190 : Nat := 118140960795 + 2426190 * 2 ^ 59
def prefixEnd_2426190 : Nat := 4983230072969 + 3 ^ 40 * 2426190 * 2
def baseEnd_2426190 : Nat := 1245801629131967754167161

theorem tailTrace_2426190 : CollatzResearch.WordTrace tailWord_2426190 prefixEnd_2426190 1245801629131967754167161 := by
  unfold tailWord_2426190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11061302385041933138525503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58993612720223643405469349 11061302385041933138525503)
  ·
    refine ⟨16591953577562899707788255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11061302385041933138525503 16591953577562899707788255)
    ·
      refine ⟨24887930366344349561682383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16591953577562899707788255 24887930366344349561682383)
      ·
        refine ⟨37331895549516524342523575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24887930366344349561682383 37331895549516524342523575)
        ·
          refine ⟨55997843324274786513785363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37331895549516524342523575 55997843324274786513785363)
          ·
            refine ⟨83996764986412179770678045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55997843324274786513785363 83996764986412179770678045)
            ·
              refine ⟨31498786869904567414004267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83996764986412179770678045 31498786869904567414004267)
              ·
                refine ⟨47248180304856851121006401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31498786869904567414004267 47248180304856851121006401)
                ·
                  refine ⟨35436135228642638340754801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47248180304856851121006401 35436135228642638340754801)
                  ·
                    refine ⟨26577101421481978755566101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35436135228642638340754801 26577101421481978755566101)
                    ·
                      refine ⟨1245801629131967754167161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26577101421481978755566101 1245801629131967754167161)
                      ·
                        rfl

theorem cell23_2426190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2426190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426190 prefixEnd_2426190 := by exact prefixLift 2426190
  have htrace : WordTrace (prefixWord ++ tailWord_2426190) baseStart_2426190 baseEnd_2426190 := by
    simpa [prefixWord, tailWord_2426190, baseEnd_2426190] using wordTrace_append hprefix tailTrace_2426190
  have hstable : (prefixWord ++ tailWord_2426190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426190).length < 2 ^ (prefixWord ++ tailWord_2426190).sum := by decide
  have hdescent : baseEnd_2426190 < baseStart_2426190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426218 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_2426218 : Nat := 118140960795 + 2426218 * 2 ^ 59
def prefixEnd_2426218 : Nat := 4983230072969 + 3 ^ 40 * 2426218 * 2
def baseEnd_2426218 : Nat := 1245816006590293644617033

theorem tailTrace_2426218 : CollatzResearch.WordTrace tailWord_2426218 prefixEnd_2426218 1245816006590293644617033 := by
  unfold tailWord_2426218
  simp only [CollatzResearch.WordTrace]
  refine ⟨22122860081058506472555827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58994293549489350593482205 22122860081058506472555827)
  ·
    refine ⟨33184290121587759708833741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22122860081058506472555827 33184290121587759708833741)
    ·
      refine ⟨12444108795595409890812653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33184290121587759708833741 12444108795595409890812653)
      ·
        refine ⟨4666540798348278709054745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12444108795595409890812653 4666540798348278709054745)
        ·
          refine ⟨3499905598761209031791059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4666540798348278709054745 3499905598761209031791059)
          ·
            refine ⟨5249858398141813547686589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499905598761209031791059 5249858398141813547686589)
            ·
              refine ⟨1968696899303180080382471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5249858398141813547686589 1968696899303180080382471)
              ·
                refine ⟨2953045348954770120573707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968696899303180080382471 2953045348954770120573707)
                ·
                  refine ⟨4429568023432155180860561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953045348954770120573707 4429568023432155180860561)
                  ·
                    refine ⟨3322176017574116385645421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4429568023432155180860561 3322176017574116385645421)
                    ·
                      refine ⟨1245816006590293644617033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3322176017574116385645421 1245816006590293644617033)
                      ·
                        rfl

theorem cell23_2426218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_2426218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426218 prefixEnd_2426218 := by exact prefixLift 2426218
  have htrace : WordTrace (prefixWord ++ tailWord_2426218) baseStart_2426218 baseEnd_2426218 := by
    simpa [prefixWord, tailWord_2426218, baseEnd_2426218] using wordTrace_append hprefix tailTrace_2426218
  have hstable : (prefixWord ++ tailWord_2426218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426218).length < 2 ^ (prefixWord ++ tailWord_2426218).sum := by decide
  have hdescent : baseEnd_2426218 < baseStart_2426218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426238 : List Nat := [4, 2, 3, 2, 2, 1, 1, 8]
def baseStart_2426238 : Nat := 118140960795 + 2426238 * 2 ^ 59
def prefixEnd_2426238 : Nat := 4983230072969 + 3 ^ 40 * 2426238 * 2
def baseEnd_2426238 : Nat := 46141713933458650606183

theorem tailTrace_2426238 : CollatzResearch.WordTrace tailWord_2426238 prefixEnd_2426238 46141713933458650606183 := by
  unfold tailWord_2426238
  simp only [CollatzResearch.WordTrace]
  refine ⟨11061521223020196163243921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58994779856107712870634245 11061521223020196163243921)
  ·
    refine ⟨8296140917265147122432941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11061521223020196163243921 8296140917265147122432941)
    ·
      refine ⟨3111052843974430170912353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8296140917265147122432941 3111052843974430170912353)
      ·
        refine ⟨2333289632980822628184265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3111052843974430170912353 2333289632980822628184265)
        ·
          refine ⟨1749967224735616971138199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2333289632980822628184265 1749967224735616971138199)
          ·
            refine ⟨2624950837103425456707299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749967224735616971138199 2624950837103425456707299)
            ·
              refine ⟨3937426255655138185060949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2624950837103425456707299 3937426255655138185060949)
              ·
                refine ⟨46141713933458650606183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3937426255655138185060949 46141713933458650606183)
                ·
                  rfl

theorem cell23_2426238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_2426238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426238 prefixEnd_2426238 := by exact prefixLift 2426238
  have htrace : WordTrace (prefixWord ++ tailWord_2426238) baseStart_2426238 baseEnd_2426238 := by
    simpa [prefixWord, tailWord_2426238, baseEnd_2426238] using wordTrace_append hprefix tailTrace_2426238
  have hstable : (prefixWord ++ tailWord_2426238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426238).length < 2 ^ (prefixWord ++ tailWord_2426238).sum := by decide
  have hdescent : baseEnd_2426238 < baseStart_2426238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426240 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_2426240 : Nat := 118140960795 + 2426240 * 2 ^ 59
def prefixEnd_2426240 : Nat := 4983230072969 + 3 ^ 40 * 2426240 * 2
def baseEnd_2426240 : Nat := 1245827303164692558541931

theorem tailTrace_2426240 : CollatzResearch.WordTrace tailWord_2426240 prefixEnd_2426240 1245827303164692558541931 := by
  unfold tailWord_2426240
  simp only [CollatzResearch.WordTrace]
  refine ⟨44246121365077161823762087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58994828486769549098349449 44246121365077161823762087)
  ·
    refine ⟨66369182047615742735643131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44246121365077161823762087 66369182047615742735643131)
    ·
      refine ⟨99553773071423614103464697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66369182047615742735643131 99553773071423614103464697)
      ·
        refine ⟨74665329803567710577598523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99553773071423614103464697 74665329803567710577598523)
        ·
          refine ⟨111997994705351565866397785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74665329803567710577598523 111997994705351565866397785)
          ·
            refine ⟨83998496029013674399798339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111997994705351565866397785 83998496029013674399798339)
            ·
              refine ⟨125997744043520511599697509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83998496029013674399798339 125997744043520511599697509)
              ·
                refine ⟨23624577008160095924943283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125997744043520511599697509 23624577008160095924943283)
                ·
                  refine ⟨35436865512240143887414925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23624577008160095924943283 35436865512240143887414925)
                  ·
                    refine ⟨13288824567090053957780597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35436865512240143887414925 13288824567090053957780597)
                    ·
                      refine ⟨1245827303164692558541931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13288824567090053957780597 1245827303164692558541931)
                      ·
                        rfl

theorem cell23_2426240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_2426240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426240 prefixEnd_2426240 := by exact prefixLift 2426240
  have htrace : WordTrace (prefixWord ++ tailWord_2426240) baseStart_2426240 baseEnd_2426240 := by
    simpa [prefixWord, tailWord_2426240, baseEnd_2426240] using wordTrace_append hprefix tailTrace_2426240
  have hstable : (prefixWord ++ tailWord_2426240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426240).length < 2 ^ (prefixWord ++ tailWord_2426240).sum := by decide
  have hdescent : baseEnd_2426240 < baseStart_2426240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426247 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 2, 6]
def baseStart_2426247 : Nat := 118140960795 + 2426247 * 2 ^ 59
def prefixEnd_2426247 : Nat := 4983230072969 + 3 ^ 40 * 2426247 * 2
def baseEnd_2426247 : Nat := 415276965843091343718133

theorem tailTrace_2426247 : CollatzResearch.WordTrace tailWord_2426247 prefixEnd_2426247 415276965843091343718133 := by
  unfold tailWord_2426247
  simp only [CollatzResearch.WordTrace]
  refine ⟨88492498041128963843028995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58994998694085975895352663 88492498041128963843028995)
  ·
    refine ⟨132738747061693445764543493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88492498041128963843028995 132738747061693445764543493)
    ·
      refine ⟨24888515074067521080851905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132738747061693445764543493 24888515074067521080851905)
      ·
        refine ⟨18666386305550640810638929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24888515074067521080851905 18666386305550640810638929)
        ·
          refine ⟨13999789729162980607979197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18666386305550640810638929 13999789729162980607979197)
          ·
            refine ⟨5249921148436117727992199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13999789729162980607979197 5249921148436117727992199)
            ·
              refine ⟨7874881722654176591988299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5249921148436117727992199 7874881722654176591988299)
              ·
                refine ⟨11812322583981264887982449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7874881722654176591988299 11812322583981264887982449)
                ·
                  refine ⟨8859241937985948665986837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11812322583981264887982449 8859241937985948665986837)
                  ·
                    refine ⟨415276965843091343718133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8859241937985948665986837 415276965843091343718133)
                    ·
                      rfl

theorem cell23_2426247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_2426247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426247 prefixEnd_2426247 := by exact prefixLift 2426247
  have htrace : WordTrace (prefixWord ++ tailWord_2426247) baseStart_2426247 baseEnd_2426247 := by
    simpa [prefixWord, tailWord_2426247, baseEnd_2426247] using wordTrace_append hprefix tailTrace_2426247
  have hstable : (prefixWord ++ tailWord_2426247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426247).length < 2 ^ (prefixWord ++ tailWord_2426247).sum := by decide
  have hdescent : baseEnd_2426247 < baseStart_2426247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426327 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_2426327 : Nat := 118140960795 + 2426327 * 2 ^ 59
def prefixEnd_2426327 : Nat := 4983230072969 + 3 ^ 40 * 2426327 * 2
def baseEnd_2426327 : Nat := 1245871975981633718154031

theorem tailTrace_2426327 : CollatzResearch.WordTrace tailWord_2426327 prefixEnd_2426327 1245871975981633718154031 := by
  unfold tailWord_2426327
  simp only [CollatzResearch.WordTrace]
  refine ⟨88495415880839137505941235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58996943920559425003960823 88495415880839137505941235)
  ·
    refine ⟨132743123821258706258911853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88495415880839137505941235 132743123821258706258911853)
    ·
      refine ⟨49778671432972014847091945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132743123821258706258911853 49778671432972014847091945)
      ·
        refine ⟨37334003574729011135318959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49778671432972014847091945 37334003574729011135318959)
        ·
          refine ⟨56001005362093516702978439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37334003574729011135318959 56001005362093516702978439)
          ·
            refine ⟨84001508043140275054467659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56001005362093516702978439 84001508043140275054467659)
            ·
              refine ⟨126002262064710412581701489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84001508043140275054467659 126002262064710412581701489)
              ·
                refine ⟨94501696548532809436276117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126002262064710412581701489 94501696548532809436276117)
                ·
                  refine ⟨4429767025712475442325443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94501696548532809436276117 4429767025712475442325443)
                  ·
                    refine ⟨6644650538568713163488165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4429767025712475442325443 6644650538568713163488165)
                    ·
                      refine ⟨1245871975981633718154031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6644650538568713163488165 1245871975981633718154031)
                      ·
                        rfl

theorem cell23_2426327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_2426327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426327 prefixEnd_2426327 := by exact prefixLift 2426327
  have htrace : WordTrace (prefixWord ++ tailWord_2426327) baseStart_2426327 baseEnd_2426327 := by
    simpa [prefixWord, tailWord_2426327, baseEnd_2426327] using wordTrace_append hprefix tailTrace_2426327
  have hstable : (prefixWord ++ tailWord_2426327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426327).length < 2 ^ (prefixWord ++ tailWord_2426327).sum := by decide
  have hdescent : baseEnd_2426327 < baseStart_2426327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426344 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2426344 : Nat := 118140960795 + 2426344 * 2 ^ 59
def prefixEnd_2426344 : Nat := 4983230072969 + 3 ^ 40 * 2426344 * 2
def baseEnd_2426344 : Nat := 1245880705152760151641453

theorem tailTrace_2426344 : CollatzResearch.WordTrace tailWord_2426344 prefixEnd_2426344 1245880705152760151641453 := by
  unfold tailWord_2426344
  simp only [CollatzResearch.WordTrace]
  refine ⟨44248017960888774704655043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58997357281185032939540057 44248017960888774704655043)
  ·
    refine ⟨66372026941333162056982565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44248017960888774704655043 66372026941333162056982565)
    ·
      refine ⟨12444755051499967885684231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66372026941333162056982565 12444755051499967885684231)
      ·
        refine ⟨18667132577249951828526347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12444755051499967885684231 18667132577249951828526347)
        ·
          refine ⟨28000698865874927742789521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18667132577249951828526347 28000698865874927742789521)
          ·
            refine ⟨21000524149406195807092141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28000698865874927742789521 21000524149406195807092141)
            ·
              refine ⟨7875196556027323427659553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21000524149406195807092141 7875196556027323427659553)
              ·
                refine ⟨5906397417020492570744665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7875196556027323427659553 5906397417020492570744665)
                ·
                  refine ⟨4429798062765369428058499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5906397417020492570744665 4429798062765369428058499)
                  ·
                    refine ⟨6644697094148054142087749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4429798062765369428058499 6644697094148054142087749)
                    ·
                      refine ⟨1245880705152760151641453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6644697094148054142087749 1245880705152760151641453)
                      ·
                        rfl

theorem cell23_2426344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2426344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426344 prefixEnd_2426344 := by exact prefixLift 2426344
  have htrace : WordTrace (prefixWord ++ tailWord_2426344) baseStart_2426344 baseEnd_2426344 := by
    simpa [prefixWord, tailWord_2426344, baseEnd_2426344] using wordTrace_append hprefix tailTrace_2426344
  have hstable : (prefixWord ++ tailWord_2426344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426344).length < 2 ^ (prefixWord ++ tailWord_2426344).sum := by decide
  have hdescent : baseEnd_2426344 < baseStart_2426344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426347 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 3]
def baseStart_2426347 : Nat := 118140960795 + 2426347 * 2 ^ 59
def prefixEnd_2426347 : Nat := 4983230072969 + 3 ^ 40 * 2426347 * 2
def baseEnd_2426347 : Nat := 1245882245594723639903939

theorem tailTrace_2426347 : CollatzResearch.WordTrace tailWord_2426347 prefixEnd_2426347 1245882245594723639903939 := by
  unfold tailWord_2426347
  simp only [CollatzResearch.WordTrace]
  refine ⟨88496145340766680921669295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58997430227177787281112863 88496145340766680921669295)
  ·
    refine ⟨132744218011150021382503943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88496145340766680921669295 132744218011150021382503943)
    ·
      refine ⟨199116327016725032073755915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132744218011150021382503943 199116327016725032073755915)
      ·
        refine ⟨298674490525087548110633873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199116327016725032073755915 298674490525087548110633873)
        ·
          refine ⟨224005867893815661082975405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298674490525087548110633873 224005867893815661082975405)
          ·
            refine ⟨84002200460180872906115777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224005867893815661082975405 84002200460180872906115777)
            ·
              refine ⟨63001650345135654679586833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84002200460180872906115777 63001650345135654679586833)
              ·
                refine ⟨47251237758851741009690125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63001650345135654679586833 47251237758851741009690125)
                ·
                  refine ⟨17719214159569402878633797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47251237758851741009690125 17719214159569402878633797)
                  ·
                    refine ⟨3322352654919263039743837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17719214159569402878633797 3322352654919263039743837)
                    ·
                      refine ⟨1245882245594723639903939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3322352654919263039743837 1245882245594723639903939)
                      ·
                        rfl

theorem cell23_2426347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 3].length) (baseStart_2426347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426347 prefixEnd_2426347 := by exact prefixLift 2426347
  have htrace : WordTrace (prefixWord ++ tailWord_2426347) baseStart_2426347 baseEnd_2426347 := by
    simpa [prefixWord, tailWord_2426347, baseEnd_2426347] using wordTrace_append hprefix tailTrace_2426347
  have hstable : (prefixWord ++ tailWord_2426347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426347).length < 2 ^ (prefixWord ++ tailWord_2426347).sum := by decide
  have hdescent : baseEnd_2426347 < baseStart_2426347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426428 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_2426428 : Nat := 118140960795 + 2426428 * 2 ^ 59
def prefixEnd_2426428 : Nat := 4983230072969 + 3 ^ 40 * 2426428 * 2
def baseEnd_2426428 : Nat := 1245923837527737822991067

theorem tailTrace_2426428 : CollatzResearch.WordTrace tailWord_2426428 prefixEnd_2426428 1245923837527737822991067 := by
  unfold tailWord_2426428
  simp only [CollatzResearch.WordTrace]
  refine ⟨44249549826736615877683969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58999399768982154503578625 44249549826736615877683969)
  ·
    refine ⟨33187162370052461908262977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44249549826736615877683969 33187162370052461908262977)
    ·
      refine ⟨24890371777539346431197233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33187162370052461908262977 24890371777539346431197233)
      ·
        refine ⟨18667778833154509823397925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24890371777539346431197233 18667778833154509823397925)
        ·
          refine ⟨3500208531216470591887111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18667778833154509823397925 3500208531216470591887111)
          ·
            refine ⟨5250312796824705887830667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500208531216470591887111 5250312796824705887830667)
            ·
              refine ⟨7875469195237058831746001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5250312796824705887830667 7875469195237058831746001)
              ·
                refine ⟨5906601896427794123809501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7875469195237058831746001 5906601896427794123809501)
                ·
                  refine ⟨2214975711160422796428563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5906601896427794123809501 2214975711160422796428563)
                  ·
                    refine ⟨3322463566740634194642845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2214975711160422796428563 3322463566740634194642845)
                    ·
                      refine ⟨1245923837527737822991067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3322463566740634194642845 1245923837527737822991067)
                      ·
                        rfl

theorem cell23_2426428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_2426428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426428 prefixEnd_2426428 := by exact prefixLift 2426428
  have htrace : WordTrace (prefixWord ++ tailWord_2426428) baseStart_2426428 baseEnd_2426428 := by
    simpa [prefixWord, tailWord_2426428, baseEnd_2426428] using wordTrace_append hprefix tailTrace_2426428
  have hstable : (prefixWord ++ tailWord_2426428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426428).length < 2 ^ (prefixWord ++ tailWord_2426428).sum := by decide
  have hdescent : baseEnd_2426428 < baseStart_2426428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426444 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_2426444 : Nat := 118140960795 + 2426444 * 2 ^ 59
def prefixEnd_2426444 : Nat := 4983230072969 + 3 ^ 40 * 2426444 * 2
def baseEnd_2426444 : Nat := 415310684406069920130331

theorem tailTrace_2426444 : CollatzResearch.WordTrace tailWord_2426444 prefixEnd_2426444 415310684406069920130331 := by
  unfold tailWord_2426444
  simp only [CollatzResearch.WordTrace]
  refine ⟨44249841610707633243975193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58999788814276844325300257 44249841610707633243975193)
  ·
    refine ⟨33187381208030724932981395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44249841610707633243975193 33187381208030724932981395)
    ·
      refine ⟨49781071812046087399472093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33187381208030724932981395 49781071812046087399472093)
      ·
        refine ⟨18667901929517282774802035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49781071812046087399472093 18667901929517282774802035)
        ·
          refine ⟨28001852894275924162203053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18667901929517282774802035 28001852894275924162203053)
          ·
            refine ⟨10500694835353471560826145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28001852894275924162203053 10500694835353471560826145)
            ·
              refine ⟨7875521126515103670619609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10500694835353471560826145 7875521126515103670619609)
              ·
                refine ⟨5906640844886327752964707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7875521126515103670619609 5906640844886327752964707)
                ·
                  refine ⟨8859961267329491629447061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5906640844886327752964707 8859961267329491629447061)
                  ·
                    refine ⟨415310684406069920130331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8859961267329491629447061 415310684406069920130331)
                    ·
                      rfl

theorem cell23_2426444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_2426444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426444 prefixEnd_2426444 := by exact prefixLift 2426444
  have htrace : WordTrace (prefixWord ++ tailWord_2426444) baseStart_2426444 baseEnd_2426444 := by
    simpa [prefixWord, tailWord_2426444, baseEnd_2426444] using wordTrace_append hprefix tailTrace_2426444
  have hstable : (prefixWord ++ tailWord_2426444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426444).length < 2 ^ (prefixWord ++ tailWord_2426444).sum := by decide
  have hdescent : baseEnd_2426444 < baseStart_2426444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426447 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_2426447 : Nat := 118140960795 + 2426447 * 2 ^ 59
def prefixEnd_2426447 : Nat := 4983230072969 + 3 ^ 40 * 2426447 * 2
def baseEnd_2426447 : Nat := 1245933593660173248653479

theorem tailTrace_2426447 : CollatzResearch.WordTrace tailWord_2426447 prefixEnd_2426447 1245933593660173248653479 := by
  unfold tailWord_2426447
  simp only [CollatzResearch.WordTrace]
  refine ⟨88499792640404398000309595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58999861760269598666873063 88499792640404398000309595)
  ·
    refine ⟨132749688960606597000464393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88499792640404398000309595 132749688960606597000464393)
    ·
      refine ⟨99562266720454947750348295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132749688960606597000464393 99562266720454947750348295)
      ·
        refine ⟨149343400080682421625522443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99562266720454947750348295 149343400080682421625522443)
        ·
          refine ⟨224015100121023632438283665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149343400080682421625522443 224015100121023632438283665)
          ·
            refine ⟨168011325090767724328712749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224015100121023632438283665 168011325090767724328712749)
            ·
              refine ⟨63004246909037896623267281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168011325090767724328712749 63004246909037896623267281)
              ·
                refine ⟨47253185181778422467450461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63004246909037896623267281 47253185181778422467450461)
                ·
                  refine ⟨17719944443166908425293923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47253185181778422467450461 17719944443166908425293923)
                  ·
                    refine ⟨26579916664750362637940885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17719944443166908425293923 26579916664750362637940885)
                    ·
                      refine ⟨1245933593660173248653479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26579916664750362637940885 1245933593660173248653479)
                      ·
                        rfl

theorem cell23_2426447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_2426447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426447 prefixEnd_2426447 := by exact prefixLift 2426447
  have htrace : WordTrace (prefixWord ++ tailWord_2426447) baseStart_2426447 baseEnd_2426447 := by
    simpa [prefixWord, tailWord_2426447, baseEnd_2426447] using wordTrace_append hprefix tailTrace_2426447
  have hstable : (prefixWord ++ tailWord_2426447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426447).length < 2 ^ (prefixWord ++ tailWord_2426447).sum := by decide
  have hdescent : baseEnd_2426447 < baseStart_2426447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426468 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_2426468 : Nat := 118140960795 + 2426468 * 2 ^ 59
def prefixEnd_2426468 : Nat := 4983230072969 + 3 ^ 40 * 2426468 * 2
def baseEnd_2426468 : Nat := 1245944376753917666490883

theorem tailTrace_2426468 : CollatzResearch.WordTrace tailWord_2426468 prefixEnd_2426468 1245944376753917666490883 := by
  unfold tailWord_2426468
  simp only [CollatzResearch.WordTrace]
  refine ⟨44250279286664159293412029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59000372382218879057882705 44250279286664159293412029)
  ·
    refine ⟨16593854732499059735029511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44250279286664159293412029 16593854732499059735029511)
    ·
      refine ⟨24890782098748589602544267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16593854732499059735029511 24890782098748589602544267)
      ·
        refine ⟨37336173148122884403816401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24890782098748589602544267 37336173148122884403816401)
        ·
          refine ⟨28002129861092163302862301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37336173148122884403816401 28002129861092163302862301)
          ·
            refine ⟨10500798697909561238573363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28002129861092163302862301 10500798697909561238573363)
            ·
              refine ⟨15751198046864341857860045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10500798697909561238573363 15751198046864341857860045)
              ·
                refine ⟨5906699267574128196697517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15751198046864341857860045 5906699267574128196697517)
                ·
                  refine ⟨2215012225340298073761569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5906699267574128196697517 2215012225340298073761569)
                  ·
                    refine ⟨1661259169005223555321177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2215012225340298073761569 1661259169005223555321177)
                    ·
                      refine ⟨1245944376753917666490883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661259169005223555321177 1245944376753917666490883)
                      ·
                        rfl

theorem cell23_2426468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_2426468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426468 prefixEnd_2426468 := by exact prefixLift 2426468
  have htrace : WordTrace (prefixWord ++ tailWord_2426468) baseStart_2426468 baseEnd_2426468 := by
    simpa [prefixWord, tailWord_2426468, baseEnd_2426468] using wordTrace_append hprefix tailTrace_2426468
  have hstable : (prefixWord ++ tailWord_2426468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426468).length < 2 ^ (prefixWord ++ tailWord_2426468).sum := by decide
  have hdescent : baseEnd_2426468 < baseStart_2426468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426478 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2426478 : Nat := 118140960795 + 2426478 * 2 ^ 59
def prefixEnd_2426478 : Nat := 4983230072969 + 3 ^ 40 * 2426478 * 2
def baseEnd_2426478 : Nat := 415316503853487542455279

theorem tailTrace_2426478 : CollatzResearch.WordTrace tailWord_2426478 prefixEnd_2426478 415316503853487542455279 := by
  unfold tailWord_2426478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11062615412911511286836011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59000615535528060196458725 11062615412911511286836011)
  ·
    refine ⟨16593923119367266930254017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11062615412911511286836011 16593923119367266930254017)
    ·
      refine ⟨12445442339525450197690513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16593923119367266930254017 12445442339525450197690513)
      ·
        refine ⟨9334081754644087648267885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12445442339525450197690513 9334081754644087648267885)
        ·
          refine ⟨3500280657991532868100457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9334081754644087648267885 3500280657991532868100457)
          ·
            refine ⟨2625210493493649651075343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3500280657991532868100457 2625210493493649651075343)
            ·
              refine ⟨3937815740240474476613015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2625210493493649651075343 3937815740240474476613015)
              ·
                refine ⟨5906723610360711714919523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3937815740240474476613015 5906723610360711714919523)
                ·
                  refine ⟨8860085415541067572379285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5906723610360711714919523 8860085415541067572379285)
                  ·
                    refine ⟨415316503853487542455279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8860085415541067572379285 415316503853487542455279)
                    ·
                      rfl

theorem cell23_2426478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2426478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426478 prefixEnd_2426478 := by exact prefixLift 2426478
  have htrace : WordTrace (prefixWord ++ tailWord_2426478) baseStart_2426478 baseEnd_2426478 := by
    simpa [prefixWord, tailWord_2426478, baseEnd_2426478] using wordTrace_append hprefix tailTrace_2426478
  have hstable : (prefixWord ++ tailWord_2426478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426478).length < 2 ^ (prefixWord ++ tailWord_2426478).sum := by decide
  have hdescent : baseEnd_2426478 < baseStart_2426478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426485 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2426485 : Nat := 118140960795 + 2426485 * 2 ^ 59
def prefixEnd_2426485 : Nat := 4983230072969 + 3 ^ 40 * 2426485 * 2
def baseEnd_2426485 : Nat := 1245953105925044099978305

theorem tailTrace_2426485 : CollatzResearch.WordTrace tailWord_2426485 prefixEnd_2426485 1245953105925044099978305 := by
  unfold tailWord_2426485
  simp only [CollatzResearch.WordTrace]
  refine ⟨88501178614266730490192909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59000785742844486993461939 88501178614266730490192909)
  ·
    refine ⟨33187941980350023933822341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88501178614266730490192909 33187941980350023933822341)
    ·
      refine ⟨6222739121315629487591689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33187941980350023933822341 6222739121315629487591689)
      ·
        refine ⟨4667054340986722115693767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6222739121315629487591689 4667054340986722115693767)
        ·
          refine ⟨7000581511480083173540651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667054340986722115693767 7000581511480083173540651)
          ·
            refine ⟨10500872267220124760310977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7000581511480083173540651 10500872267220124760310977)
            ·
              refine ⟨7875654200415093570233233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10500872267220124760310977 7875654200415093570233233)
              ·
                refine ⟨5906740650311320177674925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7875654200415093570233233 5906740650311320177674925)
                ·
                  refine ⟨2215027743866745066628097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5906740650311320177674925 2215027743866745066628097)
                  ·
                    refine ⟨1661270807900058799971073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2215027743866745066628097 1661270807900058799971073)
                    ·
                      refine ⟨1245953105925044099978305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661270807900058799971073 1245953105925044099978305)
                      ·
                        rfl

theorem cell23_2426485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2426485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426485 prefixEnd_2426485 := by exact prefixLift 2426485
  have htrace : WordTrace (prefixWord ++ tailWord_2426485) baseStart_2426485 baseEnd_2426485 := by
    simpa [prefixWord, tailWord_2426485, baseEnd_2426485] using wordTrace_append hprefix tailTrace_2426485
  have hstable : (prefixWord ++ tailWord_2426485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426485).length < 2 ^ (prefixWord ++ tailWord_2426485).sum := by decide
  have hdescent : baseEnd_2426485 < baseStart_2426485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426501 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 3]
def baseStart_2426501 : Nat := 118140960795 + 2426501 * 2 ^ 59
def prefixEnd_2426501 : Nat := 4983230072969 + 3 ^ 40 * 2426501 * 2
def baseEnd_2426501 : Nat := 1245961321615516037378231

theorem tailTrace_2426501 : CollatzResearch.WordTrace tailWord_2426501 prefixEnd_2426501 1245961321615516037378231 := by
  unfold tailWord_2426501
  simp only [CollatzResearch.WordTrace]
  refine ⟨88501762182208765222775357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59001174788139176815183571 88501762182208765222775357)
  ·
    refine ⟨33188160818328286958540759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88501762182208765222775357 33188160818328286958540759)
    ·
      refine ⟨49782241227492430437811139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33188160818328286958540759 49782241227492430437811139)
      ·
        refine ⟨74673361841238645656716709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49782241227492430437811139 74673361841238645656716709)
        ·
          refine ⟨14001255345232246060634383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74673361841238645656716709 14001255345232246060634383)
          ·
            refine ⟨21001883017848369090951575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14001255345232246060634383 21001883017848369090951575)
            ·
              refine ⟨31502824526772553636427363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21001883017848369090951575 31502824526772553636427363)
              ·
                refine ⟨47254236790158830454641045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31502824526772553636427363 47254236790158830454641045)
                ·
                  refine ⟨2215042349538695177561299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47254236790158830454641045 2215042349538695177561299)
                  ·
                    refine ⟨3322563524308042766341949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2215042349538695177561299 3322563524308042766341949)
                    ·
                      refine ⟨1245961321615516037378231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3322563524308042766341949 1245961321615516037378231)
                      ·
                        rfl

theorem cell23_2426501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_2426501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426501 prefixEnd_2426501 := by exact prefixLift 2426501
  have htrace : WordTrace (prefixWord ++ tailWord_2426501) baseStart_2426501 baseEnd_2426501 := by
    simpa [prefixWord, tailWord_2426501, baseEnd_2426501] using wordTrace_append hprefix tailTrace_2426501
  have hstable : (prefixWord ++ tailWord_2426501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426501).length < 2 ^ (prefixWord ++ tailWord_2426501).sum := by decide
  have hdescent : baseEnd_2426501 < baseStart_2426501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426544 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_2426544 : Nat := 118140960795 + 2426544 * 2 ^ 59
def prefixEnd_2426544 : Nat := 4983230072969 + 3 ^ 40 * 2426544 * 2
def baseEnd_2426544 : Nat := 1245983401283659369140533

theorem tailTrace_2426544 : CollatzResearch.WordTrace tailWord_2426544 prefixEnd_2426544 1245983401283659369140533 := by
  unfold tailWord_2426544
  simp only [CollatzResearch.WordTrace]
  refine ⟨44251665260526491783295343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59002220347368655711060457 44251665260526491783295343)
  ·
    refine ⟨66377497890789737674943015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44251665260526491783295343 66377497890789737674943015)
    ·
      refine ⟨99566246836184606512414523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66377497890789737674943015 99566246836184606512414523)
      ·
        refine ⟨149349370254276909768621785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99566246836184606512414523 149349370254276909768621785)
        ·
          refine ⟨112012027690707682326466339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149349370254276909768621785 112012027690707682326466339)
          ·
            refine ⟨168018041536061523489699509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112012027690707682326466339 168018041536061523489699509)
            ·
              refine ⟨15751691394005767827159329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168018041536061523489699509 15751691394005767827159329)
              ·
                refine ⟨11813768545504325870369497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15751691394005767827159329 11813768545504325870369497)
                ·
                  refine ⟨8860326409128244402777123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11813768545504325870369497 8860326409128244402777123)
                  ·
                    refine ⟨13290489613692366604165685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8860326409128244402777123 13290489613692366604165685)
                    ·
                      refine ⟨1245983401283659369140533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13290489613692366604165685 1245983401283659369140533)
                      ·
                        rfl

theorem cell23_2426544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_2426544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426544 prefixEnd_2426544 := by exact prefixLift 2426544
  have htrace : WordTrace (prefixWord ++ tailWord_2426544) baseStart_2426544 baseEnd_2426544 := by
    simpa [prefixWord, tailWord_2426544, baseEnd_2426544] using wordTrace_append hprefix tailTrace_2426544
  have hstable : (prefixWord ++ tailWord_2426544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426544).length < 2 ^ (prefixWord ++ tailWord_2426544).sum := by decide
  have hdescent : baseEnd_2426544 < baseStart_2426544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426558 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_2426558 : Nat := 118140960795 + 2426558 * 2 ^ 59
def prefixEnd_2426558 : Nat := 4983230072969 + 3 ^ 40 * 2426558 * 2
def baseEnd_2426558 : Nat := 1245990590012822314365469

theorem tailTrace_2426558 : CollatzResearch.WordTrace tailWord_2426558 prefixEnd_2426558 1245990590012822314365469 := by
  unfold tailWord_2426558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11062980142875282994700041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59002560762001509305066885 11062980142875282994700041)
  ·
    refine ⟨8297235107156462246025031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11062980142875282994700041 8297235107156462246025031)
    ·
      refine ⟨12445852660734693369037547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8297235107156462246025031 12445852660734693369037547)
      ·
        refine ⟨18668778991102040053556321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12445852660734693369037547 18668778991102040053556321)
        ·
          refine ⟨14001584243326530040167241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18668778991102040053556321 14001584243326530040167241)
          ·
            refine ⟨10501188182494897530125431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14001584243326530040167241 10501188182494897530125431)
            ·
              refine ⟨15751782273742346295188147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10501188182494897530125431 15751782273742346295188147)
              ·
                refine ⟨23627673410613519442782221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15751782273742346295188147 23627673410613519442782221)
                ·
                  refine ⟨8860377528980069791043333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23627673410613519442782221 8860377528980069791043333)
                  ·
                    refine ⟨1661320786683763085820625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8860377528980069791043333 1661320786683763085820625)
                    ·
                      refine ⟨1245990590012822314365469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661320786683763085820625 1245990590012822314365469)
                      ·
                        rfl

theorem cell23_2426558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_2426558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426558 prefixEnd_2426558 := by exact prefixLift 2426558
  have htrace : WordTrace (prefixWord ++ tailWord_2426558) baseStart_2426558 baseEnd_2426558 := by
    simpa [prefixWord, tailWord_2426558, baseEnd_2426558] using wordTrace_append hprefix tailTrace_2426558
  have hstable : (prefixWord ++ tailWord_2426558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426558).length < 2 ^ (prefixWord ++ tailWord_2426558).sum := by decide
  have hdescent : baseEnd_2426558 < baseStart_2426558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426591 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 3]
def baseStart_2426591 : Nat := 118140960795 + 2426591 * 2 ^ 59
def prefixEnd_2426591 : Nat := 4983230072969 + 3 ^ 40 * 2426591 * 2
def baseEnd_2426591 : Nat := 1246007534874420685252817

theorem tailTrace_2426591 : CollatzResearch.WordTrace tailWord_2426591 prefixEnd_2426591 1246007534874420685252817 := by
  unfold tailWord_2426591
  simp only [CollatzResearch.WordTrace]
  refine ⟨88505044751882710593551627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59003363167921807062367751 88505044751882710593551627)
  ·
    refine ⟨132757567127824065890327441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88505044751882710593551627 132757567127824065890327441)
    ·
      refine ⟨99568175345868049417745581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132757567127824065890327441 99568175345868049417745581)
      ·
        refine ⟨37338065754700518531654593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99568175345868049417745581 37338065754700518531654593)
        ·
          refine ⟨28003549316025388898740945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37338065754700518531654593 28003549316025388898740945)
          ·
            refine ⟨21002661987019041674055709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28003549316025388898740945 21002661987019041674055709)
            ·
              refine ⟨7875998245132140627770891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21002661987019041674055709 7875998245132140627770891)
              ·
                refine ⟨11813997367698210941656337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7875998245132140627770891 11813997367698210941656337)
                ·
                  refine ⟨8860498025773658206242253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11813997367698210941656337 8860498025773658206242253)
                  ·
                    refine ⟨3322686759665121827340845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8860498025773658206242253 3322686759665121827340845)
                    ·
                      refine ⟨1246007534874420685252817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3322686759665121827340845 1246007534874420685252817)
                      ·
                        rfl

theorem cell23_2426591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_2426591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426591 prefixEnd_2426591 := by exact prefixLift 2426591
  have htrace : WordTrace (prefixWord ++ tailWord_2426591) baseStart_2426591 baseEnd_2426591 := by
    simpa [prefixWord, tailWord_2426591, baseEnd_2426591] using wordTrace_append hprefix tailTrace_2426591
  have hstable : (prefixWord ++ tailWord_2426591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426591).length < 2 ^ (prefixWord ++ tailWord_2426591).sum := by decide
  have hdescent : baseEnd_2426591 < baseStart_2426591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426601 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 4, 5, 2]
def baseStart_2426601 : Nat := 118140960795 + 2426601 * 2 ^ 59
def prefixEnd_2426601 : Nat := 4983230072969 + 3 ^ 40 * 2426601 * 2
def baseEnd_2426601 : Nat := 1246012669680965646127771

theorem tailTrace_2426601 : CollatzResearch.WordTrace tailWord_2426601 prefixEnd_2426601 1246012669680965646127771 := by
  unfold tailWord_2426601
  simp only [CollatzResearch.WordTrace]
  refine ⟨88505409481846482301415657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59003606321230988200943771 88505409481846482301415657)
  ·
    refine ⟨66379057111384861726061743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88505409481846482301415657 66379057111384861726061743)
    ·
      refine ⟨99568585667077292589092615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66379057111384861726061743 99568585667077292589092615)
      ·
        refine ⟨149352878500615938883638923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99568585667077292589092615 149352878500615938883638923)
        ·
          refine ⟨224029317750923908325458385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149352878500615938883638923 224029317750923908325458385)
          ·
            refine ⟨168021988313192931244093789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224029317750923908325458385 168021988313192931244093789)
            ·
              refine ⟨63008245617447349216535171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168021988313192931244093789 63008245617447349216535171)
              ·
                refine ⟨94512368426171023824802757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63008245617447349216535171 94512368426171023824802757)
                ·
                  refine ⟨17721069079907066967150517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94512368426171023824802757 17721069079907066967150517)
                  ·
                    refine ⟨1661350226241287528170361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17721069079907066967150517 1661350226241287528170361)
                    ·
                      refine ⟨1246012669680965646127771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661350226241287528170361 1246012669680965646127771)
                      ·
                        rfl

theorem cell23_2426601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 5, 2].length) (baseStart_2426601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426601 prefixEnd_2426601 := by exact prefixLift 2426601
  have htrace : WordTrace (prefixWord ++ tailWord_2426601) baseStart_2426601 baseEnd_2426601 := by
    simpa [prefixWord, tailWord_2426601, baseEnd_2426601] using wordTrace_append hprefix tailTrace_2426601
  have hstable : (prefixWord ++ tailWord_2426601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426601).length < 2 ^ (prefixWord ++ tailWord_2426601).sum := by decide
  have hdescent : baseEnd_2426601 < baseStart_2426601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426604 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_2426604 : Nat := 118140960795 + 2426604 * 2 ^ 59
def prefixEnd_2426604 : Nat := 4983230072969 + 3 ^ 40 * 2426604 * 2
def baseEnd_2426604 : Nat := 1246014210122929134390257

theorem tailTrace_2426604 : CollatzResearch.WordTrace tailWord_2426604 prefixEnd_2426604 1246014210122929134390257 := by
  unfold tailWord_2426604
  simp only [CollatzResearch.WordTrace]
  refine ⟨44252759450417806906887433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59003679267223742542516577 44252759450417806906887433)
  ·
    refine ⟨33189569587813355180165575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44252759450417806906887433 33189569587813355180165575)
    ·
      refine ⟨49784354381720032770248363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33189569587813355180165575 49784354381720032770248363)
      ·
        refine ⟨74676531572580049155372545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49784354381720032770248363 74676531572580049155372545)
        ·
          refine ⟨56007398679435036866529409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74676531572580049155372545 56007398679435036866529409)
          ·
            refine ⟨42005549009576277649897057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56007398679435036866529409 42005549009576277649897057)
            ·
              refine ⟨31504161757182208237422793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42005549009576277649897057 31504161757182208237422793)
              ·
                refine ⟨23628121317886656178067095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31504161757182208237422793 23628121317886656178067095)
                ·
                  refine ⟨35442181976829984267100643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23628121317886656178067095 35442181976829984267100643)
                  ·
                    refine ⟨53163272965244976400650965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35442181976829984267100643 53163272965244976400650965)
                    ·
                      refine ⟨1246014210122929134390257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53163272965244976400650965 1246014210122929134390257)
                      ·
                        rfl

theorem cell23_2426604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_2426604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426604 prefixEnd_2426604 := by exact prefixLift 2426604
  have htrace : WordTrace (prefixWord ++ tailWord_2426604) baseStart_2426604 baseEnd_2426604 := by
    simpa [prefixWord, tailWord_2426604, baseEnd_2426604] using wordTrace_append hprefix tailTrace_2426604
  have hstable : (prefixWord ++ tailWord_2426604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426604).length < 2 ^ (prefixWord ++ tailWord_2426604).sum := by decide
  have hdescent : baseEnd_2426604 < baseStart_2426604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426611 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 2, 5]
def baseStart_2426611 : Nat := 118140960795 + 2426611 * 2 ^ 59
def prefixEnd_2426611 : Nat := 4983230072969 + 3 ^ 40 * 2426611 * 2
def baseEnd_2426611 : Nat := 415339268162503535667575

theorem tailTrace_2426611 : CollatzResearch.WordTrace tailWord_2426611 prefixEnd_2426611 415339268162503535667575 := by
  unfold tailWord_2426611
  simp only [CollatzResearch.WordTrace]
  refine ⟨88505774211810254009279687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59003849474540169339519791 88505774211810254009279687)
  ·
    refine ⟨132758661317715381013919531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88505774211810254009279687 132758661317715381013919531)
    ·
      refine ⟨199137991976573071520879297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132758661317715381013919531 199137991976573071520879297)
      ·
        refine ⟨149353493982429803640659473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199137991976573071520879297 149353493982429803640659473)
        ·
          refine ⟨112015120486822352730494605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149353493982429803640659473 112015120486822352730494605)
          ·
            refine ⟨42005670182558382273935477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112015120486822352730494605 42005670182558382273935477)
            ·
              refine ⟨3938031579614848338181451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42005670182558382273935477 3938031579614848338181451)
              ·
                refine ⟨5907047369422272507272177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938031579614848338181451 5907047369422272507272177)
                ·
                  refine ⟨4430285527066704380454133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5907047369422272507272177 4430285527066704380454133)
                  ·
                    refine ⟨415339268162503535667575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4430285527066704380454133 415339268162503535667575)
                    ·
                      rfl

theorem cell23_2426611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 5].length) (baseStart_2426611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426611 prefixEnd_2426611 := by exact prefixLift 2426611
  have htrace : WordTrace (prefixWord ++ tailWord_2426611) baseStart_2426611 baseEnd_2426611 := by
    simpa [prefixWord, tailWord_2426611, baseEnd_2426611] using wordTrace_append hprefix tailTrace_2426611
  have hstable : (prefixWord ++ tailWord_2426611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426611).length < 2 ^ (prefixWord ++ tailWord_2426611).sum := by decide
  have hdescent : baseEnd_2426611 < baseStart_2426611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426648 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 2, 4, 2]
def baseStart_2426648 : Nat := 118140960795 + 2426648 * 2 ^ 59
def prefixEnd_2426648 : Nat := 4983230072969 + 3 ^ 40 * 2426648 * 2
def baseEnd_2426648 : Nat := 1246036803271726962240055

theorem tailTrace_2426648 : CollatzResearch.WordTrace tailWord_2426648 prefixEnd_2426648 1246036803271726962240055 := by
  unfold tailWord_2426648
  simp only [CollatzResearch.WordTrace]
  refine ⟨44253561856338104664188299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59004749141784139552251065 44253561856338104664188299)
  ·
    refine ⟨66380342784507156996282449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44253561856338104664188299 66380342784507156996282449)
    ·
      refine ⟨49785257088380367747211837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66380342784507156996282449 49785257088380367747211837)
      ·
        refine ⟨18669471408142637905204439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49785257088380367747211837 18669471408142637905204439)
        ·
          refine ⟨28004207112213956857806659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18669471408142637905204439 28004207112213956857806659)
          ·
            refine ⟨42006310668320935286709989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28004207112213956857806659 42006310668320935286709989)
            ·
              refine ⟨7876183250310175366258123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42006310668320935286709989 7876183250310175366258123)
              ·
                refine ⟨11814274875465263049387185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7876183250310175366258123 11814274875465263049387185)
                ·
                  refine ⟨8860706156598947287040389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11814274875465263049387185 8860706156598947287040389)
                  ·
                    refine ⟨1661382404362302616320073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8860706156598947287040389 1661382404362302616320073)
                    ·
                      refine ⟨1246036803271726962240055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661382404362302616320073 1246036803271726962240055)
                      ·
                        rfl

theorem cell23_2426648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_2426648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426648 prefixEnd_2426648 := by exact prefixLift 2426648
  have htrace : WordTrace (prefixWord ++ tailWord_2426648) baseStart_2426648 baseEnd_2426648 := by
    simpa [prefixWord, tailWord_2426648, baseEnd_2426648] using wordTrace_append hprefix tailTrace_2426648
  have hstable : (prefixWord ++ tailWord_2426648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426648).length < 2 ^ (prefixWord ++ tailWord_2426648).sum := by decide
  have hdescent : baseEnd_2426648 < baseStart_2426648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426651 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 3]
def baseStart_2426651 : Nat := 118140960795 + 2426651 * 2 ^ 59
def prefixEnd_2426651 : Nat := 4983230072969 + 3 ^ 40 * 2426651 * 2
def baseEnd_2426651 : Nat := 1246038343713690450502541

theorem tailTrace_2426651 : CollatzResearch.WordTrace tailWord_2426651 prefixEnd_2426651 1246038343713690450502541 := by
  unfold tailWord_2426651
  simp only [CollatzResearch.WordTrace]
  refine ⟨88507233131665340840735807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59004822087776893893823871 88507233131665340840735807)
  ·
    refine ⟨132760849697498011261103711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88507233131665340840735807 132760849697498011261103711)
    ·
      refine ⟨199141274546247016891655567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132760849697498011261103711 199141274546247016891655567)
      ·
        refine ⟨298711911819370525337483351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199141274546247016891655567 298711911819370525337483351)
        ·
          refine ⟨448067867729055788006225027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298711911819370525337483351 448067867729055788006225027)
          ·
            refine ⟨672101801593583682009337541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448067867729055788006225027 672101801593583682009337541)
            ·
              refine ⟨126019087798796940376750789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 672101801593583682009337541 126019087798796940376750789)
              ·
                refine ⟨23628578962274426320640773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126019087798796940376750789 23628578962274426320640773)
                ·
                  refine ⟨4430358555426454935120145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23628578962274426320640773 4430358555426454935120145)
                  ·
                    refine ⟨3322768916569841201340109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4430358555426454935120145 3322768916569841201340109)
                    ·
                      refine ⟨1246038343713690450502541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3322768916569841201340109 1246038343713690450502541)
                      ·
                        rfl

theorem cell23_2426651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 3].length) (baseStart_2426651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426651 prefixEnd_2426651 := by exact prefixLift 2426651
  have htrace : WordTrace (prefixWord ++ tailWord_2426651) baseStart_2426651 baseEnd_2426651 := by
    simpa [prefixWord, tailWord_2426651, baseEnd_2426651] using wordTrace_append hprefix tailTrace_2426651
  have hstable : (prefixWord ++ tailWord_2426651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426651).length < 2 ^ (prefixWord ++ tailWord_2426651).sum := by decide
  have hdescent : baseEnd_2426651 < baseStart_2426651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426658 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2426658 : Nat := 118140960795 + 2426658 * 2 ^ 59
def prefixEnd_2426658 : Nat := 4983230072969 + 3 ^ 40 * 2426658 * 2
def baseEnd_2426658 : Nat := 415347312692757307705003

theorem tailTrace_2426658 : CollatzResearch.WordTrace tailWord_2426658 prefixEnd_2426658 415347312692757307705003 := by
  unfold tailWord_2426658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22126872110659995259060157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59004992295093320690827085 22126872110659995259060157)
  ·
    refine ⟨8297577041497498222147559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22126872110659995259060157 8297577041497498222147559)
    ·
      refine ⟨12446365562246247333221339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8297577041497498222147559 12446365562246247333221339)
      ·
        refine ⟨18669548343369370999832009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12446365562246247333221339 18669548343369370999832009)
        ·
          refine ⟨14002161257527028249874007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18669548343369370999832009 14002161257527028249874007)
          ·
            refine ⟨21003241886290542374811011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14002161257527028249874007 21003241886290542374811011)
            ·
              refine ⟨31504862829435813562216517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21003241886290542374811011 31504862829435813562216517)
              ·
                refine ⟨5907161780519215042915597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31504862829435813562216517 5907161780519215042915597)
                ·
                  refine ⟨2215185667694705641093349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5907161780519215042915597 2215185667694705641093349)
                  ·
                    refine ⟨415347312692757307705003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2215185667694705641093349 415347312692757307705003)
                    ·
                      rfl

theorem cell23_2426658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2426658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426658 prefixEnd_2426658 := by exact prefixLift 2426658
  have htrace : WordTrace (prefixWord ++ tailWord_2426658) baseStart_2426658 baseEnd_2426658 := by
    simpa [prefixWord, tailWord_2426658, baseEnd_2426658] using wordTrace_append hprefix tailTrace_2426658
  have hstable : (prefixWord ++ tailWord_2426658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426658).length < 2 ^ (prefixWord ++ tailWord_2426658).sum := by decide
  have hdescent : baseEnd_2426658 < baseStart_2426658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426685 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2426685 : Nat := 118140960795 + 2426685 * 2 ^ 59
def prefixEnd_2426685 : Nat := 4983230072969 + 3 ^ 40 * 2426685 * 2
def baseEnd_2426685 : Nat := 1246055802055943317477385

theorem tailTrace_2426685 : CollatzResearch.WordTrace tailWord_2426685 prefixEnd_2426685 1246055802055943317477385 := by
  unfold tailWord_2426685
  simp only [CollatzResearch.WordTrace]
  refine ⟨88508473213542164647473509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59005648809028109764982339 88508473213542164647473509)
  ·
    refine ⟨16595338727539155871401283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88508473213542164647473509 16595338727539155871401283)
    ·
      refine ⟨24893008091308733807101925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16595338727539155871401283 24893008091308733807101925)
      ·
        refine ⟨4667439017120387588831611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24893008091308733807101925 4667439017120387588831611)
        ·
          refine ⟨7001158525680581383247417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667439017120387588831611 7001158525680581383247417)
          ·
            refine ⟨5250868894260436037435563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7001158525680581383247417 5250868894260436037435563)
            ·
              refine ⟨7876303341390654056153345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5250868894260436037435563 7876303341390654056153345)
              ·
                refine ⟨5907227506042990542115009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7876303341390654056153345 5907227506042990542115009)
                ·
                  refine ⟨4430420629532242906586257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5907227506042990542115009 4430420629532242906586257)
                  ·
                    refine ⟨3322815472149182179939693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4430420629532242906586257 3322815472149182179939693)
                    ·
                      refine ⟨1246055802055943317477385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3322815472149182179939693 1246055802055943317477385)
                      ·
                        rfl

theorem cell23_2426685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2426685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426685 prefixEnd_2426685 := by exact prefixLift 2426685
  have htrace : WordTrace (prefixWord ++ tailWord_2426685) baseStart_2426685 baseEnd_2426685 := by
    simpa [prefixWord, tailWord_2426685, baseEnd_2426685] using wordTrace_append hprefix tailTrace_2426685
  have hstable : (prefixWord ++ tailWord_2426685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426685).length < 2 ^ (prefixWord ++ tailWord_2426685).sum := by decide
  have hdescent : baseEnd_2426685 < baseStart_2426685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426705 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 6]
def baseStart_2426705 : Nat := 118140960795 + 2426705 * 2 ^ 59
def prefixEnd_2426705 : Nat := 4983230072969 + 3 ^ 40 * 2426705 * 2
def baseEnd_2426705 : Nat := 138451785741003693247477

theorem tailTrace_2426705 : CollatzResearch.WordTrace tailWord_2426705 prefixEnd_2426705 138451785741003693247477 := by
  unfold tailWord_2426705
  simp only [CollatzResearch.WordTrace]
  refine ⟨88509202673469708063201569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59006135115646472042134379 88509202673469708063201569)
  ·
    refine ⟨66381902005102281047401177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88509202673469708063201569 66381902005102281047401177)
    ·
      refine ⟨49786426503826710785550883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66381902005102281047401177 49786426503826710785550883)
      ·
        refine ⟨74679639755740066178326325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49786426503826710785550883 74679639755740066178326325)
        ·
          refine ⟨7001216227100631204218093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74679639755740066178326325 7001216227100631204218093)
          ·
            refine ⟨2625456085162736701581785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7001216227100631204218093 2625456085162736701581785)
            ·
              refine ⟨1969092063872052526186339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2625456085162736701581785 1969092063872052526186339)
              ·
                refine ⟨2953638095808078789279509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969092063872052526186339 2953638095808078789279509)
                ·
                  refine ⟨138451785741003693247477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2953638095808078789279509 138451785741003693247477)
                  ·
                    rfl

theorem cell23_2426705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 6].length) (baseStart_2426705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426705 prefixEnd_2426705 := by exact prefixLift 2426705
  have htrace : WordTrace (prefixWord ++ tailWord_2426705) baseStart_2426705 baseEnd_2426705 := by
    simpa [prefixWord, tailWord_2426705, baseEnd_2426705] using wordTrace_append hprefix tailTrace_2426705
  have hstable : (prefixWord ++ tailWord_2426705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426705).length < 2 ^ (prefixWord ++ tailWord_2426705).sum := by decide
  have hdescent : baseEnd_2426705 < baseStart_2426705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426751 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_2426751 : Nat := 118140960795 + 2426751 * 2 ^ 59
def prefixEnd_2426751 : Nat := 4983230072969 + 3 ^ 40 * 2426751 * 2
def baseEnd_2426751 : Nat := 1246089691779140059252081

theorem tailTrace_2426751 : CollatzResearch.WordTrace tailWord_2426751 prefixEnd_2426751 1246089691779140059252081 := by
  unfold tailWord_2426751
  simp only [CollatzResearch.WordTrace]
  refine ⟨88510880431303057919376107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59007253620868705279584071 88510880431303057919376107)
  ·
    refine ⟨132766320646954586879064161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88510880431303057919376107 132766320646954586879064161)
    ·
      refine ⟨99574740485215940159298121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132766320646954586879064161 99574740485215940159298121)
      ·
        refine ⟨74681055363911955119473591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99574740485215940159298121 74681055363911955119473591)
        ·
          refine ⟨112021583045867932679210387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74681055363911955119473591 112021583045867932679210387)
          ·
            refine ⟨168032374568801899018815581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112021583045867932679210387 168032374568801899018815581)
            ·
              refine ⟨63012140463300712132055843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168032374568801899018815581 63012140463300712132055843)
              ·
                refine ⟨94518210694951068198083765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63012140463300712132055843 94518210694951068198083765)
                ·
                  refine ⟨8861082252651662643570353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94518210694951068198083765 8861082252651662643570353)
                  ·
                    refine ⟨6645811689488746982677765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8861082252651662643570353 6645811689488746982677765)
                    ·
                      refine ⟨1246089691779140059252081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6645811689488746982677765 1246089691779140059252081)
                      ·
                        rfl

theorem cell23_2426751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_2426751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426751 prefixEnd_2426751 := by exact prefixLift 2426751
  have htrace : WordTrace (prefixWord ++ tailWord_2426751) baseStart_2426751 baseEnd_2426751 := by
    simpa [prefixWord, tailWord_2426751, baseEnd_2426751] using wordTrace_append hprefix tailTrace_2426751
  have hstable : (prefixWord ++ tailWord_2426751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426751).length < 2 ^ (prefixWord ++ tailWord_2426751).sum := by decide
  have hdescent : baseEnd_2426751 < baseStart_2426751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426772 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_2426772 : Nat := 118140960795 + 2426772 * 2 ^ 59
def prefixEnd_2426772 : Nat := 4983230072969 + 3 ^ 40 * 2426772 * 2
def baseEnd_2426772 : Nat := 1246100474872884477089485

theorem tailTrace_2426772 : CollatzResearch.WordTrace tailWord_2426772 prefixEnd_2426772 1246100474872884477089485 := by
  unfold tailWord_2426772
  simp only [CollatzResearch.WordTrace]
  refine ⟨44255823182113489252945285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59007764242817985670593713 44255823182113489252945285)
  ·
    refine ⟨8297966846646279234927241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44255823182113489252945285 8297966846646279234927241)
    ·
      refine ⟨6223475134984709426195431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8297966846646279234927241 6223475134984709426195431)
      ·
        refine ⟨9335212702477064139293147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6223475134984709426195431 9335212702477064139293147)
        ·
          refine ⟨14002819053715596208939721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9335212702477064139293147 14002819053715596208939721)
          ·
            refine ⟨10502114290286697156704791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14002819053715596208939721 10502114290286697156704791)
            ·
              refine ⟨15753171435430045735057187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10502114290286697156704791 15753171435430045735057187)
              ·
                refine ⟨23629757153145068602585781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15753171435430045735057187 23629757153145068602585781)
                ·
                  refine ⟨2215289733107350181492417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23629757153145068602585781 2215289733107350181492417)
                  ·
                    refine ⟨1661467299830512636119313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2215289733107350181492417 1661467299830512636119313)
                    ·
                      refine ⟨1246100474872884477089485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661467299830512636119313 1246100474872884477089485)
                      ·
                        rfl

theorem cell23_2426772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_2426772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426772 prefixEnd_2426772 := by exact prefixLift 2426772
  have htrace : WordTrace (prefixWord ++ tailWord_2426772) baseStart_2426772 baseEnd_2426772 := by
    simpa [prefixWord, tailWord_2426772, baseEnd_2426772] using wordTrace_append hprefix tailTrace_2426772
  have hstable : (prefixWord ++ tailWord_2426772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426772).length < 2 ^ (prefixWord ++ tailWord_2426772).sum := by decide
  have hdescent : baseEnd_2426772 < baseStart_2426772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426776 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2426776 : Nat := 118140960795 + 2426776 * 2 ^ 59
def prefixEnd_2426776 : Nat := 4983230072969 + 3 ^ 40 * 2426776 * 2
def baseEnd_2426776 : Nat := 1246102528795502461439467

theorem tailTrace_2426776 : CollatzResearch.WordTrace tailWord_2426776 prefixEnd_2426776 1246102528795502461439467 := by
  unfold tailWord_2426776
  simp only [CollatzResearch.WordTrace]
  refine ⟨44255896128106243594518091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59007861504141658126024121 44255896128106243594518091)
  ·
    refine ⟨66383844192159365391777137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44255896128106243594518091 66383844192159365391777137)
    ·
      refine ⟨49787883144119524043832853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66383844192159365391777137 49787883144119524043832853)
      ·
        refine ⟨2333807022380602689554665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49787883144119524043832853 2333807022380602689554665)
        ·
          refine ⟨1750355266785452017165999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2333807022380602689554665 1750355266785452017165999)
          ·
            refine ⟨2625532900178178025748999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750355266785452017165999 2625532900178178025748999)
            ·
              refine ⟨3938299350267267038623499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2625532900178178025748999 3938299350267267038623499)
              ·
                refine ⟨5907449025400900557935249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938299350267267038623499 5907449025400900557935249)
                ·
                  refine ⟨4430586769050675418451437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5907449025400900557935249 4430586769050675418451437)
                  ·
                    refine ⟨1661470038394003281919289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4430586769050675418451437 1661470038394003281919289)
                    ·
                      refine ⟨1246102528795502461439467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661470038394003281919289 1246102528795502461439467)
                      ·
                        rfl

theorem cell23_2426776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2426776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426776 prefixEnd_2426776 := by exact prefixLift 2426776
  have htrace : WordTrace (prefixWord ++ tailWord_2426776) baseStart_2426776 baseEnd_2426776 := by
    simpa [prefixWord, tailWord_2426776, baseEnd_2426776] using wordTrace_append hprefix tailTrace_2426776
  have hstable : (prefixWord ++ tailWord_2426776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426776).length < 2 ^ (prefixWord ++ tailWord_2426776).sum := by decide
  have hdescent : baseEnd_2426776 < baseStart_2426776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426821 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_2426821 : Nat := 118140960795 + 2426821 * 2 ^ 59
def prefixEnd_2426821 : Nat := 4983230072969 + 3 ^ 40 * 2426821 * 2
def baseEnd_2426821 : Nat := 415375211808318261792253

theorem tailTrace_2426821 : CollatzResearch.WordTrace tailWord_2426821 prefixEnd_2426821 415375211808318261792253 := by
  unfold tailWord_2426821
  simp only [CollatzResearch.WordTrace]
  refine ⟨88513433541049459874424317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59008955694032973249616211 88513433541049459874424317)
  ·
    refine ⟨33192537577893547452909119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88513433541049459874424317 33192537577893547452909119)
    ·
      refine ⟨49788806366840321179363679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33192537577893547452909119 49788806366840321179363679)
      ·
        refine ⟨74683209550260481769045519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49788806366840321179363679 74683209550260481769045519)
        ·
          refine ⟨112024814325390722653568279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74683209550260481769045519 112024814325390722653568279)
          ·
            refine ⟨168037221488086083980352419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112024814325390722653568279 168037221488086083980352419)
            ·
              refine ⟨252055832232129125970528629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168037221488086083980352419 252055832232129125970528629)
              ·
                refine ⟨23630234271762105559737059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252055832232129125970528629 23630234271762105559737059)
                ·
                  refine ⟨35445351407643158339605589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23630234271762105559737059 35445351407643158339605589)
                  ·
                    refine ⟨415375211808318261792253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35445351407643158339605589 415375211808318261792253)
                    ·
                      rfl

theorem cell23_2426821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_2426821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426821 prefixEnd_2426821 := by exact prefixLift 2426821
  have htrace : WordTrace (prefixWord ++ tailWord_2426821) baseStart_2426821 baseEnd_2426821 := by
    simpa [prefixWord, tailWord_2426821, baseEnd_2426821] using wordTrace_append hprefix tailTrace_2426821
  have hstable : (prefixWord ++ tailWord_2426821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426821).length < 2 ^ (prefixWord ++ tailWord_2426821).sum := by decide
  have hdescent : baseEnd_2426821 < baseStart_2426821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426919 : List Nat := [1, 1, 7, 1, 2, 1, 1, 4, 5]
def baseStart_2426919 : Nat := 118140960795 + 2426919 * 2 ^ 59
def prefixEnd_2426919 : Nat := 4983230072969 + 3 ^ 40 * 2426919 * 2
def baseEnd_2426919 : Nat := 138463995169899489105701

theorem tailTrace_2426919 : CollatzResearch.WordTrace tailWord_2426919 prefixEnd_2426919 138463995169899489105701 := by
  unfold tailWord_2426919
  simp only [CollatzResearch.WordTrace]
  refine ⟨88517007894694422611491811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59011338596462948407661207 88517007894694422611491811)
  ·
    refine ⟨132775511842041633917237717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88517007894694422611491811 132775511842041633917237717)
    ·
      refine ⟨3111926058797850794935259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 132775511842041633917237717 3111926058797850794935259)
      ·
        refine ⟨4667889088196776192402889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3111926058797850794935259 4667889088196776192402889)
        ·
          refine ⟨3500916816147582144302167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4667889088196776192402889 3500916816147582144302167)
          ·
            refine ⟨5251375224221373216453251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500916816147582144302167 5251375224221373216453251)
            ·
              refine ⟨7877062836332059824679877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251375224221373216453251 7877062836332059824679877)
              ·
                refine ⟨1476949281812261217127477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7877062836332059824679877 1476949281812261217127477)
                ·
                  refine ⟨138463995169899489105701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1476949281812261217127477 138463995169899489105701)
                  ·
                    rfl

theorem cell23_2426919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 5].length) (baseStart_2426919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426919 prefixEnd_2426919 := by exact prefixLift 2426919
  have htrace : WordTrace (prefixWord ++ tailWord_2426919) baseStart_2426919 baseEnd_2426919 := by
    simpa [prefixWord, tailWord_2426919, baseEnd_2426919] using wordTrace_append hprefix tailTrace_2426919
  have hstable : (prefixWord ++ tailWord_2426919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426919).length < 2 ^ (prefixWord ++ tailWord_2426919).sum := by decide
  have hdescent : baseEnd_2426919 < baseStart_2426919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426922 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_2426922 : Nat := 118140960795 + 2426922 * 2 ^ 59
def prefixEnd_2426922 : Nat := 4983230072969 + 3 ^ 40 * 2426922 * 2
def baseEnd_2426922 : Nat := 1246177496971058890213795

theorem tailTrace_2426922 : CollatzResearch.WordTrace tailWord_2426922 prefixEnd_2426922 1246177496971058890213795 := by
  unfold tailWord_2426922
  simp only [CollatzResearch.WordTrace]
  refine ⟨22129279328420888530962755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59011411542455702749234013 22129279328420888530962755)
  ·
    refine ⟨33193918992631332796444133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22129279328420888530962755 33193918992631332796444133)
    ·
      refine ⟨6223859811118374899333275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33193918992631332796444133 6223859811118374899333275)
      ·
        refine ⟨9335789716677562348999913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6223859811118374899333275 9335789716677562348999913)
        ·
          refine ⟨7001842287508171761749935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9335789716677562348999913 7001842287508171761749935)
          ·
            refine ⟨10502763431262257642624903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7001842287508171761749935 10502763431262257642624903)
            ·
              refine ⟨15754145146893386463937355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10502763431262257642624903 15754145146893386463937355)
              ·
                refine ⟨23631217720340079695906033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15754145146893386463937355 23631217720340079695906033)
                ·
                  refine ⟨17723413290255059771929525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23631217720340079695906033 17723413290255059771929525)
                  ·
                    refine ⟨1661569995961411853618393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17723413290255059771929525 1661569995961411853618393)
                    ·
                      refine ⟨1246177496971058890213795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661569995961411853618393 1246177496971058890213795)
                      ·
                        rfl

theorem cell23_2426922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_2426922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426922 prefixEnd_2426922 := by exact prefixLift 2426922
  have htrace : WordTrace (prefixWord ++ tailWord_2426922) baseStart_2426922 baseEnd_2426922 := by
    simpa [prefixWord, tailWord_2426922, baseEnd_2426922] using wordTrace_append hprefix tailTrace_2426922
  have hstable : (prefixWord ++ tailWord_2426922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426922).length < 2 ^ (prefixWord ++ tailWord_2426922).sum := by decide
  have hdescent : baseEnd_2426922 < baseStart_2426922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426935 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 1, 6, 2]
def baseStart_2426935 : Nat := 118140960795 + 2426935 * 2 ^ 59
def prefixEnd_2426935 : Nat := 4983230072969 + 3 ^ 40 * 2426935 * 2
def baseEnd_2426935 : Nat := 1246184172219567339351235

theorem tailTrace_2426935 : CollatzResearch.WordTrace tailWord_2426935 prefixEnd_2426935 1246184172219567339351235 := by
  unfold tailWord_2426935
  simp only [CollatzResearch.WordTrace]
  refine ⟨88517591462636457344074259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59011727641757638229382839 88517591462636457344074259)
  ·
    refine ⟨132776387193954686016111389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88517591462636457344074259 132776387193954686016111389)
    ·
      refine ⟨49791145197733007256041771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132776387193954686016111389 49791145197733007256041771)
      ·
        refine ⟨74686717796599510884062657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49791145197733007256041771 74686717796599510884062657)
        ·
          refine ⟨56015038347449633163046993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74686717796599510884062657 56015038347449633163046993)
          ·
            refine ⟨42011278760587224872285245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56015038347449633163046993 42011278760587224872285245)
            ·
              refine ⟨15754229535220209327106967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42011278760587224872285245 15754229535220209327106967)
              ·
                refine ⟨23631344302830313990660451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15754229535220209327106967 23631344302830313990660451)
                ·
                  refine ⟨35447016454245470985990677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23631344302830313990660451 35447016454245470985990677)
                  ·
                    refine ⟨1661578896292756452468313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35447016454245470985990677 1661578896292756452468313)
                    ·
                      refine ⟨1246184172219567339351235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661578896292756452468313 1246184172219567339351235)
                      ·
                        rfl

theorem cell23_2426935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_2426935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426935 prefixEnd_2426935 := by exact prefixLift 2426935
  have htrace : WordTrace (prefixWord ++ tailWord_2426935) baseStart_2426935 baseEnd_2426935 := by
    simpa [prefixWord, tailWord_2426935, baseEnd_2426935] using wordTrace_append hprefix tailTrace_2426935
  have hstable : (prefixWord ++ tailWord_2426935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426935).length < 2 ^ (prefixWord ++ tailWord_2426935).sum := by decide
  have hdescent : baseEnd_2426935 < baseStart_2426935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2426992 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 6]
def baseStart_2426992 : Nat := 118140960795 + 2426992 * 2 ^ 59
def prefixEnd_2426992 : Nat := 4983230072969 + 3 ^ 40 * 2426992 * 2
def baseEnd_2426992 : Nat := 138468160068541512926497

theorem tailTrace_2426992 : CollatzResearch.WordTrace tailWord_2426992 prefixEnd_2426992 138468160068541512926497 := by
  unfold tailWord_2426992
  simp only [CollatzResearch.WordTrace]
  refine ⟨44259835211714978039449615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59013113615619970719266153 44259835211714978039449615)
  ·
    refine ⟨66389752817572467059174423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44259835211714978039449615 66389752817572467059174423)
    ·
      refine ⟨99584629226358700588761635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66389752817572467059174423 99584629226358700588761635)
      ·
        refine ⟨149376943839538050883142453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99584629226358700588761635 149376943839538050883142453)
        ·
          refine ⟨14004088484956692270294605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149376943839538050883142453 14004088484956692270294605)
          ·
            refine ⟨5251533181858759601360477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14004088484956692270294605 5251533181858759601360477)
            ·
              refine ⟨1969324943197034850510179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5251533181858759601360477 1969324943197034850510179)
              ·
                refine ⟨2953987414795552275765269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969324943197034850510179 2953987414795552275765269)
                ·
                  refine ⟨138468160068541512926497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2953987414795552275765269 138468160068541512926497)
                  ·
                    rfl

theorem cell23_2426992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 6].length) (baseStart_2426992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2426992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2426992 prefixEnd_2426992 := by exact prefixLift 2426992
  have htrace : WordTrace (prefixWord ++ tailWord_2426992) baseStart_2426992 baseEnd_2426992 := by
    simpa [prefixWord, tailWord_2426992, baseEnd_2426992] using wordTrace_append hprefix tailTrace_2426992
  have hstable : (prefixWord ++ tailWord_2426992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2426992).length < 2 ^ (prefixWord ++ tailWord_2426992).sum := by decide
  have hdescent : baseEnd_2426992 < baseStart_2426992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2426992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427012 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_2427012 : Nat := 118140960795 + 2427012 * 2 ^ 59
def prefixEnd_2427012 : Nat := 4983230072969 + 3 ^ 40 * 2427012 * 2
def baseEnd_2427012 : Nat := 1246223710229963538088381

theorem tailTrace_2427012 : CollatzResearch.WordTrace tailWord_2427012 prefixEnd_2427012 1246223710229963538088381 := by
  unfold tailWord_2427012
  simp only [CollatzResearch.WordTrace]
  refine ⟨44260199941678749747313645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59013599922238332996418193 44260199941678749747313645)
  ·
    refine ⟨16597574978129531155242617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44260199941678749747313645 16597574978129531155242617)
    ·
      refine ⟨12448181233597148366431963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16597574978129531155242617 12448181233597148366431963)
      ·
        refine ⟨18672271850395722549647945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12448181233597148366431963 18672271850395722549647945)
        ·
          refine ⟨14004203887796791912235959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18672271850395722549647945 14004203887796791912235959)
          ·
            refine ⟨21006305831695187868353939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14004203887796791912235959 21006305831695187868353939)
            ·
              refine ⟨31509458747542781802530909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21006305831695187868353939 31509458747542781802530909)
              ·
                refine ⟨11816047030328543175949091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31509458747542781802530909 11816047030328543175949091)
                ·
                  refine ⟨17724070545492814763923637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11816047030328543175949091 17724070545492814763923637)
                  ·
                    refine ⟨1661631613639951384117841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17724070545492814763923637 1661631613639951384117841)
                    ·
                      refine ⟨1246223710229963538088381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661631613639951384117841 1246223710229963538088381)
                      ·
                        rfl

theorem cell23_2427012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_2427012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427012 prefixEnd_2427012 := by exact prefixLift 2427012
  have htrace : WordTrace (prefixWord ++ tailWord_2427012) baseStart_2427012 baseEnd_2427012 := by
    simpa [prefixWord, tailWord_2427012, baseEnd_2427012] using wordTrace_append hprefix tailTrace_2427012
  have hstable : (prefixWord ++ tailWord_2427012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427012).length < 2 ^ (prefixWord ++ tailWord_2427012).sum := by decide
  have hdescent : baseEnd_2427012 < baseStart_2427012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427035 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 4, 4]
def baseStart_2427035 : Nat := 118140960795 + 2427035 * 2 ^ 59
def prefixEnd_2427035 : Nat := 4983230072969 + 3 ^ 40 * 2427035 * 2
def baseEnd_2427035 : Nat := 415411840095005649366925

theorem tailTrace_2427035 : CollatzResearch.WordTrace tailWord_2427035 prefixEnd_2427035 415411840095005649366925 := by
  unfold tailWord_2427035
  simp only [CollatzResearch.WordTrace]
  refine ⟨88521238762274174422714559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59014159174849449615143039 88521238762274174422714559)
  ·
    refine ⟨132781858143411261634071839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88521238762274174422714559 132781858143411261634071839)
    ·
      refine ⟨199172787215116892451107759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132781858143411261634071839 199172787215116892451107759)
      ·
        refine ⟨298759180822675338676661639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199172787215116892451107759 298759180822675338676661639)
        ·
          refine ⟨448138771234013008014992459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298759180822675338676661639 448138771234013008014992459)
          ·
            refine ⟨672208156851019512022488689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448138771234013008014992459 672208156851019512022488689)
            ·
              refine ⟨504156117638264634016866517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672208156851019512022488689 504156117638264634016866517)
              ·
                refine ⟨11816159007146827359770309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 504156117638264634016866517 11816159007146827359770309)
                ·
                  refine ⟨2215529813840030129956933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11816159007146827359770309 2215529813840030129956933)
                  ·
                    refine ⟨415411840095005649366925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2215529813840030129956933 415411840095005649366925)
                    ·
                      rfl

theorem cell23_2427035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 4].length) (baseStart_2427035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427035 prefixEnd_2427035 := by exact prefixLift 2427035
  have htrace : WordTrace (prefixWord ++ tailWord_2427035) baseStart_2427035 baseEnd_2427035 := by
    simpa [prefixWord, tailWord_2427035, baseEnd_2427035] using wordTrace_append hprefix tailTrace_2427035
  have hstable : (prefixWord ++ tailWord_2427035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427035).length < 2 ^ (prefixWord ++ tailWord_2427035).sum := by decide
  have hdescent : baseEnd_2427035 < baseStart_2427035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427045 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_2427045 : Nat := 118140960795 + 2427045 * 2 ^ 59
def prefixEnd_2427045 : Nat := 4983230072969 + 3 ^ 40 * 2427045 * 2
def baseEnd_2427045 : Nat := 1246240655091561908975729

theorem tailTrace_2427045 : CollatzResearch.WordTrace tailWord_2427045 prefixEnd_2427045 1246240655091561908975729 := by
  unfold tailWord_2427045
  simp only [CollatzResearch.WordTrace]
  refine ⟨88521603492237946130578589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59014402328158630753719059 88521603492237946130578589)
  ·
    refine ⟨33195601309589229798966971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88521603492237946130578589 33195601309589229798966971)
    ·
      refine ⟨49793401964383844698450457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33195601309589229798966971 49793401964383844698450457)
      ·
        refine ⟨37345051473287883523837843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49793401964383844698450457 37345051473287883523837843)
        ·
          refine ⟨56017577209931825285756765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37345051473287883523837843 56017577209931825285756765)
          ·
            refine ⟨21006591453724434482158787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56017577209931825285756765 21006591453724434482158787)
            ·
              refine ⟨31509887180586651723238181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21006591453724434482158787 31509887180586651723238181)
              ·
                refine ⟨5908103846359997198107159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31509887180586651723238181 5908103846359997198107159)
                ·
                  refine ⟨8862155769539995797160739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5908103846359997198107159 8862155769539995797160739)
                  ·
                    refine ⟨13293233654309993695741109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8862155769539995797160739 13293233654309993695741109)
                    ·
                      refine ⟨1246240655091561908975729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13293233654309993695741109 1246240655091561908975729)
                      ·
                        rfl

theorem cell23_2427045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_2427045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427045 prefixEnd_2427045 := by exact prefixLift 2427045
  have htrace : WordTrace (prefixWord ++ tailWord_2427045) baseStart_2427045 baseEnd_2427045 := by
    simpa [prefixWord, tailWord_2427045, baseEnd_2427045] using wordTrace_append hprefix tailTrace_2427045
  have hstable : (prefixWord ++ tailWord_2427045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427045).length < 2 ^ (prefixWord ++ tailWord_2427045).sum := by decide
  have hdescent : baseEnd_2427045 < baseStart_2427045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427055 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_2427055 : Nat := 118140960795 + 2427055 * 2 ^ 59
def prefixEnd_2427055 : Nat := 4983230072969 + 3 ^ 40 * 2427055 * 2
def baseEnd_2427055 : Nat := 1246245789898106869850683

theorem tailTrace_2427055 : CollatzResearch.WordTrace tailWord_2427055 prefixEnd_2427055 1246245789898106869850683 := by
  unfold tailWord_2427055
  simp only [CollatzResearch.WordTrace]
  refine ⟨88521968222201717838442619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59014645481467811892295079 88521968222201717838442619)
  ·
    refine ⟨132782952333302576757663929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88521968222201717838442619 132782952333302576757663929)
    ·
      refine ⟨99587214249976932568247947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132782952333302576757663929 99587214249976932568247947)
      ·
        refine ⟨149380821374965398852371921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99587214249976932568247947 149380821374965398852371921)
        ·
          refine ⟨112035616031224049139278941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149380821374965398852371921 112035616031224049139278941)
          ·
            refine ⟨42013356011709018427229603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112035616031224049139278941 42013356011709018427229603)
            ·
              refine ⟨63020034017563527640844405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42013356011709018427229603 63020034017563527640844405)
              ·
                refine ⟨5908128189146580716329163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63020034017563527640844405 5908128189146580716329163)
                ·
                  refine ⟨8862192283719871074493745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5908128189146580716329163 8862192283719871074493745)
                  ·
                    refine ⟨6646644212789903305870309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8862192283719871074493745 6646644212789903305870309)
                    ·
                      refine ⟨1246245789898106869850683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6646644212789903305870309 1246245789898106869850683)
                      ·
                        rfl

theorem cell23_2427055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_2427055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427055 prefixEnd_2427055 := by exact prefixLift 2427055
  have htrace : WordTrace (prefixWord ++ tailWord_2427055) baseStart_2427055 baseEnd_2427055 := by
    simpa [prefixWord, tailWord_2427055, baseEnd_2427055] using wordTrace_append hprefix tailTrace_2427055
  have hstable : (prefixWord ++ tailWord_2427055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427055).length < 2 ^ (prefixWord ++ tailWord_2427055).sum := by decide
  have hdescent : baseEnd_2427055 < baseStart_2427055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427072 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_2427072 : Nat := 118140960795 + 2427072 * 2 ^ 59
def prefixEnd_2427072 : Nat := 4983230072969 + 3 ^ 40 * 2427072 * 2
def baseEnd_2427072 : Nat := 1246254519069233303338105

theorem tailTrace_2427072 : CollatzResearch.WordTrace tailWord_2427072 prefixEnd_2427072 1246254519069233303338105 := by
  unfold tailWord_2427072
  simp only [CollatzResearch.WordTrace]
  refine ⟨44261294131570064870905735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59015058842093419827874313 44261294131570064870905735)
  ·
    refine ⟨66391941197355097306358603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44261294131570064870905735 66391941197355097306358603)
    ·
      refine ⟨99587911796032645959537905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66391941197355097306358603 99587911796032645959537905)
      ·
        refine ⟨74690933847024484469653429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99587911796032645959537905 74690933847024484469653429)
        ·
          refine ⟨7002275048158545419030009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74690933847024484469653429 7002275048158545419030009)
          ·
            refine ⟨5251706286118909064272507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7002275048158545419030009 5251706286118909064272507)
            ·
              refine ⟨7877559429178363596408761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251706286118909064272507 7877559429178363596408761)
              ·
                refine ⟨5908169571883772697306571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7877559429178363596408761 5908169571883772697306571)
                ·
                  refine ⟨8862254357825659045959857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5908169571883772697306571 8862254357825659045959857)
                  ·
                    refine ⟨6646690768369244284469893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8862254357825659045959857 6646690768369244284469893)
                    ·
                      refine ⟨1246254519069233303338105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6646690768369244284469893 1246254519069233303338105)
                      ·
                        rfl

theorem cell23_2427072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_2427072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427072 prefixEnd_2427072 := by exact prefixLift 2427072
  have htrace : WordTrace (prefixWord ++ tailWord_2427072) baseStart_2427072 baseEnd_2427072 := by
    simpa [prefixWord, tailWord_2427072, baseEnd_2427072] using wordTrace_append hprefix tailTrace_2427072
  have hstable : (prefixWord ++ tailWord_2427072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427072).length < 2 ^ (prefixWord ++ tailWord_2427072).sum := by decide
  have hdescent : baseEnd_2427072 < baseStart_2427072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427076 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_2427076 : Nat := 118140960795 + 2427076 * 2 ^ 59
def prefixEnd_2427076 : Nat := 4983230072969 + 3 ^ 40 * 2427076 * 2
def baseEnd_2427076 : Nat := 1246256572991851287688087

theorem tailTrace_2427076 : CollatzResearch.WordTrace tailWord_2427076 prefixEnd_2427076 1246256572991851287688087 := by
  unfold tailWord_2427076
  simp only [CollatzResearch.WordTrace]
  refine ⟨44261367077562819212478541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59015156103417092283304721 44261367077562819212478541)
  ·
    refine ⟨16598012654086057204679453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44261367077562819212478541 16598012654086057204679453)
    ·
      refine ⟨6224254745282271451754795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16598012654086057204679453 6224254745282271451754795)
      ·
        refine ⟨9336382117923407177632193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6224254745282271451754795 9336382117923407177632193)
        ·
          refine ⟨7002286588442555383224145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9336382117923407177632193 7002286588442555383224145)
          ·
            refine ⟨5251714941331916537418109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7002286588442555383224145 5251714941331916537418109)
            ·
              refine ⟨1969393102999468701531791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5251714941331916537418109 1969393102999468701531791)
              ·
                refine ⟨2954089654499203052297687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969393102999468701531791 2954089654499203052297687)
                ·
                  refine ⟨4431134481748804578446531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954089654499203052297687 4431134481748804578446531)
                  ·
                    refine ⟨6646701722623206867669797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4431134481748804578446531 6646701722623206867669797)
                    ·
                      refine ⟨1246256572991851287688087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6646701722623206867669797 1246256572991851287688087)
                      ·
                        rfl

theorem cell23_2427076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_2427076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427076 prefixEnd_2427076 := by exact prefixLift 2427076
  have htrace : WordTrace (prefixWord ++ tailWord_2427076) baseStart_2427076 baseEnd_2427076 := by
    simpa [prefixWord, tailWord_2427076, baseEnd_2427076] using wordTrace_append hprefix tailTrace_2427076
  have hstable : (prefixWord ++ tailWord_2427076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427076).length < 2 ^ (prefixWord ++ tailWord_2427076).sum := by decide
  have hdescent : baseEnd_2427076 < baseStart_2427076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427109 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2427109 : Nat := 118140960795 + 2427109 * 2 ^ 59
def prefixEnd_2427109 : Nat := 4983230072969 + 3 ^ 40 * 2427109 * 2
def baseEnd_2427109 : Nat := 1246273517853449658575435

theorem tailTrace_2427109 : CollatzResearch.WordTrace tailWord_2427109 prefixEnd_2427109 1246273517853449658575435 := by
  unfold tailWord_2427109
  simp only [CollatzResearch.WordTrace]
  refine ⟨88523937764006085060908381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59015958509337390040605587 88523937764006085060908381)
  ·
    refine ⟨33196476661502281897840643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88523937764006085060908381 33196476661502281897840643)
    ·
      refine ⟨49794714992253422846760965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33196476661502281897840643 49794714992253422846760965)
      ·
        refine ⟨9336509061047516783767681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49794714992253422846760965 9336509061047516783767681)
        ·
          refine ⟨7002381795785637587825761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9336509061047516783767681 7002381795785637587825761)
          ·
            refine ⟨5251786346839228190869321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7002381795785637587825761 5251786346839228190869321)
            ·
              refine ⟨3938839760129421143151991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5251786346839228190869321 3938839760129421143151991)
              ·
                refine ⟨5908259640194131714727987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938839760129421143151991 5908259640194131714727987)
                ·
                  refine ⟨8862389460291197572091981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5908259640194131714727987 8862389460291197572091981)
                  ·
                    refine ⟨3323396047609199089534493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8862389460291197572091981 3323396047609199089534493)
                    ·
                      refine ⟨1246273517853449658575435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3323396047609199089534493 1246273517853449658575435)
                      ·
                        rfl

theorem cell23_2427109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2427109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427109 prefixEnd_2427109 := by exact prefixLift 2427109
  have htrace : WordTrace (prefixWord ++ tailWord_2427109) baseStart_2427109 baseEnd_2427109 := by
    simpa [prefixWord, tailWord_2427109, baseEnd_2427109] using wordTrace_append hprefix tailTrace_2427109
  have hstable : (prefixWord ++ tailWord_2427109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427109).length < 2 ^ (prefixWord ++ tailWord_2427109).sum := by decide
  have hdescent : baseEnd_2427109 < baseStart_2427109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427115 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 4]
def baseStart_2427115 : Nat := 118140960795 + 2427115 * 2 ^ 59
def prefixEnd_2427115 : Nat := 4983230072969 + 3 ^ 40 * 2427115 * 2
def baseEnd_2427115 : Nat := 1246276598737376635100407

theorem tailTrace_2427115 : CollatzResearch.WordTrace tailWord_2427115 prefixEnd_2427115 1246276598737376635100407 := by
  unfold tailWord_2427115
  simp only [CollatzResearch.WordTrace]
  refine ⟨88524156601984348085626799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59016104401322898723751199 88524156601984348085626799)
  ·
    refine ⟨132786234902976522128440199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88524156601984348085626799 132786234902976522128440199)
    ·
      refine ⟨199179352354464783192660299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132786234902976522128440199 199179352354464783192660299)
      ·
        refine ⟨298769028531697174788990449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199179352354464783192660299 298769028531697174788990449)
        ·
          refine ⟨224076771398772881091742837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298769028531697174788990449 224076771398772881091742837)
          ·
            refine ⟨21007197318634957602350891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224076771398772881091742837 21007197318634957602350891)
            ·
              refine ⟨31510795977952436403526337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21007197318634957602350891 31510795977952436403526337)
              ·
                refine ⟨23633096983464327302644753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31510795977952436403526337 23633096983464327302644753)
                ·
                  refine ⟨17724822737598245476983565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23633096983464327302644753 17724822737598245476983565)
                  ·
                    refine ⟨6646808526599342053868837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17724822737598245476983565 6646808526599342053868837)
                    ·
                      refine ⟨1246276598737376635100407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6646808526599342053868837 1246276598737376635100407)
                      ·
                        rfl

theorem cell23_2427115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 4].length) (baseStart_2427115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427115 prefixEnd_2427115 := by exact prefixLift 2427115
  have htrace : WordTrace (prefixWord ++ tailWord_2427115) baseStart_2427115 baseEnd_2427115 := by
    simpa [prefixWord, tailWord_2427115, baseEnd_2427115] using wordTrace_append hprefix tailTrace_2427115
  have hstable : (prefixWord ++ tailWord_2427115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427115).length < 2 ^ (prefixWord ++ tailWord_2427115).sum := by decide
  have hdescent : baseEnd_2427115 < baseStart_2427115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427119 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 3, 3, 2]
def baseStart_2427119 : Nat := 118140960795 + 2427119 * 2 ^ 59
def prefixEnd_2427119 : Nat := 4983230072969 + 3 ^ 40 * 2427119 * 2
def baseEnd_2427119 : Nat := 1246278652659994619450389

theorem tailTrace_2427119 : CollatzResearch.WordTrace tailWord_2427119 prefixEnd_2427119 1246278652659994619450389 := by
  unfold tailWord_2427119
  simp only [CollatzResearch.WordTrace]
  refine ⟨88524302493969856768772411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59016201662646571179181607 88524302493969856768772411)
  ·
    refine ⟨132786453740954785153158617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88524302493969856768772411 132786453740954785153158617)
    ·
      refine ⟨99589840305716088864868963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132786453740954785153158617 99589840305716088864868963)
      ·
        refine ⟨149384760458574133297303445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99589840305716088864868963 149384760458574133297303445)
        ·
          refine ⟨7002410646495662498311099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 149384760458574133297303445 7002410646495662498311099)
          ·
            refine ⟨10503615969743493747466649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7002410646495662498311099 10503615969743493747466649)
            ·
              refine ⟨7877711977307620310599987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10503615969743493747466649 7877711977307620310599987)
              ·
                refine ⟨11816567965961430465899981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7877711977307620310599987 11816567965961430465899981)
                ·
                  refine ⟨4431212987235536424712493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11816567965961430465899981 4431212987235536424712493)
                  ·
                    refine ⟨1661704870213326159267185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4431212987235536424712493 1661704870213326159267185)
                    ·
                      refine ⟨1246278652659994619450389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661704870213326159267185 1246278652659994619450389)
                      ·
                        rfl

theorem cell23_2427119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 3, 2].length) (baseStart_2427119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427119 prefixEnd_2427119 := by exact prefixLift 2427119
  have htrace : WordTrace (prefixWord ++ tailWord_2427119) baseStart_2427119 baseEnd_2427119 := by
    simpa [prefixWord, tailWord_2427119, baseEnd_2427119] using wordTrace_append hprefix tailTrace_2427119
  have hstable : (prefixWord ++ tailWord_2427119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427119).length < 2 ^ (prefixWord ++ tailWord_2427119).sum := by decide
  have hdescent : baseEnd_2427119 < baseStart_2427119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427135 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_2427135 : Nat := 118140960795 + 2427135 * 2 ^ 59
def prefixEnd_2427135 : Nat := 4983230072969 + 3 ^ 40 * 2427135 * 2
def baseEnd_2427135 : Nat := 1246286868350466556850315

theorem tailTrace_2427135 : CollatzResearch.WordTrace tailWord_2427135 prefixEnd_2427135 1246286868350466556850315 := by
  unfold tailWord_2427135
  simp only [CollatzResearch.WordTrace]
  refine ⟨88524886061911891501354859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59016590707941261000903239 88524886061911891501354859)
  ·
    refine ⟨132787329092867837252032289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88524886061911891501354859 132787329092867837252032289)
    ·
      refine ⟨99590496819650877939024217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132787329092867837252032289 99590496819650877939024217)
      ·
        refine ⟨74692872614738158454268163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99590496819650877939024217 74692872614738158454268163)
        ·
          refine ⟨112039308922107237681402245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74692872614738158454268163 112039308922107237681402245)
          ·
            refine ⟨21007370422895107065262921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112039308922107237681402245 21007370422895107065262921)
            ·
              refine ⟨15755527817171330298947191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21007370422895107065262921 15755527817171330298947191)
              ·
                refine ⟨23633291725756995448420787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15755527817171330298947191 23633291725756995448420787)
                ·
                  refine ⟨35449937588635493172631181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23633291725756995448420787 35449937588635493172631181)
                  ·
                    refine ⟨13293726595738309939736693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35449937588635493172631181 13293726595738309939736693)
                    ·
                      refine ⟨1246286868350466556850315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13293726595738309939736693 1246286868350466556850315)
                      ·
                        rfl

theorem cell23_2427135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_2427135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427135 prefixEnd_2427135 := by exact prefixLift 2427135
  have htrace : WordTrace (prefixWord ++ tailWord_2427135) baseStart_2427135 baseEnd_2427135 := by
    simpa [prefixWord, tailWord_2427135, baseEnd_2427135] using wordTrace_append hprefix tailTrace_2427135
  have hstable : (prefixWord ++ tailWord_2427135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427135).length < 2 ^ (prefixWord ++ tailWord_2427135).sum := by decide
  have hdescent : baseEnd_2427135 < baseStart_2427135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427136 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 1, 3, 2]
def baseStart_2427136 : Nat := 118140960795 + 2427136 * 2 ^ 59
def prefixEnd_2427136 : Nat := 4983230072969 + 3 ^ 40 * 2427136 * 2
def baseEnd_2427136 : Nat := 1246287381831121052937811

theorem tailTrace_2427136 : CollatzResearch.WordTrace tailWord_2427136 prefixEnd_2427136 1246287381831121052937811 := by
  unfold tailWord_2427136
  simp only [CollatzResearch.WordTrace]
  refine ⟨44262461267454134336070631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59016615023272179114760841 44262461267454134336070631)
  ·
    refine ⟨66393691901181201504105947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44262461267454134336070631 66393691901181201504105947)
    ·
      refine ⟨99590537851771802256158921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66393691901181201504105947 99590537851771802256158921)
      ·
        refine ⟨74692903388828851692119191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99590537851771802256158921 74692903388828851692119191)
        ·
          refine ⟨112039355083243277538178787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74692903388828851692119191 112039355083243277538178787)
          ·
            refine ⟨168059032624864916307268181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112039355083243277538178787 168059032624864916307268181)
            ·
              refine ⟨1969441788572635737975799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 168059032624864916307268181 1969441788572635737975799)
              ·
                refine ⟨2954162682858953606963699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969441788572635737975799 2954162682858953606963699)
                ·
                  refine ⟨4431244024288430410445549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954162682858953606963699 4431244024288430410445549)
                  ·
                    refine ⟨1661716509108161403917081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4431244024288430410445549 1661716509108161403917081)
                    ·
                      refine ⟨1246287381831121052937811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661716509108161403917081 1246287381831121052937811)
                      ·
                        rfl

theorem cell23_2427136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_2427136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427136 prefixEnd_2427136 := by exact prefixLift 2427136
  have htrace : WordTrace (prefixWord ++ tailWord_2427136) baseStart_2427136 baseEnd_2427136 := by
    simpa [prefixWord, tailWord_2427136, baseEnd_2427136] using wordTrace_append hprefix tailTrace_2427136
  have hstable : (prefixWord ++ tailWord_2427136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427136).length < 2 ^ (prefixWord ++ tailWord_2427136).sum := by decide
  have hdescent : baseEnd_2427136 < baseStart_2427136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427172 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 7]
def baseStart_2427172 : Nat := 118140960795 + 2427172 * 2 ^ 59
def prefixEnd_2427172 : Nat := 4983230072969 + 3 ^ 40 * 2427172 * 2
def baseEnd_2427172 : Nat := 138478429681631434676405

theorem tailTrace_2427172 : CollatzResearch.WordTrace tailWord_2427172 prefixEnd_2427172 138478429681631434676405 := by
  unfold tailWord_2427172
  simp only [CollatzResearch.WordTrace]
  refine ⟨44263117781388923410225885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59017490375185231213634513 44263117781388923410225885)
  ·
    refine ⟨16598669168020846278834707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44263117781388923410225885 16598669168020846278834707)
    ·
      refine ⟨24898003752031269418252061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16598669168020846278834707 24898003752031269418252061)
      ·
        refine ⟨9336751407011726031844523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24898003752031269418252061 9336751407011726031844523)
        ·
          refine ⟨14005127110517589047766785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9336751407011726031844523 14005127110517589047766785)
          ·
            refine ⟨10503845332888191785825089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14005127110517589047766785 10503845332888191785825089)
            ·
              refine ⟨7877883999666143839368817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10503845332888191785825089 7877883999666143839368817)
              ·
                refine ⟨5908412999749607879526613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7877883999666143839368817 5908412999749607879526613)
                ·
                  refine ⟨138478429681631434676405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5908412999749607879526613 138478429681631434676405)
                  ·
                    rfl

theorem cell23_2427172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_2427172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427172 prefixEnd_2427172 := by exact prefixLift 2427172
  have htrace : WordTrace (prefixWord ++ tailWord_2427172) baseStart_2427172 baseEnd_2427172 := by
    simpa [prefixWord, tailWord_2427172, baseEnd_2427172] using wordTrace_append hprefix tailTrace_2427172
  have hstable : (prefixWord ++ tailWord_2427172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427172).length < 2 ^ (prefixWord ++ tailWord_2427172).sum := by decide
  have hdescent : baseEnd_2427172 < baseStart_2427172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427205 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_2427205 : Nat := 118140960795 + 2427205 * 2 ^ 59
def prefixEnd_2427205 : Nat := 4983230072969 + 3 ^ 40 * 2427205 * 2
def baseEnd_2427205 : Nat := 1246322811996281282974993

theorem tailTrace_2427205 : CollatzResearch.WordTrace tailWord_2427205 prefixEnd_2427205 1246322811996281282974993 := by
  unfold tailWord_2427205
  simp only [CollatzResearch.WordTrace]
  refine ⟨88527439171658293456403069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59018292781105528970935379 88527439171658293456403069)
  ·
    refine ⟨33197789689371860046151151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88527439171658293456403069 33197789689371860046151151)
    ·
      refine ⟨49796684534057790069226727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33197789689371860046151151 49796684534057790069226727)
      ·
        refine ⟨74695026801086685103840091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49796684534057790069226727 74695026801086685103840091)
        ·
          refine ⟨112042540201630027655760137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74695026801086685103840091 112042540201630027655760137)
          ·
            refine ⟨84031905151222520741820103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112042540201630027655760137 84031905151222520741820103)
            ·
              refine ⟨126047857726833781112730155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84031905151222520741820103 126047857726833781112730155)
              ·
                refine ⟨189071786590250671669095233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126047857726833781112730155 189071786590250671669095233)
                ·
                  refine ⟨141803839942688003751821425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189071786590250671669095233 141803839942688003751821425)
                  ·
                    refine ⟨106352879957016002813866069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141803839942688003751821425 106352879957016002813866069)
                    ·
                      refine ⟨1246322811996281282974993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 106352879957016002813866069 1246322811996281282974993)
                      ·
                        rfl

theorem cell23_2427205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_2427205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427205 prefixEnd_2427205 := by exact prefixLift 2427205
  have htrace : WordTrace (prefixWord ++ tailWord_2427205) baseStart_2427205 baseEnd_2427205 := by
    simpa [prefixWord, tailWord_2427205, baseEnd_2427205] using wordTrace_append hprefix tailTrace_2427205
  have hstable : (prefixWord ++ tailWord_2427205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427205).length < 2 ^ (prefixWord ++ tailWord_2427205).sum := by decide
  have hdescent : baseEnd_2427205 < baseStart_2427205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427212 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2427212 : Nat := 118140960795 + 2427212 * 2 ^ 59
def prefixEnd_2427212 : Nat := 4983230072969 + 3 ^ 40 * 2427212 * 2
def baseEnd_2427212 : Nat := 1246326406360862755587461

theorem tailTrace_2427212 : CollatzResearch.WordTrace tailWord_2427212 prefixEnd_2427212 1246326406360862755587461 := by
  unfold tailWord_2427212
  simp only [CollatzResearch.WordTrace]
  refine ⟨44263847241316466825953945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59018462988421955767938593 44263847241316466825953945)
  ·
    refine ⟨33197885430987350119465459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44263847241316466825953945 33197885430987350119465459)
    ·
      refine ⟨49796828146481025179198189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33197885430987350119465459 49796828146481025179198189)
      ·
        refine ⟨18673810554930384442199321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49796828146481025179198189 18673810554930384442199321)
        ·
          refine ⟨14005357916197788331649491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18673810554930384442199321 14005357916197788331649491)
          ·
            refine ⟨21008036874296682497474237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14005357916197788331649491 21008036874296682497474237)
            ·
              refine ⟨7878013827861255936552839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21008036874296682497474237 7878013827861255936552839)
              ·
                refine ⟨11817020741791883904829259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7878013827861255936552839 11817020741791883904829259)
                ·
                  refine ⟨17725531112687825857243889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11817020741791883904829259 17725531112687825857243889)
                  ·
                    refine ⟨13294148334515869392932917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17725531112687825857243889 13294148334515869392932917)
                    ·
                      refine ⟨1246326406360862755587461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13294148334515869392932917 1246326406360862755587461)
                      ·
                        rfl

theorem cell23_2427212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2427212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427212 prefixEnd_2427212 := by exact prefixLift 2427212
  have htrace : WordTrace (prefixWord ++ tailWord_2427212) baseStart_2427212 baseEnd_2427212 := by
    simpa [prefixWord, tailWord_2427212, baseEnd_2427212] using wordTrace_append hprefix tailTrace_2427212
  have hstable : (prefixWord ++ tailWord_2427212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427212).length < 2 ^ (prefixWord ++ tailWord_2427212).sum := by decide
  have hdescent : baseEnd_2427212 < baseStart_2427212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427215 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 2, 8]
def baseStart_2427215 : Nat := 118140960795 + 2427215 * 2 ^ 59
def prefixEnd_2427215 : Nat := 4983230072969 + 3 ^ 40 * 2427215 * 2
def baseEnd_2427215 : Nat := 415442648934275414616649

theorem tailTrace_2427215 : CollatzResearch.WordTrace tailWord_2427215 prefixEnd_2427215 415442648934275414616649 := by
  unfold tailWord_2427215
  simp only [CollatzResearch.WordTrace]
  refine ⟨88527803901622065164267099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59018535934414710109511399 88527803901622065164267099)
  ·
    refine ⟨132791705852433097746400649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88527803901622065164267099 132791705852433097746400649)
    ·
      refine ⟨99593779389324823309800487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132791705852433097746400649 99593779389324823309800487)
      ·
        refine ⟨149390669083987234964700731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99593779389324823309800487 149390669083987234964700731)
        ·
          refine ⟨224086003625980852447051097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149390669083987234964700731 224086003625980852447051097)
          ·
            refine ⟨168064502719485639335288323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224086003625980852447051097 168064502719485639335288323)
            ·
              refine ⟨252096754079228459002932485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168064502719485639335288323 252096754079228459002932485)
              ·
                refine ⟨47268141389855336063049841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252096754079228459002932485 47268141389855336063049841)
                ·
                  refine ⟨35451106042391502047287381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47268141389855336063049841 35451106042391502047287381)
                  ·
                    refine ⟨415442648934275414616649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35451106042391502047287381 415442648934275414616649)
                    ·
                      rfl

theorem cell23_2427215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_2427215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427215 prefixEnd_2427215 := by exact prefixLift 2427215
  have htrace : WordTrace (prefixWord ++ tailWord_2427215) baseStart_2427215 baseEnd_2427215 := by
    simpa [prefixWord, tailWord_2427215, baseEnd_2427215] using wordTrace_append hprefix tailTrace_2427215
  have hstable : (prefixWord ++ tailWord_2427215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427215).length < 2 ^ (prefixWord ++ tailWord_2427215).sum := by decide
  have hdescent : baseEnd_2427215 < baseStart_2427215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427239 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2427239 : Nat := 118140960795 + 2427239 * 2 ^ 59
def prefixEnd_2427239 : Nat := 4983230072969 + 3 ^ 40 * 2427239 * 2
def baseEnd_2427239 : Nat := 1246340270338534149949837

theorem tailTrace_2427239 : CollatzResearch.WordTrace tailWord_2427239 prefixEnd_2427239 1246340270338534149949837 := by
  unfold tailWord_2427239
  simp only [CollatzResearch.WordTrace]
  refine ⟨88528679253535117263140771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59019119502356744842093847 88528679253535117263140771)
  ·
    refine ⟨132793018880302675894711157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88528679253535117263140771 132793018880302675894711157)
    ·
      refine ⟨12449345520028375865129171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132793018880302675894711157 12449345520028375865129171)
      ·
        refine ⟨18674018280042563797693757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12449345520028375865129171 18674018280042563797693757)
        ·
          refine ⟨7002756855015961424135159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18674018280042563797693757 7002756855015961424135159)
          ·
            refine ⟨10504135282523942136202739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7002756855015961424135159 10504135282523942136202739)
            ·
              refine ⟨15756202923785913204304109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10504135282523942136202739 15756202923785913204304109)
              ·
                refine ⟨5908576096419717451614041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15756202923785913204304109 5908576096419717451614041)
                ·
                  refine ⟨4431432072314788088710531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5908576096419717451614041 4431432072314788088710531)
                  ·
                    refine ⟨6647148108472182133065797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4431432072314788088710531 6647148108472182133065797)
                    ·
                      refine ⟨1246340270338534149949837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6647148108472182133065797 1246340270338534149949837)
                      ·
                        rfl

theorem cell23_2427239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2427239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427239 prefixEnd_2427239 := by exact prefixLift 2427239
  have htrace : WordTrace (prefixWord ++ tailWord_2427239) baseStart_2427239 baseEnd_2427239 := by
    simpa [prefixWord, tailWord_2427239, baseEnd_2427239] using wordTrace_append hprefix tailTrace_2427239
  have hstable : (prefixWord ++ tailWord_2427239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427239).length < 2 ^ (prefixWord ++ tailWord_2427239).sum := by decide
  have hdescent : baseEnd_2427239 < baseStart_2427239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427259 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 3]
def baseStart_2427259 : Nat := 118140960795 + 2427259 * 2 ^ 59
def prefixEnd_2427259 : Nat := 4983230072969 + 3 ^ 40 * 2427259 * 2
def baseEnd_2427259 : Nat := 1246350539951624071699745

theorem tailTrace_2427259 : CollatzResearch.WordTrace tailWord_2427259 prefixEnd_2427259 1246350539951624071699745 := by
  unfold tailWord_2427259
  simp only [CollatzResearch.WordTrace]
  refine ⟨88529408713462660678868831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59019605808975107119245887 88529408713462660678868831)
  ·
    refine ⟨132794113070193991018303247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88529408713462660678868831 132794113070193991018303247)
    ·
      refine ⟨199191169605290986527454871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132794113070193991018303247 199191169605290986527454871)
      ·
        refine ⟨298786754407936479791182307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199191169605290986527454871 298786754407936479791182307)
        ·
          refine ⟨448180131611904719686773461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298786754407936479791182307 448180131611904719686773461)
          ·
            refine ⟨10504221834654016867658753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 448180131611904719686773461 10504221834654016867658753)
            ·
              refine ⟨7878166375990512650744065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10504221834654016867658753 7878166375990512650744065)
              ·
                refine ⟨5908624781992884488058049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7878166375990512650744065 5908624781992884488058049)
                ·
                  refine ⟨4431468586494663366043537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5908624781992884488058049 4431468586494663366043537)
                  ·
                    refine ⟨3323601439870997524532653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4431468586494663366043537 3323601439870997524532653)
                    ·
                      refine ⟨1246350539951624071699745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3323601439870997524532653 1246350539951624071699745)
                      ·
                        rfl

theorem cell23_2427259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 3].length) (baseStart_2427259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427259 prefixEnd_2427259 := by exact prefixLift 2427259
  have htrace : WordTrace (prefixWord ++ tailWord_2427259) baseStart_2427259 baseEnd_2427259 := by
    simpa [prefixWord, tailWord_2427259, baseEnd_2427259] using wordTrace_append hprefix tailTrace_2427259
  have hstable : (prefixWord ++ tailWord_2427259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427259).length < 2 ^ (prefixWord ++ tailWord_2427259).sum := by decide
  have hdescent : baseEnd_2427259 < baseStart_2427259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427293 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_2427293 : Nat := 118140960795 + 2427293 * 2 ^ 59
def prefixEnd_2427293 : Nat := 4983230072969 + 3 ^ 40 * 2427293 * 2
def baseEnd_2427293 : Nat := 1246367998293876938674589

theorem tailTrace_2427293 : CollatzResearch.WordTrace tailWord_2427293 prefixEnd_2427293 1246367998293876938674589 := by
  unfold tailWord_2427293
  simp only [CollatzResearch.WordTrace]
  refine ⟨88530648795339484485606533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59020432530226322990404355 88530648795339484485606533)
  ·
    refine ⟨16599496649126153341051225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88530648795339484485606533 16599496649126153341051225)
    ·
      refine ⟨12449622486844615005788419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16599496649126153341051225 12449622486844615005788419)
      ·
        refine ⟨18674433730266922508682629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12449622486844615005788419 18674433730266922508682629)
        ·
          refine ⟨3501456324425047970377993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18674433730266922508682629 3501456324425047970377993)
          ·
            refine ⟨2626092243318785977783495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3501456324425047970377993 2626092243318785977783495)
            ·
              refine ⟨3939138364978178966675243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626092243318785977783495 3939138364978178966675243)
              ·
                refine ⟨5908707547467268450012865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939138364978178966675243 5908707547467268450012865)
                ·
                  refine ⟨4431530660600451337509649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5908707547467268450012865 4431530660600451337509649)
                  ·
                    refine ⟨3323647995450338503132237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4431530660600451337509649 3323647995450338503132237)
                    ·
                      refine ⟨1246367998293876938674589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3323647995450338503132237 1246367998293876938674589)
                      ·
                        rfl

theorem cell23_2427293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_2427293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427293 prefixEnd_2427293 := by exact prefixLift 2427293
  have htrace : WordTrace (prefixWord ++ tailWord_2427293) baseStart_2427293 baseEnd_2427293 := by
    simpa [prefixWord, tailWord_2427293, baseEnd_2427293] using wordTrace_append hprefix tailTrace_2427293
  have hstable : (prefixWord ++ tailWord_2427293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427293).length < 2 ^ (prefixWord ++ tailWord_2427293).sum := by decide
  have hdescent : baseEnd_2427293 < baseStart_2427293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427322 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_2427322 : Nat := 118140960795 + 2427322 * 2 ^ 59
def prefixEnd_2427322 : Nat := 4983230072969 + 3 ^ 40 * 2427322 * 2
def baseEnd_2427322 : Nat := 415460963077619108403985

theorem tailTrace_2427322 : CollatzResearch.WordTrace tailWord_2427322 prefixEnd_2427322 415460963077619108403985 := by
  unfold tailWord_2427322
  simp only [CollatzResearch.WordTrace]
  refine ⟨22132926628058605609603055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59021137674822948292274813 22132926628058605609603055)
  ·
    refine ⟨33199389942087908414404583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22132926628058605609603055 33199389942087908414404583)
    ·
      refine ⟨49799084913131862621606875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33199389942087908414404583 49799084913131862621606875)
      ·
        refine ⟨74698627369697793932410313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49799084913131862621606875 74698627369697793932410313)
        ·
          refine ⟨56023970527273345449307735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74698627369697793932410313 56023970527273345449307735)
          ·
            refine ⟨84035955790910018173961603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56023970527273345449307735 84035955790910018173961603)
            ·
              refine ⟨126053933686365027260942405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84035955790910018173961603 126053933686365027260942405)
              ·
                refine ⟨23635112566193442611426701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126053933686365027260942405 23635112566193442611426701)
                ·
                  refine ⟨8863167212322540979285013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23635112566193442611426701 8863167212322540979285013)
                  ·
                    refine ⟨415460963077619108403985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8863167212322540979285013 415460963077619108403985)
                    ·
                      rfl

theorem cell23_2427322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_2427322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427322 prefixEnd_2427322 := by exact prefixLift 2427322
  have htrace : WordTrace (prefixWord ++ tailWord_2427322) baseStart_2427322 baseEnd_2427322 := by
    simpa [prefixWord, tailWord_2427322, baseEnd_2427322] using wordTrace_append hprefix tailTrace_2427322
  have hstable : (prefixWord ++ tailWord_2427322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427322).length < 2 ^ (prefixWord ++ tailWord_2427322).sum := by decide
  have hdescent : baseEnd_2427322 < baseStart_2427322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427437 : List Nat := [1, 5, 4, 1, 2, 1, 1, 8]
def baseStart_2427437 : Nat := 118140960795 + 2427437 * 2 ^ 59
def prefixEnd_2427437 : Nat := 4983230072969 + 3 ^ 40 * 2427437 * 2
def baseEnd_2427437 : Nat := 46164516278078680565701

theorem tailTrace_2427437 : CollatzResearch.WordTrace tailWord_2427437 prefixEnd_2427437 46164516278078680565701 := by
  unfold tailWord_2427437
  simp only [CollatzResearch.WordTrace]
  refine ⟨88535900906817797078848565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59023933937878531385899043 88535900906817797078848565)
  ·
    refine ⟨8300240710014168476142053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88535900906817797078848565 8300240710014168476142053)
    ·
      refine ⟨1556295133127656589276635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8300240710014168476142053 1556295133127656589276635)
      ·
        refine ⟨2334442699691484883914953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556295133127656589276635 2334442699691484883914953)
        ·
          refine ⟨1750832024768613662936215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2334442699691484883914953 1750832024768613662936215)
          ·
            refine ⟨2626248037152920494404323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750832024768613662936215 2626248037152920494404323)
            ·
              refine ⟨3939372055729380741606485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626248037152920494404323 3939372055729380741606485)
              ·
                refine ⟨46164516278078680565701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3939372055729380741606485 46164516278078680565701)
                ·
                  rfl

theorem cell23_2427437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 8].length) (baseStart_2427437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427437 prefixEnd_2427437 := by exact prefixLift 2427437
  have htrace : WordTrace (prefixWord ++ tailWord_2427437) baseStart_2427437 baseEnd_2427437 := by
    simpa [prefixWord, tailWord_2427437, baseEnd_2427437] using wordTrace_append hprefix tailTrace_2427437
  have hstable : (prefixWord ++ tailWord_2427437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427437).length < 2 ^ (prefixWord ++ tailWord_2427437).sum := by decide
  have hdescent : baseEnd_2427437 < baseStart_2427437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427446 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2427446 : Nat := 118140960795 + 2427446 * 2 ^ 59
def prefixEnd_2427446 : Nat := 4983230072969 + 3 ^ 40 * 2427446 * 2
def baseEnd_2427446 : Nat := 415482186944671613353795

theorem tailTrace_2427446 : CollatzResearch.WordTrace tailWord_2427446 prefixEnd_2427446 415482186944671613353795 := by
  unfold tailWord_2427446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5533514322736574475995387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59024152775856794410617461 5533514322736574475995387)
  ·
    refine ⟨8300271484104861713993081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5533514322736574475995387 8300271484104861713993081)
    ·
      refine ⟨6225203613078646285494811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8300271484104861713993081 6225203613078646285494811)
      ·
        refine ⟨9337805419617969428242217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6225203613078646285494811 9337805419617969428242217)
        ·
          refine ⟨7003354064713477071181663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9337805419617969428242217 7003354064713477071181663)
          ·
            refine ⟨10505031097070215606772495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7003354064713477071181663 10505031097070215606772495)
            ·
              refine ⟨15757546645605323410158743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10505031097070215606772495 15757546645605323410158743)
              ·
                refine ⟨23636319968407985115238115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15757546645605323410158743 23636319968407985115238115)
                ·
                  refine ⟨35454479952611977672857173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23636319968407985115238115 35454479952611977672857173)
                  ·
                    refine ⟨415482186944671613353795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35454479952611977672857173 415482186944671613353795)
                    ·
                      rfl

theorem cell23_2427446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2427446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427446 prefixEnd_2427446 := by exact prefixLift 2427446
  have htrace : WordTrace (prefixWord ++ tailWord_2427446) baseStart_2427446 baseEnd_2427446 := by
    simpa [prefixWord, tailWord_2427446, baseEnd_2427446] using wordTrace_append hprefix tailTrace_2427446
  have hstable : (prefixWord ++ tailWord_2427446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427446).length < 2 ^ (prefixWord ++ tailWord_2427446).sum := by decide
  have hdescent : baseEnd_2427446 < baseStart_2427446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427453 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_2427453 : Nat := 118140960795 + 2427453 * 2 ^ 59
def prefixEnd_2427453 : Nat := 4983230072969 + 3 ^ 40 * 2427453 * 2
def baseEnd_2427453 : Nat := 1246450155198596312673853

theorem tailTrace_2427453 : CollatzResearch.WordTrace tailWord_2427453 prefixEnd_2427453 1246450155198596312673853 := by
  unfold tailWord_2427453
  simp only [CollatzResearch.WordTrace]
  refine ⟨88536484474759831811431013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59024322983173221207620675 88536484474759831811431013)
  ·
    refine ⟨16600590839017468464643315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88536484474759831811431013 16600590839017468464643315)
    ·
      refine ⟨24900886258526202696964973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16600590839017468464643315 24900886258526202696964973)
      ·
        refine ⟨9337832346947326011361865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24900886258526202696964973 9337832346947326011361865)
        ·
          refine ⟨7003374260210494508521399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9337832346947326011361865 7003374260210494508521399)
          ·
            refine ⟨10505061390315741762782099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7003374260210494508521399 10505061390315741762782099)
            ·
              refine ⟨15757592085473612644173149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10505061390315741762782099 15757592085473612644173149)
              ·
                refine ⟨5909097032052604741564931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15757592085473612644173149 5909097032052604741564931)
                ·
                  refine ⟨8863645548078907112347397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5909097032052604741564931 8863645548078907112347397)
                  ·
                    refine ⟨1661933540264795083565137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8863645548078907112347397 1661933540264795083565137)
                    ·
                      refine ⟨1246450155198596312673853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1661933540264795083565137 1246450155198596312673853)
                      ·
                        rfl

theorem cell23_2427453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_2427453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427453 prefixEnd_2427453 := by exact prefixLift 2427453
  have htrace : WordTrace (prefixWord ++ tailWord_2427453) baseStart_2427453 baseEnd_2427453 := by
    simpa [prefixWord, tailWord_2427453, baseEnd_2427453] using wordTrace_append hprefix tailTrace_2427453
  have hstable : (prefixWord ++ tailWord_2427453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427453).length < 2 ^ (prefixWord ++ tailWord_2427453).sum := by decide
  have hdescent : baseEnd_2427453 < baseStart_2427453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427529 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_2427529 : Nat := 118140960795 + 2427529 * 2 ^ 59
def prefixEnd_2427529 : Nat := 4983230072969 + 3 ^ 40 * 2427529 * 2
def baseEnd_2427529 : Nat := 1246489179728338015323503

theorem tailTrace_2427529 : CollatzResearch.WordTrace tailWord_2427529 prefixEnd_2427529 1246489179728338015323503 := by
  unfold tailWord_2427529
  simp only [CollatzResearch.WordTrace]
  refine ⟨88539256422484496791197641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59026170948322997860798427 88539256422484496791197641)
  ·
    refine ⟨66404442316863372593398231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88539256422484496791197641 66404442316863372593398231)
    ·
      refine ⟨99606663475295058890097347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66404442316863372593398231 99606663475295058890097347)
      ·
        refine ⟨149409995212942588335146021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99606663475295058890097347 149409995212942588335146021)
        ·
          refine ⟨28014374102426735312839879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149409995212942588335146021 28014374102426735312839879)
          ·
            refine ⟨42021561153640102969259819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28014374102426735312839879 42021561153640102969259819)
            ·
              refine ⟨63032341730460154453889729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42021561153640102969259819 63032341730460154453889729)
              ·
                refine ⟨47274256297845115840417297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63032341730460154453889729 47274256297845115840417297)
                ·
                  refine ⟨35455692223383836880312973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47274256297845115840417297 35455692223383836880312973)
                  ·
                    refine ⟨13295884583768938830117365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35455692223383836880312973 13295884583768938830117365)
                    ·
                      refine ⟨1246489179728338015323503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13295884583768938830117365 1246489179728338015323503)
                      ·
                        rfl

theorem cell23_2427529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_2427529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427529 prefixEnd_2427529 := by exact prefixLift 2427529
  have htrace : WordTrace (prefixWord ++ tailWord_2427529) baseStart_2427529 baseEnd_2427529 := by
    simpa [prefixWord, tailWord_2427529, baseEnd_2427529] using wordTrace_append hprefix tailTrace_2427529
  have hstable : (prefixWord ++ tailWord_2427529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427529).length < 2 ^ (prefixWord ++ tailWord_2427529).sum := by decide
  have hdescent : baseEnd_2427529 < baseStart_2427529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427539 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 4]
def baseStart_2427539 : Nat := 118140960795 + 2427539 * 2 ^ 59
def prefixEnd_2427539 : Nat := 4983230072969 + 3 ^ 40 * 2427539 * 2
def baseEnd_2427539 : Nat := 1246494314534882976198457

theorem tailTrace_2427539 : CollatzResearch.WordTrace tailWord_2427539 prefixEnd_2427539 1246494314534882976198457 := by
  unfold tailWord_2427539
  simp only [CollatzResearch.WordTrace]
  refine ⟨88539621152448268499061671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59026414101632178999374447 88539621152448268499061671)
  ·
    refine ⟨132809431728672402748592507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88539621152448268499061671 132809431728672402748592507)
    ·
      refine ⟨199214147593008604122888761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132809431728672402748592507 199214147593008604122888761)
      ·
        refine ⟨149410610694756453092166571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199214147593008604122888761 149410610694756453092166571)
        ·
          refine ⟨224115916042134679638249857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149410610694756453092166571 224115916042134679638249857)
          ·
            refine ⟨168086937031601009728687393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224115916042134679638249857 168086937031601009728687393)
            ·
              refine ⟨126065202773700757296515545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168086937031601009728687393 126065202773700757296515545)
              ·
                refine ⟨94548902080275567972386659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126065202773700757296515545 94548902080275567972386659)
                ·
                  refine ⟨141823353120413351958579989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94548902080275567972386659 141823353120413351958579989)
                  ·
                    refine ⟨6647969677519375873058437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141823353120413351958579989 6647969677519375873058437)
                    ·
                      refine ⟨1246494314534882976198457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6647969677519375873058437 1246494314534882976198457)
                      ·
                        rfl

theorem cell23_2427539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_2427539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427539 prefixEnd_2427539 := by exact prefixLift 2427539
  have htrace : WordTrace (prefixWord ++ tailWord_2427539) baseStart_2427539 baseEnd_2427539 := by
    simpa [prefixWord, tailWord_2427539, baseEnd_2427539] using wordTrace_append hprefix tailTrace_2427539
  have hstable : (prefixWord ++ tailWord_2427539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427539).length < 2 ^ (prefixWord ++ tailWord_2427539).sum := by decide
  have hdescent : baseEnd_2427539 < baseStart_2427539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427633 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 4]
def baseStart_2427633 : Nat := 118140960795 + 2427633 * 2 ^ 59
def prefixEnd_2427633 : Nat := 4983230072969 + 3 ^ 40 * 2427633 * 2
def baseEnd_2427633 : Nat := 1246542581716405608423025

theorem tailTrace_2427633 : CollatzResearch.WordTrace tailWord_2427633 prefixEnd_2427633 1246542581716405608423025 := by
  unfold tailWord_2427633
  simp only [CollatzResearch.WordTrace]
  refine ⟨88543049614107722552983553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59028699742738481701989035 88543049614107722552983553)
  ·
    refine ⟨66407287210580791914737665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88543049614107722552983553 66407287210580791914737665)
    ·
      refine ⟨49805465407935593936053249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66407287210580791914737665 49805465407935593936053249)
      ·
        refine ⟨37354099055951695452039937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49805465407935593936053249 37354099055951695452039937)
        ·
          refine ⟨28015574291963771589029953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37354099055951695452039937 28015574291963771589029953)
          ·
            refine ⟨21011680718972828691772465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28015574291963771589029953 21011680718972828691772465)
            ·
              refine ⟨15758760539229621518829349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21011680718972828691772465 15758760539229621518829349)
              ·
                refine ⟨2954767601105554034780503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15758760539229621518829349 2954767601105554034780503)
                ·
                  refine ⟨4432151401658331052170755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954767601105554034780503 4432151401658331052170755)
                  ·
                    refine ⟨6648227102487496578256133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4432151401658331052170755 6648227102487496578256133)
                    ·
                      refine ⟨1246542581716405608423025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6648227102487496578256133 1246542581716405608423025)
                      ·
                        rfl

theorem cell23_2427633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_2427633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427633 prefixEnd_2427633 := by exact prefixLift 2427633
  have htrace : WordTrace (prefixWord ++ tailWord_2427633) baseStart_2427633 baseEnd_2427633 := by
    simpa [prefixWord, tailWord_2427633, baseEnd_2427633] using wordTrace_append hprefix tailTrace_2427633
  have hstable : (prefixWord ++ tailWord_2427633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427633).length < 2 ^ (prefixWord ++ tailWord_2427633).sum := by decide
  have hdescent : baseEnd_2427633 < baseStart_2427633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427656 : List Nat := [2, 1, 3, 2, 2, 3, 10]
def baseStart_2427656 : Nat := 118140960795 + 2427656 * 2 ^ 59
def prefixEnd_2427656 : Nat := 4983230072969 + 3 ^ 40 * 2427656 * 2
def baseEnd_2427656 : Nat := 15389560392240234795499

theorem tailTrace_2427656 : CollatzResearch.WordTrace tailWord_2427656 prefixEnd_2427656 15389560392240234795499 := by
  unfold tailWord_2427656
  simp only [CollatzResearch.WordTrace]
  refine ⟨44271944246512198740535411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59029258995349598320713881 44271944246512198740535411)
  ·
    refine ⟨66407916369768298110803117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44271944246512198740535411 66407916369768298110803117)
    ·
      refine ⟨24902968638663111791551169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66407916369768298110803117 24902968638663111791551169)
      ·
        refine ⟨18677226478997333843663377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24902968638663111791551169 18677226478997333843663377)
        ·
          refine ⟨14007919859248000382747533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18677226478997333843663377 14007919859248000382747533)
          ·
            refine ⟨5252969947218000143530325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14007919859248000382747533 5252969947218000143530325)
            ·
              refine ⟨15389560392240234795499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5252969947218000143530325 15389560392240234795499)
              ·
                rfl

theorem cell23_2427656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 10].length) (baseStart_2427656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427656 prefixEnd_2427656 := by exact prefixLift 2427656
  have htrace : WordTrace (prefixWord ++ tailWord_2427656) baseStart_2427656 baseEnd_2427656 := by
    simpa [prefixWord, tailWord_2427656, baseEnd_2427656] using wordTrace_append hprefix tailTrace_2427656
  have hstable : (prefixWord ++ tailWord_2427656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427656).length < 2 ^ (prefixWord ++ tailWord_2427656).sum := by decide
  have hdescent : baseEnd_2427656 < baseStart_2427656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427667 : List Nat := [1, 1, 1, 2, 1, 3, 3, 6, 1, 2, 2]
def baseStart_2427667 : Nat := 118140960795 + 2427667 * 2 ^ 59
def prefixEnd_2427667 : Nat := 4983230072969 + 3 ^ 40 * 2427667 * 2
def baseEnd_2427667 : Nat := 1246560040058658475397869

theorem tailTrace_2427667 : CollatzResearch.WordTrace tailWord_2427667 prefixEnd_2427667 1246560040058658475397869 := by
  unfold tailWord_2427667
  simp only [CollatzResearch.WordTrace]
  refine ⟨88544289695984546359721255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59029526463989697573147503 88544289695984546359721255)
  ·
    refine ⟨132816434543976819539581883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88544289695984546359721255 132816434543976819539581883)
    ·
      refine ⟨199224651815965229309372825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132816434543976819539581883 199224651815965229309372825)
      ·
        refine ⟨149418488861973921982029619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199224651815965229309372825 149418488861973921982029619)
        ·
          refine ⟨224127733292960882973044429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149418488861973921982029619 224127733292960882973044429)
          ·
            refine ⟨84047899984860331114891661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224127733292960882973044429 84047899984860331114891661)
            ·
              refine ⟨31517962494322624168084373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84047899984860331114891661 31517962494322624168084373)
              ·
                refine ⟨1477404491921373007878955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31517962494322624168084373 1477404491921373007878955)
                ·
                  refine ⟨2216106737882059511818433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477404491921373007878955 2216106737882059511818433)
                  ·
                    refine ⟨1662080053411544633863825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2216106737882059511818433 1662080053411544633863825)
                    ·
                      refine ⟨1246560040058658475397869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662080053411544633863825 1246560040058658475397869)
                      ·
                        rfl

theorem cell23_2427667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 2, 2].length) (baseStart_2427667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427667 prefixEnd_2427667 := by exact prefixLift 2427667
  have htrace : WordTrace (prefixWord ++ tailWord_2427667) baseStart_2427667 baseEnd_2427667 := by
    simpa [prefixWord, tailWord_2427667, baseEnd_2427667] using wordTrace_append hprefix tailTrace_2427667
  have hstable : (prefixWord ++ tailWord_2427667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427667).length < 2 ^ (prefixWord ++ tailWord_2427667).sum := by decide
  have hdescent : baseEnd_2427667 < baseStart_2427667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427677 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2427677 : Nat := 118140960795 + 2427677 * 2 ^ 59
def prefixEnd_2427677 : Nat := 4983230072969 + 3 ^ 40 * 2427677 * 2
def baseEnd_2427677 : Nat := 415521724955067812090941

theorem tailTrace_2427677 : CollatzResearch.WordTrace tailWord_2427677 prefixEnd_2427677 415521724955067812090941 := by
  unfold tailWord_2427677
  simp only [CollatzResearch.WordTrace]
  refine ⟨88544654425948318067585285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59029769617298878711723523 88544654425948318067585285)
  ·
    refine ⟨16602122704865309637672241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88544654425948318067585285 16602122704865309637672241)
    ·
      refine ⟨12451592028648982228254181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16602122704865309637672241 12451592028648982228254181)
      ·
        refine ⟨2334673505371684167797659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12451592028648982228254181 2334673505371684167797659)
        ·
          refine ⟨3502010258057526251696489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334673505371684167797659 3502010258057526251696489)
          ·
            refine ⟨2626507693543144688772367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3502010258057526251696489 2626507693543144688772367)
            ·
              refine ⟨3939761540314717033158551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626507693543144688772367 3939761540314717033158551)
              ·
                refine ⟨5909642310472075549737827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939761540314717033158551 5909642310472075549737827)
                ·
                  refine ⟨8864463465708113324606741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5909642310472075549737827 8864463465708113324606741)
                  ·
                    refine ⟨415521724955067812090941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8864463465708113324606741 415521724955067812090941)
                    ·
                      rfl

theorem cell23_2427677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2427677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427677 prefixEnd_2427677 := by exact prefixLift 2427677
  have htrace : WordTrace (prefixWord ++ tailWord_2427677) baseStart_2427677 baseEnd_2427677 := by
    simpa [prefixWord, tailWord_2427677, baseEnd_2427677] using wordTrace_append hprefix tailTrace_2427677
  have hstable : (prefixWord ++ tailWord_2427677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427677).length < 2 ^ (prefixWord ++ tailWord_2427677).sum := by decide
  have hdescent : baseEnd_2427677 < baseStart_2427677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427680 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2427680 : Nat := 118140960795 + 2427680 * 2 ^ 59
def prefixEnd_2427680 : Nat := 4983230072969 + 3 ^ 40 * 2427680 * 2
def baseEnd_2427680 : Nat := 1246566715307166924535309

theorem tailTrace_2427680 : CollatzResearch.WordTrace tailWord_2427680 prefixEnd_2427680 1246566715307166924535309 := by
  unfold tailWord_2427680
  simp only [CollatzResearch.WordTrace]
  refine ⟨44272381922468724789972247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59029842563291633053296329 44272381922468724789972247)
  ·
    refine ⟨66408572883703087184958371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44272381922468724789972247 66408572883703087184958371)
    ·
      refine ⟨99612859325554630777437557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66408572883703087184958371 99612859325554630777437557)
      ·
        refine ⟨9338705561770746635384771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99612859325554630777437557 9338705561770746635384771)
        ·
          refine ⟨14008058342656119953077157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9338705561770746635384771 14008058342656119953077157)
          ·
            refine ⟨2626510939248022491201967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14008058342656119953077157 2626510939248022491201967)
            ·
              refine ⟨3939766408872033736802951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626510939248022491201967 3939766408872033736802951)
              ·
                refine ⟨5909649613308050605204427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939766408872033736802951 5909649613308050605204427)
                ·
                  refine ⟨8864474419962075907806641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5909649613308050605204427 8864474419962075907806641)
                  ·
                    refine ⟨6648355814971556930854981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8864474419962075907806641 6648355814971556930854981)
                    ·
                      refine ⟨1246566715307166924535309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6648355814971556930854981 1246566715307166924535309)
                      ·
                        rfl

theorem cell23_2427680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2427680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427680 prefixEnd_2427680 := by exact prefixLift 2427680
  have htrace : WordTrace (prefixWord ++ tailWord_2427680) baseStart_2427680 baseEnd_2427680 := by
    simpa [prefixWord, tailWord_2427680, baseEnd_2427680] using wordTrace_append hprefix tailTrace_2427680
  have hstable : (prefixWord ++ tailWord_2427680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427680).length < 2 ^ (prefixWord ++ tailWord_2427680).sum := by decide
  have hdescent : baseEnd_2427680 < baseStart_2427680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427690 : List Nat := [3, 1, 4, 3, 1, 1, 1, 9]
def baseStart_2427690 : Nat := 118140960795 + 2427690 * 2 ^ 59
def prefixEnd_2427690 : Nat := 4983230072969 + 3 ^ 40 * 2427690 * 2
def baseEnd_2427690 : Nat := 46169327781989329089269

theorem tailTrace_2427690 : CollatzResearch.WordTrace tailWord_2427690 prefixEnd_2427690 46169327781989329089269 := by
  unfold tailWord_2427690
  simp only [CollatzResearch.WordTrace]
  refine ⟨22136282143725305321952131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59030085716600814191872349 22136282143725305321952131)
  ·
    refine ⟨33204423215587957982928197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22136282143725305321952131 33204423215587957982928197)
    ·
      refine ⟨6225829352922742121799037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33204423215587957982928197 6225829352922742121799037)
      ·
        refine ⟨2334686007346028295674639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6225829352922742121799037 2334686007346028295674639)
        ·
          refine ⟨3502029011019042443511959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334686007346028295674639 3502029011019042443511959)
          ·
            refine ⟨5253043516528563665267939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502029011019042443511959 5253043516528563665267939)
            ·
              refine ⟨7879565274792845497901909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253043516528563665267939 7879565274792845497901909)
              ·
                refine ⟨46169327781989329089269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7879565274792845497901909 46169327781989329089269)
                ·
                  rfl

theorem cell23_2427690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 9].length) (baseStart_2427690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427690 prefixEnd_2427690 := by exact prefixLift 2427690
  have htrace : WordTrace (prefixWord ++ tailWord_2427690) baseStart_2427690 baseEnd_2427690 := by
    simpa [prefixWord, tailWord_2427690, baseEnd_2427690] using wordTrace_append hprefix tailTrace_2427690
  have hstable : (prefixWord ++ tailWord_2427690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427690).length < 2 ^ (prefixWord ++ tailWord_2427690).sum := by decide
  have hdescent : baseEnd_2427690 < baseStart_2427690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427701 : List Nat := [1, 3, 3, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_2427701 : Nat := 118140960795 + 2427701 * 2 ^ 59
def prefixEnd_2427701 : Nat := 4983230072969 + 3 ^ 40 * 2427701 * 2
def baseEnd_2427701 : Nat := 1246577498400911342372713

theorem tailTrace_2427701 : CollatzResearch.WordTrace tailWord_2427701 prefixEnd_2427701 1246577498400911342372713 := by
  unfold tailWord_2427701
  simp only [CollatzResearch.WordTrace]
  refine ⟨88545529777861370166458957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59030353185240913444305971 88545529777861370166458957)
  ·
    refine ⟨33204573666698013812422109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88545529777861370166458957 33204573666698013812422109)
    ·
      refine ⟨12451715125011755179658291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33204573666698013812422109 12451715125011755179658291)
      ·
        refine ⟨18677572687517632769487437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12451715125011755179658291 18677572687517632769487437)
        ·
          refine ⟨7004089757819112288557789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18677572687517632769487437 7004089757819112288557789)
          ·
            refine ⟨2626533659182167108209171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7004089757819112288557789 2626533659182167108209171)
            ·
              refine ⟨3939800488773250662313757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626533659182167108209171 3939800488773250662313757)
              ·
                refine ⟨1477425183289968998367659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3939800488773250662313757 1477425183289968998367659)
                ·
                  refine ⟨2216137774934953497551489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477425183289968998367659 2216137774934953497551489)
                  ·
                    refine ⟨1662103331201215123163617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2216137774934953497551489 1662103331201215123163617)
                    ·
                      refine ⟨1246577498400911342372713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662103331201215123163617 1246577498400911342372713)
                      ·
                        rfl

theorem cell23_2427701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_2427701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427701 prefixEnd_2427701 := by exact prefixLift 2427701
  have htrace : WordTrace (prefixWord ++ tailWord_2427701) baseStart_2427701 baseEnd_2427701 := by
    simpa [prefixWord, tailWord_2427701, baseEnd_2427701] using wordTrace_append hprefix tailTrace_2427701
  have hstable : (prefixWord ++ tailWord_2427701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427701).length < 2 ^ (prefixWord ++ tailWord_2427701).sum := by decide
  have hdescent : baseEnd_2427701 < baseStart_2427701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427718 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2427718 : Nat := 118140960795 + 2427718 * 2 ^ 59
def prefixEnd_2427718 : Nat := 4983230072969 + 3 ^ 40 * 2427718 * 2
def baseEnd_2427718 : Nat := 1246586227572037775860135

theorem tailTrace_2427718 : CollatzResearch.WordTrace tailWord_2427718 prefixEnd_2427718 1246586227572037775860135 := by
  unfold tailWord_2427718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2767067181837493189682119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59030766545866521379885205 2767067181837493189682119)
  ·
    refine ⟨4150600772756239784523179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2767067181837493189682119 4150600772756239784523179)
    ·
      refine ⟨6225901159134359676784769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4150600772756239784523179 6225901159134359676784769)
      ·
        refine ⟨4669425869350769757588577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6225901159134359676784769 4669425869350769757588577)
        ·
          refine ⟨3502069402013077318191433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4669425869350769757588577 3502069402013077318191433)
          ·
            refine ⟨2626552051509807988643575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3502069402013077318191433 2626552051509807988643575)
            ·
              refine ⟨3939828077264711982965363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626552051509807988643575 3939828077264711982965363)
              ·
                refine ⟨5909742115897067974448045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939828077264711982965363 5909742115897067974448045)
                ·
                  refine ⟨2216153293461400490418017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5909742115897067974448045 2216153293461400490418017)
                  ·
                    refine ⟨1662114970096050367813513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2216153293461400490418017 1662114970096050367813513)
                    ·
                      refine ⟨1246586227572037775860135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662114970096050367813513 1246586227572037775860135)
                      ·
                        rfl

theorem cell23_2427718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2427718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427718 prefixEnd_2427718 := by exact prefixLift 2427718
  have htrace : WordTrace (prefixWord ++ tailWord_2427718) baseStart_2427718 baseEnd_2427718 := by
    simpa [prefixWord, tailWord_2427718, baseEnd_2427718] using wordTrace_append hprefix tailTrace_2427718
  have hstable : (prefixWord ++ tailWord_2427718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427718).length < 2 ^ (prefixWord ++ tailWord_2427718).sum := by decide
  have hdescent : baseEnd_2427718 < baseStart_2427718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427736 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2427736 : Nat := 118140960795 + 2427736 * 2 ^ 59
def prefixEnd_2427736 : Nat := 4983230072969 + 3 ^ 40 * 2427736 * 2
def baseEnd_2427736 : Nat := 1246595470223818705435051

theorem tailTrace_2427736 : CollatzResearch.WordTrace tailWord_2427736 prefixEnd_2427736 1246595470223818705435051 := by
  unfold tailWord_2427736
  simp only [CollatzResearch.WordTrace]
  refine ⟨44273403166367285571991531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59031204221823047429322041 44273403166367285571991531)
  ·
    refine ⟨66410104749550928357987297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44273403166367285571991531 66410104749550928357987297)
    ·
      refine ⟨49807578562163196268490473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66410104749550928357987297 49807578562163196268490473)
      ·
        refine ⟨37355683921622397201367855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49807578562163196268490473 37355683921622397201367855)
        ·
          refine ⟨56033525882433595802051783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37355683921622397201367855 56033525882433595802051783)
          ·
            refine ⟨84050288823650393703077675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56033525882433595802051783 84050288823650393703077675)
            ·
              refine ⟨126075433235475590554616513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84050288823650393703077675 126075433235475590554616513)
              ·
                refine ⟨94556574926606692915962385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126075433235475590554616513 94556574926606692915962385)
                ·
                  refine ⟨70917431194955019686971789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94556574926606692915962385 70917431194955019686971789)
                  ·
                    refine ⟨26594036698108132382614421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70917431194955019686971789 26594036698108132382614421)
                    ·
                      refine ⟨1246595470223818705435051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26594036698108132382614421 1246595470223818705435051)
                      ·
                        rfl

theorem cell23_2427736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2427736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427736 prefixEnd_2427736 := by exact prefixLift 2427736
  have htrace : WordTrace (prefixWord ++ tailWord_2427736) baseStart_2427736 baseEnd_2427736 := by
    simpa [prefixWord, tailWord_2427736, baseEnd_2427736] using wordTrace_append hprefix tailTrace_2427736
  have hstable : (prefixWord ++ tailWord_2427736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427736).length < 2 ^ (prefixWord ++ tailWord_2427736).sum := by decide
  have hdescent : baseEnd_2427736 < baseStart_2427736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427810 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2427810 : Nat := 118140960795 + 2427810 * 2 ^ 59
def prefixEnd_2427810 : Nat := 4983230072969 + 3 ^ 40 * 2427810 * 2
def baseEnd_2427810 : Nat := 415544489264083805303237

theorem tailTrace_2427810 : CollatzResearch.WordTrace tailWord_2427810 prefixEnd_2427810 415544489264083805303237 := by
  unfold tailWord_2427810
  simp only [CollatzResearch.WordTrace]
  refine ⟨22137376333616620445544221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59033003556310987854784589 22137376333616620445544221)
  ·
    refine ⟨8301516125106232667079083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22137376333616620445544221 8301516125106232667079083)
    ·
      refine ⟨12452274187659349000618625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8301516125106232667079083 12452274187659349000618625)
      ·
        refine ⟨9339205640744511750463969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12452274187659349000618625 9339205640744511750463969)
        ·
          refine ⟨7004404230558383812847977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9339205640744511750463969 7004404230558383812847977)
          ·
            refine ⟨5253303172918787859635983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7004404230558383812847977 5253303172918787859635983)
            ·
              refine ⟨7879954759378181789453975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253303172918787859635983 7879954759378181789453975)
              ·
                refine ⟨11819932139067272684180963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7879954759378181789453975 11819932139067272684180963)
                ·
                  refine ⟨17729898208600909026271445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11819932139067272684180963 17729898208600909026271445)
                  ·
                    refine ⟨415544489264083805303237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17729898208600909026271445 415544489264083805303237)
                    ·
                      rfl

theorem cell23_2427810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2427810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427810 prefixEnd_2427810 := by exact prefixLift 2427810
  have htrace : WordTrace (prefixWord ++ tailWord_2427810) baseStart_2427810 baseEnd_2427810 := by
    simpa [prefixWord, tailWord_2427810, baseEnd_2427810] using wordTrace_append hprefix tailTrace_2427810
  have hstable : (prefixWord ++ tailWord_2427810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427810).length < 2 ^ (prefixWord ++ tailWord_2427810).sum := by decide
  have hdescent : baseEnd_2427810 < baseStart_2427810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427840 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 3, 4]
def baseStart_2427840 : Nat := 118140960795 + 2427840 * 2 ^ 59
def prefixEnd_2427840 : Nat := 4983230072969 + 3 ^ 40 * 2427840 * 2
def baseEnd_2427840 : Nat := 415549624070628766178191

theorem tailTrace_2427840 : CollatzResearch.WordTrace tailWord_2427840 prefixEnd_2427840 415549624070628766178191 := by
  unfold tailWord_2427840
  simp only [CollatzResearch.WordTrace]
  refine ⟨44275299762178898452884487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59033733016238531270512649 44275299762178898452884487)
  ·
    refine ⟨66412949643268347679326731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44275299762178898452884487 66412949643268347679326731)
    ·
      refine ⟨99619424464902521518990097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66412949643268347679326731 99619424464902521518990097)
      ·
        refine ⟨74714568348676891139242573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99619424464902521518990097 74714568348676891139242573)
        ·
          refine ⟨28017963130753834177215965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74714568348676891139242573 28017963130753834177215965)
          ·
            refine ⟨10506736174032687816455987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28017963130753834177215965 10506736174032687816455987)
            ·
              refine ⟨15760104261049031724683981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10506736174032687816455987 15760104261049031724683981)
              ·
                refine ⟨5910039097893386896756493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15760104261049031724683981 5910039097893386896756493)
                ·
                  refine ⟨2216264661710020086283685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5910039097893386896756493 2216264661710020086283685)
                  ·
                    refine ⟨415549624070628766178191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2216264661710020086283685 415549624070628766178191)
                    ·
                      rfl

theorem cell23_2427840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 4].length) (baseStart_2427840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427840 prefixEnd_2427840 := by exact prefixLift 2427840
  have htrace : WordTrace (prefixWord ++ tailWord_2427840) baseStart_2427840 baseEnd_2427840 := by
    simpa [prefixWord, tailWord_2427840, baseEnd_2427840] using wordTrace_append hprefix tailTrace_2427840
  have hstable : (prefixWord ++ tailWord_2427840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427840).length < 2 ^ (prefixWord ++ tailWord_2427840).sum := by decide
  have hdescent : baseEnd_2427840 < baseStart_2427840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427883 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 7, 5]
def baseStart_2427883 : Nat := 118140960795 + 2427883 * 2 ^ 59
def prefixEnd_2427883 : Nat := 4983230072969 + 3 ^ 40 * 2427883 * 2
def baseEnd_2427883 : Nat := 415556983960009876765625

theorem tailTrace_2427883 : CollatzResearch.WordTrace tailWord_2427883 prefixEnd_2427883 415556983960009876765625 := by
  unfold tailWord_2427883
  simp only [CollatzResearch.WordTrace]
  refine ⟨88552167863202015249584303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59034778575468010166389535 88552167863202015249584303)
  ·
    refine ⟨132828251794803022874376455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88552167863202015249584303 132828251794803022874376455)
    ·
      refine ⟨199242377692204534311564683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132828251794803022874376455 199242377692204534311564683)
      ·
        refine ⟨298863566538306801467347025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199242377692204534311564683 298863566538306801467347025)
        ·
          refine ⟨224147674903730101100510269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298863566538306801467347025 224147674903730101100510269)
          ·
            refine ⟨84055378088898787912691351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224147674903730101100510269 84055378088898787912691351)
            ·
              refine ⟨126083067133348181869037027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84055378088898787912691351 126083067133348181869037027)
              ·
                refine ⟨189124600700022272803555541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126083067133348181869037027 189124600700022272803555541)
                ·
                  refine ⟨4432607828906772018833333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 189124600700022272803555541 4432607828906772018833333)
                  ·
                    refine ⟨415556983960009876765625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4432607828906772018833333 415556983960009876765625)
                    ·
                      rfl

theorem cell23_2427883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 5].length) (baseStart_2427883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427883 prefixEnd_2427883 := by exact prefixLift 2427883
  have htrace : WordTrace (prefixWord ++ tailWord_2427883) baseStart_2427883 baseEnd_2427883 := by
    simpa [prefixWord, tailWord_2427883, baseEnd_2427883] using wordTrace_append hprefix tailTrace_2427883
  have hstable : (prefixWord ++ tailWord_2427883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427883).length < 2 ^ (prefixWord ++ tailWord_2427883).sum := by decide
  have hdescent : baseEnd_2427883 < baseStart_2427883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427903 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_2427903 : Nat := 118140960795 + 2427903 * 2 ^ 59
def prefixEnd_2427903 : Nat := 4983230072969 + 3 ^ 40 * 2427903 * 2
def baseEnd_2427903 : Nat := 1246681221493119552046783

theorem tailTrace_2427903 : CollatzResearch.WordTrace tailWord_2427903 prefixEnd_2427903 1246681221493119552046783 := by
  unfold tailWord_2427903
  simp only [CollatzResearch.WordTrace]
  refine ⟨88552897323129558665312363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59035264882086372443541575 88552897323129558665312363)
  ·
    refine ⟨132829345984694337997968545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88552897323129558665312363 132829345984694337997968545)
    ·
      refine ⟨99622009488520753498476409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132829345984694337997968545 99622009488520753498476409)
      ·
        refine ⟨74716507116390565123857307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99622009488520753498476409 74716507116390565123857307)
        ·
          refine ⟨112074760674585847685785961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74716507116390565123857307 112074760674585847685785961)
          ·
            refine ⟨84056070505939385764339471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112074760674585847685785961 84056070505939385764339471)
            ·
              refine ⟨126084105758909078646509207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84056070505939385764339471 126084105758909078646509207)
              ·
                refine ⟨189126158638363617969763811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126084105758909078646509207 189126158638363617969763811)
                ·
                  refine ⟨283689237957545426954645717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189126158638363617969763811 283689237957545426954645717)
                  ·
                    refine ⟨6648966514629970944249509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 283689237957545426954645717 6648966514629970944249509)
                    ·
                      refine ⟨1246681221493119552046783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6648966514629970944249509 1246681221493119552046783)
                      ·
                        rfl

theorem cell23_2427903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_2427903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427903 prefixEnd_2427903 := by exact prefixLift 2427903
  have htrace : WordTrace (prefixWord ++ tailWord_2427903) baseStart_2427903 baseEnd_2427903 := by
    simpa [prefixWord, tailWord_2427903, baseEnd_2427903] using wordTrace_append hprefix tailTrace_2427903
  have hstable : (prefixWord ++ tailWord_2427903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427903).length < 2 ^ (prefixWord ++ tailWord_2427903).sum := by decide
  have hdescent : baseEnd_2427903 < baseStart_2427903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427913 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 5, 6]
def baseStart_2427913 : Nat := 118140960795 + 2427913 * 2 ^ 59
def prefixEnd_2427913 : Nat := 4983230072969 + 3 ^ 40 * 2427913 * 2
def baseEnd_2427913 : Nat := 415562118766554837640579

theorem tailTrace_2427913 : CollatzResearch.WordTrace tailWord_2427913 prefixEnd_2427913 415562118766554837640579 := by
  unfold tailWord_2427913
  simp only [CollatzResearch.WordTrace]
  refine ⟨88553262053093330373176393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59035508035395553582117595 88553262053093330373176393)
  ·
    refine ⟨66414946539819997779882295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88553262053093330373176393 66414946539819997779882295)
    ·
      refine ⟨99622419809729996669823443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66414946539819997779882295 99622419809729996669823443)
      ·
        refine ⟨149433629714594995004735165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99622419809729996669823443 149433629714594995004735165)
        ·
          refine ⟨56037611142973123126775687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149433629714594995004735165 56037611142973123126775687)
          ·
            refine ⟨84056416714459684690163531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56037611142973123126775687 84056416714459684690163531)
            ·
              refine ⟨126084625071689527035245297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84056416714459684690163531 126084625071689527035245297)
              ·
                refine ⟨94563468803767145276433973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126084625071689527035245297 94563468803767145276433973)
                ·
                  refine ⟨8865325200353169869665685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94563468803767145276433973 8865325200353169869665685)
                  ·
                    refine ⟨415562118766554837640579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8865325200353169869665685 415562118766554837640579)
                    ·
                      rfl

theorem cell23_2427913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_2427913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427913 prefixEnd_2427913 := by exact prefixLift 2427913
  have htrace : WordTrace (prefixWord ++ tailWord_2427913) baseStart_2427913 baseEnd_2427913 := by
    simpa [prefixWord, tailWord_2427913, baseEnd_2427913] using wordTrace_append hprefix tailTrace_2427913
  have hstable : (prefixWord ++ tailWord_2427913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427913).length < 2 ^ (prefixWord ++ tailWord_2427913).sum := by decide
  have hdescent : baseEnd_2427913 < baseStart_2427913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427930 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_2427930 : Nat := 118140960795 + 2427930 * 2 ^ 59
def prefixEnd_2427930 : Nat := 4983230072969 + 3 ^ 40 * 2427930 * 2
def baseEnd_2427930 : Nat := 415565028490263648803053

theorem tailTrace_2427930 : CollatzResearch.WordTrace tailWord_2427930 prefixEnd_2427930 415565028490263648803053 := by
  unfold tailWord_2427930
  simp only [CollatzResearch.WordTrace]
  refine ⟨22138470523507935569136311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59035921396021161517696829 22138470523507935569136311)
  ·
    refine ⟨33207705785261903353704467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22138470523507935569136311 33207705785261903353704467)
    ·
      refine ⟨49811558677892855030556701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33207705785261903353704467 49811558677892855030556701)
      ·
        refine ⟨18679334504209820636458763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49811558677892855030556701 18679334504209820636458763)
        ·
          refine ⟨28019001756314730954688145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18679334504209820636458763 28019001756314730954688145)
          ·
            refine ⟨21014251317236048216016109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28019001756314730954688145 21014251317236048216016109)
            ·
              refine ⟨7880344243963518081006041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21014251317236048216016109 7880344243963518081006041)
              ·
                refine ⟨5910258182972638560754531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7880344243963518081006041 5910258182972638560754531)
                ·
                  refine ⟨8865387274458957841131797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5910258182972638560754531 8865387274458957841131797)
                  ·
                    refine ⟨415565028490263648803053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8865387274458957841131797 415565028490263648803053)
                    ·
                      rfl

theorem cell23_2427930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_2427930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427930 prefixEnd_2427930 := by exact prefixLift 2427930
  have htrace : WordTrace (prefixWord ++ tailWord_2427930) baseStart_2427930 baseEnd_2427930 := by
    simpa [prefixWord, tailWord_2427930, baseEnd_2427930] using wordTrace_append hprefix tailTrace_2427930
  have hstable : (prefixWord ++ tailWord_2427930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427930).length < 2 ^ (prefixWord ++ tailWord_2427930).sum := by decide
  have hdescent : baseEnd_2427930 < baseStart_2427930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427947 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 2, 4]
def baseStart_2427947 : Nat := 118140960795 + 2427947 * 2 ^ 59
def prefixEnd_2427947 : Nat := 4983230072969 + 3 ^ 40 * 2427947 * 2
def baseEnd_2427947 : Nat := 415567938213972459965527

theorem tailTrace_2427947 : CollatzResearch.WordTrace tailWord_2427947 prefixEnd_2427947 415567938213972459965527 := by
  unfold tailWord_2427947
  simp only [CollatzResearch.WordTrace]
  refine ⟨88554502134970154179914095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59036334756646769453276063 88554502134970154179914095)
  ·
    refine ⟨132831753202455231269871143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88554502134970154179914095 132831753202455231269871143)
    ·
      refine ⟨199247629803682846904806715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132831753202455231269871143 199247629803682846904806715)
      ·
        refine ⟨298871444705524270357210073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199247629803682846904806715 298871444705524270357210073)
        ·
          refine ⟨224153583529143202767907555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298871444705524270357210073 224153583529143202767907555)
          ·
            refine ⟨336230375293714804151861333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224153583529143202767907555 336230375293714804151861333)
            ·
              refine ⟨3940199710473220361154625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 336230375293714804151861333 3940199710473220361154625)
              ·
                refine ⟨2955149782854915270865969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940199710473220361154625 2955149782854915270865969)
                ·
                  refine ⟨2216362337141186453149477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2955149782854915270865969 2216362337141186453149477)
                  ·
                    refine ⟨415567938213972459965527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2216362337141186453149477 415567938213972459965527)
                    ·
                      rfl

theorem cell23_2427947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 4].length) (baseStart_2427947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427947 prefixEnd_2427947 := by exact prefixLift 2427947
  have htrace : WordTrace (prefixWord ++ tailWord_2427947) baseStart_2427947 baseEnd_2427947 := by
    simpa [prefixWord, tailWord_2427947, baseEnd_2427947] using wordTrace_append hprefix tailTrace_2427947
  have hstable : (prefixWord ++ tailWord_2427947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427947).length < 2 ^ (prefixWord ++ tailWord_2427947).sum := by decide
  have hdescent : baseEnd_2427947 < baseStart_2427947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427954 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_2427954 : Nat := 118140960795 + 2427954 * 2 ^ 59
def prefixEnd_2427954 : Nat := 4983230072969 + 3 ^ 40 * 2427954 * 2
def baseEnd_2427954 : Nat := 1246707409006498852509049

theorem tailTrace_2427954 : CollatzResearch.WordTrace tailWord_2427954 prefixEnd_2427954 1246707409006498852509049 := by
  unfold tailWord_2427954
  simp only [CollatzResearch.WordTrace]
  refine ⟨22138689361486198593854729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59036504963963196250279277 22138689361486198593854729)
  ·
    refine ⟨16604017021114648945391047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22138689361486198593854729 16604017021114648945391047)
    ·
      refine ⟨24906025531671973418086571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16604017021114648945391047 24906025531671973418086571)
      ·
        refine ⟨37359038297507960127129857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24906025531671973418086571 37359038297507960127129857)
        ·
          refine ⟨28019278723130970095347393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37359038297507960127129857 28019278723130970095347393)
          ·
            refine ⟨21014459042348227571510545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28019278723130970095347393 21014459042348227571510545)
            ·
              refine ⟨15760844281761170678632909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21014459042348227571510545 15760844281761170678632909)
              ·
                refine ⟨5910316605660439004487341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15760844281761170678632909 5910316605660439004487341)
                ·
                  refine ⟨2216368727122664626682753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5910316605660439004487341 2216368727122664626682753)
                  ·
                    refine ⟨1662276545341998470012065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2216368727122664626682753 1662276545341998470012065)
                    ·
                      refine ⟨1246707409006498852509049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662276545341998470012065 1246707409006498852509049)
                      ·
                        rfl

theorem cell23_2427954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_2427954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427954 prefixEnd_2427954 := by exact prefixLift 2427954
  have htrace : WordTrace (prefixWord ++ tailWord_2427954) baseStart_2427954 baseEnd_2427954 := by
    simpa [prefixWord, tailWord_2427954, baseEnd_2427954] using wordTrace_append hprefix tailTrace_2427954
  have hstable : (prefixWord ++ tailWord_2427954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427954).length < 2 ^ (prefixWord ++ tailWord_2427954).sum := by decide
  have hdescent : baseEnd_2427954 < baseStart_2427954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427960 : List Nat := [2, 1, 2, 1, 5, 1, 3, 8]
def baseStart_2427960 : Nat := 118140960795 + 2427960 * 2 ^ 59
def prefixEnd_2427960 : Nat := 4983230072969 + 3 ^ 40 * 2427960 * 2
def baseEnd_2427960 : Nat := 46174462588534289964223

theorem tailTrace_2427960 : CollatzResearch.WordTrace tailWord_2427960 prefixEnd_2427960 46174462588534289964223 := by
  unfold tailWord_2427960
  simp only [CollatzResearch.WordTrace]
  refine ⟨44277488141961528700068667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59036650855948704933424889 44277488141961528700068667)
  ·
    refine ⟨66416232212942293050103001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44277488141961528700068667 66416232212942293050103001)
    ·
      refine ⟨49812174159706719787577251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66416232212942293050103001 49812174159706719787577251)
      ·
        refine ⟨74718261239560079681365877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49812174159706719787577251 74718261239560079681365877)
        ·
          refine ⟨7004836991208757470128051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74718261239560079681365877 7004836991208757470128051)
          ·
            refine ⟨10507255486813136205192077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7004836991208757470128051 10507255486813136205192077)
            ·
              refine ⟨3940220807554926076947029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10507255486813136205192077 3940220807554926076947029)
              ·
                refine ⟨46174462588534289964223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3940220807554926076947029 46174462588534289964223)
                ·
                  rfl

theorem cell23_2427960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 8].length) (baseStart_2427960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427960 prefixEnd_2427960 := by exact prefixLift 2427960
  have htrace : WordTrace (prefixWord ++ tailWord_2427960) baseStart_2427960 baseEnd_2427960 := by
    simpa [prefixWord, tailWord_2427960, baseEnd_2427960] using wordTrace_append hprefix tailTrace_2427960
  have hstable : (prefixWord ++ tailWord_2427960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427960).length < 2 ^ (prefixWord ++ tailWord_2427960).sum := by decide
  have hdescent : baseEnd_2427960 < baseStart_2427960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2427998 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2427998 : Nat := 118140960795 + 2427998 * 2 ^ 59
def prefixEnd_2427998 : Nat := 4983230072969 + 3 ^ 40 * 2427998 * 2
def baseEnd_2427998 : Nat := 415576667385098893452949

theorem tailTrace_2427998 : CollatzResearch.WordTrace tailWord_2427998 prefixEnd_2427998 415576667385098893452949 := by
  unfold tailWord_2427998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11069545282223173736252581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59037574838523593260013765 11069545282223173736252581)
  ·
    refine ⟨2075539740416845075547359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11069545282223173736252581 2075539740416845075547359)
    ·
      refine ⟨3113309610625267613321039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2075539740416845075547359 3113309610625267613321039)
      ·
        refine ⟨4669964415937901419981559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113309610625267613321039 4669964415937901419981559)
        ·
          refine ⟨7004946623906852129972339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4669964415937901419981559 7004946623906852129972339)
          ·
            refine ⟨10507419935860278194958509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7004946623906852129972339 10507419935860278194958509)
            ·
              refine ⟨3940282475947604323109441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10507419935860278194958509 3940282475947604323109441)
              ·
                refine ⟨2955211856960703242332081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940282475947604323109441 2955211856960703242332081)
                ·
                  refine ⟨2216408892720527431749061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2955211856960703242332081 2216408892720527431749061)
                  ·
                    refine ⟨415576667385098893452949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2216408892720527431749061 415576667385098893452949)
                    ·
                      rfl

theorem cell23_2427998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2427998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2427998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2427998 prefixEnd_2427998 := by exact prefixLift 2427998
  have htrace : WordTrace (prefixWord ++ tailWord_2427998) baseStart_2427998 baseEnd_2427998 := by
    simpa [prefixWord, tailWord_2427998, baseEnd_2427998] using wordTrace_append hprefix tailTrace_2427998
  have hstable : (prefixWord ++ tailWord_2427998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2427998).length < 2 ^ (prefixWord ++ tailWord_2427998).sum := by decide
  have hdescent : baseEnd_2427998 < baseStart_2427998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2427998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428061 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_2428061 : Nat := 118140960795 + 2428061 * 2 ^ 59
def prefixEnd_2428061 : Nat := 4983230072969 + 3 ^ 40 * 2428061 * 2
def baseEnd_2428061 : Nat := 1246762351436529933871057

theorem tailTrace_2428061 : CollatzResearch.WordTrace tailWord_2428061 prefixEnd_2428061 1246762351436529933871057 := by
  unfold tailWord_2428061
  simp only [CollatzResearch.WordTrace]
  refine ⟨88558660056557151649564037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59039106704371434433042691 88558660056557151649564037)
  ·
    refine ⟨16604748760604465934293257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88558660056557151649564037 16604748760604465934293257)
    ·
      refine ⟨12453561570453349450719943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16604748760604465934293257 12453561570453349450719943)
      ·
        refine ⟨18680342355680024176079915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12453561570453349450719943 18680342355680024176079915)
        ·
          refine ⟨28020513533520036264119873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18680342355680024176079915 28020513533520036264119873)
          ·
            refine ⟨21015385150140027198089905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28020513533520036264119873 21015385150140027198089905)
            ·
              refine ⟨15761538862605020398567429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21015385150140027198089905 15761538862605020398567429)
              ·
                refine ⟨2955288536738441324731393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15761538862605020398567429 2955288536738441324731393)
                ·
                  refine ⟨2216466402553830993548545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2955288536738441324731393 2216466402553830993548545)
                  ·
                    refine ⟨1662349801915373245161409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2216466402553830993548545 1662349801915373245161409)
                    ·
                      refine ⟨1246762351436529933871057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662349801915373245161409 1246762351436529933871057)
                      ·
                        rfl

theorem cell23_2428061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_2428061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428061 prefixEnd_2428061 := by exact prefixLift 2428061
  have htrace : WordTrace (prefixWord ++ tailWord_2428061) baseStart_2428061 baseEnd_2428061 := by
    simpa [prefixWord, tailWord_2428061, baseEnd_2428061] using wordTrace_append hprefix tailTrace_2428061
  have hstable : (prefixWord ++ tailWord_2428061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428061).length < 2 ^ (prefixWord ++ tailWord_2428061).sum := by decide
  have hdescent : baseEnd_2428061 < baseStart_2428061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428067 : List Nat := [1, 1, 1, 4, 1, 1, 1, 8, 5]
def baseStart_2428067 : Nat := 118140960795 + 2428067 * 2 ^ 59
def prefixEnd_2428067 : Nat := 4983230072969 + 3 ^ 40 * 2428067 * 2
def baseEnd_2428067 : Nat := 138529492480050767821781

theorem tailTrace_2428067 : CollatzResearch.WordTrace tailWord_2428067 prefixEnd_2428067 138529492480050767821781 := by
  unfold tailWord_2428067
  simp only [CollatzResearch.WordTrace]
  refine ⟨88558878894535414674282455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59039252596356943116188303 88558878894535414674282455)
  ·
    refine ⟨132838318341803122011423683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88558878894535414674282455 132838318341803122011423683)
    ·
      refine ⟨199257477512704683017135525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132838318341803122011423683 199257477512704683017135525)
      ·
        refine ⟨37360777033632128065712911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199257477512704683017135525 37360777033632128065712911)
        ·
          refine ⟨56041165550448192098569367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37360777033632128065712911 56041165550448192098569367)
          ·
            refine ⟨84061748325672288147854051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56041165550448192098569367 84061748325672288147854051)
            ·
              refine ⟨126092622488508432221781077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84061748325672288147854051 126092622488508432221781077)
              ·
                refine ⟨1477647919787208190098997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 126092622488508432221781077 1477647919787208190098997)
                ·
                  refine ⟨138529492480050767821781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1477647919787208190098997 138529492480050767821781)
                  ·
                    rfl

theorem cell23_2428067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 5].length) (baseStart_2428067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428067 prefixEnd_2428067 := by exact prefixLift 2428067
  have htrace : WordTrace (prefixWord ++ tailWord_2428067) baseStart_2428067 baseEnd_2428067 := by
    simpa [prefixWord, tailWord_2428067, baseEnd_2428067] using wordTrace_append hprefix tailTrace_2428067
  have hstable : (prefixWord ++ tailWord_2428067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428067).length < 2 ^ (prefixWord ++ tailWord_2428067).sum := by decide
  have hdescent : baseEnd_2428067 < baseStart_2428067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428090 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_2428090 : Nat := 118140960795 + 2428090 * 2 ^ 59
def prefixEnd_2428090 : Nat := 4983230072969 + 3 ^ 40 * 2428090 * 2
def baseEnd_2428090 : Nat := 1246777242375510320408423

theorem tailTrace_2428090 : CollatzResearch.WordTrace tailWord_2428090 prefixEnd_2428090 1246777242375510320408423 := by
  unfold tailWord_2428090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22139929443363022400592431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59039811848968059734913149 22139929443363022400592431)
  ·
    refine ⟨33209894165044533600888647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22139929443363022400592431 33209894165044533600888647)
    ·
      refine ⟨49814841247566800401332971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33209894165044533600888647 49814841247566800401332971)
      ·
        refine ⟨74722261871350200601999457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49814841247566800401332971 74722261871350200601999457)
        ·
          refine ⟨56041696403512650451499593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74722261871350200601999457 56041696403512650451499593)
          ·
            refine ⟨42031272302634487838624695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56041696403512650451499593 42031272302634487838624695)
            ·
              refine ⟨63046908453951731757937043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42031272302634487838624695 63046908453951731757937043)
              ·
                refine ⟨94570362680927597636905565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63046908453951731757937043 94570362680927597636905565)
                ·
                  refine ⟨35463886005347849113839587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94570362680927597636905565 35463886005347849113839587)
                  ·
                    refine ⟨53195829008021773670759381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35463886005347849113839587 53195829008021773670759381)
                    ·
                      refine ⟨1246777242375510320408423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53195829008021773670759381 1246777242375510320408423)
                      ·
                        rfl

theorem cell23_2428090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_2428090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428090 prefixEnd_2428090 := by exact prefixLift 2428090
  have htrace : WordTrace (prefixWord ++ tailWord_2428090) baseStart_2428090 baseEnd_2428090 := by
    simpa [prefixWord, tailWord_2428090, baseEnd_2428090] using wordTrace_append hprefix tailTrace_2428090
  have hstable : (prefixWord ++ tailWord_2428090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428090).length < 2 ^ (prefixWord ++ tailWord_2428090).sum := by decide
  have hdescent : baseEnd_2428090 < baseStart_2428090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428118 : List Nat := [5, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2428118 : Nat := 118140960795 + 2428118 * 2 ^ 59
def prefixEnd_2428118 : Nat := 4983230072969 + 3 ^ 40 * 2428118 * 2
def baseEnd_2428118 : Nat := 138532402203759578984255

theorem tailTrace_2428118 : CollatzResearch.WordTrace tailWord_2428118 prefixEnd_2428118 138532402203759578984255 := by
  unfold tailWord_2428118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5535046188584415649024313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59040492678233766922926005 5535046188584415649024313)
  ·
    refine ⟨4151284641438311736768235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5535046188584415649024313 4151284641438311736768235)
    ·
      refine ⟨6226926962157467605152353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4151284641438311736768235 6226926962157467605152353)
      ·
        refine ⟨4670195221618100703864265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6226926962157467605152353 4670195221618100703864265)
        ·
          refine ⟨3502646416213575527898199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4670195221618100703864265 3502646416213575527898199)
          ·
            refine ⟨5253969624320363291847299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502646416213575527898199 5253969624320363291847299)
            ·
              refine ⟨7880954436480544937770949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253969624320363291847299 7880954436480544937770949)
              ·
                refine ⟨1477678956840102175832053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7880954436480544937770949 1477678956840102175832053)
                ·
                  refine ⟨138532402203759578984255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1477678956840102175832053 138532402203759578984255)
                  ·
                    rfl

theorem cell23_2428118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2428118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428118 prefixEnd_2428118 := by exact prefixLift 2428118
  have htrace : WordTrace (prefixWord ++ tailWord_2428118) baseStart_2428118 baseEnd_2428118 := by
    simpa [prefixWord, tailWord_2428118, baseEnd_2428118] using wordTrace_append hprefix tailTrace_2428118
  have hstable : (prefixWord ++ tailWord_2428118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428118).length < 2 ^ (prefixWord ++ tailWord_2428118).sum := by decide
  have hdescent : baseEnd_2428118 < baseStart_2428118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428148 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2428148 : Nat := 118140960795 + 2428148 * 2 ^ 59
def prefixEnd_2428148 : Nat := 4983230072969 + 3 ^ 40 * 2428148 * 2
def baseEnd_2428148 : Nat := 415602341417823697827719

theorem tailTrace_2428148 : CollatzResearch.WordTrace tailWord_2428148 prefixEnd_2428148 415602341417823697827719 := by
  unfold tailWord_2428148
  simp only [CollatzResearch.WordTrace]
  refine ⟨44280916603620982753990549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59041222138161310338654065 44280916603620982753990549)
  ·
    refine ⟨2075667965794733566593307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44280916603620982753990549 2075667965794733566593307)
    ·
      refine ⟨3113501948692100349889961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2075667965794733566593307 3113501948692100349889961)
      ·
        refine ⟨2335126461519075262417471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3113501948692100349889961 2335126461519075262417471)
        ·
          refine ⟨3502689692278612893626207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335126461519075262417471 3502689692278612893626207)
          ·
            refine ⟨5254034538417919340439311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502689692278612893626207 5254034538417919340439311)
            ·
              refine ⟨7881051807626879010658967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254034538417919340439311 7881051807626879010658967)
              ·
                refine ⟨11821577711440318515988451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7881051807626879010658967 11821577711440318515988451)
                ·
                  refine ⟨17732366567160477773982677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11821577711440318515988451 17732366567160477773982677)
                  ·
                    refine ⟨415602341417823697827719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17732366567160477773982677 415602341417823697827719)
                    ·
                      rfl

theorem cell23_2428148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2428148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428148 prefixEnd_2428148 := by exact prefixLift 2428148
  have htrace : WordTrace (prefixWord ++ tailWord_2428148) baseStart_2428148 baseEnd_2428148 := by
    simpa [prefixWord, tailWord_2428148, baseEnd_2428148] using wordTrace_append hprefix tailTrace_2428148
  have hstable : (prefixWord ++ tailWord_2428148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428148).length < 2 ^ (prefixWord ++ tailWord_2428148).sum := by decide
  have hdescent : baseEnd_2428148 < baseStart_2428148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428161 : List Nat := [1, 2, 4, 1, 1, 3, 1, 5, 1, 4]
def baseStart_2428161 : Nat := 118140960795 + 2428161 * 2 ^ 59
def prefixEnd_2428161 : Nat := 4983230072969 + 3 ^ 40 * 2428161 * 2
def baseEnd_2428161 : Nat := 415604566500659847540199

theorem tailTrace_2428161 : CollatzResearch.WordTrace tailWord_2428161 prefixEnd_2428161 415604566500659847540199 := by
  unfold tailWord_2428161
  simp only [CollatzResearch.WordTrace]
  refine ⟨88562307356194868728204337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59041538237463245818802891 88562307356194868728204337)
  ·
    refine ⟨66421730517146151546153253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88562307356194868728204337 66421730517146151546153253)
    ·
      refine ⟨12454074471964903414903735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66421730517146151546153253 12454074471964903414903735)
      ·
        refine ⟨18681111707947355122355603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12454074471964903414903735 18681111707947355122355603)
        ·
          refine ⟨28021667561921032683533405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18681111707947355122355603 28021667561921032683533405)
          ·
            refine ⟨10508125335720387256325027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28021667561921032683533405 10508125335720387256325027)
            ·
              refine ⟨15762188003580580884487541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10508125335720387256325027 15762188003580580884487541)
              ·
                refine ⟨1477705125335679457920707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15762188003580580884487541 1477705125335679457920707)
                ·
                  refine ⟨2216557688003519186881061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477705125335679457920707 2216557688003519186881061)
                  ·
                    refine ⟨415604566500659847540199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2216557688003519186881061 415604566500659847540199)
                    ·
                      rfl

theorem cell23_2428161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_2428161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428161 prefixEnd_2428161 := by exact prefixLift 2428161
  have htrace : WordTrace (prefixWord ++ tailWord_2428161) baseStart_2428161 baseEnd_2428161 := by
    simpa [prefixWord, tailWord_2428161, baseEnd_2428161] using wordTrace_append hprefix tailTrace_2428161
  have hstable : (prefixWord ++ tailWord_2428161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428161).length < 2 ^ (prefixWord ++ tailWord_2428161).sum := by decide
  have hdescent : baseEnd_2428161 < baseStart_2428161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428174 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_2428174 : Nat := 118140960795 + 2428174 * 2 ^ 59
def prefixEnd_2428174 : Nat := 4983230072969 + 3 ^ 40 * 2428174 * 2
def baseEnd_2428174 : Nat := 138535597194498665750893

theorem tailTrace_2428174 : CollatzResearch.WordTrace tailWord_2428174 prefixEnd_2428174 138535597194498665750893 := by
  unfold tailWord_2428174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11070347688143471493553447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59041854336765181298951717 11070347688143471493553447)
  ·
    refine ⟨16605521532215207240330171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11070347688143471493553447 16605521532215207240330171)
    ·
      refine ⟨24908282298322810860495257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16605521532215207240330171 24908282298322810860495257)
      ·
        refine ⟨18681211723742108145371443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24908282298322810860495257 18681211723742108145371443)
        ·
          refine ⟨28021817585613162218057165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18681211723742108145371443 28021817585613162218057165)
          ·
            refine ⟨10508181594604935831771437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28021817585613162218057165 10508181594604935831771437)
            ·
              refine ⟨3940568097976850936914289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10508181594604935831771437 3940568097976850936914289)
              ·
                refine ⟨2955426073482638202685717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3940568097976850936914289 2955426073482638202685717)
                ·
                  refine ⟨138535597194498665750893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2955426073482638202685717 138535597194498665750893)
                  ·
                    rfl

theorem cell23_2428174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_2428174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428174 prefixEnd_2428174 := by exact prefixLift 2428174
  have htrace : WordTrace (prefixWord ++ tailWord_2428174) baseStart_2428174 baseEnd_2428174 := by
    simpa [prefixWord, tailWord_2428174, baseEnd_2428174] using wordTrace_append hprefix tailTrace_2428174
  have hstable : (prefixWord ++ tailWord_2428174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428174).length < 2 ^ (prefixWord ++ tailWord_2428174).sum := by decide
  have hdescent : baseEnd_2428174 < baseStart_2428174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428191 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 6]
def baseStart_2428191 : Nat := 118140960795 + 2428191 * 2 ^ 59
def prefixEnd_2428191 : Nat := 4983230072969 + 3 ^ 40 * 2428191 * 2
def baseEnd_2428191 : Nat := 138536567102401602805051

theorem tailTrace_2428191 : CollatzResearch.WordTrace tailWord_2428191 prefixEnd_2428191 138536567102401602805051 := by
  unfold tailWord_2428191
  simp only [CollatzResearch.WordTrace]
  refine ⟨88563401546086183851796427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59042267697390789234530951 88563401546086183851796427)
  ·
    refine ⟨132845102319129275777694641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88563401546086183851796427 132845102319129275777694641)
    ·
      refine ⟨99633826739346956833270981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132845102319129275777694641 99633826739346956833270981)
      ·
        refine ⟨18681342513627554406238309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99633826739346956833270981 18681342513627554406238309)
        ·
          refine ⟨3502751721305166451169683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18681342513627554406238309 3502751721305166451169683)
          ·
            refine ⟨5254127581957749676754525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502751721305166451169683 5254127581957749676754525)
            ·
              refine ⟨1970297843234156128782947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5254127581957749676754525 1970297843234156128782947)
              ·
                refine ⟨2955446764851234193174421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970297843234156128782947 2955446764851234193174421)
                ·
                  refine ⟨138536567102401602805051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2955446764851234193174421 138536567102401602805051)
                  ·
                    rfl

theorem cell23_2428191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 6].length) (baseStart_2428191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428191 prefixEnd_2428191 := by exact prefixLift 2428191
  have htrace : WordTrace (prefixWord ++ tailWord_2428191) baseStart_2428191 baseEnd_2428191 := by
    simpa [prefixWord, tailWord_2428191, baseEnd_2428191] using wordTrace_append hprefix tailTrace_2428191
  have hstable : (prefixWord ++ tailWord_2428191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428191).length < 2 ^ (prefixWord ++ tailWord_2428191).sum := by decide
  have hdescent : baseEnd_2428191 < baseStart_2428191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428224 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 4]
def baseStart_2428224 : Nat := 118140960795 + 2428224 * 2 ^ 59
def prefixEnd_2428224 : Nat := 4983230072969 + 3 ^ 40 * 2428224 * 2
def baseEnd_2428224 : Nat := 1246846048783212796132807

theorem tailTrace_2428224 : CollatzResearch.WordTrace tailWord_2428224 prefixEnd_2428224 1246846048783212796132807 := by
  unfold tailWord_2428224
  simp only [CollatzResearch.WordTrace]
  refine ⟨44282302577483315243873863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59043070103311086991831817 44282302577483315243873863)
  ·
    refine ⟨66423453866224972865810795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44282302577483315243873863 66423453866224972865810795)
    ·
      refine ⟨99635180799337459298716193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66423453866224972865810795 99635180799337459298716193)
      ·
        refine ⟨74726385599503094474037145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99635180799337459298716193 74726385599503094474037145)
        ·
          refine ⟨56044789199627320855527859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74726385599503094474037145 56044789199627320855527859)
          ·
            refine ⟨84067183799440981283291789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56044789199627320855527859 84067183799440981283291789)
            ·
              refine ⟨31525193924790367981234421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84067183799440981283291789 31525193924790367981234421)
              ·
                refine ⟨2955486930449096998240727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31525193924790367981234421 2955486930449096998240727)
                ·
                  refine ⟨4433230395673645497361091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955486930449096998240727 4433230395673645497361091)
                  ·
                    refine ⟨6649845593510468246041637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4433230395673645497361091 6649845593510468246041637)
                    ·
                      refine ⟨1246846048783212796132807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6649845593510468246041637 1246846048783212796132807)
                      ·
                        rfl

theorem cell23_2428224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_2428224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428224 prefixEnd_2428224 := by exact prefixLift 2428224
  have htrace : WordTrace (prefixWord ++ tailWord_2428224) baseStart_2428224 baseEnd_2428224 := by
    simpa [prefixWord, tailWord_2428224, baseEnd_2428224] using wordTrace_append hprefix tailTrace_2428224
  have hstable : (prefixWord ++ tailWord_2428224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428224).length < 2 ^ (prefixWord ++ tailWord_2428224).sum := by decide
  have hdescent : baseEnd_2428224 < baseStart_2428224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428228 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_2428228 : Nat := 118140960795 + 2428228 * 2 ^ 59
def prefixEnd_2428228 : Nat := 4983230072969 + 3 ^ 40 * 2428228 * 2
def baseEnd_2428228 : Nat := 1246848102705830780482789

theorem tailTrace_2428228 : CollatzResearch.WordTrace tailWord_2428228 prefixEnd_2428228 1246848102705830780482789 := by
  unfold tailWord_2428228
  simp only [CollatzResearch.WordTrace]
  refine ⟨44282375523476069585446669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59043167364634759447262225 44282375523476069585446669)
  ·
    refine ⟨16605890821303526094542501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44282375523476069585446669 16605890821303526094542501)
    ·
      refine ⟨3113604528994411142726719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16605890821303526094542501 3113604528994411142726719)
      ·
        refine ⟨4670406793491616714090079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113604528994411142726719 4670406793491616714090079)
        ·
          refine ⟨7005610190237425071135119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670406793491616714090079 7005610190237425071135119)
          ·
            refine ⟨10508415285356137606702679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7005610190237425071135119 10508415285356137606702679)
            ·
              refine ⟨15762622928034206410054019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10508415285356137606702679 15762622928034206410054019)
              ·
                refine ⟨23643934392051309615081029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15762622928034206410054019 23643934392051309615081029)
                ·
                  refine ⟨4433237698509620552827693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23643934392051309615081029 4433237698509620552827693)
                  ·
                    refine ⟨1662464136941107707310385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4433237698509620552827693 1662464136941107707310385)
                    ·
                      refine ⟨1246848102705830780482789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662464136941107707310385 1246848102705830780482789)
                      ·
                        rfl

theorem cell23_2428228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_2428228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428228 prefixEnd_2428228 := by exact prefixLift 2428228
  have htrace : WordTrace (prefixWord ++ tailWord_2428228) baseStart_2428228 baseEnd_2428228 := by
    simpa [prefixWord, tailWord_2428228, baseEnd_2428228] using wordTrace_append hprefix tailTrace_2428228
  have hstable : (prefixWord ++ tailWord_2428228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428228).length < 2 ^ (prefixWord ++ tailWord_2428228).sum := by decide
  have hdescent : baseEnd_2428228 < baseStart_2428228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428244 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_2428244 : Nat := 118140960795 + 2428244 * 2 ^ 59
def prefixEnd_2428244 : Nat := 4983230072969 + 3 ^ 40 * 2428244 * 2
def baseEnd_2428244 : Nat := 1246856318396302717882715

theorem tailTrace_2428244 : CollatzResearch.WordTrace tailWord_2428244 prefixEnd_2428244 1246856318396302717882715 := by
  unfold tailWord_2428244
  simp only [CollatzResearch.WordTrace]
  refine ⟨44282667307447086951737893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59043556409929449268983857 44282667307447086951737893)
  ·
    refine ⟨8303000120146328803450855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44282667307447086951737893 8303000120146328803450855)
    ·
      refine ⟨12454500180219493205176283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8303000120146328803450855 12454500180219493205176283)
      ·
        refine ⟨18681750270329239807764425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12454500180219493205176283 18681750270329239807764425)
        ·
          refine ⟨14011312702746929855823319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18681750270329239807764425 14011312702746929855823319)
          ·
            refine ⟨21016969054120394783734979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14011312702746929855823319 21016969054120394783734979)
            ·
              refine ⟨31525453581180592175602469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21016969054120394783734979 31525453581180592175602469)
              ·
                refine ⟨5911022546471361032925463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31525453581180592175602469 5911022546471361032925463)
                ·
                  refine ⟨8866533819707041549388195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5911022546471361032925463 8866533819707041549388195)
                  ·
                    refine ⟨13299800729560562324082293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8866533819707041549388195 13299800729560562324082293)
                    ·
                      refine ⟨1246856318396302717882715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13299800729560562324082293 1246856318396302717882715)
                      ·
                        rfl

theorem cell23_2428244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_2428244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428244 prefixEnd_2428244 := by exact prefixLift 2428244
  have htrace : WordTrace (prefixWord ++ tailWord_2428244) baseStart_2428244 baseEnd_2428244 := by
    simpa [prefixWord, tailWord_2428244, baseEnd_2428244] using wordTrace_append hprefix tailTrace_2428244
  have hstable : (prefixWord ++ tailWord_2428244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428244).length < 2 ^ (prefixWord ++ tailWord_2428244).sum := by decide
  have hdescent : baseEnd_2428244 < baseStart_2428244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428247 : List Nat := [1, 1, 3, 2, 3, 2, 1, 10]
def baseStart_2428247 : Nat := 118140960795 + 2428247 * 2 ^ 59
def prefixEnd_2428247 : Nat := 4983230072969 + 3 ^ 40 * 2428247 * 2
def baseEnd_2428247 : Nat := 46179920697713563190563

theorem tailTrace_2428247 : CollatzResearch.WordTrace tailWord_2428247 prefixEnd_2428247 46179920697713563190563 := by
  unfold tailWord_2428247
  simp only [CollatzResearch.WordTrace]
  refine ⟨88565444033883305415834995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59043629355922203610556663 88565444033883305415834995)
  ·
    refine ⟨132848166050824958123752493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88565444033883305415834995 132848166050824958123752493)
    ·
      refine ⟨49818062269059359296407185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132848166050824958123752493 49818062269059359296407185)
      ·
        refine ⟨37363546701794519472305389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49818062269059359296407185 37363546701794519472305389)
        ·
          refine ⟨14011330013172944802114521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37363546701794519472305389 14011330013172944802114521)
          ·
            refine ⟨10508497509879708601585891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14011330013172944802114521 10508497509879708601585891)
            ·
              refine ⟨15762746264819562902378837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10508497509879708601585891 15762746264819562902378837)
              ·
                refine ⟨46179920697713563190563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15762746264819562902378837 46179920697713563190563)
                ·
                  rfl

theorem cell23_2428247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 10].length) (baseStart_2428247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428247 prefixEnd_2428247 := by exact prefixLift 2428247
  have htrace : WordTrace (prefixWord ++ tailWord_2428247) baseStart_2428247 baseEnd_2428247 := by
    simpa [prefixWord, tailWord_2428247, baseEnd_2428247] using wordTrace_append hprefix tailTrace_2428247
  have hstable : (prefixWord ++ tailWord_2428247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428247).length < 2 ^ (prefixWord ++ tailWord_2428247).sum := by decide
  have hdescent : baseEnd_2428247 < baseStart_2428247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428258 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_2428258 : Nat := 118140960795 + 2428258 * 2 ^ 59
def prefixEnd_2428258 : Nat := 4983230072969 + 3 ^ 40 * 2428258 * 2
def baseEnd_2428258 : Nat := 1246863507125465663107651

theorem tailTrace_2428258 : CollatzResearch.WordTrace tailWord_2428258 prefixEnd_2428258 1246863507125465663107651 := by
  unfold tailWord_2428258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22141461309210863573621357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59043896824562302862990285 22141461309210863573621357)
  ·
    refine ⟨8303047990954073840108009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22141461309210863573621357 8303047990954073840108009)
    ·
      refine ⟨6227285993215555380081007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8303047990954073840108009 6227285993215555380081007)
      ·
        refine ⟨9340928989823333070121511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6227285993215555380081007 9340928989823333070121511)
        ·
          refine ⟨14011393484734999605182267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9340928989823333070121511 14011393484734999605182267)
          ·
            refine ⟨21017090227102499407773401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14011393484734999605182267 21017090227102499407773401)
            ·
              refine ⟨15762817670326874555830051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21017090227102499407773401 15762817670326874555830051)
              ·
                refine ⟨23644226505490311833745077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15762817670326874555830051 23644226505490311833745077)
                ·
                  refine ⟨2216646234889716734413601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23644226505490311833745077 2216646234889716734413601)
                  ·
                    refine ⟨1662484676167287550810201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2216646234889716734413601 1662484676167287550810201)
                    ·
                      refine ⟨1246863507125465663107651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662484676167287550810201 1246863507125465663107651)
                      ·
                        rfl

theorem cell23_2428258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_2428258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428258 prefixEnd_2428258 := by exact prefixLift 2428258
  have htrace : WordTrace (prefixWord ++ tailWord_2428258) baseStart_2428258 baseEnd_2428258 := by
    simpa [prefixWord, tailWord_2428258, baseEnd_2428258] using wordTrace_append hprefix tailTrace_2428258
  have hstable : (prefixWord ++ tailWord_2428258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428258).length < 2 ^ (prefixWord ++ tailWord_2428258).sum := by decide
  have hdescent : baseEnd_2428258 < baseStart_2428258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428286 : List Nat := [4, 2, 3, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2428286 : Nat := 118140960795 + 2428286 * 2 ^ 59
def prefixEnd_2428286 : Nat := 4983230072969 + 3 ^ 40 * 2428286 * 2
def baseEnd_2428286 : Nat := 1246877884583791553557523

theorem tailTrace_2428286 : CollatzResearch.WordTrace tailWord_2428286 prefixEnd_2428286 1246877884583791553557523 := by
  unfold tailWord_2428286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11070858310092751884563089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59044577653828010051003141 11070858310092751884563089)
  ·
    refine ⟨8303143732569563913422317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11070858310092751884563089 8303143732569563913422317)
    ·
      refine ⟨3113678899713586467533369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8303143732569563913422317 3113678899713586467533369)
      ·
        refine ⟨2335259174785189850650027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3113678899713586467533369 2335259174785189850650027)
        ·
          refine ⟨3502888762177784775975041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335259174785189850650027 3502888762177784775975041)
          ·
            refine ⟨2627166571633338581981281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3502888762177784775975041 2627166571633338581981281)
            ·
              refine ⟨1970374928725003936485961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2627166571633338581981281 1970374928725003936485961)
              ·
                refine ⟨1477781196543752952364471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970374928725003936485961 1477781196543752952364471)
                ·
                  refine ⟨2216671794815629428546707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477781196543752952364471 2216671794815629428546707)
                  ·
                    refine ⟨3325007692223444142820061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2216671794815629428546707 3325007692223444142820061)
                    ·
                      refine ⟨1246877884583791553557523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3325007692223444142820061 1246877884583791553557523)
                      ·
                        rfl

theorem cell23_2428286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2428286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428286 prefixEnd_2428286 := by exact prefixLift 2428286
  have htrace : WordTrace (prefixWord ++ tailWord_2428286) baseStart_2428286 baseEnd_2428286 := by
    simpa [prefixWord, tailWord_2428286, baseEnd_2428286] using wordTrace_append hprefix tailTrace_2428286
  have hstable : (prefixWord ++ tailWord_2428286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428286).length < 2 ^ (prefixWord ++ tailWord_2428286).sum := by decide
  have hdescent : baseEnd_2428286 < baseStart_2428286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428292 : List Nat := [2, 3, 2, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_2428292 : Nat := 118140960795 + 2428292 * 2 ^ 59
def prefixEnd_2428292 : Nat := 4983230072969 + 3 ^ 40 * 2428292 * 2
def baseEnd_2428292 : Nat := 1246880965467718530082495

theorem tailTrace_2428292 : CollatzResearch.WordTrace tailWord_2428292 prefixEnd_2428292 1246880965467718530082495 := by
  unfold tailWord_2428292
  simp only [CollatzResearch.WordTrace]
  refine ⟨44283542659360139050611565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59044723545813518734148753 44283542659360139050611565)
  ·
    refine ⟨16606328497260052143979337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44283542659360139050611565 16606328497260052143979337)
    ·
      refine ⟨12454746372945039107984503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16606328497260052143979337 12454746372945039107984503)
      ·
        refine ⟨18682119559417558661976755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12454746372945039107984503 18682119559417558661976755)
        ·
          refine ⟨28023179339126337992965133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18682119559417558661976755 28023179339126337992965133)
          ·
            refine ⟨10508692252172376747361925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28023179339126337992965133 10508692252172376747361925)
            ·
              refine ⟨1970379797282320640130361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10508692252172376747361925 1970379797282320640130361)
              ·
                refine ⟨1477784847961740480097771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970379797282320640130361 1477784847961740480097771)
                ·
                  refine ⟨2216677271942610720146657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477784847961740480097771 2216677271942610720146657)
                  ·
                    refine ⟨1662507953956958040109993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2216677271942610720146657 1662507953956958040109993)
                    ·
                      refine ⟨1246880965467718530082495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662507953956958040109993 1246880965467718530082495)
                      ·
                        rfl

theorem cell23_2428292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_2428292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428292 prefixEnd_2428292 := by exact prefixLift 2428292
  have htrace : WordTrace (prefixWord ++ tailWord_2428292) baseStart_2428292 baseEnd_2428292 := by
    simpa [prefixWord, tailWord_2428292, baseEnd_2428292] using wordTrace_append hprefix tailTrace_2428292
  have hstable : (prefixWord ++ tailWord_2428292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428292).length < 2 ^ (prefixWord ++ tailWord_2428292).sum := by decide
  have hdescent : baseEnd_2428292 < baseStart_2428292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428308 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2428308 : Nat := 118140960795 + 2428308 * 2 ^ 59
def prefixEnd_2428308 : Nat := 4983230072969 + 3 ^ 40 * 2428308 * 2
def baseEnd_2428308 : Nat := 1246889181158190467482421

theorem tailTrace_2428308 : CollatzResearch.WordTrace tailWord_2428308 prefixEnd_2428308 1246889181158190467482421 := by
  unfold tailWord_2428308
  simp only [CollatzResearch.WordTrace]
  refine ⟨44283834443331156416902789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59045112591108208555870385 44283834443331156416902789)
  ·
    refine ⟨8303218958124591828169273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44283834443331156416902789 8303218958124591828169273)
    ·
      refine ⟨6227414218593443871126955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8303218958124591828169273 6227414218593443871126955)
      ·
        refine ⟨9341121327890165806690433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6227414218593443871126955 9341121327890165806690433)
        ·
          refine ⟨7005840995917624355017825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9341121327890165806690433 7005840995917624355017825)
          ·
            refine ⟨5254380746938218266263369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7005840995917624355017825 5254380746938218266263369)
            ·
              refine ⟨3940785560203663699697527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5254380746938218266263369 3940785560203663699697527)
              ·
                refine ⟨5911178340305495549546291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940785560203663699697527 5911178340305495549546291)
                ·
                  refine ⟨8866767510458243324319437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5911178340305495549546291 8866767510458243324319437)
                  ·
                    refine ⟨3325037816421841246619789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8866767510458243324319437 3325037816421841246619789)
                    ·
                      refine ⟨1246889181158190467482421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3325037816421841246619789 1246889181158190467482421)
                      ·
                        rfl

theorem cell23_2428308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2428308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428308 prefixEnd_2428308 := by exact prefixLift 2428308
  have htrace : WordTrace (prefixWord ++ tailWord_2428308) baseStart_2428308 baseEnd_2428308 := by
    simpa [prefixWord, tailWord_2428308, baseEnd_2428308] using wordTrace_append hprefix tailTrace_2428308
  have hstable : (prefixWord ++ tailWord_2428308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428308).length < 2 ^ (prefixWord ++ tailWord_2428308).sum := by decide
  have hdescent : baseEnd_2428308 < baseStart_2428308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428314 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2428314 : Nat := 118140960795 + 2428314 * 2 ^ 59
def prefixEnd_2428314 : Nat := 4983230072969 + 3 ^ 40 * 2428314 * 2
def baseEnd_2428314 : Nat := 1246892262042117444007393

theorem tailTrace_2428314 : CollatzResearch.WordTrace tailWord_2428314 prefixEnd_2428314 1246892262042117444007393 := by
  unfold tailWord_2428314
  simp only [CollatzResearch.WordTrace]
  refine ⟨22141971931160143964630999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59045258483093717239015997 22141971931160143964630999)
  ·
    refine ⟨33212957896740215946946499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22141971931160143964630999 33212957896740215946946499)
    ·
      refine ⟨49819436845110323920419749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33212957896740215946946499 49819436845110323920419749)
      ·
        refine ⟨9341144408458185735078703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49819436845110323920419749 9341144408458185735078703)
        ·
          refine ⟨14011716612687278602618055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9341144408458185735078703 14011716612687278602618055)
          ·
            refine ⟨21017574919030917903927083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14011716612687278602618055 21017574919030917903927083)
            ·
              refine ⟨31526362378546376855890625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21017574919030917903927083 31526362378546376855890625)
              ·
                refine ⟨23644771783909782641917969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31526362378546376855890625 23644771783909782641917969)
                ·
                  refine ⟨17733578837932336981438477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23644771783909782641917969 17733578837932336981438477)
                  ·
                    refine ⟨6650092064224626368039429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17733578837932336981438477 6650092064224626368039429)
                    ·
                      refine ⟨1246892262042117444007393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6650092064224626368039429 1246892262042117444007393)
                      ·
                        rfl

theorem cell23_2428314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2428314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428314 prefixEnd_2428314 := by exact prefixLift 2428314
  have htrace : WordTrace (prefixWord ++ tailWord_2428314) baseStart_2428314 baseEnd_2428314 := by
    simpa [prefixWord, tailWord_2428314, baseEnd_2428314] using wordTrace_append hprefix tailTrace_2428314
  have hstable : (prefixWord ++ tailWord_2428314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428314).length < 2 ^ (prefixWord ++ tailWord_2428314).sum := by decide
  have hdescent : baseEnd_2428314 < baseStart_2428314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428344 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_2428344 : Nat := 118140960795 + 2428344 * 2 ^ 59
def prefixEnd_2428344 : Nat := 4983230072969 + 3 ^ 40 * 2428344 * 2
def baseEnd_2428344 : Nat := 1246907666461752326632255

theorem tailTrace_2428344 : CollatzResearch.WordTrace tailWord_2428344 prefixEnd_2428344 1246907666461752326632255 := by
  unfold tailWord_2428344
  simp only [CollatzResearch.WordTrace]
  refine ⟨44284490957265945491058043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59045987943021260654744057 44284490957265945491058043)
  ·
    refine ⟨66426736435898918236587065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44284490957265945491058043 66426736435898918236587065)
    ·
      refine ⟨49820052326924188677440299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66426736435898918236587065 49820052326924188677440299)
      ·
        refine ⟨74730078490386283016160449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49820052326924188677440299 74730078490386283016160449)
        ·
          refine ⟨56047558867789712262120337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74730078490386283016160449 56047558867789712262120337)
          ·
            refine ⟨42035669150842284196590253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56047558867789712262120337 42035669150842284196590253)
            ·
              refine ⟨15763375931565856573721345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42035669150842284196590253 15763375931565856573721345)
              ·
                refine ⟨11822531948674392430291009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15763375931565856573721345 11822531948674392430291009)
                ·
                  refine ⟨8866898961505794322718257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11822531948674392430291009 8866898961505794322718257)
                  ·
                    refine ⟨6650174221129345742038693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8866898961505794322718257 6650174221129345742038693)
                    ·
                      refine ⟨1246907666461752326632255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6650174221129345742038693 1246907666461752326632255)
                      ·
                        rfl

theorem cell23_2428344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_2428344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428344 prefixEnd_2428344 := by exact prefixLift 2428344
  have htrace : WordTrace (prefixWord ++ tailWord_2428344) baseStart_2428344 baseEnd_2428344 := by
    simpa [prefixWord, tailWord_2428344, baseEnd_2428344] using wordTrace_append hprefix tailTrace_2428344
  have hstable : (prefixWord ++ tailWord_2428344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428344).length < 2 ^ (prefixWord ++ tailWord_2428344).sum := by decide
  have hdescent : baseEnd_2428344 < baseStart_2428344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428401 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 2, 5]
def baseStart_2428401 : Nat := 118140960795 + 2428401 * 2 ^ 59
def prefixEnd_2428401 : Nat := 4983230072969 + 3 ^ 40 * 2428401 * 2
def baseEnd_2428401 : Nat := 415645644953019534539831

theorem tailTrace_2428401 : CollatzResearch.WordTrace tailWord_2428401 prefixEnd_2428401 415645644953019534539831 := by
  unfold tailWord_2428401
  simp only [CollatzResearch.WordTrace]
  refine ⟨88571060875325389716941057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59047373916883593144627371 88571060875325389716941057)
  ·
    refine ⟨66428295656494042287705793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88571060875325389716941057 66428295656494042287705793)
    ·
      refine ⟨49821221742370531715779345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66428295656494042287705793 49821221742370531715779345)
      ·
        refine ⟨37365916306777898786834509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49821221742370531715779345 37365916306777898786834509)
        ·
          refine ⟨14012218615041712045062941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37365916306777898786834509 14012218615041712045062941)
          ·
            refine ⟨5254581980640642016898603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14012218615041712045062941 5254581980640642016898603)
            ·
              refine ⟨7881872970960963025347905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254581980640642016898603 7881872970960963025347905)
              ·
                refine ⟨5911404728220722269010929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7881872970960963025347905 5911404728220722269010929)
                ·
                  refine ⟨4433553546165541701758197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5911404728220722269010929 4433553546165541701758197)
                  ·
                    refine ⟨415645644953019534539831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4433553546165541701758197 415645644953019534539831)
                    ·
                      rfl

theorem cell23_2428401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_2428401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428401 prefixEnd_2428401 := by exact prefixLift 2428401
  have htrace : WordTrace (prefixWord ++ tailWord_2428401) baseStart_2428401 baseEnd_2428401 := by
    simpa [prefixWord, tailWord_2428401, baseEnd_2428401] using wordTrace_append hprefix tailTrace_2428401
  have hstable : (prefixWord ++ tailWord_2428401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428401).length < 2 ^ (prefixWord ++ tailWord_2428401).sum := by decide
  have hdescent : baseEnd_2428401 < baseStart_2428401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428421 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 1, 6, 2]
def baseStart_2428421 : Nat := 118140960795 + 2428421 * 2 ^ 59
def prefixEnd_2428421 : Nat := 4983230072969 + 3 ^ 40 * 2428421 * 2
def baseEnd_2428421 : Nat := 1246947204472148525369401

theorem tailTrace_2428421 : CollatzResearch.WordTrace tailWord_2428421 prefixEnd_2428421 1246947204472148525369401 := by
  unfold tailWord_2428421
  simp only [CollatzResearch.WordTrace]
  refine ⟨88571790335252933132669117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59047860223501955421779411 88571790335252933132669117)
  ·
    refine ⟨33214421375719849924750919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88571790335252933132669117 33214421375719849924750919)
    ·
      refine ⟨49821632063579774887126379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33214421375719849924750919 49821632063579774887126379)
      ·
        refine ⟨74732448095369662330689569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49821632063579774887126379 74732448095369662330689569)
        ·
          refine ⟨56049336071527246748017177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74732448095369662330689569 56049336071527246748017177)
          ·
            refine ⟨42037002053645435061012883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56049336071527246748017177 42037002053645435061012883)
            ·
              refine ⟨63055503080468152591519325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42037002053645435061012883 63055503080468152591519325)
              ·
                refine ⟨23645813655175557221819747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63055503080468152591519325 23645813655175557221819747)
                ·
                  refine ⟨35468720482763335832729621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23645813655175557221819747 35468720482763335832729621)
                  ·
                    refine ⟨1662596272629531367159201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35468720482763335832729621 1662596272629531367159201)
                    ·
                      refine ⟨1246947204472148525369401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662596272629531367159201 1246947204472148525369401)
                      ·
                        rfl

theorem cell23_2428421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_2428421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428421 prefixEnd_2428421 := by exact prefixLift 2428421
  have htrace : WordTrace (prefixWord ++ tailWord_2428421) baseStart_2428421 baseEnd_2428421 := by
    simpa [prefixWord, tailWord_2428421, baseEnd_2428421] using wordTrace_append hprefix tailTrace_2428421
  have hstable : (prefixWord ++ tailWord_2428421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428421).length < 2 ^ (prefixWord ++ tailWord_2428421).sum := by decide
  have hdescent : baseEnd_2428421 < baseStart_2428421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428458 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2428458 : Nat := 118140960795 + 2428458 * 2 ^ 59
def prefixEnd_2428458 : Nat := 4983230072969 + 3 ^ 40 * 2428458 * 2
def baseEnd_2428458 : Nat := 1246966203256364880606731

theorem tailTrace_2428458 : CollatzResearch.WordTrace tailWord_2428458 prefixEnd_2428458 1246966203256364880606731 := by
  unfold tailWord_2428458
  simp only [CollatzResearch.WordTrace]
  refine ⟨22143284959029722112941507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59048759890745925634510685 22143284959029722112941507)
  ·
    refine ⟨33214927438544583169412261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22143284959029722112941507 33214927438544583169412261)
    ·
      refine ⟨6227798894727109344264799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33214927438544583169412261 6227798894727109344264799)
      ·
        refine ⟨9341698342090664016397199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6227798894727109344264799 9341698342090664016397199)
        ·
          refine ⟨14012547513135996024595799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9341698342090664016397199 14012547513135996024595799)
          ·
            refine ⟨21018821269703994036893699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14012547513135996024595799 21018821269703994036893699)
            ·
              refine ⟨31528231904555991055340549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21018821269703994036893699 31528231904555991055340549)
              ·
                refine ⟨5911543482104248322876353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31528231904555991055340549 5911543482104248322876353)
                ·
                  refine ⟨4433657611578186242157265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5911543482104248322876353 4433657611578186242157265)
                  ·
                    refine ⟨3325243208683639681617949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4433657611578186242157265 3325243208683639681617949)
                    ·
                      refine ⟨1246966203256364880606731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3325243208683639681617949 1246966203256364880606731)
                      ·
                        rfl

theorem cell23_2428458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2428458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428458 prefixEnd_2428458 := by exact prefixLift 2428458
  have htrace : WordTrace (prefixWord ++ tailWord_2428458) baseStart_2428458 baseEnd_2428458 := by
    simpa [prefixWord, tailWord_2428458, baseEnd_2428458] using wordTrace_append hprefix tailTrace_2428458
  have hstable : (prefixWord ++ tailWord_2428458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428458).length < 2 ^ (prefixWord ++ tailWord_2428458).sum := by decide
  have hdescent : baseEnd_2428458 < baseStart_2428458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428464 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_2428464 : Nat := 118140960795 + 2428464 * 2 ^ 59
def prefixEnd_2428464 : Nat := 4983230072969 + 3 ^ 40 * 2428464 * 2
def baseEnd_2428464 : Nat := 1246969284140291857131703

theorem tailTrace_2428464 : CollatzResearch.WordTrace tailWord_2428464 prefixEnd_2428464 1246969284140291857131703 := by
  unfold tailWord_2428464
  simp only [CollatzResearch.WordTrace]
  refine ⟨44286679337048575738242223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59048905782731434317656297 44286679337048575738242223)
  ·
    refine ⟨66430019005572863607363335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44286679337048575738242223 66430019005572863607363335)
    ·
      refine ⟨99645028508359295411045003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66430019005572863607363335 99645028508359295411045003)
      ·
        refine ⟨149467542762538943116567505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99645028508359295411045003 149467542762538943116567505)
        ·
          refine ⟨112100657071904207337425629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149467542762538943116567505 112100657071904207337425629)
          ·
            refine ⟨42037746401964077751534611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112100657071904207337425629 42037746401964077751534611)
            ·
              refine ⟨63056619602946116627301917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42037746401964077751534611 63056619602946116627301917)
              ·
                refine ⟨23646232351104793735238219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63056619602946116627301917 23646232351104793735238219)
                ·
                  refine ⟨35469348526657190602857329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23646232351104793735238219 35469348526657190602857329)
                  ·
                    refine ⟨26602011394992892952142997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35469348526657190602857329 26602011394992892952142997)
                    ·
                      refine ⟨1246969284140291857131703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26602011394992892952142997 1246969284140291857131703)
                      ·
                        rfl

theorem cell23_2428464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_2428464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428464 prefixEnd_2428464 := by exact prefixLift 2428464
  have htrace : WordTrace (prefixWord ++ tailWord_2428464) baseStart_2428464 baseEnd_2428464 := by
    simpa [prefixWord, tailWord_2428464, baseEnd_2428464] using wordTrace_append hprefix tailTrace_2428464
  have hstable : (prefixWord ++ tailWord_2428464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428464).length < 2 ^ (prefixWord ++ tailWord_2428464).sum := by decide
  have hdescent : baseEnd_2428464 < baseStart_2428464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428491 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 1, 5]
def baseStart_2428491 : Nat := 118140960795 + 2428491 * 2 ^ 59
def prefixEnd_2428491 : Nat := 4983230072969 + 3 ^ 40 * 2428491 * 2
def baseEnd_2428491 : Nat := 415661049372654417164693

theorem tailTrace_2428491 : CollatzResearch.WordTrace tailWord_2428491 prefixEnd_2428491 415661049372654417164693 := by
  unfold tailWord_2428491
  simp only [CollatzResearch.WordTrace]
  refine ⟨88574343444999335087717327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59049562296666223391811551 88574343444999335087717327)
  ·
    refine ⟨132861515167499002631575991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88574343444999335087717327 132861515167499002631575991)
    ·
      refine ⟨199292272751248503947363987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132861515167499002631575991 199292272751248503947363987)
      ·
        refine ⟨298938409126872755921045981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199292272751248503947363987 298938409126872755921045981)
        ·
          refine ⟨112101903422577283470392243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298938409126872755921045981 112101903422577283470392243)
          ·
            refine ⟨168152855133865925205588365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112101903422577283470392243 168152855133865925205588365)
            ·
              refine ⟨63057320675199721952095637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168152855133865925205588365 63057320675199721952095637)
              ·
                refine ⟨2955811906649986966504483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63057320675199721952095637 2955811906649986966504483)
                ·
                  refine ⟨4433717859974980449756725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955811906649986966504483 4433717859974980449756725)
                  ·
                    refine ⟨415661049372654417164693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4433717859974980449756725 415661049372654417164693)
                    ·
                      rfl

theorem cell23_2428491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 5].length) (baseStart_2428491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428491 prefixEnd_2428491 := by exact prefixLift 2428491
  have htrace : WordTrace (prefixWord ++ tailWord_2428491) baseStart_2428491 baseEnd_2428491 := by
    simpa [prefixWord, tailWord_2428491, baseEnd_2428491] using wordTrace_append hprefix tailTrace_2428491
  have hstable : (prefixWord ++ tailWord_2428491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428491).length < 2 ^ (prefixWord ++ tailWord_2428491).sum := by decide
  have hdescent : baseEnd_2428491 < baseStart_2428491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428522 : List Nat := [3, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_2428522 : Nat := 118140960795 + 2428522 * 2 ^ 59
def prefixEnd_2428522 : Nat := 4983230072969 + 3 ^ 40 * 2428522 * 2
def baseEnd_2428522 : Nat := 1246999066018252630206437

theorem tailTrace_2428522 : CollatzResearch.WordTrace tailWord_2428522 prefixEnd_2428522 1246999066018252630206437 := by
  unfold tailWord_2428522
  simp only [CollatzResearch.WordTrace]
  refine ⟨22143868526971756845523955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59050316071924684921397213 22143868526971756845523955)
  ·
    refine ⟨33215802790457635268285933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22143868526971756845523955 33215802790457635268285933)
    ·
      refine ⟨12455926046421613225607225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33215802790457635268285933 12455926046421613225607225)
      ·
        refine ⟨9341944534816209919205419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12455926046421613225607225 9341944534816209919205419)
        ·
          refine ⟨14012916802224314878808129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9341944534816209919205419 14012916802224314878808129)
          ·
            refine ⟨10509687601668236159106097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14012916802224314878808129 10509687601668236159106097)
            ·
              refine ⟨7882265701251177119329573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10509687601668236159106097 7882265701251177119329573)
              ·
                refine ⟨1477924818984595709874295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7882265701251177119329573 1477924818984595709874295)
                ·
                  refine ⟨2216887228476893564811443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477924818984595709874295 2216887228476893564811443)
                  ·
                    refine ⟨3325330842715340347217165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2216887228476893564811443 3325330842715340347217165)
                    ·
                      refine ⟨1246999066018252630206437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3325330842715340347217165 1246999066018252630206437)
                      ·
                        rfl

theorem cell23_2428522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_2428522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428522 prefixEnd_2428522 := by exact prefixLift 2428522
  have htrace : WordTrace (prefixWord ++ tailWord_2428522) baseStart_2428522 baseEnd_2428522 := by
    simpa [prefixWord, tailWord_2428522, baseEnd_2428522] using wordTrace_append hprefix tailTrace_2428522
  have hstable : (prefixWord ++ tailWord_2428522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428522).length < 2 ^ (prefixWord ++ tailWord_2428522).sum := by decide
  have hdescent : baseEnd_2428522 < baseStart_2428522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428545 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2428545 : Nat := 118140960795 + 2428545 * 2 ^ 59
def prefixEnd_2428545 : Nat := 4983230072969 + 3 ^ 40 * 2428545 * 2
def baseEnd_2428545 : Nat := 1247010876073306040218831

theorem tailTrace_2428545 : CollatzResearch.WordTrace tailWord_2428545 prefixEnd_2428545 1247010876073306040218831 := by
  unfold tailWord_2428545
  simp only [CollatzResearch.WordTrace]
  refine ⟨88576312986803702310183089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59050875324535801540122059 88576312986803702310183089)
  ·
    refine ⟨66432234740102776732637317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88576312986803702310183089 66432234740102776732637317)
    ·
      refine ⟨12456044013769270637369497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66432234740102776732637317 12456044013769270637369497)
      ·
        refine ⟨9342033010326952978027123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12456044013769270637369497 9342033010326952978027123)
        ·
          refine ⟨14013049515490429467040685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9342033010326952978027123 14013049515490429467040685)
          ·
            refine ⟨5254893568308911050140257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14013049515490429467040685 5254893568308911050140257)
            ·
              refine ⟨3941170176231683287605193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5254893568308911050140257 3941170176231683287605193)
              ·
                refine ⟨2955877632173762465703895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3941170176231683287605193 2955877632173762465703895)
                ·
                  refine ⟨4433816448260643698555843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955877632173762465703895 4433816448260643698555843)
                  ·
                    refine ⟨6650724672390965547833765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4433816448260643698555843 6650724672390965547833765)
                    ·
                      refine ⟨1247010876073306040218831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6650724672390965547833765 1247010876073306040218831)
                      ·
                        rfl

theorem cell23_2428545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2428545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428545 prefixEnd_2428545 := by exact prefixLift 2428545
  have htrace : WordTrace (prefixWord ++ tailWord_2428545) baseStart_2428545 baseEnd_2428545 := by
    simpa [prefixWord, tailWord_2428545, baseEnd_2428545] using wordTrace_append hprefix tailTrace_2428545
  have hstable : (prefixWord ++ tailWord_2428545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428545).length < 2 ^ (prefixWord ++ tailWord_2428545).sum := by decide
  have hdescent : baseEnd_2428545 < baseStart_2428545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428551 : List Nat := [1, 1, 4, 2, 1, 4, 1, 9]
def baseStart_2428551 : Nat := 118140960795 + 2428551 * 2 ^ 59
def prefixEnd_2428551 : Nat := 4983230072969 + 3 ^ 40 * 2428551 * 2
def baseEnd_2428551 : Nat := 46185702109527148768289

theorem tailTrace_2428551 : CollatzResearch.WordTrace tailWord_2428551 prefixEnd_2428551 46185702109527148768289 := by
  unfold tailWord_2428551
  simp only [CollatzResearch.WordTrace]
  refine ⟨88576531824781965334901507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59051021216521310223267671 88576531824781965334901507)
  ·
    refine ⟨132864797737172948002352261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88576531824781965334901507 132864797737172948002352261)
    ·
      refine ⟨24912149575719927750441049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132864797737172948002352261 24912149575719927750441049)
      ·
        refine ⟨18684112181789945812830787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24912149575719927750441049 18684112181789945812830787)
        ·
          refine ⟨28026168272684918719246181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18684112181789945812830787 28026168272684918719246181)
          ·
            refine ⟨5254906551128422259858659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28026168272684918719246181 5254906551128422259858659)
            ·
              refine ⟨7882359826692633389787989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254906551128422259858659 7882359826692633389787989)
              ·
                refine ⟨46185702109527148768289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7882359826692633389787989 46185702109527148768289)
                ·
                  rfl

theorem cell23_2428551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 9].length) (baseStart_2428551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428551 prefixEnd_2428551 := by exact prefixLift 2428551
  have htrace : WordTrace (prefixWord ++ tailWord_2428551) baseStart_2428551 baseEnd_2428551 := by
    simpa [prefixWord, tailWord_2428551, baseEnd_2428551] using wordTrace_append hprefix tailTrace_2428551
  have hstable : (prefixWord ++ tailWord_2428551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428551).length < 2 ^ (prefixWord ++ tailWord_2428551).sum := by decide
  have hdescent : baseEnd_2428551 < baseStart_2428551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428579 : List Nat := [1, 1, 1, 4, 1, 1, 7, 2, 1, 2, 2]
def baseStart_2428579 : Nat := 118140960795 + 2428579 * 2 ^ 59
def prefixEnd_2428579 : Nat := 4983230072969 + 3 ^ 40 * 2428579 * 2
def baseEnd_2428579 : Nat := 1247028334415558907193675

theorem tailTrace_2428579 : CollatzResearch.WordTrace tailWord_2428579 prefixEnd_2428579 1247028334415558907193675 := by
  unfold tailWord_2428579
  simp only [CollatzResearch.WordTrace]
  refine ⟨88577553068680526116920791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59051702045787017411280527 88577553068680526116920791)
  ·
    refine ⟨132866329603020789175381187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88577553068680526116920791 132866329603020789175381187)
    ·
      refine ⟨199299494404531183763071781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132866329603020789175381187 199299494404531183763071781)
      ·
        refine ⟨37368655200849596955575959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199299494404531183763071781 37368655200849596955575959)
        ·
          refine ⟨56052982801274395433363939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37368655200849596955575959 56052982801274395433363939)
          ·
            refine ⟨84079474201911593150045909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56052982801274395433363939 84079474201911593150045909)
            ·
              refine ⟨1970612676607302964454201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84079474201911593150045909 1970612676607302964454201)
              ·
                refine ⟨1477959507455477223340651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970612676607302964454201 1477959507455477223340651)
                ·
                  refine ⟨2216939261183215835010977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477959507455477223340651 2216939261183215835010977)
                  ·
                    refine ⟨1662704445887411876258233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2216939261183215835010977 1662704445887411876258233)
                    ·
                      refine ⟨1247028334415558907193675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662704445887411876258233 1247028334415558907193675)
                      ·
                        rfl

theorem cell23_2428579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_2428579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428579 prefixEnd_2428579 := by exact prefixLift 2428579
  have htrace : WordTrace (prefixWord ++ tailWord_2428579) baseStart_2428579 baseEnd_2428579 := by
    simpa [prefixWord, tailWord_2428579, baseEnd_2428579] using wordTrace_append hprefix tailTrace_2428579
  have hstable : (prefixWord ++ tailWord_2428579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428579).length < 2 ^ (prefixWord ++ tailWord_2428579).sum := by decide
  have hdescent : baseEnd_2428579 < baseStart_2428579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428595 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 3]
def baseStart_2428595 : Nat := 118140960795 + 2428595 * 2 ^ 59
def prefixEnd_2428595 : Nat := 4983230072969 + 3 ^ 40 * 2428595 * 2
def baseEnd_2428595 : Nat := 1247036550106030844593601

theorem tailTrace_2428595 : CollatzResearch.WordTrace tailWord_2428595 prefixEnd_2428595 1247036550106030844593601 := by
  unfold tailWord_2428595
  simp only [CollatzResearch.WordTrace]
  refine ⟨88578136636622560849503239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59052091091081707233002159 88578136636622560849503239)
  ·
    refine ⟨132867204954933841274254859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88578136636622560849503239 132867204954933841274254859)
    ·
      refine ⟨199300807432400761911382289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132867204954933841274254859 199300807432400761911382289)
      ·
        refine ⟨149475605574300571433536717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199300807432400761911382289 149475605574300571433536717)
        ·
          refine ⟨56053352090362714287576269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149475605574300571433536717 56053352090362714287576269)
          ·
            refine ⟨21020007033886017857841101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56053352090362714287576269 21020007033886017857841101)
            ·
              refine ⟨7882502637707256696690413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21020007033886017857841101 7882502637707256696690413)
              ·
                refine ⟨2955938489140221261258905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7882502637707256696690413 2955938489140221261258905)
                ·
                  refine ⟨2216953866855165945944179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2955938489140221261258905 2216953866855165945944179)
                  ·
                    refine ⟨3325430800282748918916269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2216953866855165945944179 3325430800282748918916269)
                    ·
                      refine ⟨1247036550106030844593601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3325430800282748918916269 1247036550106030844593601)
                      ·
                        rfl

theorem cell23_2428595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 3].length) (baseStart_2428595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428595 prefixEnd_2428595 := by exact prefixLift 2428595
  have htrace : WordTrace (prefixWord ++ tailWord_2428595) baseStart_2428595 baseEnd_2428595 := by
    simpa [prefixWord, tailWord_2428595, baseEnd_2428595] using wordTrace_append hprefix tailTrace_2428595
  have hstable : (prefixWord ++ tailWord_2428595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428595).length < 2 ^ (prefixWord ++ tailWord_2428595).sum := by decide
  have hdescent : baseEnd_2428595 < baseStart_2428595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428605 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_2428605 : Nat := 118140960795 + 2428605 * 2 ^ 59
def prefixEnd_2428605 : Nat := 4983230072969 + 3 ^ 40 * 2428605 * 2
def baseEnd_2428605 : Nat := 1247041684912575805468555

theorem tailTrace_2428605 : CollatzResearch.WordTrace tailWord_2428605 prefixEnd_2428605 1247041684912575805468555 := by
  unfold tailWord_2428605
  simp only [CollatzResearch.WordTrace]
  refine ⟨88578501366586332557367269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59052334244390888371578179 88578501366586332557367269)
  ·
    refine ⟨16608469006234937354506363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88578501366586332557367269 16608469006234937354506363)
    ·
      refine ⟨24912703509352406031759545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16608469006234937354506363 24912703509352406031759545)
      ·
        refine ⟨18684527632014304523819659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24912703509352406031759545 18684527632014304523819659)
        ·
          refine ⟨28026791448021456785729489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18684527632014304523819659 28026791448021456785729489)
          ·
            refine ⟨21020093586016092589297117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28026791448021456785729489 21020093586016092589297117)
            ·
              refine ⟨7882535094756034720986419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21020093586016092589297117 7882535094756034720986419)
              ·
                refine ⟨11823802642134052081479629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7882535094756034720986419 11823802642134052081479629)
                ·
                  refine ⟨4433925990800269530554861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11823802642134052081479629 4433925990800269530554861)
                  ·
                    refine ⟨1662722246550101073958073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4433925990800269530554861 1662722246550101073958073)
                    ·
                      refine ⟨1247041684912575805468555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662722246550101073958073 1247041684912575805468555)
                      ·
                        rfl

theorem cell23_2428605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_2428605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428605 prefixEnd_2428605 := by exact prefixLift 2428605
  have htrace : WordTrace (prefixWord ++ tailWord_2428605) baseStart_2428605 baseEnd_2428605 := by
    simpa [prefixWord, tailWord_2428605, baseEnd_2428605] using wordTrace_append hprefix tailTrace_2428605
  have hstable : (prefixWord ++ tailWord_2428605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428605).length < 2 ^ (prefixWord ++ tailWord_2428605).sum := by decide
  have hdescent : baseEnd_2428605 < baseStart_2428605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428648 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2428648 : Nat := 118140960795 + 2428648 * 2 ^ 59
def prefixEnd_2428648 : Nat := 4983230072969 + 3 ^ 40 * 2428648 * 2
def baseEnd_2428648 : Nat := 1247063764580719137230857

theorem tailTrace_2428648 : CollatzResearch.WordTrace tailWord_2428648 prefixEnd_2428648 1247063764580719137230857 := by
  unfold tailWord_2428648
  simp only [CollatzResearch.WordTrace]
  refine ⟨44290034852715275450591299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59053379803620367267455065 44290034852715275450591299)
  ·
    refine ⟨66435052279072913175886949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44290034852715275450591299 66435052279072913175886949)
    ·
      refine ⟨12456572302326171220478803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66435052279072913175886949 12456572302326171220478803)
      ·
        refine ⟨18684858453489256830718205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12456572302326171220478803 18684858453489256830718205)
        ·
          refine ⟨7006821920058471311519327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18684858453489256830718205 7006821920058471311519327)
          ·
            refine ⟨10510232880087706967278991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7006821920058471311519327 10510232880087706967278991)
            ·
              refine ⟨15765349320131560450918487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10510232880087706967278991 15765349320131560450918487)
              ·
                refine ⟨23648023980197340676377731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15765349320131560450918487 23648023980197340676377731)
                ·
                  refine ⟨35472035970296011014566597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23648023980197340676377731 35472035970296011014566597)
                  ·
                    refine ⟨6651006744430502065231237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35472035970296011014566597 6651006744430502065231237)
                    ·
                      refine ⟨1247063764580719137230857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6651006744430502065231237 1247063764580719137230857)
                      ·
                        rfl

theorem cell23_2428648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2428648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428648 prefixEnd_2428648 := by exact prefixLift 2428648
  have htrace : WordTrace (prefixWord ++ tailWord_2428648) baseStart_2428648 baseEnd_2428648 := by
    simpa [prefixWord, tailWord_2428648, baseEnd_2428648] using wordTrace_append hprefix tailTrace_2428648
  have hstable : (prefixWord ++ tailWord_2428648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428648).length < 2 ^ (prefixWord ++ tailWord_2428648).sum := by decide
  have hdescent : baseEnd_2428648 < baseStart_2428648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428652 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 2, 2, 2]
def baseStart_2428652 : Nat := 118140960795 + 2428652 * 2 ^ 59
def prefixEnd_2428652 : Nat := 4983230072969 + 3 ^ 40 * 2428652 * 2
def baseEnd_2428652 : Nat := 1247065818503337121580839

theorem tailTrace_2428652 : CollatzResearch.WordTrace tailWord_2428652 prefixEnd_2428652 1247065818503337121580839 := by
  unfold tailWord_2428652
  simp only [CollatzResearch.WordTrace]
  refine ⟨44290107798708029792164105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59053477064944039722885473 44290107798708029792164105)
  ·
    refine ⟨33217580849031022344123079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44290107798708029792164105 33217580849031022344123079)
    ·
      refine ⟨49826371273546533516184619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33217580849031022344123079 49826371273546533516184619)
      ·
        refine ⟨74739556910319800274276929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49826371273546533516184619 74739556910319800274276929)
        ·
          refine ⟨56054667682739850205707697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74739556910319800274276929 56054667682739850205707697)
          ·
            refine ⟨42041000762054887654280773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56054667682739850205707697 42041000762054887654280773)
            ·
              refine ⟨7882687642885291435177645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42041000762054887654280773 7882687642885291435177645)
              ·
                refine ⟨2956007866081984288191617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7882687642885291435177645 2956007866081984288191617)
                ·
                  refine ⟨2217005899561488216143713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2956007866081984288191617 2217005899561488216143713)
                  ·
                    refine ⟨1662754424671116162107785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2217005899561488216143713 1662754424671116162107785)
                    ·
                      refine ⟨1247065818503337121580839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1662754424671116162107785 1247065818503337121580839)
                      ·
                        rfl

theorem cell23_2428652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_2428652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428652 prefixEnd_2428652 := by exact prefixLift 2428652
  have htrace : WordTrace (prefixWord ++ tailWord_2428652) baseStart_2428652 baseEnd_2428652 := by
    simpa [prefixWord, tailWord_2428652, baseEnd_2428652] using wordTrace_append hprefix tailTrace_2428652
  have hstable : (prefixWord ++ tailWord_2428652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428652).length < 2 ^ (prefixWord ++ tailWord_2428652).sum := by decide
  have hdescent : baseEnd_2428652 < baseStart_2428652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428658 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 7]
def baseStart_2428658 : Nat := 118140960795 + 2428658 * 2 ^ 59
def prefixEnd_2428658 : Nat := 4983230072969 + 3 ^ 40 * 2428658 * 2
def baseEnd_2428658 : Nat := 138563211043029344233979

theorem tailTrace_2428658 : CollatzResearch.WordTrace tailWord_2428658 prefixEnd_2428658 138563211043029344233979 := by
  unfold tailWord_2428658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22145108608848580652261657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59053622956929548406031085 22145108608848580652261657)
  ·
    refine ⟨16608831456636435489196243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22145108608848580652261657 16608831456636435489196243)
    ·
      refine ⟨24913247184954653233794365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16608831456636435489196243 24913247184954653233794365)
      ·
        refine ⟨9342467694357994962672887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24913247184954653233794365 9342467694357994962672887)
        ·
          refine ⟨14013701541536992444009331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9342467694357994962672887 14013701541536992444009331)
          ·
            refine ⟨21020552312305488666013997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14013701541536992444009331 21020552312305488666013997)
            ·
              refine ⟨7882707117114558249755249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21020552312305488666013997 7882707117114558249755249)
              ·
                refine ⟨5912030337835918687316437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7882707117114558249755249 5912030337835918687316437)
                ·
                  refine ⟨138563211043029344233979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5912030337835918687316437 138563211043029344233979)
                  ·
                    rfl

theorem cell23_2428658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_2428658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428658 prefixEnd_2428658 := by exact prefixLift 2428658
  have htrace : WordTrace (prefixWord ++ tailWord_2428658) baseStart_2428658 baseEnd_2428658 := by
    simpa [prefixWord, tailWord_2428658, baseEnd_2428658] using wordTrace_append hprefix tailTrace_2428658
  have hstable : (prefixWord ++ tailWord_2428658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428658).length < 2 ^ (prefixWord ++ tailWord_2428658).sum := by decide
  have hdescent : baseEnd_2428658 < baseStart_2428658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428668 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_2428668 : Nat := 118140960795 + 2428668 * 2 ^ 59
def prefixEnd_2428668 : Nat := 4983230072969 + 3 ^ 40 * 2428668 * 2
def baseEnd_2428668 : Nat := 1247074034193809058980765

theorem tailTrace_2428668 : CollatzResearch.WordTrace tailWord_2428668 prefixEnd_2428668 1247074034193809058980765 := by
  unfold tailWord_2428668
  simp only [CollatzResearch.WordTrace]
  refine ⟨44290399582679047158455329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59053866110238729544607105 44290399582679047158455329)
  ·
    refine ⟨33217799687009285368841497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44290399582679047158455329 33217799687009285368841497)
    ·
      refine ⟨24913349765256964026631123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33217799687009285368841497 24913349765256964026631123)
      ·
        refine ⟨37370024647885446039946685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24913349765256964026631123 37370024647885446039946685)
        ·
          refine ⟨14013759242957042264980007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37370024647885446039946685 14013759242957042264980007)
          ·
            refine ⟨21020638864435563397470011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14013759242957042264980007 21020638864435563397470011)
            ·
              refine ⟨31530958296653345096205017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21020638864435563397470011 31530958296653345096205017)
              ·
                refine ⟨23648218722490008822153763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31530958296653345096205017 23648218722490008822153763)
                ·
                  refine ⟨35472328083735013233230645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23648218722490008822153763 35472328083735013233230645)
                  ·
                    refine ⟨3325530757850157490615373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35472328083735013233230645 3325530757850157490615373)
                    ·
                      refine ⟨1247074034193809058980765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3325530757850157490615373 1247074034193809058980765)
                      ·
                        rfl

theorem cell23_2428668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_2428668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428668 prefixEnd_2428668 := by exact prefixLift 2428668
  have htrace : WordTrace (prefixWord ++ tailWord_2428668) baseStart_2428668 baseEnd_2428668 := by
    simpa [prefixWord, tailWord_2428668, baseEnd_2428668] using wordTrace_append hprefix tailTrace_2428668
  have hstable : (prefixWord ++ tailWord_2428668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428668).length < 2 ^ (prefixWord ++ tailWord_2428668).sum := by decide
  have hdescent : baseEnd_2428668 < baseStart_2428668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428745 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 3]
def baseStart_2428745 : Nat := 118140960795 + 2428745 * 2 ^ 59
def prefixEnd_2428745 : Nat := 4983230072969 + 3 ^ 40 * 2428745 * 2
def baseEnd_2428745 : Nat := 1247113572204205257717911

theorem tailTrace_2428745 : CollatzResearch.WordTrace tailWord_2428745 prefixEnd_2428745 1247113572204205257717911 := by
  unfold tailWord_2428745
  simp only [CollatzResearch.WordTrace]
  refine ⟨88583607586079136467463689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59055738390719424311642459 88583607586079136467463689)
  ·
    refine ⟨66437705689559352350597767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88583607586079136467463689 66437705689559352350597767)
    ·
      refine ⟨99656558534339028525896651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66437705689559352350597767 99656558534339028525896651)
      ·
        refine ⟨149484837801508542788844977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99656558534339028525896651 149484837801508542788844977)
        ·
          refine ⟨112113628351131407091633733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149484837801508542788844977 112113628351131407091633733)
          ·
            refine ⟨21021305315837138829681325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112113628351131407091633733 21021305315837138829681325)
            ·
              refine ⟨7882989493438927061130497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21021305315837138829681325 7882989493438927061130497)
              ·
                refine ⟨5912242120079195295847873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7882989493438927061130497 5912242120079195295847873)
                ·
                  refine ⟨4434181590059396471885905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5912242120079195295847873 4434181590059396471885905)
                  ·
                    refine ⟨3325636192544547353914429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4434181590059396471885905 3325636192544547353914429)
                    ·
                      refine ⟨1247113572204205257717911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3325636192544547353914429 1247113572204205257717911)
                      ·
                        rfl

theorem cell23_2428745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_2428745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428745 prefixEnd_2428745 := by exact prefixLift 2428745
  have htrace : WordTrace (prefixWord ++ tailWord_2428745) baseStart_2428745 baseEnd_2428745 := by
    simpa [prefixWord, tailWord_2428745, baseEnd_2428745] using wordTrace_append hprefix tailTrace_2428745
  have hstable : (prefixWord ++ tailWord_2428745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428745).length < 2 ^ (prefixWord ++ tailWord_2428745).sum := by decide
  have hdescent : baseEnd_2428745 < baseStart_2428745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428809 : List Nat := [1, 2, 1, 1, 5, 1, 3, 4, 1, 1, 3]
def baseStart_2428809 : Nat := 118140960795 + 2428809 * 2 ^ 59
def prefixEnd_2428809 : Nat := 4983230072969 + 3 ^ 40 * 2428809 * 2
def baseEnd_2428809 : Nat := 1247146434966093007317617

theorem tailTrace_2428809 : CollatzResearch.WordTrace tailWord_2428809 prefixEnd_2428809 1247146434966093007317617 := by
  unfold tailWord_2428809
  simp only [CollatzResearch.WordTrace]
  refine ⟨88585941857847275397793481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59057294571898183598528987 88585941857847275397793481)
  ·
    refine ⟨66439456393385456548345111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88585941857847275397793481 66439456393385456548345111)
    ·
      refine ⟨99659184590078184822517667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66439456393385456548345111 99659184590078184822517667)
      ·
        refine ⟨149488776885117277233776501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99659184590078184822517667 149488776885117277233776501)
        ·
          refine ⟨14014572832979744740666547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149488776885117277233776501 14014572832979744740666547)
          ·
            refine ⟨21021859249469617110999821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14014572832979744740666547 21021859249469617110999821)
            ·
              refine ⟨7883197218551106416624933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21021859249469617110999821 7883197218551106416624933)
              ·
                refine ⟨1478099478478332453117175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7883197218551106416624933 1478099478478332453117175)
                ·
                  refine ⟨2217149217717498679675763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478099478478332453117175 2217149217717498679675763)
                  ·
                    refine ⟨3325723826576248019513645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2217149217717498679675763 3325723826576248019513645)
                    ·
                      refine ⟨1247146434966093007317617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3325723826576248019513645 1247146434966093007317617)
                      ·
                        rfl

theorem cell23_2428809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 1, 3].length) (baseStart_2428809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428809 prefixEnd_2428809 := by exact prefixLift 2428809
  have htrace : WordTrace (prefixWord ++ tailWord_2428809) baseStart_2428809 baseEnd_2428809 := by
    simpa [prefixWord, tailWord_2428809, baseEnd_2428809] using wordTrace_append hprefix tailTrace_2428809
  have hstable : (prefixWord ++ tailWord_2428809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428809).length < 2 ^ (prefixWord ++ tailWord_2428809).sum := by decide
  have hdescent : baseEnd_2428809 < baseStart_2428809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428849 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 1, 1, 4]
def baseStart_2428849 : Nat := 118140960795 + 2428849 * 2 ^ 59
def prefixEnd_2428849 : Nat := 4983230072969 + 3 ^ 40 * 2428849 * 2
def baseEnd_2428849 : Nat := 1247166974192272850817433

theorem tailTrace_2428849 : CollatzResearch.WordTrace tailWord_2428849 prefixEnd_2428849 1247166974192272850817433 := by
  unfold tailWord_2428849
  simp only [CollatzResearch.WordTrace]
  refine ⟨88587400777702362229249601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59058267185134908152833067 88587400777702362229249601)
  ·
    refine ⟨66440550583276771671937201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88587400777702362229249601 66440550583276771671937201)
    ·
      refine ⟨49830412937457578753952901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66440550583276771671937201 49830412937457578753952901)
      ·
        refine ⟨9343202425773296016366169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49830412937457578753952901 9343202425773296016366169)
        ·
          refine ⟨7007401819329972012274627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9343202425773296016366169 7007401819329972012274627)
          ·
            refine ⟨10511102728994958018411941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7007401819329972012274627 10511102728994958018411941)
            ·
              refine ⟨1970831761686554628452239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10511102728994958018411941 1970831761686554628452239)
              ·
                refine ⟨2956247642529831942678359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970831761686554628452239 2956247642529831942678359)
                ·
                  refine ⟨4434371463794747914017539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2956247642529831942678359 4434371463794747914017539)
                  ·
                    refine ⟨6651557195692121871026309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4434371463794747914017539 6651557195692121871026309)
                    ·
                      refine ⟨1247166974192272850817433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6651557195692121871026309 1247166974192272850817433)
                      ·
                        rfl

theorem cell23_2428849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_2428849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428849 prefixEnd_2428849 := by exact prefixLift 2428849
  have htrace : WordTrace (prefixWord ++ tailWord_2428849) baseStart_2428849 baseEnd_2428849 := by
    simpa [prefixWord, tailWord_2428849, baseEnd_2428849] using wordTrace_append hprefix tailTrace_2428849
  have hstable : (prefixWord ++ tailWord_2428849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428849).length < 2 ^ (prefixWord ++ tailWord_2428849).sum := by decide
  have hdescent : baseEnd_2428849 < baseStart_2428849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428889 : List Nat := [1, 2, 1, 2, 7, 1, 2, 7]
def baseStart_2428889 : Nat := 118140960795 + 2428889 * 2 ^ 59
def prefixEnd_2428889 : Nat := 4983230072969 + 3 ^ 40 * 2428889 * 2
def baseEnd_2428889 : Nat := 46192130126609359048787

theorem tailTrace_2428889 : CollatzResearch.WordTrace tailWord_2428889 prefixEnd_2428889 46192130126609359048787 := by
  unfold tailWord_2428889
  simp only [CollatzResearch.WordTrace]
  refine ⟨88588859697557449060705721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59059239798371632707137147 88588859697557449060705721)
  ·
    refine ⟨66441644773168086795529291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88588859697557449060705721 66441644773168086795529291)
    ·
      refine ⟨99662467159752130193293937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66441644773168086795529291 99662467159752130193293937)
      ·
        refine ⟨74746850369814097644970453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99662467159752130193293937 74746850369814097644970453)
        ·
          refine ⟨1751879305542517913553995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 74746850369814097644970453 1751879305542517913553995)
          ·
            refine ⟨2627818958313776870330993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751879305542517913553995 2627818958313776870330993)
            ·
              refine ⟨1970864218735332652748245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2627818958313776870330993 1970864218735332652748245)
              ·
                refine ⟨46192130126609359048787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1970864218735332652748245 46192130126609359048787)
                ·
                  rfl

theorem cell23_2428889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 7].length) (baseStart_2428889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428889 prefixEnd_2428889 := by exact prefixLift 2428889
  have htrace : WordTrace (prefixWord ++ tailWord_2428889) baseStart_2428889 baseEnd_2428889 := by
    simpa [prefixWord, tailWord_2428889, baseEnd_2428889] using wordTrace_append hprefix tailTrace_2428889
  have hstable : (prefixWord ++ tailWord_2428889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428889).length < 2 ^ (prefixWord ++ tailWord_2428889).sum := by decide
  have hdescent : baseEnd_2428889 < baseStart_2428889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428895 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_2428895 : Nat := 118140960795 + 2428895 * 2 ^ 59
def prefixEnd_2428895 : Nat := 4983230072969 + 3 ^ 40 * 2428895 * 2
def baseEnd_2428895 : Nat := 1247190594302379670842221

theorem tailTrace_2428895 : CollatzResearch.WordTrace tailWord_2428895 prefixEnd_2428895 1247190594302379670842221 := by
  unfold tailWord_2428895
  simp only [CollatzResearch.WordTrace]
  refine ⟨88589078535535712085424139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59059385690357141390282759 88589078535535712085424139)
  ·
    refine ⟨132883617803303568128136209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88589078535535712085424139 132883617803303568128136209)
    ·
      refine ⟨99662713352477676096102157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132883617803303568128136209 99662713352477676096102157)
      ·
        refine ⟨37373517507179128536038309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99662713352477676096102157 37373517507179128536038309)
        ·
          refine ⟨7007534532596086600507183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37373517507179128536038309 7007534532596086600507183)
          ·
            refine ⟨10511301798894129900760775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7007534532596086600507183 10511301798894129900760775)
            ·
              refine ⟨15766952698341194851141163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10511301798894129900760775 15766952698341194851141163)
              ·
                refine ⟨23650429047511792276711745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15766952698341194851141163 23650429047511792276711745)
                ·
                  refine ⟨17737821785633844207533809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23650429047511792276711745 17737821785633844207533809)
                  ·
                    refine ⟨13303366339225383155650357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17737821785633844207533809 13303366339225383155650357)
                    ·
                      refine ⟨1247190594302379670842221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13303366339225383155650357 1247190594302379670842221)
                      ·
                        rfl

theorem cell23_2428895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_2428895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428895 prefixEnd_2428895 := by exact prefixLift 2428895
  have htrace : WordTrace (prefixWord ++ tailWord_2428895) baseStart_2428895 baseEnd_2428895 := by
    simpa [prefixWord, tailWord_2428895, baseEnd_2428895] using wordTrace_append hprefix tailTrace_2428895
  have hstable : (prefixWord ++ tailWord_2428895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428895).length < 2 ^ (prefixWord ++ tailWord_2428895).sum := by decide
  have hdescent : baseEnd_2428895 < baseStart_2428895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428955 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 3]
def baseStart_2428955 : Nat := 118140960795 + 2428955 * 2 ^ 59
def prefixEnd_2428955 : Nat := 4983230072969 + 3 ^ 40 * 2428955 * 2
def baseEnd_2428955 : Nat := 1247221403141649436091945

theorem tailTrace_2428955 : CollatzResearch.WordTrace tailWord_2428955 prefixEnd_2428955 1247221403141649436091945 := by
  unfold tailWord_2428955
  simp only [CollatzResearch.WordTrace]
  refine ⟨88591266915318342332608319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59060844610212228221738879 88591266915318342332608319)
  ·
    refine ⟨132886900372977513498912479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88591266915318342332608319 132886900372977513498912479)
    ·
      refine ⟨199330350559466270248368719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132886900372977513498912479 199330350559466270248368719)
      ·
        refine ⟨298995525839199405372553079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199330350559466270248368719 298995525839199405372553079)
        ·
          refine ⟨448493288758799108058829619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298995525839199405372553079 448493288758799108058829619)
          ·
            refine ⟨672739933138198662088244429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448493288758799108058829619 672739933138198662088244429)
            ·
              refine ⟨252277474926824498283091661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 672739933138198662088244429 252277474926824498283091661)
              ·
                refine ⟨94604053097559186856159373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252277474926824498283091661 94604053097559186856159373)
                ·
                  refine ⟨35476519911584695071059765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94604053097559186856159373 35476519911584695071059765)
                  ·
                    refine ⟨3325923741711065162911853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35476519911584695071059765 3325923741711065162911853)
                    ·
                      refine ⟨1247221403141649436091945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3325923741711065162911853 1247221403141649436091945)
                      ·
                        rfl

theorem cell23_2428955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 3].length) (baseStart_2428955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428955 prefixEnd_2428955 := by exact prefixLift 2428955
  have htrace : WordTrace (prefixWord ++ tailWord_2428955) baseStart_2428955 baseEnd_2428955 := by
    simpa [prefixWord, tailWord_2428955, baseEnd_2428955] using wordTrace_append hprefix tailTrace_2428955
  have hstable : (prefixWord ++ tailWord_2428955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428955).length < 2 ^ (prefixWord ++ tailWord_2428955).sum := by decide
  have hdescent : baseEnd_2428955 < baseStart_2428955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428975 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 4, 5]
def baseStart_2428975 : Nat := 118140960795 + 2428975 * 2 ^ 59
def prefixEnd_2428975 : Nat := 4983230072969 + 3 ^ 40 * 2428975 * 2
def baseEnd_2428975 : Nat := 415743890918246452613951

theorem tailTrace_2428975 : CollatzResearch.WordTrace tailWord_2428975 prefixEnd_2428975 415743890918246452613951 := by
  unfold tailWord_2428975
  simp only [CollatzResearch.WordTrace]
  refine ⟨88591996375245885748336379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59061330916830590498890919 88591996375245885748336379)
  ·
    refine ⟨132887994562868828622504569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88591996375245885748336379 132887994562868828622504569)
    ·
      refine ⟨99665995922151621466878427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132887994562868828622504569 99665995922151621466878427)
      ·
        refine ⟨149498993883227432200317641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99665995922151621466878427 149498993883227432200317641)
        ·
          refine ⟨112124245412420574150238231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149498993883227432200317641 112124245412420574150238231)
          ·
            refine ⟨168186368118630861225357347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112124245412420574150238231 168186368118630861225357347)
            ·
              refine ⟨252279552177946291838036021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168186368118630861225357347 252279552177946291838036021)
              ·
                refine ⟨23651208016682464859815877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252279552177946291838036021 23651208016682464859815877)
                ·
                  refine ⟨4434601503127962161215477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23651208016682464859815877 4434601503127962161215477)
                  ·
                    refine ⟨415743890918246452613951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4434601503127962161215477 415743890918246452613951)
                    ·
                      rfl

theorem cell23_2428975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_2428975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428975 prefixEnd_2428975 := by exact prefixLift 2428975
  have htrace : WordTrace (prefixWord ++ tailWord_2428975) baseStart_2428975 baseEnd_2428975 := by
    simpa [prefixWord, tailWord_2428975, baseEnd_2428975] using wordTrace_append hprefix tailTrace_2428975
  have hstable : (prefixWord ++ tailWord_2428975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428975).length < 2 ^ (prefixWord ++ tailWord_2428975).sum := by decide
  have hdescent : baseEnd_2428975 < baseStart_2428975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2428979 : List Nat := [1, 1, 1, 2, 4, 1, 6, 2, 5]
def baseStart_2428979 : Nat := 118140960795 + 2428979 * 2 ^ 59
def prefixEnd_2428979 : Nat := 4983230072969 + 3 ^ 40 * 2428979 * 2
def baseEnd_2428979 : Nat := 138581525186373038021315

theorem tailTrace_2428979 : CollatzResearch.WordTrace tailWord_2428979 prefixEnd_2428979 138581525186373038021315 := by
  unfold tailWord_2428979
  simp only [CollatzResearch.WordTrace]
  refine ⟨88592142267231394431481991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59061428178154262954321327 88592142267231394431481991)
  ·
    refine ⟨132888213400847091647222987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88592142267231394431481991 132888213400847091647222987)
    ·
      refine ⟨199332320101270637470834481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132888213400847091647222987 199332320101270637470834481)
      ·
        refine ⟨149499240075952978103125861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199332320101270637470834481 149499240075952978103125861)
        ·
          refine ⟨28031107514241183394336099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149499240075952978103125861 28031107514241183394336099)
          ·
            refine ⟨42046661271361775091504149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28031107514241183394336099 42046661271361775091504149)
            ·
              refine ⟨1970937247095083207414257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42046661271361775091504149 1970937247095083207414257)
              ·
                refine ⟨1478202935321312405560693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970937247095083207414257 1478202935321312405560693)
                ·
                  refine ⟨138581525186373038021315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1478202935321312405560693 138581525186373038021315)
                  ·
                    rfl

theorem cell23_2428979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 5].length) (baseStart_2428979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2428979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2428979 prefixEnd_2428979 := by exact prefixLift 2428979
  have htrace : WordTrace (prefixWord ++ tailWord_2428979) baseStart_2428979 baseEnd_2428979 := by
    simpa [prefixWord, tailWord_2428979, baseEnd_2428979] using wordTrace_append hprefix tailTrace_2428979
  have hstable : (prefixWord ++ tailWord_2428979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2428979).length < 2 ^ (prefixWord ++ tailWord_2428979).sum := by decide
  have hdescent : baseEnd_2428979 < baseStart_2428979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2428979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429029 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 2, 4, 2]
def baseStart_2429029 : Nat := 118140960795 + 2429029 * 2 ^ 59
def prefixEnd_2429029 : Nat := 4983230072969 + 3 ^ 40 * 2429029 * 2
def baseEnd_2429029 : Nat := 1247259400710082146566605

theorem tailTrace_2429029 : CollatzResearch.WordTrace tailWord_2429029 prefixEnd_2429029 1247259400710082146566605 := by
  unfold tailWord_2429029
  simp only [CollatzResearch.WordTrace]
  refine ⟨88593965917050252970802141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59062643944700168647201427 88593965917050252970802141)
  ·
    refine ⟨33222737218893844864050803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88593965917050252970802141 33222737218893844864050803)
    ·
      refine ⟨49834105828340767296076205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33222737218893844864050803 49834105828340767296076205)
      ·
        refine ⟨18687789685627787736028577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49834105828340767296076205 18687789685627787736028577)
        ·
          refine ⟨14015842264220840802021433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18687789685627787736028577 14015842264220840802021433)
          ·
            refine ⟨10511881698165630601516075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14015842264220840802021433 10511881698165630601516075)
            ·
              refine ⟨15767822547248445902274113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10511881698165630601516075 15767822547248445902274113)
              ·
                refine ⟨11825866910436334426705585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15767822547248445902274113 11825866910436334426705585)
                ·
                  refine ⟨8869400182827250820029189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11825866910436334426705585 8869400182827250820029189)
                  ·
                    refine ⟨1663012534280109528755473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8869400182827250820029189 1663012534280109528755473)
                    ·
                      refine ⟨1247259400710082146566605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663012534280109528755473 1247259400710082146566605)
                      ·
                        rfl

theorem cell23_2429029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_2429029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429029 prefixEnd_2429029 := by exact prefixLift 2429029
  have htrace : WordTrace (prefixWord ++ tailWord_2429029) baseStart_2429029 baseEnd_2429029 := by
    simpa [prefixWord, tailWord_2429029, baseEnd_2429029] using wordTrace_append hprefix tailTrace_2429029
  have hstable : (prefixWord ++ tailWord_2429029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429029).length < 2 ^ (prefixWord ++ tailWord_2429029).sum := by decide
  have hdescent : baseEnd_2429029 < baseStart_2429029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429039 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 3, 4]
def baseStart_2429039 : Nat := 118140960795 + 2429039 * 2 ^ 59
def prefixEnd_2429039 : Nat := 4983230072969 + 3 ^ 40 * 2429039 * 2
def baseEnd_2429039 : Nat := 415754845172209035813853

theorem tailTrace_2429039 : CollatzResearch.WordTrace tailWord_2429039 prefixEnd_2429039 415754845172209035813853 := by
  unfold tailWord_2429039
  simp only [CollatzResearch.WordTrace]
  refine ⟨88594330647014024678666171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59062887098009349785777447 88594330647014024678666171)
  ·
    refine ⟨132891495970521037017999257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88594330647014024678666171 132891495970521037017999257)
    ·
      refine ⟨99668621977890777763499443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132891495970521037017999257 99668621977890777763499443)
      ·
        refine ⟨149502932966836166645249165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99668621977890777763499443 149502932966836166645249165)
        ·
          refine ⟨56063599862563562491968437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149502932966836166645249165 56063599862563562491968437)
          ·
            refine ⟨5255962487115333983622041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56063599862563562491968437 5255962487115333983622041)
            ·
              refine ⟨3941971865336500487716531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5255962487115333983622041 3941971865336500487716531)
              ·
                refine ⟨5912957798004750731574797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941971865336500487716531 5912957798004750731574797)
                ·
                  refine ⟨2217359174251781524340549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5912957798004750731574797 2217359174251781524340549)
                  ·
                    refine ⟨415754845172209035813853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2217359174251781524340549 415754845172209035813853)
                    ·
                      rfl

theorem cell23_2429039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 4].length) (baseStart_2429039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429039 prefixEnd_2429039 := by exact prefixLift 2429039
  have htrace : WordTrace (prefixWord ++ tailWord_2429039) baseStart_2429039 baseEnd_2429039 := by
    simpa [prefixWord, tailWord_2429039, baseEnd_2429039] using wordTrace_append hprefix tailTrace_2429039
  have hstable : (prefixWord ++ tailWord_2429039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429039).length < 2 ^ (prefixWord ++ tailWord_2429039).sum := by decide
  have hdescent : baseEnd_2429039 < baseStart_2429039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429046 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_2429046 : Nat := 118140960795 + 2429046 * 2 ^ 59
def prefixEnd_2429046 : Nat := 4983230072969 + 3 ^ 40 * 2429046 * 2
def baseEnd_2429046 : Nat := 1247268129881208580054027

theorem tailTrace_2429046 : CollatzResearch.WordTrace tailWord_2429046 prefixEnd_2429046 1247268129881208580054027 := by
  unfold tailWord_2429046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537161622374291554635687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59063057305325776582780661 5537161622374291554635687)
  ·
    refine ⟨8305742433561437331953531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5537161622374291554635687 8305742433561437331953531)
    ·
      refine ⟨12458613650342155997930297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8305742433561437331953531 12458613650342155997930297)
      ·
        refine ⟨9343960237756616998447723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12458613650342155997930297 9343960237756616998447723)
        ·
          refine ⟨14015940356634925497671585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9343960237756616998447723 14015940356634925497671585)
          ·
            refine ⟨10511955267476194123253689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14015940356634925497671585 10511955267476194123253689)
            ·
              refine ⟨7883966450607145592440267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10511955267476194123253689 7883966450607145592440267)
              ·
                refine ⟨11825949675910718388660401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7883966450607145592440267 11825949675910718388660401)
                ·
                  refine ⟨8869462256933038791495301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11825949675910718388660401 8869462256933038791495301)
                  ·
                    refine ⟨1663024173174944773405369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8869462256933038791495301 1663024173174944773405369)
                    ·
                      refine ⟨1247268129881208580054027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663024173174944773405369 1247268129881208580054027)
                      ·
                        rfl

theorem cell23_2429046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_2429046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429046 prefixEnd_2429046 := by exact prefixLift 2429046
  have htrace : WordTrace (prefixWord ++ tailWord_2429046) baseStart_2429046 baseEnd_2429046 := by
    simpa [prefixWord, tailWord_2429046, baseEnd_2429046] using wordTrace_append hprefix tailTrace_2429046
  have hstable : (prefixWord ++ tailWord_2429046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429046).length < 2 ^ (prefixWord ++ tailWord_2429046).sum := by decide
  have hdescent : baseEnd_2429046 < baseStart_2429046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429090 : List Nat := [3, 3, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_2429090 : Nat := 118140960795 + 2429090 * 2 ^ 59
def prefixEnd_2429090 : Nat := 4983230072969 + 3 ^ 40 * 2429090 * 2
def baseEnd_2429090 : Nat := 415763574343335469301275

theorem tailTrace_2429090 : CollatzResearch.WordTrace tailWord_2429090 prefixEnd_2429090 415763574343335469301275 := by
  unfold tailWord_2429090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22149047692457315097193181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59064127179886173592515149 22149047692457315097193181)
  ·
    refine ⟨8305892884671493161447443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22149047692457315097193181 8305892884671493161447443)
    ·
      refine ⟨12458839327007239742171165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8305892884671493161447443 12458839327007239742171165)
      ·
        refine ⟨4672064747627714903314187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12458839327007239742171165 4672064747627714903314187)
        ·
          refine ⟨7008097121441572354971281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4672064747627714903314187 7008097121441572354971281)
          ·
            refine ⟨5256072841081179266228461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7008097121441572354971281 5256072841081179266228461)
            ·
              refine ⟨1971027315405442224835673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5256072841081179266228461 1971027315405442224835673)
              ·
                refine ⟨1478270486554081668626755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1971027315405442224835673 1478270486554081668626755)
                ·
                  refine ⟨2217405729831122502940133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478270486554081668626755 2217405729831122502940133)
                  ·
                    refine ⟨415763574343335469301275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2217405729831122502940133 415763574343335469301275)
                    ·
                      rfl

theorem cell23_2429090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_2429090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429090 prefixEnd_2429090 := by exact prefixLift 2429090
  have htrace : WordTrace (prefixWord ++ tailWord_2429090) baseStart_2429090 baseEnd_2429090 := by
    simpa [prefixWord, tailWord_2429090, baseEnd_2429090] using wordTrace_append hprefix tailTrace_2429090
  have hstable : (prefixWord ++ tailWord_2429090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429090).length < 2 ^ (prefixWord ++ tailWord_2429090).sum := by decide
  have hdescent : baseEnd_2429090 < baseStart_2429090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429112 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 1, 6]
def baseStart_2429112 : Nat := 118140960795 + 2429112 * 2 ^ 59
def prefixEnd_2429112 : Nat := 4983230072969 + 3 ^ 40 * 2429112 * 2
def baseEnd_2429112 : Nat := 415767339868135107276241

theorem tailTrace_2429112 : CollatzResearch.WordTrace tailWord_2429112 prefixEnd_2429112 415767339868135107276241 := by
  unfold tailWord_2429112
  simp only [CollatzResearch.WordTrace]
  refine ⟨44298496587874779073036795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59064662117166372097382393 44298496587874779073036795)
  ·
    refine ⟨66447744881812168609555193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44298496587874779073036795 66447744881812168609555193)
    ·
      refine ⟨49835808661359126457166395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66447744881812168609555193 49835808661359126457166395)
      ·
        refine ⟨74753712992038689685749593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49835808661359126457166395 74753712992038689685749593)
        ·
          refine ⟨56065284744029017264312195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74753712992038689685749593 56065284744029017264312195)
          ·
            refine ⟨84097927116043525896468293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56065284744029017264312195 84097927116043525896468293)
            ·
              refine ⟨15768361334258161105587805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84097927116043525896468293 15768361334258161105587805)
              ·
                refine ⟨5913135500346810414595427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15768361334258161105587805 5913135500346810414595427)
                ·
                  refine ⟨8869703250520215621893141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5913135500346810414595427 8869703250520215621893141)
                  ·
                    refine ⟨415767339868135107276241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8869703250520215621893141 415767339868135107276241)
                    ·
                      rfl

theorem cell23_2429112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_2429112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429112 prefixEnd_2429112 := by exact prefixLift 2429112
  have htrace : WordTrace (prefixWord ++ tailWord_2429112) baseStart_2429112 baseEnd_2429112 := by
    simpa [prefixWord, tailWord_2429112, baseEnd_2429112] using wordTrace_append hprefix tailTrace_2429112
  have hstable : (prefixWord ++ tailWord_2429112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429112).length < 2 ^ (prefixWord ++ tailWord_2429112).sum := by decide
  have hdescent : baseEnd_2429112 < baseStart_2429112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429159 : List Nat := [1, 1, 5, 3, 1, 1, 3, 8]
def baseStart_2429159 : Nat := 118140960795 + 2429159 * 2 ^ 59
def prefixEnd_2429159 : Nat := 4983230072969 + 3 ^ 40 * 2429159 * 2
def baseEnd_2429159 : Nat := 46197264933154319923741

theorem tailTrace_2429159 : CollatzResearch.WordTrace tailWord_2429159 prefixEnd_2429159 46197264933154319923741 := by
  unfold tailWord_2429159
  simp only [CollatzResearch.WordTrace]
  refine ⟨88598707406579285173034531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59065804937719523448689687 88598707406579285173034531)
  ·
    refine ⟨132898061109868927759551797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88598707406579285173034531 132898061109868927759551797)
    ·
      refine ⟨12459193229050211977457981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132898061109868927759551797 12459193229050211977457981)
      ·
        refine ⟨4672197460893829491546743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12459193229050211977457981 4672197460893829491546743)
        ·
          refine ⟨7008296191340744237320115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4672197460893829491546743 7008296191340744237320115)
          ·
            refine ⟨10512444287011116355980173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7008296191340744237320115 10512444287011116355980173)
            ·
              refine ⟨3942166607629168633492565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10512444287011116355980173 3942166607629168633492565)
              ·
                refine ⟨46197264933154319923741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3942166607629168633492565 46197264933154319923741)
                ·
                  rfl

theorem cell23_2429159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 8].length) (baseStart_2429159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429159 prefixEnd_2429159 := by exact prefixLift 2429159
  have htrace : WordTrace (prefixWord ++ tailWord_2429159) baseStart_2429159 baseEnd_2429159 := by
    simpa [prefixWord, tailWord_2429159, baseEnd_2429159] using wordTrace_append hprefix tailTrace_2429159
  have hstable : (prefixWord ++ tailWord_2429159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429159).length < 2 ^ (prefixWord ++ tailWord_2429159).sum := by decide
  have hdescent : baseEnd_2429159 < baseStart_2429159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429169 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_2429169 : Nat := 118140960795 + 2429169 * 2 ^ 59
def prefixEnd_2429169 : Nat := 4983230072969 + 3 ^ 40 * 2429169 * 2
def baseEnd_2429169 : Nat := 1247331288001711598815961

theorem tailTrace_2429169 : CollatzResearch.WordTrace tailWord_2429169 prefixEnd_2429169 1247331288001711598815961 := by
  unfold tailWord_2429169
  simp only [CollatzResearch.WordTrace]
  refine ⟨88599072136543056880898561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59066048091028704587265707 88599072136543056880898561)
  ·
    refine ⟨66449304102407292660673921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88599072136543056880898561 66449304102407292660673921)
    ·
      refine ⟨49836978076805469495505441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66449304102407292660673921 49836978076805469495505441)
      ·
        refine ⟨37377733557604102121629081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49836978076805469495505441 37377733557604102121629081)
        ·
          refine ⟨28033300168203076591221811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37377733557604102121629081 28033300168203076591221811)
          ·
            refine ⟨42049950252304614886832717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28033300168203076591221811 42049950252304614886832717)
            ·
              refine ⟨15768731344614230582562269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42049950252304614886832717 15768731344614230582562269)
              ·
                refine ⟨5913274254230336468460851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15768731344614230582562269 5913274254230336468460851)
                ·
                  refine ⟨8869911381345504702691277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5913274254230336468460851 8869911381345504702691277)
                  ·
                    refine ⟨3326216768004564263509229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8869911381345504702691277 3326216768004564263509229)
                    ·
                      refine ⟨1247331288001711598815961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3326216768004564263509229 1247331288001711598815961)
                      ·
                        rfl

theorem cell23_2429169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_2429169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429169 prefixEnd_2429169 := by exact prefixLift 2429169
  have htrace : WordTrace (prefixWord ++ tailWord_2429169) baseStart_2429169 baseEnd_2429169 := by
    simpa [prefixWord, tailWord_2429169, baseEnd_2429169] using wordTrace_append hprefix tailTrace_2429169
  have hstable : (prefixWord ++ tailWord_2429169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429169).length < 2 ^ (prefixWord ++ tailWord_2429169).sum := by decide
  have hdescent : baseEnd_2429169 < baseStart_2429169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429209 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 10, 2]
def baseStart_2429209 : Nat := 118140960795 + 2429209 * 2 ^ 59
def prefixEnd_2429209 : Nat := 4983230072969 + 3 ^ 40 * 2429209 * 2
def baseEnd_2429209 : Nat := 1247351827227891442315777

theorem tailTrace_2429209 : CollatzResearch.WordTrace tailWord_2429209 prefixEnd_2429209 1247351827227891442315777 := by
  unfold tailWord_2429209
  simp only [CollatzResearch.WordTrace]
  refine ⟨88600531056398143712354681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59067020704265429141569787 88600531056398143712354681)
  ·
    refine ⟨66450398292298607784266011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88600531056398143712354681 66450398292298607784266011)
    ·
      refine ⟨99675597438447911676399017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66450398292298607784266011 99675597438447911676399017)
      ·
        refine ⟨74756698078835933757299263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99675597438447911676399017 74756698078835933757299263)
        ·
          refine ⟨112135047118253900635948895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74756698078835933757299263 112135047118253900635948895)
          ·
            refine ⟨168202570677380850953923343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112135047118253900635948895 168202570677380850953923343)
            ·
              refine ⟨252303856016071276430885015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168202570677380850953923343 252303856016071276430885015)
              ·
                refine ⟨378455784024106914646327523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252303856016071276430885015 378455784024106914646327523)
                ·
                  refine ⟨567683676036160371969491285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378455784024106914646327523 567683676036160371969491285)
                  ·
                    refine ⟨1663135769637188589754369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 567683676036160371969491285 1663135769637188589754369)
                    ·
                      refine ⟨1247351827227891442315777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663135769637188589754369 1247351827227891442315777)
                      ·
                        rfl

theorem cell23_2429209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_2429209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429209 prefixEnd_2429209 := by exact prefixLift 2429209
  have htrace : WordTrace (prefixWord ++ tailWord_2429209) baseStart_2429209 baseEnd_2429209 := by
    simpa [prefixWord, tailWord_2429209, baseEnd_2429209] using wordTrace_append hprefix tailTrace_2429209
  have hstable : (prefixWord ++ tailWord_2429209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429209).length < 2 ^ (prefixWord ++ tailWord_2429209).sum := by decide
  have hdescent : baseEnd_2429209 < baseStart_2429209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429220 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_2429220 : Nat := 118140960795 + 2429220 * 2 ^ 59
def prefixEnd_2429220 : Nat := 4983230072969 + 3 ^ 40 * 2429220 * 2
def baseEnd_2429220 : Nat := 1247357475515090899278227

theorem tailTrace_2429220 : CollatzResearch.WordTrace tailWord_2429220 prefixEnd_2429220 1247357475515090899278227 := by
  unfold tailWord_2429220
  simp only [CollatzResearch.WordTrace]
  refine ⟨44300466129679146295502557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59067288172905528394003409 44300466129679146295502557)
  ·
    refine ⟨16612674798629679860813459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44300466129679146295502557 16612674798629679860813459)
    ·
      refine ⟨24919012197944519791220189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16612674798629679860813459 24919012197944519791220189)
      ·
        refine ⟨9344629574229194921707571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24919012197944519791220189 9344629574229194921707571)
        ·
          refine ⟨14016944361343792382561357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9344629574229194921707571 14016944361343792382561357)
          ·
            refine ⟨5256354135503922143460509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14016944361343792382561357 5256354135503922143460509)
            ·
              refine ⟨1971132800813970803797691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5256354135503922143460509 1971132800813970803797691)
              ·
                refine ⟨2956699201220956205696537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971132800813970803797691 2956699201220956205696537)
                ·
                  refine ⟨2217524400915717154272403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2956699201220956205696537 2217524400915717154272403)
                  ·
                    refine ⟨3326286601373575731408605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2217524400915717154272403 3326286601373575731408605)
                    ·
                      refine ⟨1247357475515090899278227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3326286601373575731408605 1247357475515090899278227)
                      ·
                        rfl

theorem cell23_2429220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_2429220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429220 prefixEnd_2429220 := by exact prefixLift 2429220
  have htrace : WordTrace (prefixWord ++ tailWord_2429220) baseStart_2429220 baseEnd_2429220 := by
    simpa [prefixWord, tailWord_2429220, baseEnd_2429220] using wordTrace_append hprefix tailTrace_2429220
  have hstable : (prefixWord ++ tailWord_2429220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429220).length < 2 ^ (prefixWord ++ tailWord_2429220).sum := by decide
  have hdescent : baseEnd_2429220 < baseStart_2429220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429232 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 9]
def baseStart_2429232 : Nat := 118140960795 + 2429232 * 2 ^ 59
def prefixEnd_2429232 : Nat := 4983230072969 + 3 ^ 40 * 2429232 * 2
def baseEnd_2429232 : Nat := 138595959698104983592019

theorem tailTrace_2429232 : CollatzResearch.WordTrace tailWord_2429232 prefixEnd_2429232 138595959698104983592019 := by
  unfold tailWord_2429232
  simp only [CollatzResearch.WordTrace]
  refine ⟨44300684967657409320220975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59067579956876545760294633 44300684967657409320220975)
  ·
    refine ⟨66451027451486113980331463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44300684967657409320220975 66451027451486113980331463)
    ·
      refine ⟨99676541177229170970497195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66451027451486113980331463 99676541177229170970497195)
      ·
        refine ⟨149514811765843756455745793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99676541177229170970497195 149514811765843756455745793)
        ·
          refine ⟨112136108824382817341809345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149514811765843756455745793 112136108824382817341809345)
          ·
            refine ⟨84102081618287113006357009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112136108824382817341809345 84102081618287113006357009)
            ·
              refine ⟨63076561213715334754767757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84102081618287113006357009 63076561213715334754767757)
              ·
                refine ⟨23653710455143250533037909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63076561213715334754767757 23653710455143250533037909)
                ·
                  refine ⟨138595959698104983592019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23653710455143250533037909 138595959698104983592019)
                  ·
                    rfl

theorem cell23_2429232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 9].length) (baseStart_2429232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429232 prefixEnd_2429232 := by exact prefixLift 2429232
  have htrace : WordTrace (prefixWord ++ tailWord_2429232) baseStart_2429232 baseEnd_2429232 := by
    simpa [prefixWord, tailWord_2429232, baseEnd_2429232] using wordTrace_append hprefix tailTrace_2429232
  have hstable : (prefixWord ++ tailWord_2429232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429232).length < 2 ^ (prefixWord ++ tailWord_2429232).sum := by decide
  have hdescent : baseEnd_2429232 < baseStart_2429232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429246 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2429246 : Nat := 118140960795 + 2429246 * 2 ^ 59
def prefixEnd_2429246 : Nat := 4983230072969 + 3 ^ 40 * 2429246 * 2
def baseEnd_2429246 : Nat := 1247370826012107797553107

theorem tailTrace_2429246 : CollatzResearch.WordTrace tailWord_2429246 prefixEnd_2429246 1247370826012107797553107 := by
  unfold tailWord_2429246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11075235069658012378931449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59067920371509399354301061 11075235069658012378931449)
  ·
    refine ⟨8306426302243509284198587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11075235069658012378931449 8306426302243509284198587)
    ·
      refine ⟨12459639453365263926297881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8306426302243509284198587 12459639453365263926297881)
      ·
        refine ⟨9344729590023947944723411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12459639453365263926297881 9344729590023947944723411)
        ·
          refine ⟨14017094385035921917085117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9344729590023947944723411 14017094385035921917085117)
          ·
            refine ⟨5256410394388470718906919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14017094385035921917085117 5256410394388470718906919)
            ·
              refine ⟨7884615591582706078360379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5256410394388470718906919 7884615591582706078360379)
              ·
                refine ⟨11826923387374059117540569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7884615591582706078360379 11826923387374059117540569)
                ·
                  refine ⟨8870192540530544338155427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11826923387374059117540569 8870192540530544338155427)
                  ·
                    refine ⟨13305288810795816507233141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8870192540530544338155427 13305288810795816507233141)
                    ·
                      refine ⟨1247370826012107797553107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13305288810795816507233141 1247370826012107797553107)
                      ·
                        rfl

theorem cell23_2429246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2429246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429246 prefixEnd_2429246 := by exact prefixLift 2429246
  have htrace : WordTrace (prefixWord ++ tailWord_2429246) baseStart_2429246 baseEnd_2429246 := by
    simpa [prefixWord, tailWord_2429246, baseEnd_2429246] using wordTrace_append hprefix tailTrace_2429246
  have hstable : (prefixWord ++ tailWord_2429246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429246).length < 2 ^ (prefixWord ++ tailWord_2429246).sum := by decide
  have hdescent : baseEnd_2429246 < baseStart_2429246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429259 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 3]
def baseStart_2429259 : Nat := 118140960795 + 2429259 * 2 ^ 59
def prefixEnd_2429259 : Nat := 4983230072969 + 3 ^ 40 * 2429259 * 2
def baseEnd_2429259 : Nat := 1247377501260616246690547

theorem tailTrace_2429259 : CollatzResearch.WordTrace tailWord_2429259 prefixEnd_2429259 1247377501260616246690547 := by
  unfold tailWord_2429259
  simp only [CollatzResearch.WordTrace]
  refine ⟨88602354706217002251674831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59068236470811334834449887 88602354706217002251674831)
  ·
    refine ⟨132903532059325503377512247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88602354706217002251674831 132903532059325503377512247)
    ·
      refine ⟨199355298088988255066268371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132903532059325503377512247 199355298088988255066268371)
      ·
        refine ⟨299032947133482382599402557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199355298088988255066268371 299032947133482382599402557)
        ·
          refine ⟨112137355175055893474775959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299032947133482382599402557 112137355175055893474775959)
          ·
            refine ⟨168206032762583840212163939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112137355175055893474775959 168206032762583840212163939)
            ·
              refine ⟨252309049143875760318245909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168206032762583840212163939 252309049143875760318245909)
              ·
                refine ⟨11826986678619176264917777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 252309049143875760318245909 11826986678619176264917777)
                ·
                  refine ⟨8870240008964382198688333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11826986678619176264917777 8870240008964382198688333)
                  ·
                    refine ⟨3326340003361643324508125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8870240008964382198688333 3326340003361643324508125)
                    ·
                      refine ⟨1247377501260616246690547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3326340003361643324508125 1247377501260616246690547)
                      ·
                        rfl

theorem cell23_2429259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 3].length) (baseStart_2429259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429259 prefixEnd_2429259 := by exact prefixLift 2429259
  have htrace : WordTrace (prefixWord ++ tailWord_2429259) baseStart_2429259 baseEnd_2429259 := by
    simpa [prefixWord, tailWord_2429259, baseEnd_2429259] using wordTrace_append hprefix tailTrace_2429259
  have hstable : (prefixWord ++ tailWord_2429259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429259).length < 2 ^ (prefixWord ++ tailWord_2429259).sum := by decide
  have hdescent : baseEnd_2429259 < baseStart_2429259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429266 : List Nat := [3, 2, 2, 1, 1, 1, 2, 6, 5]
def baseStart_2429266 : Nat := 118140960795 + 2429266 * 2 ^ 59
def prefixEnd_2429266 : Nat := 4983230072969 + 3 ^ 40 * 2429266 * 2
def baseEnd_2429266 : Nat := 138597899513910857700335

theorem tailTrace_2429266 : CollatzResearch.WordTrace tailWord_2429266 prefixEnd_2429266 138597899513910857700335 := by
  unfold tailWord_2429266
  simp only [CollatzResearch.WordTrace]
  refine ⟨22150652504297910611794913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59068406678127761631453101 22150652504297910611794913)
  ·
    refine ⟨16612989378223432958846185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22150652504297910611794913 16612989378223432958846185)
    ·
      refine ⟨12459742033667574719134639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16612989378223432958846185 12459742033667574719134639)
      ·
        refine ⟨18689613050501362078701959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12459742033667574719134639 18689613050501362078701959)
        ·
          refine ⟨28034419575752043118052939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18689613050501362078701959 28034419575752043118052939)
          ·
            refine ⟨42051629363628064677079409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28034419575752043118052939 42051629363628064677079409)
            ·
              refine ⟨31538722022721048507809557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42051629363628064677079409 31538722022721048507809557)
              ·
                refine ⟨1478377594815049148803573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31538722022721048507809557 1478377594815049148803573)
                ·
                  refine ⟨138597899513910857700335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1478377594815049148803573 138597899513910857700335)
                  ·
                    rfl

theorem cell23_2429266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_2429266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429266 prefixEnd_2429266 := by exact prefixLift 2429266
  have htrace : WordTrace (prefixWord ++ tailWord_2429266) baseStart_2429266 baseEnd_2429266 := by
    simpa [prefixWord, tailWord_2429266, baseEnd_2429266] using wordTrace_append hprefix tailTrace_2429266
  have hstable : (prefixWord ++ tailWord_2429266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429266).length < 2 ^ (prefixWord ++ tailWord_2429266).sum := by decide
  have hdescent : baseEnd_2429266 < baseStart_2429266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429296 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 2, 5]
def baseStart_2429296 : Nat := 118140960795 + 2429296 * 2 ^ 59
def prefixEnd_2429296 : Nat := 4983230072969 + 3 ^ 40 * 2429296 * 2
def baseEnd_2429296 : Nat := 415798833348277533975959

theorem tailTrace_2429296 : CollatzResearch.WordTrace tailWord_2429296 prefixEnd_2429296 415798833348277533975959 := by
  unfold tailWord_2429296
  simp only [CollatzResearch.WordTrace]
  refine ⟨44301852103541478785385871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59069136138055305047181161 44301852103541478785385871)
  ·
    refine ⟨66452778155312218178078807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44301852103541478785385871 66452778155312218178078807)
    ·
      refine ⟨99679167232968327267118211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66452778155312218178078807 99679167232968327267118211)
      ·
        refine ⟨149518750849452490900677317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99679167232968327267118211 149518750849452490900677317)
        ·
          refine ⟨28034765784272342043876997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149518750849452490900677317 28034765784272342043876997)
          ·
            refine ⟨5256518584551064133226937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28034765784272342043876997 5256518584551064133226937)
            ·
              refine ⟨3942388938413298099920203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5256518584551064133226937 3942388938413298099920203)
              ·
                refine ⟨5913583407619947149880305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3942388938413298099920203 5913583407619947149880305)
                ·
                  refine ⟨4435187555714960362410229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5913583407619947149880305 4435187555714960362410229)
                  ·
                    refine ⟨415798833348277533975959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4435187555714960362410229 415798833348277533975959)
                    ·
                      rfl

theorem cell23_2429296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_2429296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429296 prefixEnd_2429296 := by exact prefixLift 2429296
  have htrace : WordTrace (prefixWord ++ tailWord_2429296) baseStart_2429296 baseEnd_2429296 := by
    simpa [prefixWord, tailWord_2429296, baseEnd_2429296] using wordTrace_append hprefix tailTrace_2429296
  have hstable : (prefixWord ++ tailWord_2429296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429296).length < 2 ^ (prefixWord ++ tailWord_2429296).sum := by decide
  have hdescent : baseEnd_2429296 < baseStart_2429296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429299 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 4]
def baseStart_2429299 : Nat := 118140960795 + 2429299 * 2 ^ 59
def prefixEnd_2429299 : Nat := 4983230072969 + 3 ^ 40 * 2429299 * 2
def baseEnd_2429299 : Nat := 1247398040486796090190363

theorem tailTrace_2429299 : CollatzResearch.WordTrace tailWord_2429299 prefixEnd_2429299 1247398040486796090190363 := by
  unfold tailWord_2429299
  simp only [CollatzResearch.WordTrace]
  refine ⟨88603813626072089083130951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59069209084048059388753967 88603813626072089083130951)
  ·
    refine ⟨132905720439108133624696427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88603813626072089083130951 132905720439108133624696427)
    ·
      refine ⟨199358580658662200437044641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132905720439108133624696427 199358580658662200437044641)
      ·
        refine ⟨149518935493996650327783481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199358580658662200437044641 149518935493996650327783481)
        ·
          refine ⟨112139201620497487745837611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149518935493996650327783481 112139201620497487745837611)
          ·
            refine ⟨168208802430746231618756417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112139201620497487745837611 168208802430746231618756417)
            ·
              refine ⟨126156601823059673714067313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168208802430746231618756417 126156601823059673714067313)
              ·
                refine ⟨94617451367294755285550485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126156601823059673714067313 94617451367294755285550485)
                ·
                  refine ⟨4435193032841941654010179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94617451367294755285550485 4435193032841941654010179)
                  ·
                    refine ⟨6652789549262912481015269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4435193032841941654010179 6652789549262912481015269)
                    ·
                      refine ⟨1247398040486796090190363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6652789549262912481015269 1247398040486796090190363)
                      ·
                        rfl

theorem cell23_2429299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_2429299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429299 prefixEnd_2429299 := by exact prefixLift 2429299
  have htrace : WordTrace (prefixWord ++ tailWord_2429299) baseStart_2429299 baseEnd_2429299 := by
    simpa [prefixWord, tailWord_2429299, baseEnd_2429299] using wordTrace_append hprefix tailTrace_2429299
  have hstable : (prefixWord ++ tailWord_2429299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429299).length < 2 ^ (prefixWord ++ tailWord_2429299).sum := by decide
  have hdescent : baseEnd_2429299 < baseStart_2429299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429316 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_2429316 : Nat := 118140960795 + 2429316 * 2 ^ 59
def prefixEnd_2429316 : Nat := 4983230072969 + 3 ^ 40 * 2429316 * 2
def baseEnd_2429316 : Nat := 1247406769657922523677785

theorem tailTrace_2429316 : CollatzResearch.WordTrace tailWord_2429316 prefixEnd_2429316 1247406769657922523677785 := by
  unfold tailWord_2429316
  simp only [CollatzResearch.WordTrace]
  refine ⟨44302216833505250493249901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59069622444673667324333201 44302216833505250493249901)
  ·
    refine ⟨16613331312564468934968713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44302216833505250493249901 16613331312564468934968713)
    ·
      refine ⟨12459998484423351701226535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16613331312564468934968713 12459998484423351701226535)
      ·
        refine ⟨18689997726635027551839803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12459998484423351701226535 18689997726635027551839803)
        ·
          refine ⟨28034996589952541327759705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18689997726635027551839803 28034996589952541327759705)
          ·
            refine ⟨21026247442464405995819779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28034996589952541327759705 21026247442464405995819779)
            ·
              refine ⟨31539371163696608993729669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21026247442464405995819779 31539371163696608993729669)
              ·
                refine ⟨5913632093193114186324313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31539371163696608993729669 5913632093193114186324313)
                ·
                  refine ⟨4435224069894835639743235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5913632093193114186324313 4435224069894835639743235)
                  ·
                    refine ⟨6652836104842253459614853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4435224069894835639743235 6652836104842253459614853)
                    ·
                      refine ⟨1247406769657922523677785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6652836104842253459614853 1247406769657922523677785)
                      ·
                        rfl

theorem cell23_2429316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_2429316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429316 prefixEnd_2429316 := by exact prefixLift 2429316
  have htrace : WordTrace (prefixWord ++ tailWord_2429316) baseStart_2429316 baseEnd_2429316 := by
    simpa [prefixWord, tailWord_2429316, baseEnd_2429316] using wordTrace_append hprefix tailTrace_2429316
  have hstable : (prefixWord ++ tailWord_2429316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429316).length < 2 ^ (prefixWord ++ tailWord_2429316).sum := by decide
  have hdescent : baseEnd_2429316 < baseStart_2429316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429319 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_2429319 : Nat := 118140960795 + 2429319 * 2 ^ 59
def prefixEnd_2429319 : Nat := 4983230072969 + 3 ^ 40 * 2429319 * 2
def baseEnd_2429319 : Nat := 1247408310099886011940271

theorem tailTrace_2429319 : CollatzResearch.WordTrace tailWord_2429319 prefixEnd_2429319 1247408310099886011940271 := by
  unfold tailWord_2429319
  simp only [CollatzResearch.WordTrace]
  refine ⟨88604543085999632498859011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59069695390666421665906007 88604543085999632498859011)
  ·
    refine ⟨132906814628999448748288517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88604543085999632498859011 132906814628999448748288517)
    ·
      refine ⟨24920027742937396640304097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132906814628999448748288517 24920027742937396640304097)
      ·
        refine ⟨18690020807203047480228073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24920027742937396640304097 18690020807203047480228073)
        ·
          refine ⟨14017515605402285610171055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18690020807203047480228073 14017515605402285610171055)
          ·
            refine ⟨21026273408103428415256583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14017515605402285610171055 21026273408103428415256583)
            ·
              refine ⟨31539410112155142622884875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21026273408103428415256583 31539410112155142622884875)
              ·
                refine ⟨47309115168232713934327313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31539410112155142622884875 47309115168232713934327313)
                ·
                  refine ⟨35481836376174535450745485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47309115168232713934327313 35481836376174535450745485)
                  ·
                    refine ⟨13305688641065450794029557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35481836376174535450745485 13305688641065450794029557)
                    ·
                      refine ⟨1247408310099886011940271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13305688641065450794029557 1247408310099886011940271)
                      ·
                        rfl

theorem cell23_2429319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_2429319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429319 prefixEnd_2429319 := by exact prefixLift 2429319
  have htrace : WordTrace (prefixWord ++ tailWord_2429319) baseStart_2429319 baseEnd_2429319 := by
    simpa [prefixWord, tailWord_2429319, baseEnd_2429319] using wordTrace_append hprefix tailTrace_2429319
  have hstable : (prefixWord ++ tailWord_2429319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429319).length < 2 ^ (prefixWord ++ tailWord_2429319).sum := by decide
  have hdescent : baseEnd_2429319 < baseStart_2429319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429373 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 6]
def baseStart_2429373 : Nat := 118140960795 + 2429373 * 2 ^ 59
def prefixEnd_2429373 : Nat := 4983230072969 + 3 ^ 40 * 2429373 * 2
def baseEnd_2429373 : Nat := 138604004228358755629447

theorem tailTrace_2429373 : CollatzResearch.WordTrace tailWord_2429373 prefixEnd_2429373 138604004228358755629447 := by
  unfold tailWord_2429373
  simp only [CollatzResearch.WordTrace]
  refine ⟨88606512627803999721324773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59071008418535999814216515 88606512627803999721324773)
  ·
    refine ⟨16613721117713249947748395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88606512627803999721324773 16613721117713249947748395)
    ·
      refine ⟨24920581676569874921622593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16613721117713249947748395 24920581676569874921622593)
      ·
        refine ⟨18690436257427406191216945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24920581676569874921622593 18690436257427406191216945)
        ·
          refine ⟨14017827193070554643412709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18690436257427406191216945 14017827193070554643412709)
          ·
            refine ⟨2628342598700728995639883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14017827193070554643412709 2628342598700728995639883)
            ·
              refine ⟨3942513898051093493459825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628342598700728995639883 3942513898051093493459825)
              ·
                refine ⟨2956885423538320120094869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3942513898051093493459825 2956885423538320120094869)
                ·
                  refine ⟨138604004228358755629447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2956885423538320120094869 138604004228358755629447)
                  ·
                    rfl

theorem cell23_2429373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_2429373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429373 prefixEnd_2429373 := by exact prefixLift 2429373
  have htrace : WordTrace (prefixWord ++ tailWord_2429373) baseStart_2429373 baseEnd_2429373 := by
    simpa [prefixWord, tailWord_2429373, baseEnd_2429373] using wordTrace_append hprefix tailTrace_2429373
  have hstable : (prefixWord ++ tailWord_2429373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429373).length < 2 ^ (prefixWord ++ tailWord_2429373).sum := by decide
  have hdescent : baseEnd_2429373 < baseStart_2429373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429383 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_2429383 : Nat := 118140960795 + 2429383 * 2 ^ 59
def prefixEnd_2429383 : Nat := 4983230072969 + 3 ^ 40 * 2429383 * 2
def baseEnd_2429383 : Nat := 1247441172861773761539977

theorem tailTrace_2429383 : CollatzResearch.WordTrace tailWord_2429383 prefixEnd_2429383 1247441172861773761539977 := by
  unfold tailWord_2429383
  simp only [CollatzResearch.WordTrace]
  refine ⟨88606877357767771429188803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59071251571845180952792535 88606877357767771429188803)
  ·
    refine ⟨132910316036651657143783205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88606877357767771429188803 132910316036651657143783205)
    ·
      refine ⟨24920684256872185714459351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132910316036651657143783205 24920684256872185714459351)
      ·
        refine ⟨37381026385308278571689027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24920684256872185714459351 37381026385308278571689027)
        ·
          refine ⟨56071539577962417857533541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37381026385308278571689027 56071539577962417857533541)
          ·
            refine ⟨10513413670867953348287539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56071539577962417857533541 10513413670867953348287539)
            ·
              refine ⟨15770120506301930022431309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10513413670867953348287539 15770120506301930022431309)
              ·
                refine ⟨5913795189863223758411741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15770120506301930022431309 5913795189863223758411741)
                ·
                  refine ⟨2217673196198708909404403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5913795189863223758411741 2217673196198708909404403)
                  ·
                    refine ⟨3326509794298063364106605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2217673196198708909404403 3326509794298063364106605)
                    ·
                      refine ⟨1247441172861773761539977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3326509794298063364106605 1247441172861773761539977)
                      ·
                        rfl

theorem cell23_2429383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_2429383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429383 prefixEnd_2429383 := by exact prefixLift 2429383
  have htrace : WordTrace (prefixWord ++ tailWord_2429383) baseStart_2429383 baseEnd_2429383 := by
    simpa [prefixWord, tailWord_2429383, baseEnd_2429383] using wordTrace_append hprefix tailTrace_2429383
  have hstable : (prefixWord ++ tailWord_2429383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429383).length < 2 ^ (prefixWord ++ tailWord_2429383).sum := by decide
  have hdescent : baseEnd_2429383 < baseStart_2429383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429473 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_2429473 : Nat := 118140960795 + 2429473 * 2 ^ 59
def prefixEnd_2429473 : Nat := 4983230072969 + 3 ^ 40 * 2429473 * 2
def baseEnd_2429473 : Nat := 1247487386120678409414563

theorem tailTrace_2429473 : CollatzResearch.WordTrace tailWord_2429473 prefixEnd_2429473 1247487386120678409414563 := by
  unfold tailWord_2429473
  simp only [CollatzResearch.WordTrace]
  refine ⟨88610159927441716799965073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59073439951627811199976715 88610159927441716799965073)
  ·
    refine ⟨66457619945581287599973805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88610159927441716799965073 66457619945581287599973805)
    ·
      refine ⟨24921607479592982849990177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66457619945581287599973805 24921607479592982849990177)
      ·
        refine ⟨18691205609694737137492633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24921607479592982849990177 18691205609694737137492633)
        ·
          refine ⟨14018404207271052853119475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18691205609694737137492633 14018404207271052853119475)
          ·
            refine ⟨21027606310906579279679213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14018404207271052853119475 21027606310906579279679213)
            ·
              refine ⟨7885352366589967229879705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21027606310906579279679213 7885352366589967229879705)
              ·
                refine ⟨5914014274942475422409779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7885352366589967229879705 5914014274942475422409779)
                ·
                  refine ⟨8871021412413713133614669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5914014274942475422409779 8871021412413713133614669)
                  ·
                    refine ⟨3326633029655142425105501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8871021412413713133614669 3326633029655142425105501)
                    ·
                      refine ⟨1247487386120678409414563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3326633029655142425105501 1247487386120678409414563)
                      ·
                        rfl

theorem cell23_2429473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_2429473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429473 prefixEnd_2429473 := by exact prefixLift 2429473
  have htrace : WordTrace (prefixWord ++ tailWord_2429473) baseStart_2429473 baseEnd_2429473 := by
    simpa [prefixWord, tailWord_2429473, baseEnd_2429473] using wordTrace_append hprefix tailTrace_2429473
  have hstable : (prefixWord ++ tailWord_2429473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429473).length < 2 ^ (prefixWord ++ tailWord_2429473).sum := by decide
  have hdescent : baseEnd_2429473 < baseStart_2429473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429485 : List Nat := [1, 5, 4, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2429485 : Nat := 118140960795 + 2429485 * 2 ^ 59
def prefixEnd_2429485 : Nat := 4983230072969 + 3 ^ 40 * 2429485 * 2
def baseEnd_2429485 : Nat := 1247493547888532362464509

theorem tailTrace_2429485 : CollatzResearch.WordTrace tailWord_2429485 prefixEnd_2429485 1247493547888532362464509 := by
  unfold tailWord_2429485
  simp only [CollatzResearch.WordTrace]
  refine ⟨88610597603398242849401909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59073731735598828566267939 88610597603398242849401909)
  ·
    refine ⟨8307243525318585267131429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88610597603398242849401909 8307243525318585267131429)
    ·
      refine ⟨1557608160997234737587143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8307243525318585267131429 1557608160997234737587143)
      ·
        refine ⟨2336412241495852106380715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557608160997234737587143 2336412241495852106380715)
        ·
          refine ⟨3504618362243778159571073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336412241495852106380715 3504618362243778159571073)
          ·
            refine ⟨2628463771682833619678305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3504618362243778159571073 2628463771682833619678305)
            ·
              refine ⟨1971347828762125214758729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2628463771682833619678305 1971347828762125214758729)
              ·
                refine ⟨1478510871571593911069047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1971347828762125214758729 1478510871571593911069047)
                ·
                  refine ⟨2217766307357390866603571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478510871571593911069047 2217766307357390866603571)
                  ·
                    refine ⟨3326649461036086299905357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2217766307357390866603571 3326649461036086299905357)
                    ·
                      refine ⟨1247493547888532362464509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3326649461036086299905357 1247493547888532362464509)
                      ·
                        rfl

theorem cell23_2429485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2429485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429485 prefixEnd_2429485 := by exact prefixLift 2429485
  have htrace : WordTrace (prefixWord ++ tailWord_2429485) baseStart_2429485 baseEnd_2429485 := by
    simpa [prefixWord, tailWord_2429485, baseEnd_2429485] using wordTrace_append hprefix tailTrace_2429485
  have hstable : (prefixWord ++ tailWord_2429485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429485).length < 2 ^ (prefixWord ++ tailWord_2429485).sum := by decide
  have hdescent : baseEnd_2429485 < baseStart_2429485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429490 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_2429490 : Nat := 118140960795 + 2429490 * 2 ^ 59
def prefixEnd_2429490 : Nat := 4983230072969 + 3 ^ 40 * 2429490 * 2
def baseEnd_2429490 : Nat := 1247496115291804842901985

theorem tailTrace_2429490 : CollatzResearch.WordTrace tailWord_2429490 prefixEnd_2429490 1247496115291804842901985 := by
  unfold tailWord_2429490
  simp only [CollatzResearch.WordTrace]
  refine ⟨22152694992095032175833481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59073853312253419135555949 22152694992095032175833481)
  ·
    refine ⟨16614521244071274131875111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22152694992095032175833481 16614521244071274131875111)
    ·
      refine ⟨24921781866106911197812667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16614521244071274131875111 24921781866106911197812667)
      ·
        refine ⟨37382672799160366796719001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24921781866106911197812667 37382672799160366796719001)
        ·
          refine ⟨28037004599370275097539251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37382672799160366796719001 28037004599370275097539251)
          ·
            refine ⟨42055506899055412646308877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28037004599370275097539251 42055506899055412646308877)
            ·
              refine ⟨15770815087145779742365829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42055506899055412646308877 15770815087145779742365829)
              ·
                refine ⟨2957027828839833701693593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15770815087145779742365829 2957027828839833701693593)
                ·
                  refine ⟨2217770871629875276270195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2957027828839833701693593 2217770871629875276270195)
                  ·
                    refine ⟨3326656307444812914405293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2217770871629875276270195 3326656307444812914405293)
                    ·
                      refine ⟨1247496115291804842901985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3326656307444812914405293 1247496115291804842901985)
                      ·
                        rfl

theorem cell23_2429490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_2429490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429490 prefixEnd_2429490 := by exact prefixLift 2429490
  have htrace : WordTrace (prefixWord ++ tailWord_2429490) baseStart_2429490 baseEnd_2429490 := by
    simpa [prefixWord, tailWord_2429490, baseEnd_2429490] using wordTrace_append hprefix tailTrace_2429490
  have hstable : (prefixWord ++ tailWord_2429490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429490).length < 2 ^ (prefixWord ++ tailWord_2429490).sum := by decide
  have hdescent : baseEnd_2429490 < baseStart_2429490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429496 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_2429496 : Nat := 118140960795 + 2429496 * 2 ^ 59
def prefixEnd_2429496 : Nat := 4983230072969 + 3 ^ 40 * 2429496 * 2
def baseEnd_2429496 : Nat := 1247499196175731819426957

theorem tailTrace_2429496 : CollatzResearch.WordTrace tailWord_2429496 prefixEnd_2429496 1247499196175731819426957 := by
  unfold tailWord_2429496
  simp only [CollatzResearch.WordTrace]
  refine ⟨44305499403179195864026171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59073999204238927818701561 44305499403179195864026171)
  ·
    refine ⟨66458249104768793796039257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44305499403179195864026171 66458249104768793796039257)
    ·
      refine ⟨49843686828576595347029443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66458249104768793796039257 49843686828576595347029443)
      ·
        refine ⟨74765530242864893020544165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49843686828576595347029443 74765530242864893020544165)
        ·
          refine ⟨14018536920537167441352031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74765530242864893020544165 14018536920537167441352031)
          ·
            refine ⟨21027805380805751162028047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14018536920537167441352031 21027805380805751162028047)
            ·
              refine ⟨31541708071208626743042071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21027805380805751162028047 31541708071208626743042071)
              ·
                refine ⟨47312562106812940114563107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31541708071208626743042071 47312562106812940114563107)
                ·
                  refine ⟨70968843160219410171844661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47312562106812940114563107 70968843160219410171844661)
                  ·
                    refine ⟨6653329046270569703610437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70968843160219410171844661 6653329046270569703610437)
                    ·
                      refine ⟨1247499196175731819426957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6653329046270569703610437 1247499196175731819426957)
                      ·
                        rfl

theorem cell23_2429496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_2429496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429496 prefixEnd_2429496 := by exact prefixLift 2429496
  have htrace : WordTrace (prefixWord ++ tailWord_2429496) baseStart_2429496 baseEnd_2429496 := by
    simpa [prefixWord, tailWord_2429496, baseEnd_2429496] using wordTrace_append hprefix tailTrace_2429496
  have hstable : (prefixWord ++ tailWord_2429496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429496).length < 2 ^ (prefixWord ++ tailWord_2429496).sum := by decide
  have hdescent : baseEnd_2429496 < baseStart_2429496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429500 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_2429500 : Nat := 118140960795 + 2429500 * 2 ^ 59
def prefixEnd_2429500 : Nat := 4983230072969 + 3 ^ 40 * 2429500 * 2
def baseEnd_2429500 : Nat := 1247501250098349803776939

theorem tailTrace_2429500 : CollatzResearch.WordTrace tailWord_2429500 prefixEnd_2429500 1247501250098349803776939 := by
  unfold tailWord_2429500
  simp only [CollatzResearch.WordTrace]
  refine ⟨44305572349171950205598977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59074096465562600274131969 44305572349171950205598977)
  ·
    refine ⟨33229179261878962654199233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44305572349171950205598977 33229179261878962654199233)
    ·
      refine ⟨24921884446409221990649425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33229179261878962654199233 24921884446409221990649425)
      ·
        refine ⟨18691413334806916492987069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24921884446409221990649425 18691413334806916492987069)
        ·
          refine ⟨7009280000552593684870151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18691413334806916492987069 7009280000552593684870151)
          ·
            refine ⟨10513920000828890527305227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7009280000552593684870151 10513920000828890527305227)
            ·
              refine ⟨15770880001243335790957841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10513920000828890527305227 15770880001243335790957841)
              ·
                refine ⟨11828160000932501843218381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15770880001243335790957841 11828160000932501843218381)
                ·
                  refine ⟨4435560000349688191206893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11828160000932501843218381 4435560000349688191206893)
                  ·
                    refine ⟨1663335000131133071702585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4435560000349688191206893 1663335000131133071702585)
                    ·
                      refine ⟨1247501250098349803776939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663335000131133071702585 1247501250098349803776939)
                      ·
                        rfl

theorem cell23_2429500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_2429500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429500 prefixEnd_2429500 := by exact prefixLift 2429500
  have htrace : WordTrace (prefixWord ++ tailWord_2429500) baseStart_2429500 baseEnd_2429500 := by
    simpa [prefixWord, tailWord_2429500, baseEnd_2429500] using wordTrace_append hprefix tailTrace_2429500
  have hstable : (prefixWord ++ tailWord_2429500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429500).length < 2 ^ (prefixWord ++ tailWord_2429500).sum := by decide
  have hdescent : baseEnd_2429500 < baseStart_2429500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429517 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_2429517 : Nat := 118140960795 + 2429517 * 2 ^ 59
def prefixEnd_2429517 : Nat := 4983230072969 + 3 ^ 40 * 2429517 * 2
def baseEnd_2429517 : Nat := 1247509979269476237264361

theorem tailTrace_2429517 : CollatzResearch.WordTrace tailWord_2429517 prefixEnd_2429517 1247509979269476237264361 := by
  unfold tailWord_2429517
  simp only [CollatzResearch.WordTrace]
  refine ⟨88611764739282312314566805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59074509826188208209711203 88611764739282312314566805)
  ·
    refine ⟨4153676472153858389745319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88611764739282312314566805 4153676472153858389745319)
    ·
      refine ⟨6230514708230787584617979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4153676472153858389745319 6230514708230787584617979)
      ·
        refine ⟨9345772062346181376926969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6230514708230787584617979 9345772062346181376926969)
        ·
          refine ⟨7009329046759636032695227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9345772062346181376926969 7009329046759636032695227)
          ·
            refine ⟨10513993570139454049042841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7009329046759636032695227 10513993570139454049042841)
            ·
              refine ⟨7885495177604590536782131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10513993570139454049042841 7885495177604590536782131)
              ·
                refine ⟨11828242766406885805173197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7885495177604590536782131 11828242766406885805173197)
                ·
                  refine ⟨4435591037402582176939949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11828242766406885805173197 4435591037402582176939949)
                  ·
                    refine ⟨1663346639025968316352481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4435591037402582176939949 1663346639025968316352481)
                    ·
                      refine ⟨1247509979269476237264361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663346639025968316352481 1247509979269476237264361)
                      ·
                        rfl

theorem cell23_2429517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_2429517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429517 prefixEnd_2429517 := by exact prefixLift 2429517
  have htrace : WordTrace (prefixWord ++ tailWord_2429517) baseStart_2429517 baseEnd_2429517 := by
    simpa [prefixWord, tailWord_2429517, baseEnd_2429517] using wordTrace_append hprefix tailTrace_2429517
  have hstable : (prefixWord ++ tailWord_2429517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429517).length < 2 ^ (prefixWord ++ tailWord_2429517).sum := by decide
  have hdescent : baseEnd_2429517 < baseStart_2429517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429600 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 2, 5]
def baseStart_2429600 : Nat := 118140960795 + 2429600 * 2 ^ 59
def prefixEnd_2429600 : Nat := 4983230072969 + 3 ^ 40 * 2429600 * 2
def baseEnd_2429600 : Nat := 415850866054599804175493

theorem tailTrace_2429600 : CollatzResearch.WordTrace tailWord_2429600 prefixEnd_2429600 415850866054599804175493 := by
  unfold tailWord_2429600
  simp only [CollatzResearch.WordTrace]
  refine ⟨44307395998990808744919127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59076527998654411659892169 44307395998990808744919127)
  ·
    refine ⟨66461093998486213117378691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44307395998990808744919127 66461093998486213117378691)
    ·
      refine ⟨99691640997729319676068037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66461093998486213117378691 99691640997729319676068037)
      ·
        refine ⟨18692182687074247439262757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99691640997729319676068037 18692182687074247439262757)
        ·
          refine ⟨3504784253826421394861767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18692182687074247439262757 3504784253826421394861767)
          ·
            refine ⟨5257176380739632092292651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504784253826421394861767 5257176380739632092292651)
            ·
              refine ⟨7885764571109448138438977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5257176380739632092292651 7885764571109448138438977)
              ·
                refine ⟨5914323428332086103829233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7885764571109448138438977 5914323428332086103829233)
                ·
                  refine ⟨4435742571249064577871925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5914323428332086103829233 4435742571249064577871925)
                  ·
                    refine ⟨415850866054599804175493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4435742571249064577871925 415850866054599804175493)
                    ·
                      rfl

theorem cell23_2429600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_2429600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429600 prefixEnd_2429600 := by exact prefixLift 2429600
  have htrace : WordTrace (prefixWord ++ tailWord_2429600) baseStart_2429600 baseEnd_2429600 := by
    simpa [prefixWord, tailWord_2429600, baseEnd_2429600] using wordTrace_append hprefix tailTrace_2429600
  have hstable : (prefixWord ++ tailWord_2429600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429600).length < 2 ^ (prefixWord ++ tailWord_2429600).sum := by decide
  have hdescent : baseEnd_2429600 < baseStart_2429600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429630 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_2429630 : Nat := 118140960795 + 2429630 * 2 ^ 59
def prefixEnd_2429630 : Nat := 4983230072969 + 3 ^ 40 * 2429630 * 2
def baseEnd_2429630 : Nat := 415856000861144765050447

theorem tailTrace_2429630 : CollatzResearch.WordTrace tailWord_2429630 prefixEnd_2429630 415856000861144765050447 := by
  unfold tailWord_2429630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11076985773484116576678793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59077257458581955075620229 11076985773484116576678793)
  ·
    refine ⟨8307739330113087432509095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11076985773484116576678793 8307739330113087432509095)
    ·
      refine ⟨12461608995169631148763643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8307739330113087432509095 12461608995169631148763643)
      ·
        refine ⟨18692413492754446723145465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12461608995169631148763643 18692413492754446723145465)
        ·
          refine ⟨14019310119565835042359099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18692413492754446723145465 14019310119565835042359099)
          ·
            refine ⟨21028965179348752563538649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14019310119565835042359099 21028965179348752563538649)
            ·
              refine ⟨15771723884511564422653987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21028965179348752563538649 15771723884511564422653987)
              ·
                refine ⟨23657585826767346633980981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15771723884511564422653987 23657585826767346633980981)
                ·
                  refine ⟨2217898671259438746935717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23657585826767346633980981 2217898671259438746935717)
                  ·
                    refine ⟨415856000861144765050447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2217898671259438746935717 415856000861144765050447)
                    ·
                      rfl

theorem cell23_2429630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_2429630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429630 prefixEnd_2429630 := by exact prefixLift 2429630
  have htrace : WordTrace (prefixWord ++ tailWord_2429630) baseStart_2429630 baseEnd_2429630 := by
    simpa [prefixWord, tailWord_2429630, baseEnd_2429630] using wordTrace_append hprefix tailTrace_2429630
  have hstable : (prefixWord ++ tailWord_2429630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429630).length < 2 ^ (prefixWord ++ tailWord_2429630).sum := by decide
  have hdescent : baseEnd_2429630 < baseStart_2429630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429640 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_2429640 : Nat := 118140960795 + 2429640 * 2 ^ 59
def prefixEnd_2429640 : Nat := 4983230072969 + 3 ^ 40 * 2429640 * 2
def baseEnd_2429640 : Nat := 1247573137389979256026295

theorem tailTrace_2429640 : CollatzResearch.WordTrace tailWord_2429640 prefixEnd_2429640 1247573137389979256026295 := by
  unfold tailWord_2429640
  simp only [CollatzResearch.WordTrace]
  refine ⟨44308125458918352160647187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59077500611891136214196249 44308125458918352160647187)
  ·
    refine ⟨66462188188377528240970781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44308125458918352160647187 66462188188377528240970781)
    ·
      refine ⟨24923320570641573090364043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66462188188377528240970781 24923320570641573090364043)
      ·
        refine ⟨37384980855962359635546065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24923320570641573090364043 37384980855962359635546065)
        ·
          refine ⟨28038735641971769726659549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37384980855962359635546065 28038735641971769726659549)
          ·
            refine ⟨10514525865739413647497331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28038735641971769726659549 10514525865739413647497331)
            ·
              refine ⟨15771788798609120471245997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514525865739413647497331 15771788798609120471245997)
              ·
                refine ⟨5914420799478420176717249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15771788798609120471245997 5914420799478420176717249)
                ·
                  refine ⟨4435815599608815132537937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5914420799478420176717249 4435815599608815132537937)
                  ·
                    refine ⟨3326861699706611349403453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4435815599608815132537937 3326861699706611349403453)
                    ·
                      refine ⟨1247573137389979256026295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3326861699706611349403453 1247573137389979256026295)
                      ·
                        rfl

theorem cell23_2429640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_2429640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429640 prefixEnd_2429640 := by exact prefixLift 2429640
  have htrace : WordTrace (prefixWord ++ tailWord_2429640) baseStart_2429640 baseEnd_2429640 := by
    simpa [prefixWord, tailWord_2429640, baseEnd_2429640] using wordTrace_append hprefix tailTrace_2429640
  have hstable : (prefixWord ++ tailWord_2429640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429640).length < 2 ^ (prefixWord ++ tailWord_2429640).sum := by decide
  have hdescent : baseEnd_2429640 < baseStart_2429640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429673 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 3, 5]
def baseStart_2429673 : Nat := 118140960795 + 2429673 * 2 ^ 59
def prefixEnd_2429673 : Nat := 4983230072969 + 3 ^ 40 * 2429673 * 2
def baseEnd_2429673 : Nat := 415863360750525875637881

theorem tailTrace_2429673 : CollatzResearch.WordTrace tailWord_2429673 prefixEnd_2429673 415863360750525875637881 := by
  unfold tailWord_2429673
  simp only [CollatzResearch.WordTrace]
  refine ⟨88617454526717150957245673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59078303017811433971497115 88617454526717150957245673)
  ·
    refine ⟨66463090895037863217934255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88617454526717150957245673 66463090895037863217934255)
    ·
      refine ⟨99694636342556794826901383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66463090895037863217934255 99694636342556794826901383)
      ·
        refine ⟨149541954513835192240352075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99694636342556794826901383 149541954513835192240352075)
        ·
          refine ⟨224312931770752788360528113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149541954513835192240352075 224312931770752788360528113)
          ·
            refine ⟨168234698828064591270396085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224312931770752788360528113 168234698828064591270396085)
            ·
              refine ⟨15772003015131055431599633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168234698828064591270396085 15772003015131055431599633)
              ·
                refine ⟨11829002261348291573699725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15772003015131055431599633 11829002261348291573699725)
                ·
                  refine ⟨4435875848005609340137397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11829002261348291573699725 4435875848005609340137397)
                  ·
                    refine ⟨415863360750525875637881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4435875848005609340137397 415863360750525875637881)
                    ·
                      rfl

theorem cell23_2429673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_2429673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429673 prefixEnd_2429673 := by exact prefixLift 2429673
  have htrace : WordTrace (prefixWord ++ tailWord_2429673) baseStart_2429673 baseEnd_2429673 := by
    simpa [prefixWord, tailWord_2429673, baseEnd_2429673] using wordTrace_append hprefix tailTrace_2429673
  have hstable : (prefixWord ++ tailWord_2429673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429673).length < 2 ^ (prefixWord ++ tailWord_2429673).sum := by decide
  have hdescent : baseEnd_2429673 < baseStart_2429673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429680 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 1, 5, 2]
def baseStart_2429680 : Nat := 118140960795 + 2429680 * 2 ^ 59
def prefixEnd_2429680 : Nat := 4983230072969 + 3 ^ 40 * 2429680 * 2
def baseEnd_2429680 : Nat := 1247593676616159099526111

theorem tailTrace_2429680 : CollatzResearch.WordTrace tailWord_2429680 prefixEnd_2429680 1247593676616159099526111 := by
  unfold tailWord_2429680
  simp only [CollatzResearch.WordTrace]
  refine ⟨44308854918845895576375247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59078473225127860768500329 44308854918845895576375247)
  ·
    refine ⟨66463282378268843364562871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44308854918845895576375247 66463282378268843364562871)
    ·
      refine ⟨99694923567403265046844307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66463282378268843364562871 99694923567403265046844307)
      ·
        refine ⟨149542385351104897570266461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99694923567403265046844307 149542385351104897570266461)
        ·
          refine ⟨56078394506664336588849923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149542385351104897570266461 56078394506664336588849923)
          ·
            refine ⟨84117591759996504883274885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56078394506664336588849923 84117591759996504883274885)
            ·
              refine ⟨15772048454999344665614041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84117591759996504883274885 15772048454999344665614041)
              ·
                refine ⟨11829036341249508499210531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15772048454999344665614041 11829036341249508499210531)
                ·
                  refine ⟨17743554511874262748815797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11829036341249508499210531 17743554511874262748815797)
                  ·
                    refine ⟨1663458235488212132701481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17743554511874262748815797 1663458235488212132701481)
                    ·
                      refine ⟨1247593676616159099526111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663458235488212132701481 1247593676616159099526111)
                      ·
                        rfl

theorem cell23_2429680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 5, 2].length) (baseStart_2429680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429680 prefixEnd_2429680 := by exact prefixLift 2429680
  have htrace : WordTrace (prefixWord ++ tailWord_2429680) baseStart_2429680 baseEnd_2429680 := by
    simpa [prefixWord, tailWord_2429680, baseEnd_2429680] using wordTrace_append hprefix tailTrace_2429680
  have hstable : (prefixWord ++ tailWord_2429680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429680).length < 2 ^ (prefixWord ++ tailWord_2429680).sum := by decide
  have hdescent : baseEnd_2429680 < baseStart_2429680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429704 : List Nat := [2, 1, 3, 2, 2, 2, 1, 5, 1, 1, 3]
def baseStart_2429704 : Nat := 118140960795 + 2429704 * 2 ^ 59
def prefixEnd_2429704 : Nat := 4983230072969 + 3 ^ 40 * 2429704 * 2
def baseEnd_2429704 : Nat := 1247606000151867005626001

theorem tailTrace_2429704 : CollatzResearch.WordTrace tailWord_2429704 prefixEnd_2429704 1247606000151867005626001 := by
  unfold tailWord_2429704
  simp only [CollatzResearch.WordTrace]
  refine ⟨44309292594802421625812083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59079056793069895501082777 44309292594802421625812083)
  ·
    refine ⟨66463938892203632438718125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44309292594802421625812083 66463938892203632438718125)
    ·
      refine ⟨24923977084576362164519297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66463938892203632438718125 24923977084576362164519297)
      ·
        refine ⟨18692982813432271623389473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24923977084576362164519297 18692982813432271623389473)
        ·
          refine ⟨14019737110074203717542105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18692982813432271623389473 14019737110074203717542105)
          ·
            refine ⟨10514802832555652788156579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14019737110074203717542105 10514802832555652788156579)
            ·
              refine ⟨15772204248833479182234869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514802832555652788156579 15772204248833479182234869)
              ·
                refine ⟨1478644148328138673334519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15772204248833479182234869 1478644148328138673334519)
                ·
                  refine ⟨2217966222492208010001779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478644148328138673334519 2217966222492208010001779)
                  ·
                    refine ⟨3326949333738312015002669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2217966222492208010001779 3326949333738312015002669)
                    ·
                      refine ⟨1247606000151867005626001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3326949333738312015002669 1247606000151867005626001)
                      ·
                        rfl

theorem cell23_2429704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_2429704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429704 prefixEnd_2429704 := by exact prefixLift 2429704
  have htrace : WordTrace (prefixWord ++ tailWord_2429704) baseStart_2429704 baseEnd_2429704 := by
    simpa [prefixWord, tailWord_2429704, baseEnd_2429704] using wordTrace_append hprefix tailTrace_2429704
  have hstable : (prefixWord ++ tailWord_2429704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429704).length < 2 ^ (prefixWord ++ tailWord_2429704).sum := by decide
  have hdescent : baseEnd_2429704 < baseStart_2429704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429730 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2429730 : Nat := 118140960795 + 2429730 * 2 ^ 59
def prefixEnd_2429730 : Nat := 4983230072969 + 3 ^ 40 * 2429730 * 2
def baseEnd_2429730 : Nat := 1247619350648883903900881

theorem tailTrace_2429730 : CollatzResearch.WordTrace tailWord_2429730 prefixEnd_2429730 1247619350648883903900881 := by
  unfold tailWord_2429730
  simp only [CollatzResearch.WordTrace]
  refine ⟨22154883371877662423017661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59079688991673766461380429 22154883371877662423017661)
  ·
    refine ⟨8308081264454123408631623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22154883371877662423017661 8308081264454123408631623)
    ·
      refine ⟨12462121896681185112947435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8308081264454123408631623 12462121896681185112947435)
      ·
        refine ⟨18693182845021777669421153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12462121896681185112947435 18693182845021777669421153)
        ·
          refine ⟨14019887133766333252065865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18693182845021777669421153 14019887133766333252065865)
          ·
            refine ⟨10514915350324749939049399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14019887133766333252065865 10514915350324749939049399)
            ·
              refine ⟨15772373025487124908574099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514915350324749939049399 15772373025487124908574099)
              ·
                refine ⟨23658559538230687362861149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15772373025487124908574099 23658559538230687362861149)
                ·
                  refine ⟨8871959826836507761072931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23658559538230687362861149 8871959826836507761072931)
                  ·
                    refine ⟨13307939740254761641609397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8871959826836507761072931 13307939740254761641609397)
                    ·
                      refine ⟨1247619350648883903900881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13307939740254761641609397 1247619350648883903900881)
                      ·
                        rfl

theorem cell23_2429730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2429730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429730 prefixEnd_2429730 := by exact prefixLift 2429730
  have htrace : WordTrace (prefixWord ++ tailWord_2429730) baseStart_2429730 baseEnd_2429730 := by
    simpa [prefixWord, tailWord_2429730, baseEnd_2429730] using wordTrace_append hprefix tailTrace_2429730
  have hstable : (prefixWord ++ tailWord_2429730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429730).length < 2 ^ (prefixWord ++ tailWord_2429730).sum := by decide
  have hdescent : baseEnd_2429730 < baseStart_2429730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429733 : List Nat := [1, 3, 1, 2, 3, 1, 2, 10]
def baseStart_2429733 : Nat := 118140960795 + 2429733 * 2 ^ 59
def prefixEnd_2429733 : Nat := 4983230072969 + 3 ^ 40 * 2429733 * 2
def baseEnd_2429733 : Nat := 46208181151512866376421

theorem tailTrace_2429733 : CollatzResearch.WordTrace tailWord_2429733 prefixEnd_2429733 46208181151512866376421 := by
  unfold tailWord_2429733
  simp only [CollatzResearch.WordTrace]
  refine ⟨88619642906499781204429853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59079761937666520802953235 88619642906499781204429853)
  ·
    refine ⟨33232366089937417951661195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88619642906499781204429853 33232366089937417951661195)
    ·
      refine ⟨49848549134906126927491793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33232366089937417951661195 49848549134906126927491793)
      ·
        refine ⟨37386411851179595195618845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49848549134906126927491793 37386411851179595195618845)
        ·
          refine ⟨14019904444192348198357067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37386411851179595195618845 14019904444192348198357067)
          ·
            refine ⟨21029856666288522297535601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14019904444192348198357067 21029856666288522297535601)
            ·
              refine ⟨15772392499716391723151701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21029856666288522297535601 15772392499716391723151701)
              ·
                refine ⟨46208181151512866376421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15772392499716391723151701 46208181151512866376421)
                ·
                  rfl

theorem cell23_2429733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 10].length) (baseStart_2429733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429733 prefixEnd_2429733 := by exact prefixLift 2429733
  have htrace : WordTrace (prefixWord ++ tailWord_2429733) baseStart_2429733 baseEnd_2429733 := by
    simpa [prefixWord, tailWord_2429733, baseEnd_2429733] using wordTrace_append hprefix tailTrace_2429733
  have hstable : (prefixWord ++ tailWord_2429733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429733).length < 2 ^ (prefixWord ++ tailWord_2429733).sum := by decide
  have hdescent : baseEnd_2429733 < baseStart_2429733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429741 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2429741 : Nat := 118140960795 + 2429741 * 2 ^ 59
def prefixEnd_2429741 : Nat := 4983230072969 + 3 ^ 40 * 2429741 * 2
def baseEnd_2429741 : Nat := 415874999645361120287777

theorem tailTrace_2429741 : CollatzResearch.WordTrace tailWord_2429741 prefixEnd_2429741 415874999645361120287777 := by
  unfold tailWord_2429741
  simp only [CollatzResearch.WordTrace]
  refine ⟨88619934690470798570721077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59079956460313865713814051 88619934690470798570721077)
  ·
    refine ⟨8308118877231637366005101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88619934690470798570721077 8308118877231637366005101)
    ·
      refine ⟨3115544578961864012251913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8308118877231637366005101 3115544578961864012251913)
      ·
        refine ⟨2336658434221398009188935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3115544578961864012251913 2336658434221398009188935)
        ·
          refine ⟨3504987651332097013783403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336658434221398009188935 3504987651332097013783403)
          ·
            refine ⟨5257481476998145520675105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504987651332097013783403 5257481476998145520675105)
            ·
              refine ⟨3943111107748609140506329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257481476998145520675105 3943111107748609140506329)
              ·
                refine ⟨2957333330811456855379747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943111107748609140506329 2957333330811456855379747)
                ·
                  refine ⟨4435999996217185283069621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957333330811456855379747 4435999996217185283069621)
                  ·
                    refine ⟨415874999645361120287777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4435999996217185283069621 415874999645361120287777)
                    ·
                      rfl

theorem cell23_2429741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2429741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429741 prefixEnd_2429741 := by exact prefixLift 2429741
  have htrace : WordTrace (prefixWord ++ tailWord_2429741) baseStart_2429741 baseEnd_2429741 := by
    simpa [prefixWord, tailWord_2429741, baseEnd_2429741] using wordTrace_append hprefix tailTrace_2429741
  have hstable : (prefixWord ++ tailWord_2429741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429741).length < 2 ^ (prefixWord ++ tailWord_2429741).sum := by decide
  have hdescent : baseEnd_2429741 < baseStart_2429741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429747 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 3]
def baseStart_2429747 : Nat := 118140960795 + 2429747 * 2 ^ 59
def prefixEnd_2429747 : Nat := 4983230072969 + 3 ^ 40 * 2429747 * 2
def baseEnd_2429747 : Nat := 1247628079820010337388303

theorem tailTrace_2429747 : CollatzResearch.WordTrace tailWord_2429747 prefixEnd_2429747 1247628079820010337388303 := by
  unfold tailWord_2429747
  simp only [CollatzResearch.WordTrace]
  refine ⟨88620153528449061595439495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59080102352299374396959663 88620153528449061595439495)
  ·
    refine ⟨132930230292673592393159243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88620153528449061595439495 132930230292673592393159243)
    ·
      refine ⟨199395345439010388589738865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132930230292673592393159243 199395345439010388589738865)
      ·
        refine ⟨149546509079257791442304149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199395345439010388589738865 149546509079257791442304149)
        ·
          refine ⟨7009992613090208973858007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 149546509079257791442304149 7009992613090208973858007)
          ·
            refine ⟨10514988919635313460787011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7009992613090208973858007 10514988919635313460787011)
            ·
              refine ⟨15772483379452970191180517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514988919635313460787011 15772483379452970191180517)
              ·
                refine ⟨2957340633647431910846347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15772483379452970191180517 2957340633647431910846347)
                ·
                  refine ⟨4436010950471147866269521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957340633647431910846347 4436010950471147866269521)
                  ·
                    refine ⟨3327008212853360899702141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4436010950471147866269521 3327008212853360899702141)
                    ·
                      refine ⟨1247628079820010337388303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3327008212853360899702141 1247628079820010337388303)
                      ·
                        rfl

theorem cell23_2429747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 3].length) (baseStart_2429747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429747 prefixEnd_2429747 := by exact prefixLift 2429747
  have htrace : WordTrace (prefixWord ++ tailWord_2429747) baseStart_2429747 baseEnd_2429747 := by
    simpa [prefixWord, tailWord_2429747, baseEnd_2429747] using wordTrace_append hprefix tailTrace_2429747
  have hstable : (prefixWord ++ tailWord_2429747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429747).length < 2 ^ (prefixWord ++ tailWord_2429747).sum := by decide
  have hdescent : baseEnd_2429747 < baseStart_2429747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429760 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3]
def baseStart_2429760 : Nat := 118140960795 + 2429760 * 2 ^ 59
def prefixEnd_2429760 : Nat := 4983230072969 + 3 ^ 40 * 2429760 * 2
def baseEnd_2429760 : Nat := 1247634755068518786525743

theorem tailTrace_2429760 : CollatzResearch.WordTrace tailWord_2429760 prefixEnd_2429760 1247634755068518786525743 := by
  unfold tailWord_2429760
  simp only [CollatzResearch.WordTrace]
  refine ⟨44310313838700982407831367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59080418451601309877108489 44310313838700982407831367)
  ·
    refine ⟨66465470758051473611747051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44310313838700982407831367 66465470758051473611747051)
    ·
      refine ⟨99698206137077210417620577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66465470758051473611747051 99698206137077210417620577)
      ·
        refine ⟨74773654602807907813215433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99698206137077210417620577 74773654602807907813215433)
        ·
          refine ⟨56080240952105930859911575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74773654602807907813215433 56080240952105930859911575)
          ·
            refine ⟨84120361428158896289867363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56080240952105930859911575 84120361428158896289867363)
            ·
              refine ⟨126180542142238344434801045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84120361428158896289867363 126180542142238344434801045)
              ·
                refine ⟨5914712912917422395381299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126180542142238344434801045 5914712912917422395381299)
                ·
                  refine ⟨8872069369376133593071949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5914712912917422395381299 8872069369376133593071949)
                  ·
                    refine ⟨3327026013516050097401981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8872069369376133593071949 3327026013516050097401981)
                    ·
                      refine ⟨1247634755068518786525743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3327026013516050097401981 1247634755068518786525743)
                      ·
                        rfl

theorem cell23_2429760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_2429760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429760 prefixEnd_2429760 := by exact prefixLift 2429760
  have htrace : WordTrace (prefixWord ++ tailWord_2429760) baseStart_2429760 baseEnd_2429760 := by
    simpa [prefixWord, tailWord_2429760, baseEnd_2429760] using wordTrace_append hprefix tailTrace_2429760
  have hstable : (prefixWord ++ tailWord_2429760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429760).length < 2 ^ (prefixWord ++ tailWord_2429760).sum := by decide
  have hdescent : baseEnd_2429760 < baseStart_2429760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429778 : List Nat := [3, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_2429778 : Nat := 118140960795 + 2429778 * 2 ^ 59
def prefixEnd_2429778 : Nat := 4983230072969 + 3 ^ 40 * 2429778 * 2
def baseEnd_2429778 : Nat := 1247643997720299716100661

theorem tailTrace_2429778 : CollatzResearch.WordTrace tailWord_2429778 prefixEnd_2429778 1247643997720299716100661 := by
  unfold tailWord_2429778
  simp only [CollatzResearch.WordTrace]
  refine ⟨22155321047834188472454497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59080856127557835926545325 22155321047834188472454497)
  ·
    refine ⟨16616490785875641354340873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22155321047834188472454497 16616490785875641354340873)
    ·
      refine ⟨12462368089406731015755655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16616490785875641354340873 12462368089406731015755655)
      ·
        refine ⟨18693552134110096523633483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12462368089406731015755655 18693552134110096523633483)
        ·
          refine ⟨28040328201165144785450225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18693552134110096523633483 28040328201165144785450225)
          ·
            refine ⟨21030246150873858589087669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28040328201165144785450225 21030246150873858589087669)
            ·
              refine ⟨1971585576644424242726969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21030246150873858589087669 1971585576644424242726969)
              ·
                refine ⟨1478689182483318182045227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1971585576644424242726969 1478689182483318182045227)
                ·
                  refine ⟨2218033773724977273067841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478689182483318182045227 2218033773724977273067841)
                  ·
                    refine ⟨1663525330293732954800881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2218033773724977273067841 1663525330293732954800881)
                    ·
                      refine ⟨1247643997720299716100661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663525330293732954800881 1247643997720299716100661)
                      ·
                        rfl

theorem cell23_2429778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_2429778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429778 prefixEnd_2429778 := by exact prefixLift 2429778
  have htrace : WordTrace (prefixWord ++ tailWord_2429778) baseStart_2429778 baseEnd_2429778 := by
    simpa [prefixWord, tailWord_2429778, baseEnd_2429778] using wordTrace_append hprefix tailTrace_2429778
  have hstable : (prefixWord ++ tailWord_2429778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429778).length < 2 ^ (prefixWord ++ tailWord_2429778).sum := by decide
  have hdescent : baseEnd_2429778 < baseStart_2429778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429817 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 3, 4, 2]
def baseStart_2429817 : Nat := 118140960795 + 2429817 * 2 ^ 59
def prefixEnd_2429817 : Nat := 4983230072969 + 3 ^ 40 * 2429817 * 2
def baseEnd_2429817 : Nat := 1247664023465825063512981

theorem tailTrace_2429817 : CollatzResearch.WordTrace tailWord_2429817 prefixEnd_2429817 1247664023465825063512981 := by
  unfold tailWord_2429817
  simp only [CollatzResearch.WordTrace]
  refine ⟨88622706638195463550487705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59081804425463642366991803 88622706638195463550487705)
  ·
    refine ⟨66467029978646597662865779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88622706638195463550487705 66467029978646597662865779)
    ·
      refine ⟨99700544967969896494298669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66467029978646597662865779 99700544967969896494298669)
      ·
        refine ⟨37387704362988711185362001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99700544967969896494298669 37387704362988711185362001)
        ·
          refine ⟨28040778272241533389021501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37387704362988711185362001 28040778272241533389021501)
          ·
            refine ⟨10515291852090575020883063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28040778272241533389021501 10515291852090575020883063)
            ·
              refine ⟨15772937778135862531324595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10515291852090575020883063 15772937778135862531324595)
              ·
                refine ⟨23659406667203793796986893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15772937778135862531324595 23659406667203793796986893)
                ·
                  refine ⟨8872277500201422673870085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23659406667203793796986893 8872277500201422673870085)
                  ·
                    refine ⟨1663552031287766751350641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8872277500201422673870085 1663552031287766751350641)
                    ·
                      refine ⟨1247664023465825063512981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663552031287766751350641 1247664023465825063512981)
                      ·
                        rfl

theorem cell23_2429817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_2429817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429817 prefixEnd_2429817 := by exact prefixLift 2429817
  have htrace : WordTrace (prefixWord ++ tailWord_2429817) baseStart_2429817 baseEnd_2429817 := by
    simpa [prefixWord, tailWord_2429817, baseEnd_2429817] using wordTrace_append hprefix tailTrace_2429817
  have hstable : (prefixWord ++ tailWord_2429817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429817).length < 2 ^ (prefixWord ++ tailWord_2429817).sum := by decide
  have hdescent : baseEnd_2429817 < baseStart_2429817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429820 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_2429820 : Nat := 118140960795 + 2429820 * 2 ^ 59
def prefixEnd_2429820 : Nat := 4983230072969 + 3 ^ 40 * 2429820 * 2
def baseEnd_2429820 : Nat := 1247665563907788551775467

theorem tailTrace_2429820 : CollatzResearch.WordTrace tailWord_2429820 prefixEnd_2429820 1247665563907788551775467 := by
  unfold tailWord_2429820
  simp only [CollatzResearch.WordTrace]
  refine ⟨44311408028592297531423457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59081877371456396708564609 44311408028592297531423457)
  ·
    refine ⟨33233556021444223148567593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44311408028592297531423457 33233556021444223148567593)
    ·
      refine ⟨24925167016083167361425695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33233556021444223148567593 24925167016083167361425695)
      ·
        refine ⟨37387750524124751042138543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24925167016083167361425695 37387750524124751042138543)
        ·
          refine ⟨56081625786187126563207815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37387750524124751042138543 56081625786187126563207815)
          ·
            refine ⟨84122438679280689844811723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56081625786187126563207815 84122438679280689844811723)
            ·
              refine ⟨126183658018921034767217585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84122438679280689844811723 126183658018921034767217585)
              ·
                refine ⟨94637743514190776075413189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126183658018921034767217585 94637743514190776075413189)
                ·
                  refine ⟨17744576908910770514139973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94637743514190776075413189 17744576908910770514139973)
                  ·
                    refine ⟨3327108170420769471401245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17744576908910770514139973 3327108170420769471401245)
                    ·
                      refine ⟨1247665563907788551775467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3327108170420769471401245 1247665563907788551775467)
                      ·
                        rfl

theorem cell23_2429820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_2429820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429820 prefixEnd_2429820 := by exact prefixLift 2429820
  have htrace : WordTrace (prefixWord ++ tailWord_2429820) baseStart_2429820 baseEnd_2429820 := by
    simpa [prefixWord, tailWord_2429820, baseEnd_2429820] using wordTrace_append hprefix tailTrace_2429820
  have hstable : (prefixWord ++ tailWord_2429820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429820).length < 2 ^ (prefixWord ++ tailWord_2429820).sum := by decide
  have hdescent : baseEnd_2429820 < baseStart_2429820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429857 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 7]
def baseStart_2429857 : Nat := 118140960795 + 2429857 * 2 ^ 59
def prefixEnd_2429857 : Nat := 4983230072969 + 3 ^ 40 * 2429857 * 2
def baseEnd_2429857 : Nat := 138631618076889434112533

theorem tailTrace_2429857 : CollatzResearch.WordTrace tailWord_2429857 prefixEnd_2429857 138631618076889434112533 := by
  unfold tailWord_2429857
  simp only [CollatzResearch.WordTrace]
  refine ⟨88624165558050550381943825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59082777038700366921295883 88624165558050550381943825)
  ·
    refine ⟨66468124168537912786457869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88624165558050550381943825 66468124168537912786457869)
    ·
      refine ⟨24925546563201717294921701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66468124168537912786457869 24925546563201717294921701)
      ·
        refine ⟨4673539980600321992797819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24925546563201717294921701 4673539980600321992797819)
        ·
          refine ⟨7010309970900482989196729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673539980600321992797819 7010309970900482989196729)
          ·
            refine ⟨5257732478175362241897547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7010309970900482989196729 5257732478175362241897547)
            ·
              refine ⟨7886598717263043362846321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5257732478175362241897547 7886598717263043362846321)
              ·
                refine ⟨5914949037947282522134741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7886598717263043362846321 5914949037947282522134741)
                ·
                  refine ⟨138631618076889434112533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5914949037947282522134741 138631618076889434112533)
                  ·
                    rfl

theorem cell23_2429857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 7].length) (baseStart_2429857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429857 prefixEnd_2429857 := by exact prefixLift 2429857
  have htrace : WordTrace (prefixWord ++ tailWord_2429857) baseStart_2429857 baseEnd_2429857 := by
    simpa [prefixWord, tailWord_2429857, baseEnd_2429857] using wordTrace_append hprefix tailTrace_2429857
  have hstable : (prefixWord ++ tailWord_2429857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429857).length < 2 ^ (prefixWord ++ tailWord_2429857).sum := by decide
  have hdescent : baseEnd_2429857 < baseStart_2429857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429885 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_2429885 : Nat := 118140960795 + 2429885 * 2 ^ 59
def prefixEnd_2429885 : Nat := 4983230072969 + 3 ^ 40 * 2429885 * 2
def baseEnd_2429885 : Nat := 1247698940150330797462669

theorem tailTrace_2429885 : CollatzResearch.WordTrace tailWord_2429885 prefixEnd_2429885 1247698940150330797462669 := by
  unfold tailWord_2429885
  simp only [CollatzResearch.WordTrace]
  refine ⟨88625186801949111163963109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59083457867966074109308739 88625186801949111163963109)
  ·
    refine ⟨16617222525365458343243083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88625186801949111163963109 16617222525365458343243083)
    ·
      refine ⟨24925833788048187514864625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16617222525365458343243083 24925833788048187514864625)
      ·
        refine ⟨18694375341036140636148469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24925833788048187514864625 18694375341036140636148469)
        ·
          refine ⟨1752597688222138184638919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18694375341036140636148469 1752597688222138184638919)
          ·
            refine ⟨2628896532333207276958379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752597688222138184638919 2628896532333207276958379)
            ·
              refine ⟨3943344798499810915437569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628896532333207276958379 3943344798499810915437569)
              ·
                refine ⟨2957508598874858186578177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943344798499810915437569 2957508598874858186578177)
                ·
                  refine ⟨2218131449156143639933633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2957508598874858186578177 2218131449156143639933633)
                  ·
                    refine ⟨1663598586867107729950225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2218131449156143639933633 1663598586867107729950225)
                    ·
                      refine ⟨1247698940150330797462669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663598586867107729950225 1247698940150330797462669)
                      ·
                        rfl

theorem cell23_2429885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_2429885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429885 prefixEnd_2429885 := by exact prefixLift 2429885
  have htrace : WordTrace (prefixWord ++ tailWord_2429885) baseStart_2429885 baseEnd_2429885 := by
    simpa [prefixWord, tailWord_2429885, baseEnd_2429885] using wordTrace_append hprefix tailTrace_2429885
  have hstable : (prefixWord ++ tailWord_2429885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429885).length < 2 ^ (prefixWord ++ tailWord_2429885).sum := by decide
  have hdescent : baseEnd_2429885 < baseStart_2429885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2429964 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 6]
def baseStart_2429964 : Nat := 118140960795 + 2429964 * 2 ^ 59
def prefixEnd_2429964 : Nat := 4983230072969 + 3 ^ 40 * 2429964 * 2
def baseEnd_2429964 : Nat := 138637722791337332041645

theorem tailTrace_2429964 : CollatzResearch.WordTrace tailWord_2429964 prefixEnd_2429964 138637722791337332041645 := by
  unfold tailWord_2429964
  simp only [CollatzResearch.WordTrace]
  refine ⟨44314034084331453828044473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59085378779108605104059297 44314034084331453828044473)
  ·
    refine ⟨33235525563248590371033355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44314034084331453828044473 33235525563248590371033355)
    ·
      refine ⟨49853288344872885556550033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33235525563248590371033355 49853288344872885556550033)
      ·
        refine ⟨37389966258654664167412525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49853288344872885556550033 37389966258654664167412525)
        ·
          refine ⟨14021237346995499062779697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37389966258654664167412525 14021237346995499062779697)
          ·
            refine ⟨10515928010246624297084773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14021237346995499062779697 10515928010246624297084773)
            ·
              refine ⟨1971736501921242055703395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10515928010246624297084773 1971736501921242055703395)
              ·
                refine ⟨2957604752881863083555093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971736501921242055703395 2957604752881863083555093)
                ·
                  refine ⟨138637722791337332041645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2957604752881863083555093 138637722791337332041645)
                  ·
                    rfl

theorem cell23_2429964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_2429964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2429964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2429964 prefixEnd_2429964 := by exact prefixLift 2429964
  have htrace : WordTrace (prefixWord ++ tailWord_2429964) baseStart_2429964 baseEnd_2429964 := by
    simpa [prefixWord, tailWord_2429964, baseEnd_2429964] using wordTrace_append hprefix tailTrace_2429964
  have hstable : (prefixWord ++ tailWord_2429964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2429964).length < 2 ^ (prefixWord ++ tailWord_2429964).sum := by decide
  have hdescent : baseEnd_2429964 < baseStart_2429964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2429964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430008 : List Nat := [2, 1, 2, 1, 5, 2, 1, 4, 1, 1, 3]
def baseStart_2430008 : Nat := 118140960795 + 2430008 * 2 ^ 59
def prefixEnd_2430008 : Nat := 4983230072969 + 3 ^ 40 * 2430008 * 2
def baseEnd_2430008 : Nat := 1247762098270833816224603

theorem tailTrace_2430008 : CollatzResearch.WordTrace tailWord_2430008 prefixEnd_2430008 1247762098270833816224603 := by
  unfold tailWord_2430008
  simp only [CollatzResearch.WordTrace]
  refine ⟨44314836490251751585345339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59086448653669002113793785 44314836490251751585345339)
  ·
    refine ⟨66472254735377627378018009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44314836490251751585345339 66472254735377627378018009)
    ·
      refine ⟨49854191051533220533513507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66472254735377627378018009 49854191051533220533513507)
      ·
        refine ⟨74781286577299830800270261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49854191051533220533513507 74781286577299830800270261)
        ·
          refine ⟨7010745616621859137525337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74781286577299830800270261 7010745616621859137525337)
          ·
            refine ⟨5258059212466394353144003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7010745616621859137525337 5258059212466394353144003)
            ·
              refine ⟨7887088818699591529716005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5258059212466394353144003 7887088818699591529716005)
              ·
                refine ⟨1478829153506173411821751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7887088818699591529716005 1478829153506173411821751)
                ·
                  refine ⟨2218243730259260117732627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478829153506173411821751 2218243730259260117732627)
                  ·
                    refine ⟨3327365595388890176598941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2218243730259260117732627 3327365595388890176598941)
                    ·
                      refine ⟨1247762098270833816224603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3327365595388890176598941 1247762098270833816224603)
                      ·
                        rfl

theorem cell23_2430008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 1, 3].length) (baseStart_2430008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430008 prefixEnd_2430008 := by exact prefixLift 2430008
  have htrace : WordTrace (prefixWord ++ tailWord_2430008) baseStart_2430008 baseEnd_2430008 := by
    simpa [prefixWord, tailWord_2430008, baseEnd_2430008] using wordTrace_append hprefix tailTrace_2430008
  have hstable : (prefixWord ++ tailWord_2430008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430008).length < 2 ^ (prefixWord ++ tailWord_2430008).sum := by decide
  have hdescent : baseEnd_2430008 < baseStart_2430008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430024 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 2, 4]
def baseStart_2430024 : Nat := 118140960795 + 2430024 * 2 ^ 59
def prefixEnd_2430024 : Nat := 4983230072969 + 3 ^ 40 * 2430024 * 2
def baseEnd_2430024 : Nat := 415923437987101917874843

theorem tailTrace_2430024 : CollatzResearch.WordTrace tailWord_2430024 prefixEnd_2430024 415923437987101917874843 := by
  unfold tailWord_2430024
  simp only [CollatzResearch.WordTrace]
  refine ⟨44315128274222768951636563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59086837698963691935515417 44315128274222768951636563)
  ·
    refine ⟨66472692411334153427454845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44315128274222768951636563 66472692411334153427454845)
    ·
      refine ⟨24927259654250307535295567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66472692411334153427454845 24927259654250307535295567)
      ·
        refine ⟨37390889481375461302943351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24927259654250307535295567 37390889481375461302943351)
        ·
          refine ⟨56086334222063191954415027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37390889481375461302943351 56086334222063191954415027)
          ·
            refine ⟨84129501333094787931622541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56086334222063191954415027 84129501333094787931622541)
            ·
              refine ⟨31548562999910545474358453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84129501333094787931622541 31548562999910545474358453)
              ·
                refine ⟨2957677781241613638221105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31548562999910545474358453 2957677781241613638221105)
                ·
                  refine ⟨2218258335931210228665829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2957677781241613638221105 2218258335931210228665829)
                  ·
                    refine ⟨415923437987101917874843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2218258335931210228665829 415923437987101917874843)
                    ·
                      rfl

theorem cell23_2430024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_2430024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430024 prefixEnd_2430024 := by exact prefixLift 2430024
  have htrace : WordTrace (prefixWord ++ tailWord_2430024) baseStart_2430024 baseEnd_2430024 := by
    simpa [prefixWord, tailWord_2430024, baseEnd_2430024] using wordTrace_append hprefix tailTrace_2430024
  have hstable : (prefixWord ++ tailWord_2430024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430024).length < 2 ^ (prefixWord ++ tailWord_2430024).sum := by decide
  have hdescent : baseEnd_2430024 < baseStart_2430024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430044 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2430044 : Nat := 118140960795 + 2430044 * 2 ^ 59
def prefixEnd_2430044 : Nat := 4983230072969 + 3 ^ 40 * 2430044 * 2
def baseEnd_2430044 : Nat := 1247780583574395675374437

theorem tailTrace_2430044 : CollatzResearch.WordTrace tailWord_2430044 prefixEnd_2430044 1247780583574395675374437 := by
  unfold tailWord_2430044
  simp only [CollatzResearch.WordTrace]
  refine ⟨44315493004186540659500593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59087324005582054212667457 44315493004186540659500593)
  ·
    refine ⟨33236619753139905494625445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44315493004186540659500593 33236619753139905494625445)
    ·
      refine ⟨6231866203713732280242271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33236619753139905494625445 6231866203713732280242271)
      ·
        refine ⟨9347799305570598420363407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231866203713732280242271 9347799305570598420363407)
        ·
          refine ⟨14021698958355897630545111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9347799305570598420363407 14021698958355897630545111)
          ·
            refine ⟨21032548437533846445817667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14021698958355897630545111 21032548437533846445817667)
            ·
              refine ⟨31548822656300769668726501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21032548437533846445817667 31548822656300769668726501)
              ·
                refine ⟨5915404248056394312886219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31548822656300769668726501 5915404248056394312886219)
                ·
                  refine ⟨8873106372084591469329329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915404248056394312886219 8873106372084591469329329)
                  ·
                    refine ⟨6654829779063443601996997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8873106372084591469329329 6654829779063443601996997)
                    ·
                      refine ⟨1247780583574395675374437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6654829779063443601996997 1247780583574395675374437)
                      ·
                        rfl

theorem cell23_2430044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2430044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430044 prefixEnd_2430044 := by exact prefixLift 2430044
  have htrace : WordTrace (prefixWord ++ tailWord_2430044) baseStart_2430044 baseEnd_2430044 := by
    simpa [prefixWord, tailWord_2430044, baseEnd_2430044] using wordTrace_append hprefix tailTrace_2430044
  have hstable : (prefixWord ++ tailWord_2430044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430044).length < 2 ^ (prefixWord ++ tailWord_2430044).sum := by decide
  have hdescent : baseEnd_2430044 < baseStart_2430044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430045 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2430045 : Nat := 118140960795 + 2430045 * 2 ^ 59
def prefixEnd_2430045 : Nat := 4983230072969 + 3 ^ 40 * 2430045 * 2
def baseEnd_2430045 : Nat := 415927032351683390487311

theorem tailTrace_2430045 : CollatzResearch.WordTrace tailWord_2430045 prefixEnd_2430045 415927032351683390487311 := by
  unfold tailWord_2430045
  simp only [CollatzResearch.WordTrace]
  refine ⟨88631022481369458489787589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59087348320912972326525059 88631022481369458489787589)
  ·
    refine ⟨16618316715256773466835173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88631022481369458489787589 16618316715256773466835173)
    ·
      refine ⟨3115934384110645025031595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16618316715256773466835173 3115934384110645025031595)
      ·
        refine ⟨4673901576165967537547393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115934384110645025031595 4673901576165967537547393)
        ·
          refine ⟨3505426182124475653160545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4673901576165967537547393 3505426182124475653160545)
          ·
            refine ⟨2629069636593356739870409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3505426182124475653160545 2629069636593356739870409)
            ·
              refine ⟨1971802227445017554902807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2629069636593356739870409 1971802227445017554902807)
              ·
                refine ⟨2957703341167526332354211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971802227445017554902807 2957703341167526332354211)
                ·
                  refine ⟨4436555011751289498531317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957703341167526332354211 4436555011751289498531317)
                  ·
                    refine ⟨415927032351683390487311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4436555011751289498531317 415927032351683390487311)
                    ·
                      rfl

theorem cell23_2430045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2430045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430045 prefixEnd_2430045 := by exact prefixLift 2430045
  have htrace : WordTrace (prefixWord ++ tailWord_2430045) baseStart_2430045 baseEnd_2430045 := by
    simpa [prefixWord, tailWord_2430045, baseEnd_2430045] using wordTrace_append hprefix tailTrace_2430045
  have hstable : (prefixWord ++ tailWord_2430045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430045).length < 2 ^ (prefixWord ++ tailWord_2430045).sum := by decide
  have hdescent : baseEnd_2430045 < baseStart_2430045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430058 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_2430058 : Nat := 118140960795 + 2430058 * 2 ^ 59
def prefixEnd_2430058 : Nat := 4983230072969 + 3 ^ 40 * 2430058 * 2
def baseEnd_2430058 : Nat := 415929257434519540199791

theorem tailTrace_2430058 : CollatzResearch.WordTrace tailWord_2430058 prefixEnd_2430058 415929257434519540199791 := by
  unfold tailWord_2430058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22157874157580590427502707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59087664420214907806673885 22157874157580590427502707)
  ·
    refine ⟨33236811236370885641254061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22157874157580590427502707 33236811236370885641254061)
    ·
      refine ⟨12463804213639082115470273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33236811236370885641254061 12463804213639082115470273)
      ·
        refine ⟨9347853160229311586602705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12463804213639082115470273 9347853160229311586602705)
        ·
          refine ⟨7010889870171983689952029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9347853160229311586602705 7010889870171983689952029)
          ·
            refine ⟨2629083701314493883732011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7010889870171983689952029 2629083701314493883732011)
            ·
              refine ⟨3943625551971740825598017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629083701314493883732011 3943625551971740825598017)
              ·
                refine ⟨2957719163978805619198513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943625551971740825598017 2957719163978805619198513)
                ·
                  refine ⟨2218289372984104214398885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2957719163978805619198513 2218289372984104214398885)
                  ·
                    refine ⟨415929257434519540199791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2218289372984104214398885 415929257434519540199791)
                    ·
                      rfl

theorem cell23_2430058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_2430058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430058 prefixEnd_2430058 := by exact prefixLift 2430058
  have htrace : WordTrace (prefixWord ++ tailWord_2430058) baseStart_2430058 baseEnd_2430058 := by
    simpa [prefixWord, tailWord_2430058, baseEnd_2430058] using wordTrace_append hprefix tailTrace_2430058
  have hstable : (prefixWord ++ tailWord_2430058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430058).length < 2 ^ (prefixWord ++ tailWord_2430058).sum := by decide
  have hdescent : baseEnd_2430058 < baseStart_2430058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430081 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2430081 : Nat := 118140960795 + 2430081 * 2 ^ 59
def prefixEnd_2430081 : Nat := 4983230072969 + 3 ^ 40 * 2430081 * 2
def baseEnd_2430081 : Nat := 1247799582358612030611767

theorem tailTrace_2430081 : CollatzResearch.WordTrace tailWord_2430081 prefixEnd_2430081 1247799582358612030611767 := by
  unfold tailWord_2430081
  simp only [CollatzResearch.WordTrace]
  refine ⟨88632335509239036638098097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59088223672826024425398731 88632335509239036638098097)
  ·
    refine ⟨66474251631929277478573573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88632335509239036638098097 66474251631929277478573573)
    ·
      refine ⟨12463922180986739527232545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66474251631929277478573573 12463922180986739527232545)
      ·
        refine ⟨9347941635740054645424409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12463922180986739527232545 9347941635740054645424409)
        ·
          refine ⟨7010956226805040984068307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9347941635740054645424409 7010956226805040984068307)
          ·
            refine ⟨10516434340207561476102461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010956226805040984068307 10516434340207561476102461)
            ·
              refine ⟨3943662877577835553538423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10516434340207561476102461 3943662877577835553538423)
              ·
                refine ⟨5915494316366753330307635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943662877577835553538423 5915494316366753330307635)
                ·
                  refine ⟨8873241474550129995461453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915494316366753330307635 8873241474550129995461453)
                  ·
                    refine ⟨3327465552956298748298045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8873241474550129995461453 3327465552956298748298045)
                    ·
                      refine ⟨1247799582358612030611767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3327465552956298748298045 1247799582358612030611767)
                      ·
                        rfl

theorem cell23_2430081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2430081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430081 prefixEnd_2430081 := by exact prefixLift 2430081
  have htrace : WordTrace (prefixWord ++ tailWord_2430081) baseStart_2430081 baseEnd_2430081 := by
    simpa [prefixWord, tailWord_2430081, baseEnd_2430081] using wordTrace_append hprefix tailTrace_2430081
  have hstable : (prefixWord ++ tailWord_2430081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430081).length < 2 ^ (prefixWord ++ tailWord_2430081).sum := by decide
  have hdescent : baseEnd_2430081 < baseStart_2430081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430088 : List Nat := [2, 1, 3, 4, 3, 1, 2, 7]
def baseStart_2430088 : Nat := 118140960795 + 2430088 * 2 ^ 59
def prefixEnd_2430088 : Nat := 4983230072969 + 3 ^ 40 * 2430088 * 2
def baseEnd_2430088 : Nat := 46214932471229389008305

theorem tailTrace_2430088 : CollatzResearch.WordTrace tailWord_2430088 prefixEnd_2430088 46214932471229389008305 := by
  unfold tailWord_2430088
  simp only [CollatzResearch.WordTrace]
  refine ⟨44316295410106838416801459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59088393880142451222401945 44316295410106838416801459)
  ·
    refine ⟨66474443115160257625202189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44316295410106838416801459 66474443115160257625202189)
    ·
      refine ⟨24927916168185096609450821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66474443115160257625202189 24927916168185096609450821)
      ·
        refine ⟨4673984281534705614272029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24927916168185096609450821 4673984281534705614272029)
        ·
          refine ⟨1752744105575514605352011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4673984281534705614272029 1752744105575514605352011)
          ·
            refine ⟨2629116158363271908028017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752744105575514605352011 2629116158363271908028017)
            ·
              refine ⟨1971837118772453931021013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2629116158363271908028017 1971837118772453931021013)
              ·
                refine ⟨46214932471229389008305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1971837118772453931021013 46214932471229389008305)
                ·
                  rfl

theorem cell23_2430088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 7].length) (baseStart_2430088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430088 prefixEnd_2430088 := by exact prefixLift 2430088
  have htrace : WordTrace (prefixWord ++ tailWord_2430088) baseStart_2430088 baseEnd_2430088 := by
    simpa [prefixWord, tailWord_2430088, baseEnd_2430088] using wordTrace_append hprefix tailTrace_2430088
  have hstable : (prefixWord ++ tailWord_2430088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430088).length < 2 ^ (prefixWord ++ tailWord_2430088).sum := by decide
  have hdescent : baseEnd_2430088 < baseStart_2430088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430094 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2430094 : Nat := 118140960795 + 2430094 * 2 ^ 59
def prefixEnd_2430094 : Nat := 4983230072969 + 3 ^ 40 * 2430094 * 2
def baseEnd_2430094 : Nat := 1247806257607120479749207

theorem tailTrace_2430094 : CollatzResearch.WordTrace tailWord_2430094 prefixEnd_2430094 1247806257607120479749207 := by
  unfold tailWord_2430094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11079101207273992482290167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59088539772127959905547557 11079101207273992482290167)
  ·
    refine ⟨16618651810910988723435251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11079101207273992482290167 16618651810910988723435251)
    ·
      refine ⟨24927977716366483085152877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16618651810910988723435251 24927977716366483085152877)
      ·
        refine ⟨9347991643637431156932329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24927977716366483085152877 9347991643637431156932329)
        ·
          refine ⟨7010993732728073367699247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9347991643637431156932329 7010993732728073367699247)
          ·
            refine ⟨10516490599092110051548871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010993732728073367699247 10516490599092110051548871)
            ·
              refine ⟨15774735898638165077323307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10516490599092110051548871 15774735898638165077323307)
              ·
                refine ⟨23662103847957247615984961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15774735898638165077323307 23662103847957247615984961)
                ·
                  refine ⟨17746577885967935711988721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23662103847957247615984961 17746577885967935711988721)
                  ·
                    refine ⟨13309933414475951783991541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17746577885967935711988721 13309933414475951783991541)
                    ·
                      refine ⟨1247806257607120479749207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13309933414475951783991541 1247806257607120479749207)
                      ·
                        rfl

theorem cell23_2430094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2430094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430094 prefixEnd_2430094 := by exact prefixLift 2430094
  have htrace : WordTrace (prefixWord ++ tailWord_2430094) baseStart_2430094 baseEnd_2430094 := by
    simpa [prefixWord, tailWord_2430094, baseEnd_2430094] using wordTrace_append hprefix tailTrace_2430094
  have hstable : (prefixWord ++ tailWord_2430094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430094).length < 2 ^ (prefixWord ++ tailWord_2430094).sum := by decide
  have hdescent : baseEnd_2430094 < baseStart_2430094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430108 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_2430108 : Nat := 118140960795 + 2430108 * 2 ^ 59
def prefixEnd_2430108 : Nat := 4983230072969 + 3 ^ 40 * 2430108 * 2
def baseEnd_2430108 : Nat := 1247813446336283424974143

theorem tailTrace_2430108 : CollatzResearch.WordTrace tailWord_2430108 prefixEnd_2430108 1247813446336283424974143 := by
  unfold tailWord_2430108
  simp only [CollatzResearch.WordTrace]
  refine ⟨44316660140070610124665489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59088880186760813499553985 44316660140070610124665489)
  ·
    refine ⟨33237495105052957593499117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44316660140070610124665489 33237495105052957593499117)
    ·
      refine ⟨12464060664394859097562169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33237495105052957593499117 12464060664394859097562169)
      ·
        refine ⟨9348045498296144323171627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12464060664394859097562169 9348045498296144323171627)
        ·
          refine ⟨14022068247444216484757441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9348045498296144323171627 14022068247444216484757441)
          ·
            refine ⟨10516551185583162363568081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14022068247444216484757441 10516551185583162363568081)
            ·
              refine ⟨7887413389187371772676061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10516551185583162363568081 7887413389187371772676061)
              ·
                refine ⟨2957780020945264414753523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7887413389187371772676061 2957780020945264414753523)
                ·
                  refine ⟨4436670031417896622130285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957780020945264414753523 4436670031417896622130285)
                  ·
                    refine ⟨1663751261781711233298857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4436670031417896622130285 1663751261781711233298857)
                    ·
                      refine ⟨1247813446336283424974143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663751261781711233298857 1247813446336283424974143)
                      ·
                        rfl

theorem cell23_2430108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_2430108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430108 prefixEnd_2430108 := by exact prefixLift 2430108
  have htrace : WordTrace (prefixWord ++ tailWord_2430108) baseStart_2430108 baseEnd_2430108 := by
    simpa [prefixWord, tailWord_2430108, baseEnd_2430108] using wordTrace_append hprefix tailTrace_2430108
  have hstable : (prefixWord ++ tailWord_2430108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430108).length < 2 ^ (prefixWord ++ tailWord_2430108).sum := by decide
  have hdescent : baseEnd_2430108 < baseStart_2430108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430184 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2430184 : Nat := 118140960795 + 2430184 * 2 ^ 59
def prefixEnd_2430184 : Nat := 4983230072969 + 3 ^ 40 * 2430184 * 2
def baseEnd_2430184 : Nat := 1247852470866025127623793

theorem tailTrace_2430184 : CollatzResearch.WordTrace tailWord_2430184 prefixEnd_2430184 1247852470866025127623793 := by
  unfold tailWord_2430184
  simp only [CollatzResearch.WordTrace]
  refine ⟨44318046113932942614548803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59090728151910590152731737 44318046113932942614548803)
  ·
    refine ⟨66477069170899413921823205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44318046113932942614548803 66477069170899413921823205)
    ·
      refine ⟨12464450469543640110341851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66477069170899413921823205 12464450469543640110341851)
      ·
        refine ⟨18696675704315460165512777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12464450469543640110341851 18696675704315460165512777)
        ·
          refine ⟨14022506778236595124134583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18696675704315460165512777 14022506778236595124134583)
          ·
            refine ⟨21033760167354892686201875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14022506778236595124134583 21033760167354892686201875)
            ·
              refine ⟨31550640251032339029302813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21033760167354892686201875 31550640251032339029302813)
              ·
                refine ⟨11831490094137127135988555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31550640251032339029302813 11831490094137127135988555)
                ·
                  refine ⟨17747235141205690703982833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11831490094137127135988555 17747235141205690703982833)
                  ·
                    refine ⟨13310426355904268027987125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17747235141205690703982833 13310426355904268027987125)
                    ·
                      refine ⟨1247852470866025127623793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13310426355904268027987125 1247852470866025127623793)
                      ·
                        rfl

theorem cell23_2430184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2430184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430184 prefixEnd_2430184 := by exact prefixLift 2430184
  have htrace : WordTrace (prefixWord ++ tailWord_2430184) baseStart_2430184 baseEnd_2430184 := by
    simpa [prefixWord, tailWord_2430184, baseEnd_2430184] using wordTrace_append hprefix tailTrace_2430184
  have hstable : (prefixWord ++ tailWord_2430184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430184).length < 2 ^ (prefixWord ++ tailWord_2430184).sum := by decide
  have hdescent : baseEnd_2430184 < baseStart_2430184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430211 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 4]
def baseStart_2430211 : Nat := 118140960795 + 2430211 * 2 ^ 59
def prefixEnd_2430211 : Nat := 4983230072969 + 3 ^ 40 * 2430211 * 2
def baseEnd_2430211 : Nat := 1247866334843696521986169

theorem tailTrace_2430211 : CollatzResearch.WordTrace tailWord_2430211 prefixEnd_2430211 1247866334843696521986169 := by
  unfold tailWord_2430211
  simp only [CollatzResearch.WordTrace]
  refine ⟨88637076998768068840330487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59091384665845379226886991 88637076998768068840330487)
  ·
    refine ⟨132955615498152103260495731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88637076998768068840330487 132955615498152103260495731)
    ·
      refine ⟨199433423247228154890743597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132955615498152103260495731 199433423247228154890743597)
      ·
        refine ⟨74787533717710558084028849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199433423247228154890743597 74787533717710558084028849)
        ·
          refine ⟨56090650288282918563021637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74787533717710558084028849 56090650288282918563021637)
          ·
            refine ⟨10516996929053047230566557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56090650288282918563021637 10516996929053047230566557)
            ·
              refine ⟨3943873848394892711462459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10516996929053047230566557 3943873848394892711462459)
              ·
                refine ⟨5915810772592339067193689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943873848394892711462459 5915810772592339067193689)
                ·
                  refine ⟨4436858079444254300395267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5915810772592339067193689 4436858079444254300395267)
                  ·
                    refine ⟨6655287119166381450592901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4436858079444254300395267 6655287119166381450592901)
                    ·
                      refine ⟨1247866334843696521986169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6655287119166381450592901 1247866334843696521986169)
                      ·
                        rfl

theorem cell23_2430211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_2430211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430211 prefixEnd_2430211 := by exact prefixLift 2430211
  have htrace : WordTrace (prefixWord ++ tailWord_2430211) baseStart_2430211 baseEnd_2430211 := by
    simpa [prefixWord, tailWord_2430211, baseEnd_2430211] using wordTrace_append hprefix tailTrace_2430211
  have hstable : (prefixWord ++ tailWord_2430211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430211).length < 2 ^ (prefixWord ++ tailWord_2430211).sum := by decide
  have hdescent : baseEnd_2430211 < baseStart_2430211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
