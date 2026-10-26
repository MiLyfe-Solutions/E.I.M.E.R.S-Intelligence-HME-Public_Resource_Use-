import V185TrunkScan23Chunk1365

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8090776 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 2, 2, 2]
def baseStart_8090776 : Nat := 118140960795 + 8090776 * 2 ^ 59
def prefixEnd_8090776 : Nat := 4983230072969 + 3 ^ 40 * 8090776 * 2
def baseEnd_8090776 : Nat := 4154456955861342035391205

theorem tailTrace_8090776 : CollatzResearch.WordTrace tailWord_8090776 prefixEnd_8090776 4154456955861342035391205 := by
  unfold tailWord_8090776
  simp only [CollatzResearch.WordTrace]
  refine ⟨147547421868253910687814091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196729895824338547583752121 147547421868253910687814091)
  ·
    refine ⟨221321132802380866031721137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147547421868253910687814091 221321132802380866031721137)
    ·
      refine ⟨165990849601785649523790853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221321132802380866031721137 165990849601785649523790853)
      ·
        refine ⟨31123284300334809285710785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165990849601785649523790853 31123284300334809285710785)
        ·
          refine ⟨23342463225251106964283089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31123284300334809285710785 23342463225251106964283089)
          ·
            refine ⟨17506847418938330223212317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23342463225251106964283089 17506847418938330223212317)
            ·
              refine ⟨6565067782101873833704619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17506847418938330223212317 6565067782101873833704619)
              ·
                refine ⟨9847601673152810750556929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6565067782101873833704619 9847601673152810750556929)
                ·
                  refine ⟨7385701254864608062917697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9847601673152810750556929 7385701254864608062917697)
                  ·
                    refine ⟨5539275941148456047188273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7385701254864608062917697 5539275941148456047188273)
                    ·
                      refine ⟨4154456955861342035391205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539275941148456047188273 4154456955861342035391205)
                      ·
                        rfl

theorem cell23_8090776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_8090776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090776 prefixEnd_8090776 := by exact prefixLift 8090776
  have htrace : WordTrace (prefixWord ++ tailWord_8090776) baseStart_8090776 baseEnd_8090776 := by
    simpa [prefixWord, tailWord_8090776, baseEnd_8090776] using wordTrace_append hprefix tailTrace_8090776
  have hstable : (prefixWord ++ tailWord_8090776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090776).length < 2 ^ (prefixWord ++ tailWord_8090776).sum := by decide
  have hdescent : baseEnd_8090776 < baseStart_8090776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090815 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 4, 4, 2]
def baseStart_8090815 : Nat := 118140960795 + 8090815 * 2 ^ 59
def prefixEnd_8090815 : Nat := 4983230072969 + 3 ^ 40 * 8090815 * 2
def baseEnd_8090815 : Nat := 4154476981606867382803525

theorem tailTrace_8090815 : CollatzResearch.WordTrace tailWord_8090815 prefixEnd_8090815 4154476981606867382803525 := by
  unfold tailWord_8090815
  simp only [CollatzResearch.WordTrace]
  refine ⟨295096266183366531036297899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196730844122244354024198599 295096266183366531036297899)
  ·
    refine ⟨442644399275049796554446849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295096266183366531036297899 442644399275049796554446849)
    ·
      refine ⟨331983299456287347415835137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442644399275049796554446849 331983299456287347415835137)
      ·
        refine ⟨248987474592215510561876353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331983299456287347415835137 248987474592215510561876353)
        ·
          refine ⟨186740605944161632921407265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248987474592215510561876353 186740605944161632921407265)
          ·
            refine ⟨140055454458121224691055449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186740605944161632921407265 140055454458121224691055449)
            ·
              refine ⟨105041590843590918518291587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140055454458121224691055449 105041590843590918518291587)
              ·
                refine ⟨157562386265386377777437381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105041590843590918518291587 157562386265386377777437381)
                ·
                  refine ⟨29542947424759945833269509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157562386265386377777437381 29542947424759945833269509)
                  ·
                    refine ⟨5539302642142489843738033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29542947424759945833269509 5539302642142489843738033)
                    ·
                      refine ⟨4154476981606867382803525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539302642142489843738033 4154476981606867382803525)
                      ·
                        rfl

theorem cell23_8090815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_8090815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090815 prefixEnd_8090815 := by exact prefixLift 8090815
  have htrace : WordTrace (prefixWord ++ tailWord_8090815) baseStart_8090815 baseEnd_8090815 := by
    simpa [prefixWord, tailWord_8090815, baseEnd_8090815] using wordTrace_append hprefix tailTrace_8090815
  have hstable : (prefixWord ++ tailWord_8090815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090815).length < 2 ^ (prefixWord ++ tailWord_8090815).sum := by decide
  have hdescent : baseEnd_8090815 < baseStart_8090815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090909 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_8090909 : Nat := 118140960795 + 8090909 * 2 ^ 59
def prefixEnd_8090909 : Nat := 4983230072969 + 3 ^ 40 * 8090909 * 2
def baseEnd_8090909 : Nat := 4154525248788390015028093

theorem tailTrace_8090909 : CollatzResearch.WordTrace tailWord_8090909 prefixEnd_8090909 4154525248788390015028093 := by
  unfold tailWord_8090909
  simp only [CollatzResearch.WordTrace]
  refine ⟨295099694645025985090219781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196733129763350656726813187 295099694645025985090219781)
  ·
    refine ⟨55331192745942372204416209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295099694645025985090219781 55331192745942372204416209)
    ·
      refine ⟨41498394559456779153312157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55331192745942372204416209 41498394559456779153312157)
      ·
        refine ⟨15561897959796292182492059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41498394559456779153312157 15561897959796292182492059)
        ·
          refine ⟨23342846939694438273738089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15561897959796292182492059 23342846939694438273738089)
          ·
            refine ⟨17507135204770828705303567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23342846939694438273738089 17507135204770828705303567)
            ·
              refine ⟨26260702807156243057955351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17507135204770828705303567 26260702807156243057955351)
              ·
                refine ⟨39391054210734364586933027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26260702807156243057955351 39391054210734364586933027)
                ·
                  refine ⟨59086581316101546880399541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39391054210734364586933027 59086581316101546880399541)
                  ·
                    refine ⟨5539366998384520020037457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59086581316101546880399541 5539366998384520020037457)
                    ·
                      refine ⟨4154525248788390015028093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539366998384520020037457 4154525248788390015028093)
                      ·
                        rfl

theorem cell23_8090909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_8090909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090909 prefixEnd_8090909 := by exact prefixLift 8090909
  have htrace : WordTrace (prefixWord ++ tailWord_8090909) baseStart_8090909 baseEnd_8090909 := by
    simpa [prefixWord, tailWord_8090909, baseEnd_8090909] using wordTrace_append hprefix tailTrace_8090909
  have hstable : (prefixWord ++ tailWord_8090909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090909).length < 2 ^ (prefixWord ++ tailWord_8090909).sum := by decide
  have hdescent : baseEnd_8090909 < baseStart_8090909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090915 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 1, 6]
def baseStart_8090915 : Nat := 118140960795 + 8090915 * 2 ^ 59
def prefixEnd_8090915 : Nat := 4983230072969 + 3 ^ 40 * 8090915 * 2
def baseEnd_8090915 : Nat := 1384842776557438997184355

theorem tailTrace_8090915 : CollatzResearch.WordTrace tailWord_8090915 prefixEnd_8090915 1384842776557438997184355 := by
  unfold tailWord_8090915
  simp only [CollatzResearch.WordTrace]
  refine ⟨295099913483004248114938199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196733275655336165409958799 295099913483004248114938199)
  ·
    refine ⟨442649870224506372172407299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295099913483004248114938199 442649870224506372172407299)
    ·
      refine ⟨663974805336759558258610949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442649870224506372172407299 663974805336759558258610949)
      ·
        refine ⟨124495276000642417173489553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 663974805336759558258610949 124495276000642417173489553)
        ·
          refine ⟨93371457000481812880117165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124495276000642417173489553 93371457000481812880117165)
          ·
            refine ⟨35014296375180679830043937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93371457000481812880117165 35014296375180679830043937)
            ·
              refine ⟨26260722281385509872532953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35014296375180679830043937 26260722281385509872532953)
              ·
                refine ⟨19695541711039132404399715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26260722281385509872532953 19695541711039132404399715)
                ·
                  refine ⟨29543312566558698606599573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19695541711039132404399715 29543312566558698606599573)
                  ·
                    refine ⟨1384842776557438997184355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29543312566558698606599573 1384842776557438997184355)
                    ·
                      rfl

theorem cell23_8090915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 6].length) (baseStart_8090915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090915 prefixEnd_8090915 := by exact prefixLift 8090915
  have htrace : WordTrace (prefixWord ++ tailWord_8090915) baseStart_8090915 baseEnd_8090915 := by
    simpa [prefixWord, tailWord_8090915, baseEnd_8090915] using wordTrace_append hprefix tailTrace_8090915
  have hstable : (prefixWord ++ tailWord_8090915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090915).length < 2 ^ (prefixWord ++ tailWord_8090915).sum := by decide
  have hdescent : baseEnd_8090915 < baseStart_8090915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090916 : List Nat := [2, 3, 1, 3, 1, 1, 4, 3, 1, 1, 3]
def baseStart_8090916 : Nat := 118140960795 + 8090916 * 2 ^ 59
def prefixEnd_8090916 : Nat := 4983230072969 + 3 ^ 40 * 8090916 * 2
def baseEnd_8090916 : Nat := 4154528843152971487640561

theorem tailTrace_8090916 : CollatzResearch.WordTrace tailWord_8090916 prefixEnd_8090916 4154528843152971487640561 := by
  unfold tailWord_8090916
  simp only [CollatzResearch.WordTrace]
  refine ⟨147549974978000312642862301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196733299970667083523816401 147549974978000312642862301)
  ·
    refine ⟨55331240616750117241073363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147549974978000312642862301 55331240616750117241073363)
    ·
      refine ⟨82996860925125175861610045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55331240616750117241073363 82996860925125175861610045)
      ·
        refine ⟨31123822846921940948103767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82996860925125175861610045 31123822846921940948103767)
        ·
          refine ⟨46685734270382911422155651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31123822846921940948103767 46685734270382911422155651)
          ·
            refine ⟨70028601405574367133233477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46685734270382911422155651 70028601405574367133233477)
            ·
              refine ⟨13130362763545193837481277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70028601405574367133233477 13130362763545193837481277)
              ·
                refine ⟨4923886036329447689055479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13130362763545193837481277 4923886036329447689055479)
                ·
                  refine ⟨7385829054494171533583219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923886036329447689055479 7385829054494171533583219)
                  ·
                    refine ⟨11078743581741257300374829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7385829054494171533583219 11078743581741257300374829)
                    ·
                      refine ⟨4154528843152971487640561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11078743581741257300374829 4154528843152971487640561)
                      ·
                        rfl

theorem cell23_8090916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_8090916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090916 prefixEnd_8090916 := by exact prefixLift 8090916
  have htrace : WordTrace (prefixWord ++ tailWord_8090916) baseStart_8090916 baseEnd_8090916 := by
    simpa [prefixWord, tailWord_8090916, baseEnd_8090916] using wordTrace_append hprefix tailTrace_8090916
  have hstable : (prefixWord ++ tailWord_8090916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090916).length < 2 ^ (prefixWord ++ tailWord_8090916).sum := by decide
  have hdescent : baseEnd_8090916 < baseStart_8090916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090928 : List Nat := [2, 1, 1, 1, 2, 2, 14]
def baseStart_8090928 : Nat := 118140960795 + 8090928 * 2 ^ 59
def prefixEnd_8090928 : Nat := 4983230072969 + 3 ^ 40 * 8090928 * 2
def baseEnd_8090928 : Nat := 51290555616306486922105

theorem tailTrace_8090928 : CollatzResearch.WordTrace tailWord_8090928 prefixEnd_8090928 51290555616306486922105 := by
  unfold tailWord_8090928
  simp only [CollatzResearch.WordTrace]
  refine ⟨147550193815978575667580719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196733591754638100890107625 147550193815978575667580719)
  ·
    refine ⟨221325290723967863501371079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147550193815978575667580719 221325290723967863501371079)
    ·
      refine ⟨331987936085951795252056619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221325290723967863501371079 331987936085951795252056619)
      ·
        refine ⟨497981904128927692878084929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331987936085951795252056619 497981904128927692878084929)
        ·
          refine ⟨373486428096695769658563697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497981904128927692878084929 373486428096695769658563697)
          ·
            refine ⟨280114821072521827243922773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373486428096695769658563697 280114821072521827243922773)
            ·
              refine ⟨51290555616306486922105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 280114821072521827243922773 51290555616306486922105)
              ·
                rfl

theorem cell23_8090928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 14].length) (baseStart_8090928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090928 prefixEnd_8090928 := by exact prefixLift 8090928
  have htrace : WordTrace (prefixWord ++ tailWord_8090928) baseStart_8090928 baseEnd_8090928 := by
    simpa [prefixWord, tailWord_8090928, baseEnd_8090928] using wordTrace_append hprefix tailTrace_8090928
  have hstable : (prefixWord ++ tailWord_8090928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090928).length < 2 ^ (prefixWord ++ tailWord_8090928).sum := by decide
  have hdescent : baseEnd_8090928 < baseStart_8090928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090942 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_8090942 : Nat := 118140960795 + 8090942 * 2 ^ 59
def prefixEnd_8090942 : Nat := 4983230072969 + 3 ^ 40 * 8090942 * 2
def baseEnd_8090942 : Nat := 4154542193649988385915441

theorem tailTrace_8090942 : CollatzResearch.WordTrace tailWord_8090942 prefixEnd_8090942 4154542193649988385915441 := by
  unfold tailWord_8090942
  simp only [CollatzResearch.WordTrace]
  refine ⟨36887612281738303965771385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196733932169270954484114053 36887612281738303965771385)
  ·
    refine ⟨27665709211303727974328539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36887612281738303965771385 27665709211303727974328539)
    ·
      refine ⟨41498563816955591961492809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27665709211303727974328539 41498563816955591961492809)
      ·
        refine ⟨31123922862716693971119607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41498563816955591961492809 31123922862716693971119607)
        ·
          refine ⟨46685884294075040956679411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31123922862716693971119607 46685884294075040956679411)
          ·
            refine ⟨70028826441112561435019117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46685884294075040956679411 70028826441112561435019117)
            ·
              refine ⟨26260809915417210538132169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70028826441112561435019117 26260809915417210538132169)
              ·
                refine ⟨19695607436562907903599127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26260809915417210538132169 19695607436562907903599127)
                ·
                  refine ⟨29543411154844361855398691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19695607436562907903599127 29543411154844361855398691)
                  ·
                    refine ⟨44315116732266542783098037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29543411154844361855398691 44315116732266542783098037)
                    ·
                      refine ⟨4154542193649988385915441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44315116732266542783098037 4154542193649988385915441)
                      ·
                        rfl

theorem cell23_8090942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_8090942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090942 prefixEnd_8090942 := by exact prefixLift 8090942
  have htrace : WordTrace (prefixWord ++ tailWord_8090942) baseStart_8090942 baseEnd_8090942 := by
    simpa [prefixWord, tailWord_8090942, baseEnd_8090942] using wordTrace_append hprefix tailTrace_8090942
  have hstable : (prefixWord ++ tailWord_8090942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090942).length < 2 ^ (prefixWord ++ tailWord_8090942).sum := by decide
  have hdescent : baseEnd_8090942 < baseStart_8090942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090989 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_8090989 : Nat := 118140960795 + 8090989 * 2 ^ 59
def prefixEnd_8090989 : Nat := 4983230072969 + 3 ^ 40 * 8090989 * 2
def baseEnd_8090989 : Nat := 4154566327240749702027725

theorem tailTrace_8090989 : CollatzResearch.WordTrace tailWord_8090989 prefixEnd_8090989 4154566327240749702027725 := by
  unfold tailWord_8090989
  simp only [CollatzResearch.WordTrace]
  refine ⟨295102612484736158753132021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196735074989824105835421347 295102612484736158753132021)
  ·
    refine ⟨27665869920444014883106127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295102612484736158753132021 27665869920444014883106127)
    ·
      refine ⟨41498804880666022324659191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27665869920444014883106127 41498804880666022324659191)
      ·
        refine ⟨62248207320999033486988787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41498804880666022324659191 62248207320999033486988787)
        ·
          refine ⟨93372310981498550230483181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62248207320999033486988787 93372310981498550230483181)
          ·
            refine ⟨35014616618061956336431193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93372310981498550230483181 35014616618061956336431193)
            ·
              refine ⟨26260962463546467252323395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35014616618061956336431193 26260962463546467252323395)
              ·
                refine ⟨39391443695319700878485093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26260962463546467252323395 39391443695319700878485093)
                ·
                  refine ⟨7385895692872443914715955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39391443695319700878485093 7385895692872443914715955)
                  ·
                    refine ⟨11078843539308665872073933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7385895692872443914715955 11078843539308665872073933)
                    ·
                      refine ⟨4154566327240749702027725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11078843539308665872073933 4154566327240749702027725)
                      ·
                        rfl

theorem cell23_8090989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_8090989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090989 prefixEnd_8090989 := by exact prefixLift 8090989
  have htrace : WordTrace (prefixWord ++ tailWord_8090989) baseStart_8090989 baseEnd_8090989 := by
    simpa [prefixWord, tailWord_8090989, baseEnd_8090989] using wordTrace_append hprefix tailTrace_8090989
  have hstable : (prefixWord ++ tailWord_8090989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090989).length < 2 ^ (prefixWord ++ tailWord_8090989).sum := by decide
  have hdescent : baseEnd_8090989 < baseStart_8090989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090990 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_8090990 : Nat := 118140960795 + 8090990 * 2 ^ 59
def prefixEnd_8090990 : Nat := 4983230072969 + 3 ^ 40 * 8090990 * 2
def baseEnd_8090990 : Nat := 4154566840721404198115221

theorem tailTrace_8090990 : CollatzResearch.WordTrace tailWord_8090990 prefixEnd_8090990 4154566840721404198115221 := by
  unfold tailWord_8090990
  simp only [CollatzResearch.WordTrace]
  refine ⟨36887831119716566990489803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196735099305155023949278949 36887831119716566990489803)
  ·
    refine ⟨55331746679574850485734705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36887831119716566990489803 55331746679574850485734705)
    ·
      refine ⟨41498810009681137864301029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55331746679574850485734705 41498810009681137864301029)
      ·
        refine ⟨7781026876815213349556443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41498810009681137864301029 7781026876815213349556443)
        ·
          refine ⟨11671540315222820024334665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781026876815213349556443 11671540315222820024334665)
          ·
            refine ⟨8753655236417115018250999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11671540315222820024334665 8753655236417115018250999)
            ·
              refine ⟨13130482854625672527376499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8753655236417115018250999 13130482854625672527376499)
              ·
                refine ⟨19695724281938508791064749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13130482854625672527376499 19695724281938508791064749)
                ·
                  refine ⟨7385896605726940796649281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19695724281938508791064749 7385896605726940796649281)
                  ·
                    refine ⟨5539422454295205597486961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7385896605726940796649281 5539422454295205597486961)
                    ·
                      refine ⟨4154566840721404198115221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539422454295205597486961 4154566840721404198115221)
                      ·
                        rfl

theorem cell23_8090990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_8090990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090990 prefixEnd_8090990 := by exact prefixLift 8090990
  have htrace : WordTrace (prefixWord ++ tailWord_8090990) baseStart_8090990 baseEnd_8090990 := by
    simpa [prefixWord, tailWord_8090990, baseEnd_8090990] using wordTrace_append hprefix tailTrace_8090990
  have hstable : (prefixWord ++ tailWord_8090990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090990).length < 2 ^ (prefixWord ++ tailWord_8090990).sum := by decide
  have hdescent : baseEnd_8090990 < baseStart_8090990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091005 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_8091005 : Nat := 118140960795 + 8091005 * 2 ^ 59
def prefixEnd_8091005 : Nat := 4983230072969 + 3 ^ 40 * 8091005 * 2
def baseEnd_8091005 : Nat := 1384858180977073879809217

theorem tailTrace_8091005 : CollatzResearch.WordTrace tailWord_8091005 prefixEnd_8091005 1384858180977073879809217 := by
  unfold tailWord_8091005
  simp only [CollatzResearch.WordTrace]
  refine ⟨295103196052678193485714469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196735464035118795657142979 295103196052678193485714469)
  ·
    refine ⟨55331849259877161278571463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295103196052678193485714469 55331849259877161278571463)
    ·
      refine ⟨82997773889815741917857195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55331849259877161278571463 82997773889815741917857195)
      ·
        refine ⟨124496660834723612876785793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82997773889815741917857195 124496660834723612876785793)
        ·
          refine ⟨93372495626042709657589345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124496660834723612876785793 93372495626042709657589345)
          ·
            refine ⟨70029371719532032243192009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93372495626042709657589345 70029371719532032243192009)
            ·
              refine ⟨52522028789649024182394007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70029371719532032243192009 52522028789649024182394007)
              ·
                refine ⟨78783043184473536273591011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52522028789649024182394007 78783043184473536273591011)
                ·
                  refine ⟨118174564776710304410386517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78783043184473536273591011 118174564776710304410386517)
                  ·
                    refine ⟨1384858180977073879809217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118174564776710304410386517 1384858180977073879809217)
                    ·
                      rfl

theorem cell23_8091005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_8091005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091005 prefixEnd_8091005 := by exact prefixLift 8091005
  have htrace : WordTrace (prefixWord ++ tailWord_8091005) baseStart_8091005 baseEnd_8091005 := by
    simpa [prefixWord, tailWord_8091005, baseEnd_8091005] using wordTrace_append hprefix tailTrace_8091005
  have hstable : (prefixWord ++ tailWord_8091005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091005).length < 2 ^ (prefixWord ++ tailWord_8091005).sum := by decide
  have hdescent : baseEnd_8091005 < baseStart_8091005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091016 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_8091016 : Nat := 118140960795 + 8091016 * 2 ^ 59
def prefixEnd_8091016 : Nat := 4983230072969 + 3 ^ 40 * 8091016 * 2
def baseEnd_8091016 : Nat := 4154580191218421096390101

theorem tailTrace_8091016 : CollatzResearch.WordTrace tailWord_8091016 prefixEnd_8091016 4154580191218421096390101 := by
  unfold tailWord_8091016
  simp only [CollatzResearch.WordTrace]
  refine ⟨147551798627819171182182451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196735731503758894909576601 147551798627819171182182451)
  ·
    refine ⟨221327697941728756773273677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147551798627819171182182451 221327697941728756773273677)
    ·
      refine ⟨82997886728148283789977629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221327697941728756773273677 82997886728148283789977629)
      ·
        refine ⟨31124207523055606421241611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82997886728148283789977629 31124207523055606421241611)
        ·
          refine ⟨46686311284583409631862417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31124207523055606421241611 46686311284583409631862417)
          ·
            refine ⟨35014733463437557223896813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46686311284583409631862417 35014733463437557223896813)
            ·
              refine ⟨13130525048789083958961305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35014733463437557223896813 13130525048789083958961305)
              ·
                refine ⟨9847893786591812969220979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13130525048789083958961305 9847893786591812969220979)
                ·
                  refine ⟨14771840679887719453831469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9847893786591812969220979 14771840679887719453831469)
                  ·
                    refine ⟨5539440254957894795186801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14771840679887719453831469 5539440254957894795186801)
                    ·
                      refine ⟨4154580191218421096390101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539440254957894795186801 4154580191218421096390101)
                      ·
                        rfl

theorem cell23_8091016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_8091016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091016 prefixEnd_8091016 := by exact prefixLift 8091016
  have htrace : WordTrace (prefixWord ++ tailWord_8091016) baseStart_8091016 baseEnd_8091016 := by
    simpa [prefixWord, tailWord_8091016, baseEnd_8091016] using wordTrace_append hprefix tailTrace_8091016
  have hstable : (prefixWord ++ tailWord_8091016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091016).length < 2 ^ (prefixWord ++ tailWord_8091016).sum := by decide
  have hdescent : baseEnd_8091016 < baseStart_8091016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091025 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_8091025 : Nat := 118140960795 + 8091025 * 2 ^ 59
def prefixEnd_8091025 : Nat := 4983230072969 + 3 ^ 40 * 8091025 * 2
def baseEnd_8091025 : Nat := 4154584812544311561177559

theorem tailTrace_8091025 : CollatzResearch.WordTrace tailWord_8091025 prefixEnd_8091025 4154584812544311561177559 := by
  unfold tailWord_8091025
  simp only [CollatzResearch.WordTrace]
  refine ⟨295103925512605736901442529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196735950341737157934295019 295103925512605736901442529)
  ·
    refine ⟨221327944134454302676081897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295103925512605736901442529 221327944134454302676081897)
    ·
      refine ⟨165995958100840727007061423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221327944134454302676081897 165995958100840727007061423)
      ·
        refine ⟨248993937151261090510592135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165995958100840727007061423 248993937151261090510592135)
        ·
          refine ⟨373490905726891635765888203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248993937151261090510592135 373490905726891635765888203)
          ·
            refine ⟨560236358590337453648832305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373490905726891635765888203 560236358590337453648832305)
            ·
              refine ⟨420177268942753090236624229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560236358590337453648832305 420177268942753090236624229)
              ·
                refine ⟨78783237926766204419367043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420177268942753090236624229 78783237926766204419367043)
                ·
                  refine ⟨118174856890149306629050565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78783237926766204419367043 118174856890149306629050565)
                  ·
                    refine ⟨22157785666902994992946981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118174856890149306629050565 22157785666902994992946981)
                    ·
                      refine ⟨4154584812544311561177559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22157785666902994992946981 4154584812544311561177559)
                      ·
                        rfl

theorem cell23_8091025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_8091025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091025 prefixEnd_8091025 := by exact prefixLift 8091025
  have htrace : WordTrace (prefixWord ++ tailWord_8091025) baseStart_8091025 baseEnd_8091025 := by
    simpa [prefixWord, tailWord_8091025, baseEnd_8091025] using wordTrace_append hprefix tailTrace_8091025
  have hstable : (prefixWord ++ tailWord_8091025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091025).length < 2 ^ (prefixWord ++ tailWord_8091025).sum := by decide
  have hdescent : baseEnd_8091025 < baseStart_8091025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091029 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_8091029 : Nat := 118140960795 + 8091029 * 2 ^ 59
def prefixEnd_8091029 : Nat := 4983230072969 + 3 ^ 40 * 8091029 * 2
def baseEnd_8091029 : Nat := 4154586866466929545527541

theorem tailTrace_8091029 : CollatzResearch.WordTrace tailWord_8091029 prefixEnd_8091029 4154586866466929545527541 := by
  unfold tailWord_8091029
  simp only [CollatzResearch.WordTrace]
  refine ⟨295104071404591245584588141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196736047603060830389725427 295104071404591245584588141)
  ·
    refine ⟨110664026776721717094220553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295104071404591245584588141 110664026776721717094220553)
    ·
      refine ⟨82998020082541287820665415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110664026776721717094220553 82998020082541287820665415)
      ·
        refine ⟨124497030123811931730998123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82998020082541287820665415 124497030123811931730998123)
        ·
          refine ⟨186745545185717897596497185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124497030123811931730998123 186745545185717897596497185)
          ·
            refine ⟨140059158889288423197372889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186745545185717897596497185 140059158889288423197372889)
            ·
              refine ⟨105044369166966317398029667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140059158889288423197372889 105044369166966317398029667)
              ·
                refine ⟨157566553750449476097044501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105044369166966317398029667 157566553750449476097044501)
                ·
                  refine ⟨7385932207052319192048961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157566553750449476097044501 7385932207052319192048961)
                  ·
                    refine ⟨5539449155289239394036721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7385932207052319192048961 5539449155289239394036721)
                    ·
                      refine ⟨4154586866466929545527541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539449155289239394036721 4154586866466929545527541)
                      ·
                        rfl

theorem cell23_8091029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_8091029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091029 prefixEnd_8091029 := by exact prefixLift 8091029
  have htrace : WordTrace (prefixWord ++ tailWord_8091029) baseStart_8091029 baseEnd_8091029 := by
    simpa [prefixWord, tailWord_8091029, baseEnd_8091029] using wordTrace_append hprefix tailTrace_8091029
  have hstable : (prefixWord ++ tailWord_8091029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091029).length < 2 ^ (prefixWord ++ tailWord_8091029).sum := by decide
  have hdescent : baseEnd_8091029 < baseStart_8091029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091075 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 7]
def baseStart_8091075 : Nat := 118140960795 + 8091075 * 2 ^ 59
def prefixEnd_8091075 : Nat := 4983230072969 + 3 ^ 40 * 8091075 * 2
def baseEnd_8091075 : Nat := 4154610486577036365552329

theorem tailTrace_8091075 : CollatzResearch.WordTrace tailWord_8091075 prefixEnd_8091075 4154610486577036365552329 := by
  unfold tailWord_8091075
  simp only [CollatzResearch.WordTrace]
  refine ⟨295105749162424595440762679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196737166108283063627175119 295105749162424595440762679)
  ·
    refine ⟨442658623743636893161144019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295105749162424595440762679 442658623743636893161144019)
    ·
      refine ⟨663987935615455339741716029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442658623743636893161144019 663987935615455339741716029)
      ·
        refine ⟨248995475855795752403143511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663987935615455339741716029 248995475855795752403143511)
        ·
          refine ⟨373493213783693628604715267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248995475855795752403143511 373493213783693628604715267)
          ·
            refine ⟨560239820675540442907072901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373493213783693628604715267 560239820675540442907072901)
            ·
              refine ⟨105044966376663833045076169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 560239820675540442907072901 105044966376663833045076169)
              ·
                refine ⟨78783724782497874783807127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105044966376663833045076169 78783724782497874783807127)
                ·
                  refine ⟨118175587173746812175710691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78783724782497874783807127 118175587173746812175710691)
                  ·
                    refine ⟨177263380760620218263566037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118175587173746812175710691 177263380760620218263566037)
                    ·
                      refine ⟨4154610486577036365552329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177263380760620218263566037 4154610486577036365552329)
                      ·
                        rfl

theorem cell23_8091075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_8091075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091075 prefixEnd_8091075 := by exact prefixLift 8091075
  have htrace : WordTrace (prefixWord ++ tailWord_8091075) baseStart_8091075 baseEnd_8091075 := by
    simpa [prefixWord, tailWord_8091075, baseEnd_8091075] using wordTrace_append hprefix tailTrace_8091075
  have hstable : (prefixWord ++ tailWord_8091075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091075).length < 2 ^ (prefixWord ++ tailWord_8091075).sum := by decide
  have hdescent : baseEnd_8091075 < baseStart_8091075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091082 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_8091082 : Nat := 118140960795 + 8091082 * 2 ^ 59
def prefixEnd_8091082 : Nat := 4983230072969 + 3 ^ 40 * 8091082 * 2
def baseEnd_8091082 : Nat := 1384871360313872612721599

theorem tailTrace_8091082 : CollatzResearch.WordTrace tailWord_8091082 prefixEnd_8091082 1384871360313872612721599 := by
  unfold tailWord_8091082
  simp only [CollatzResearch.WordTrace]
  refine ⟨73776501118349808909066875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196737336315599490424178333 73776501118349808909066875)
  ·
    refine ⟨110664751677524713363600313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73776501118349808909066875 110664751677524713363600313)
    ·
      refine ⟨82998563758143535022700235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110664751677524713363600313 82998563758143535022700235)
      ·
        refine ⟨124497845637215302534050353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82998563758143535022700235 124497845637215302534050353)
        ·
          refine ⟨93373384227911476900537765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124497845637215302534050353 93373384227911476900537765)
          ·
            refine ⟨17507509542733401918850831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93373384227911476900537765 17507509542733401918850831)
            ·
              refine ⟨26261264314100102878276247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17507509542733401918850831 26261264314100102878276247)
              ·
                refine ⟨39391896471150154317414371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26261264314100102878276247 39391896471150154317414371)
                ·
                  refine ⟨59087844706725231476121557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39391896471150154317414371 59087844706725231476121557)
                  ·
                    refine ⟨1384871360313872612721599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59087844706725231476121557 1384871360313872612721599)
                    ·
                      rfl

theorem cell23_8091082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_8091082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091082 prefixEnd_8091082 := by exact prefixLift 8091082
  have htrace : WordTrace (prefixWord ++ tailWord_8091082) baseStart_8091082 baseEnd_8091082 := by
    simpa [prefixWord, tailWord_8091082, baseEnd_8091082] using wordTrace_append hprefix tailTrace_8091082
  have hstable : (prefixWord ++ tailWord_8091082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091082).length < 2 ^ (prefixWord ++ tailWord_8091082).sum := by decide
  have hdescent : baseEnd_8091082 < baseStart_8091082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091095 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 1, 10]
def baseStart_8091095 : Nat := 118140960795 + 8091095 * 2 ^ 59
def prefixEnd_8091095 : Nat := 4983230072969 + 3 ^ 40 * 8091095 * 2
def baseEnd_8091095 : Nat := 1384873585396708762434079

theorem tailTrace_8091095 : CollatzResearch.WordTrace tailWord_8091095 prefixEnd_8091095 1384873585396708762434079 := by
  unfold tailWord_8091095
  simp only [CollatzResearch.WordTrace]
  refine ⟨295106478622352138856490739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196737652414901425904327159 295106478622352138856490739)
  ·
    refine ⟨442659717933528208284736109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295106478622352138856490739 442659717933528208284736109)
    ·
      refine ⟨165997394225073078106776041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442659717933528208284736109 165997394225073078106776041)
      ·
        refine ⟨124498045668804808580082031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165997394225073078106776041 124498045668804808580082031)
        ·
          refine ⟨186747068503207212870123047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124498045668804808580082031 186747068503207212870123047)
          ·
            refine ⟨280120602754810819305184571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186747068503207212870123047 280120602754810819305184571)
            ·
              refine ⟨420180904132216228957776857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280120602754810819305184571 420180904132216228957776857)
              ·
                refine ⟨315135678099162171718332643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420180904132216228957776857 315135678099162171718332643)
                ·
                  refine ⟨472703517148743257577498965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315135678099162171718332643 472703517148743257577498965)
                  ·
                    refine ⟨1384873585396708762434079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 472703517148743257577498965 1384873585396708762434079)
                    ·
                      rfl

theorem cell23_8091095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_8091095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091095 prefixEnd_8091095 := by exact prefixLift 8091095
  have htrace : WordTrace (prefixWord ++ tailWord_8091095) baseStart_8091095 baseEnd_8091095 := by
    simpa [prefixWord, tailWord_8091095, baseEnd_8091095] using wordTrace_append hprefix tailTrace_8091095
  have hstable : (prefixWord ++ tailWord_8091095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091095).length < 2 ^ (prefixWord ++ tailWord_8091095).sum := by decide
  have hdescent : baseEnd_8091095 < baseStart_8091095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091119 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 2, 4, 2]
def baseStart_8091119 : Nat := 118140960795 + 8091119 * 2 ^ 59
def prefixEnd_8091119 : Nat := 4983230072969 + 3 ^ 40 * 8091119 * 2
def baseEnd_8091119 : Nat := 4154633079725834193402127

theorem tailTrace_8091119 : CollatzResearch.WordTrace tailWord_8091119 prefixEnd_8091119 4154633079725834193402127 := by
  unfold tailWord_8091119
  simp only [CollatzResearch.WordTrace]
  refine ⟨295107353974265190955364411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196738235982843460636909607 295107353974265190955364411)
  ·
    refine ⟨442661030961397786433046617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295107353974265190955364411 442661030961397786433046617)
    ·
      refine ⟨331995773221048339824784963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442661030961397786433046617 331995773221048339824784963)
      ·
        refine ⟨497993659831572509737177445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331995773221048339824784963 497993659831572509737177445)
        ·
          refine ⟨93373811218419845575720771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 497993659831572509737177445 93373811218419845575720771)
          ·
            refine ⟨140060716827629768363581157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93373811218419845575720771 140060716827629768363581157)
            ·
              refine ⟨26261384405180581568171467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140060716827629768363581157 26261384405180581568171467)
              ·
                refine ⟨39392076607770872352257201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26261384405180581568171467 39392076607770872352257201)
                ·
                  refine ⟨29544057455828154264192901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39392076607770872352257201 29544057455828154264192901)
                  ·
                    refine ⟨5539510772967778924536169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29544057455828154264192901 5539510772967778924536169)
                    ·
                      refine ⟨4154633079725834193402127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539510772967778924536169 4154633079725834193402127)
                      ·
                        rfl

theorem cell23_8091119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 4, 2].length) (baseStart_8091119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091119 prefixEnd_8091119 := by exact prefixLift 8091119
  have htrace : WordTrace (prefixWord ++ tailWord_8091119) baseStart_8091119 baseEnd_8091119 := by
    simpa [prefixWord, tailWord_8091119, baseEnd_8091119] using wordTrace_append hprefix tailTrace_8091119
  have hstable : (prefixWord ++ tailWord_8091119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091119).length < 2 ^ (prefixWord ++ tailWord_8091119).sum := by decide
  have hdescent : baseEnd_8091119 < baseStart_8091119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091176 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 6]
def baseStart_8091176 : Nat := 118140960795 + 8091176 * 2 ^ 59
def prefixEnd_8091176 : Nat := 4983230072969 + 3 ^ 40 * 8091176 * 2
def baseEnd_8091176 : Nat := 461629149791460052265485

theorem tailTrace_8091176 : CollatzResearch.WordTrace tailWord_8091176 prefixEnd_8091176 461629149791460052265485 := by
  unfold tailWord_8091176
  simp only [CollatzResearch.WordTrace]
  refine ⟨147554716467529344845094691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196739621956705793126792921 147554716467529344845094691)
  ·
    refine ⟨221332074701294017267642037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147554716467529344845094691 221332074701294017267642037)
    ·
      refine ⟨20749882003246314118841441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221332074701294017267642037 20749882003246314118841441)
      ·
        refine ⟨15562411502434735589131081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20749882003246314118841441 15562411502434735589131081)
        ·
          refine ⟨11671808626826051691848311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15562411502434735589131081 11671808626826051691848311)
          ·
            refine ⟨17507712940239077537772467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11671808626826051691848311 17507712940239077537772467)
            ·
              refine ⟨26261569410358616306658701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17507712940239077537772467 26261569410358616306658701)
              ·
                refine ⟨9848088528884481114997013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26261569410358616306658701 9848088528884481114997013)
                ·
                  refine ⟨461629149791460052265485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9848088528884481114997013 461629149791460052265485)
                  ·
                    rfl

theorem cell23_8091176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 6].length) (baseStart_8091176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091176 prefixEnd_8091176 := by exact prefixLift 8091176
  have htrace : WordTrace (prefixWord ++ tailWord_8091176) baseStart_8091176 baseEnd_8091176 := by
    simpa [prefixWord, tailWord_8091176, baseEnd_8091176] using wordTrace_append hprefix tailTrace_8091176
  have hstable : (prefixWord ++ tailWord_8091176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091176).length < 2 ^ (prefixWord ++ tailWord_8091176).sum := by decide
  have hdescent : baseEnd_8091176 < baseStart_8091176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091189 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_8091189 : Nat := 118140960795 + 8091189 * 2 ^ 59
def prefixEnd_8091189 : Nat := 4983230072969 + 3 ^ 40 * 8091189 * 2
def baseEnd_8091189 : Nat := 1384889674457216306508935

theorem tailTrace_8091189 : CollatzResearch.WordTrace tailWord_8091189 prefixEnd_8091189 1384889674457216306508935 := by
  unfold tailWord_8091189
  simp only [CollatzResearch.WordTrace]
  refine ⟨295109907084011592910412621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196739938056007728606941747 295109907084011592910412621)
  ·
    refine ⟨110666215156504347341404733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295109907084011592910412621 110666215156504347341404733)
    ·
      refine ⟨41499830683689130253026775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110666215156504347341404733 41499830683689130253026775)
      ·
        refine ⟨62249746025533695379540163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41499830683689130253026775 62249746025533695379540163)
        ·
          refine ⟨93374619038300543069310245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62249746025533695379540163 93374619038300543069310245)
          ·
            refine ⟨17507741069681351825495671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93374619038300543069310245 17507741069681351825495671)
            ·
              refine ⟨26261611604522027738243507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17507741069681351825495671 26261611604522027738243507)
              ·
                refine ⟨39392417406783041607365261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26261611604522027738243507 39392417406783041607365261)
                ·
                  refine ⟨14772156527543640602761973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39392417406783041607365261 14772156527543640602761973)
                  ·
                    refine ⟨1384889674457216306508935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14772156527543640602761973 1384889674457216306508935)
                    ·
                      rfl

theorem cell23_8091189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_8091189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091189 prefixEnd_8091189 := by exact prefixLift 8091189
  have htrace : WordTrace (prefixWord ++ tailWord_8091189) baseStart_8091189 baseEnd_8091189 := by
    simpa [prefixWord, tailWord_8091189, baseEnd_8091189] using wordTrace_append hprefix tailTrace_8091189
  have hstable : (prefixWord ++ tailWord_8091189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091189).length < 2 ^ (prefixWord ++ tailWord_8091189).sum := by decide
  have hdescent : baseEnd_8091189 < baseStart_8091189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091209 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 4]
def baseStart_8091209 : Nat := 118140960795 + 8091209 * 2 ^ 59
def prefixEnd_8091209 : Nat := 4983230072969 + 3 ^ 40 * 8091209 * 2
def baseEnd_8091209 : Nat := 4154679292984738841276713

theorem tailTrace_8091209 : CollatzResearch.WordTrace tailWord_8091209 prefixEnd_8091209 4154679292984738841276713 := by
  unfold tailWord_8091209
  simp only [CollatzResearch.WordTrace]
  refine ⟨295110636543939136326140681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196740424362626090884093787 295110636543939136326140681)
  ·
    refine ⟨221332977407954352244605511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295110636543939136326140681 221332977407954352244605511)
    ·
      refine ⟨331999466111931528366908267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221332977407954352244605511 331999466111931528366908267)
      ·
        refine ⟨497999199167897292550362401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331999466111931528366908267 497999199167897292550362401)
        ·
          refine ⟨373499399375922969412771801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497999199167897292550362401 373499399375922969412771801)
          ·
            refine ⟨280124549531942227059578851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373499399375922969412771801 280124549531942227059578851)
            ·
              refine ⟨420186824297913340589368277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280124549531942227059578851 420186824297913340589368277)
              ·
                refine ⟨9848128694482343920063319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 420186824297913340589368277 9848128694482343920063319)
                ·
                  refine ⟨14772193041723515880094979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9848128694482343920063319 14772193041723515880094979)
                  ·
                    refine ⟨22158289562585273820142469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14772193041723515880094979 22158289562585273820142469)
                    ·
                      refine ⟨4154679292984738841276713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22158289562585273820142469 4154679292984738841276713)
                      ·
                        rfl

theorem cell23_8091209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 4].length) (baseStart_8091209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091209 prefixEnd_8091209 := by exact prefixLift 8091209
  have htrace : WordTrace (prefixWord ++ tailWord_8091209) baseStart_8091209 baseEnd_8091209 := by
    simpa [prefixWord, tailWord_8091209, baseEnd_8091209] using wordTrace_append hprefix tailTrace_8091209
  have hstable : (prefixWord ++ tailWord_8091209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091209).length < 2 ^ (prefixWord ++ tailWord_8091209).sum := by decide
  have hdescent : baseEnd_8091209 < baseStart_8091209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091226 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2]
def baseStart_8091226 : Nat := 118140960795 + 8091226 * 2 ^ 59
def prefixEnd_8091226 : Nat := 4983230072969 + 3 ^ 40 * 8091226 * 2
def baseEnd_8091226 : Nat := 4154688022155865274764135

theorem tailTrace_8091226 : CollatzResearch.WordTrace tailWord_8091226 prefixEnd_8091226 4154688022155865274764135 := by
  unfold tailWord_8091226
  simp only [CollatzResearch.WordTrace]
  refine ⟨73777814146219387057377383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196740837723251698819673021 73777814146219387057377383)
  ·
    refine ⟨110666721219329080586066075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73777814146219387057377383 110666721219329080586066075)
    ·
      refine ⟨166000081828993620879099113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110666721219329080586066075 166000081828993620879099113)
      ·
        refine ⟨124500061371745215659324335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166000081828993620879099113 124500061371745215659324335)
        ·
          refine ⟨186750092057617823488986503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124500061371745215659324335 186750092057617823488986503)
          ·
            refine ⟨280125138086426735233479755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186750092057617823488986503 280125138086426735233479755)
            ·
              refine ⟨420187707129640102850219633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280125138086426735233479755 420187707129640102850219633)
              ·
                refine ⟨315140780347230077137664725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420187707129640102850219633 315140780347230077137664725)
                ·
                  refine ⟨7386112039388204932914017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 315140780347230077137664725 7386112039388204932914017)
                  ·
                    refine ⟨5539584029541153699685513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7386112039388204932914017 5539584029541153699685513)
                    ·
                      refine ⟨4154688022155865274764135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539584029541153699685513 4154688022155865274764135)
                      ·
                        rfl

theorem cell23_8091226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_8091226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091226 prefixEnd_8091226 := by exact prefixLift 8091226
  have htrace : WordTrace (prefixWord ++ tailWord_8091226) baseStart_8091226 baseEnd_8091226 := by
    simpa [prefixWord, tailWord_8091226, baseEnd_8091226] using wordTrace_append hprefix tailTrace_8091226
  have hstable : (prefixWord ++ tailWord_8091226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091226).length < 2 ^ (prefixWord ++ tailWord_8091226).sum := by decide
  have hdescent : baseEnd_8091226 < baseStart_8091226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091236 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_8091236 : Nat := 118140960795 + 8091236 * 2 ^ 59
def prefixEnd_8091236 : Nat := 4983230072969 + 3 ^ 40 * 8091236 * 2
def baseEnd_8091236 : Nat := 1384897718987470078546363

theorem tailTrace_8091236 : CollatzResearch.WordTrace tailWord_8091236 prefixEnd_8091236 1384897718987470078546363 := by
  unfold tailWord_8091236
  simp only [CollatzResearch.WordTrace]
  refine ⟨147555810657420659968686781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196741080876560879958249041 147555810657420659968686781)
  ·
    refine ⟨55333428996532747488257543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147555810657420659968686781 55333428996532747488257543)
    ·
      refine ⟨83000143494799121232386315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55333428996532747488257543 83000143494799121232386315)
      ·
        refine ⟨124500215242198681848579473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83000143494799121232386315 124500215242198681848579473)
        ·
          refine ⟨93375161431649011386434605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124500215242198681848579473 93375161431649011386434605)
          ·
            refine ⟨35015685536868379269912977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93375161431649011386434605 35015685536868379269912977)
            ·
              refine ⟨26261764152651284452434733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35015685536868379269912977 26261764152651284452434733)
              ·
                refine ⟨9848161557244231669663025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26261764152651284452434733 9848161557244231669663025)
                ·
                  refine ⟨7386121167933173752247269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9848161557244231669663025 7386121167933173752247269)
                  ·
                    refine ⟨1384897718987470078546363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7386121167933173752247269 1384897718987470078546363)
                    ·
                      rfl

theorem cell23_8091236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_8091236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091236 prefixEnd_8091236 := by exact prefixLift 8091236
  have htrace : WordTrace (prefixWord ++ tailWord_8091236) baseStart_8091236 baseEnd_8091236 := by
    simpa [prefixWord, tailWord_8091236, baseEnd_8091236] using wordTrace_append hprefix tailTrace_8091236
  have hstable : (prefixWord ++ tailWord_8091236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091236).length < 2 ^ (prefixWord ++ tailWord_8091236).sum := by decide
  have hdescent : baseEnd_8091236 < baseStart_8091236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091239 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_8091239 : Nat := 118140960795 + 8091239 * 2 ^ 59
def prefixEnd_8091239 : Nat := 4983230072969 + 3 ^ 40 * 8091239 * 2
def baseEnd_8091239 : Nat := 4154694697404373723901575

theorem tailTrace_8091239 : CollatzResearch.WordTrace tailWord_8091239 prefixEnd_8091239 4154694697404373723901575 := by
  unfold tailWord_8091239
  simp only [CollatzResearch.WordTrace]
  refine ⟨295111730733830451449732771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196741153822553634299821847 295111730733830451449732771)
  ·
    refine ⟨442667596100745677174599157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295111730733830451449732771 442667596100745677174599157)
    ·
      refine ⟨41500087134444907235118671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 442667596100745677174599157 41500087134444907235118671)
      ·
        refine ⟨62250130701667360852678007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41500087134444907235118671 62250130701667360852678007)
        ·
          refine ⟨93375196052501041279017011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62250130701667360852678007 93375196052501041279017011)
          ·
            refine ⟨140062794078751561918525517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93375196052501041279017011 140062794078751561918525517)
            ·
              refine ⟨52523547779531835719447069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140062794078751561918525517 52523547779531835719447069)
              ·
                refine ⟨19696330417324438394792651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52523547779531835719447069 19696330417324438394792651)
                ·
                  refine ⟨29544495625986657592188977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19696330417324438394792651 29544495625986657592188977)
                  ·
                    refine ⟨22158371719489993194141733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29544495625986657592188977 22158371719489993194141733)
                    ·
                      refine ⟨4154694697404373723901575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22158371719489993194141733 4154694697404373723901575)
                      ·
                        rfl

theorem cell23_8091239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_8091239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091239 prefixEnd_8091239 := by exact prefixLift 8091239
  have htrace : WordTrace (prefixWord ++ tailWord_8091239) baseStart_8091239 baseEnd_8091239 := by
    simpa [prefixWord, tailWord_8091239, baseEnd_8091239] using wordTrace_append hprefix tailTrace_8091239
  have hstable : (prefixWord ++ tailWord_8091239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091239).length < 2 ^ (prefixWord ++ tailWord_8091239).sum := by decide
  have hdescent : baseEnd_8091239 < baseStart_8091239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091259 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 3]
def baseStart_8091259 : Nat := 118140960795 + 8091259 * 2 ^ 59
def prefixEnd_8091259 : Nat := 4983230072969 + 3 ^ 40 * 8091259 * 2
def baseEnd_8091259 : Nat := 4154704967017463645651483

theorem tailTrace_8091259 : CollatzResearch.WordTrace tailWord_8091259 prefixEnd_8091259 4154704967017463645651483 := by
  unfold tailWord_8091259
  simp only [CollatzResearch.WordTrace]
  refine ⟨295112460193757994865460831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196741640129171996576973887 295112460193757994865460831)
  ·
    refine ⟨442668690290636992298191247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295112460193757994865460831 442668690290636992298191247)
    ·
      refine ⟨664003035435955488447286871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442668690290636992298191247 664003035435955488447286871)
      ·
        refine ⟨996004553153933232670930307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664003035435955488447286871 996004553153933232670930307)
        ·
          refine ⟨1494006829730899849006395461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996004553153933232670930307 1494006829730899849006395461)
          ·
            refine ⟨280126280574543721688699149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1494006829730899849006395461 280126280574543721688699149)
            ·
              refine ⟨105047355215453895633262181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280126280574543721688699149 105047355215453895633262181)
              ·
                refine ⟨19696379102897605431236659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105047355215453895633262181 19696379102897605431236659)
                ·
                  refine ⟨29544568654346408146854989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19696379102897605431236659 29544568654346408146854989)
                  ·
                    refine ⟨11079213245379903055070621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29544568654346408146854989 11079213245379903055070621)
                    ·
                      refine ⟨4154704967017463645651483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11079213245379903055070621 4154704967017463645651483)
                      ·
                        rfl

theorem cell23_8091259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 3].length) (baseStart_8091259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091259 prefixEnd_8091259 := by exact prefixLift 8091259
  have htrace : WordTrace (prefixWord ++ tailWord_8091259) baseStart_8091259 baseEnd_8091259 := by
    simpa [prefixWord, tailWord_8091259, baseEnd_8091259] using wordTrace_append hprefix tailTrace_8091259
  have hstable : (prefixWord ++ tailWord_8091259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091259).length < 2 ^ (prefixWord ++ tailWord_8091259).sum := by decide
  have hdescent : baseEnd_8091259 < baseStart_8091259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091276 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 4, 1, 3]
def baseStart_8091276 : Nat := 118140960795 + 8091276 * 2 ^ 59
def prefixEnd_8091276 : Nat := 4983230072969 + 3 ^ 40 * 8091276 * 2
def baseEnd_8091276 : Nat := 4154713696188590079138905

theorem tailTrace_8091276 : CollatzResearch.WordTrace tailWord_8091276 prefixEnd_8091276 4154713696188590079138905 := by
  unfold tailWord_8091276
  simp only [CollatzResearch.WordTrace]
  refine ⟨147556540117348203384414841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196742053489797604512553121 147556540117348203384414841)
  ·
    refine ⟨110667405088011152538311131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147556540117348203384414841 110667405088011152538311131)
    ·
      refine ⟨166001107632016728807466697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110667405088011152538311131 166001107632016728807466697)
      ·
        refine ⟨124500830724012546605600023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166001107632016728807466697 124500830724012546605600023)
        ·
          refine ⟨186751246086018819908400035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124500830724012546605600023 186751246086018819908400035)
          ·
            refine ⟨280126869129028229862600053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186751246086018819908400035 280126869129028229862600053)
            ·
              refine ⟨26261893980846396549618755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280126869129028229862600053 26261893980846396549618755)
              ·
                refine ⟨39392840971269594824428133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26261893980846396549618755 39392840971269594824428133)
                ·
                  refine ⟨7386157682113049029580275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39392840971269594824428133 7386157682113049029580275)
                  ·
                    refine ⟨11079236523169573544370413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7386157682113049029580275 11079236523169573544370413)
                    ·
                      refine ⟨4154713696188590079138905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11079236523169573544370413 4154713696188590079138905)
                      ·
                        rfl

theorem cell23_8091276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_8091276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091276 prefixEnd_8091276 := by exact prefixLift 8091276
  have htrace : WordTrace (prefixWord ++ tailWord_8091276) baseStart_8091276 baseEnd_8091276 := by
    simpa [prefixWord, tailWord_8091276, baseEnd_8091276] using wordTrace_append hprefix tailTrace_8091276
  have hstable : (prefixWord ++ tailWord_8091276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091276).length < 2 ^ (prefixWord ++ tailWord_8091276).sum := by decide
  have hdescent : baseEnd_8091276 < baseStart_8091276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091319 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_8091319 : Nat := 118140960795 + 8091319 * 2 ^ 59
def prefixEnd_8091319 : Nat := 4983230072969 + 3 ^ 40 * 8091319 * 2
def baseEnd_8091319 : Nat := 4154735775856733410901207

theorem tailTrace_8091319 : CollatzResearch.WordTrace tailWord_8091319 prefixEnd_8091319 4154735775856733410901207 := by
  unfold tailWord_8091319
  simp only [CollatzResearch.WordTrace]
  refine ⟨295114648573540625112645011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196743099049027083408430007 295114648573540625112645011)
  ·
    refine ⟨442671972860310937668967517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295114648573540625112645011 442671972860310937668967517)
    ·
      refine ⟨166001989822616601625862819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442671972860310937668967517 166001989822616601625862819)
      ·
        refine ⟨249002984733924902438794229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166001989822616601625862819 249002984733924902438794229)
        ·
          refine ⟨23344029818805459603636959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249002984733924902438794229 23344029818805459603636959)
          ·
            refine ⟨35016044728208189405455439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23344029818805459603636959 35016044728208189405455439)
            ·
              refine ⟨52524067092312284108183159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35016044728208189405455439 52524067092312284108183159)
              ·
                refine ⟨78786100638468426162274739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52524067092312284108183159 78786100638468426162274739)
                ·
                  refine ⟨118179150957702639243412109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78786100638468426162274739 118179150957702639243412109)
                  ·
                    refine ⟨44317181609138489716279541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118179150957702639243412109 44317181609138489716279541)
                    ·
                      refine ⟨4154735775856733410901207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44317181609138489716279541 4154735775856733410901207)
                      ·
                        rfl

theorem cell23_8091319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_8091319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091319 prefixEnd_8091319 := by exact prefixLift 8091319
  have htrace : WordTrace (prefixWord ++ tailWord_8091319) baseStart_8091319 baseEnd_8091319 := by
    simpa [prefixWord, tailWord_8091319, baseEnd_8091319] using wordTrace_append hprefix tailTrace_8091319
  have hstable : (prefixWord ++ tailWord_8091319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091319).length < 2 ^ (prefixWord ++ tailWord_8091319).sum := by decide
  have hdescent : baseEnd_8091319 < baseStart_8091319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091379 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 5]
def baseStart_8091379 : Nat := 118140960795 + 8091379 * 2 ^ 59
def prefixEnd_8091379 : Nat := 4983230072969 + 3 ^ 40 * 8091379 * 2
def baseEnd_8091379 : Nat := 4154766584696003176150931

theorem tailTrace_8091379 : CollatzResearch.WordTrace tailWord_8091379 prefixEnd_8091379 4154766584696003176150931 := by
  unfold tailWord_8091379
  simp only [CollatzResearch.WordTrace]
  refine ⟨295116836953323255359829191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196744557968882170239886127 295116836953323255359829191)
  ·
    refine ⟨442675255429984883039743787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295116836953323255359829191 442675255429984883039743787)
    ·
      refine ⟨664012883144977324559615681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442675255429984883039743787 664012883144977324559615681)
      ·
        refine ⟨498009662358732993419711761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664012883144977324559615681 498009662358732993419711761)
        ·
          refine ⟨373507246769049745064783821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498009662358732993419711761 373507246769049745064783821)
          ·
            refine ⟨140065217538393654399293933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373507246769049745064783821 140065217538393654399293933)
            ·
              refine ⟨52524456576897620399735225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140065217538393654399293933 52524456576897620399735225)
              ·
                refine ⟨39393342432673215299801419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52524456576897620399735225 39393342432673215299801419)
                ·
                  refine ⟨59090013649009822949702129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39393342432673215299801419 59090013649009822949702129)
                  ·
                    refine ⟨44317510236757367212276597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59090013649009822949702129 44317510236757367212276597)
                    ·
                      refine ⟨4154766584696003176150931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44317510236757367212276597 4154766584696003176150931)
                      ·
                        rfl

theorem cell23_8091379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_8091379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091379 prefixEnd_8091379 := by exact prefixLift 8091379
  have htrace : WordTrace (prefixWord ++ tailWord_8091379) baseStart_8091379 baseEnd_8091379 := by
    simpa [prefixWord, tailWord_8091379, baseEnd_8091379] using wordTrace_append hprefix tailTrace_8091379
  have hstable : (prefixWord ++ tailWord_8091379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091379).length < 2 ^ (prefixWord ++ tailWord_8091379).sum := by decide
  have hdescent : baseEnd_8091379 < baseStart_8091379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091390 : List Nat := [4, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_8091390 : Nat := 118140960795 + 8091390 * 2 ^ 59
def prefixEnd_8091390 : Nat := 4983230072969 + 3 ^ 40 * 8091390 * 2
def baseEnd_8091390 : Nat := 461641359220355848123709

theorem tailTrace_8091390 : CollatzResearch.WordTrace tailWord_8091390 prefixEnd_8091390 461641359220355848123709 := by
  unfold tailWord_8091390
  simp only [CollatzResearch.WordTrace]
  refine ⟨36889654769535425529809953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196744825437522269492319749 36889654769535425529809953)
  ·
    refine ⟨27667241077151569147357465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36889654769535425529809953 27667241077151569147357465)
    ·
      refine ⟨20750430807863676860518099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27667241077151569147357465 20750430807863676860518099)
      ·
        refine ⟨31125646211795515290777149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20750430807863676860518099 31125646211795515290777149)
        ·
          refine ⟨11672117329423318234041431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31125646211795515290777149 11672117329423318234041431)
          ·
            refine ⟨17508175994134977351062147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672117329423318234041431 17508175994134977351062147)
            ·
              refine ⟨26262263991202466026593221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17508175994134977351062147 26262263991202466026593221)
              ·
                refine ⟨4924174498350462379986229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26262263991202466026593221 4924174498350462379986229)
                ·
                  refine ⟨461641359220355848123709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4924174498350462379986229 461641359220355848123709)
                  ·
                    rfl

theorem cell23_8091390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_8091390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091390 prefixEnd_8091390 := by exact prefixLift 8091390
  have htrace : WordTrace (prefixWord ++ tailWord_8091390) baseStart_8091390 baseEnd_8091390 := by
    simpa [prefixWord, tailWord_8091390, baseEnd_8091390] using wordTrace_append hprefix tailTrace_8091390
  have hstable : (prefixWord ++ tailWord_8091390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091390).length < 2 ^ (prefixWord ++ tailWord_8091390).sum := by decide
  have hdescent : baseEnd_8091390 < baseStart_8091390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091396 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_8091396 : Nat := 118140960795 + 8091396 * 2 ^ 59
def prefixEnd_8091396 : Nat := 4983230072969 + 3 ^ 40 * 8091396 * 2
def baseEnd_8091396 : Nat := 4154775313867129609638353

theorem tailTrace_8091396 : CollatzResearch.WordTrace tailWord_8091396 prefixEnd_8091396 4154775313867129609638353 := by
  unfold tailWord_8091396
  simp only [CollatzResearch.WordTrace]
  refine ⟨147558728497130833631599021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196744971329507778175465361 147558728497130833631599021)
  ·
    refine ⟨55334523186424062611849633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147558728497130833631599021 55334523186424062611849633)
    ·
      refine ⟨41500892389818046958887225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55334523186424062611849633 41500892389818046958887225)
      ·
        refine ⟨31125669292363535219165419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41500892389818046958887225 31125669292363535219165419)
        ·
          refine ⟨46688503938545302828748129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31125669292363535219165419 46688503938545302828748129)
          ·
            refine ⟨35016377953908977121561097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46688503938545302828748129 35016377953908977121561097)
            ·
              refine ⟨26262283465431732841170823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35016377953908977121561097 26262283465431732841170823)
              ·
                refine ⟨39393425198147599261756235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26262283465431732841170823 39393425198147599261756235)
                ·
                  refine ⟨59090137797221398892634353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39393425198147599261756235 59090137797221398892634353)
                  ·
                    refine ⟨44317603347916049169475765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59090137797221398892634353 44317603347916049169475765)
                    ·
                      refine ⟨4154775313867129609638353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44317603347916049169475765 4154775313867129609638353)
                      ·
                        rfl

theorem cell23_8091396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_8091396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091396 prefixEnd_8091396 := by exact prefixLift 8091396
  have htrace : WordTrace (prefixWord ++ tailWord_8091396) baseStart_8091396 baseEnd_8091396 := by
    simpa [prefixWord, tailWord_8091396, baseEnd_8091396] using wordTrace_append hprefix tailTrace_8091396
  have hstable : (prefixWord ++ tailWord_8091396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091396).length < 2 ^ (prefixWord ++ tailWord_8091396).sum := by decide
  have hdescent : baseEnd_8091396 < baseStart_8091396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091406 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_8091406 : Nat := 118140960795 + 8091406 * 2 ^ 59
def prefixEnd_8091406 : Nat := 4983230072969 + 3 ^ 40 * 8091406 * 2
def baseEnd_8091406 : Nat := 4154780448673674570513307

theorem tailTrace_8091406 : CollatzResearch.WordTrace tailWord_8091406 prefixEnd_8091406 4154780448673674570513307 := by
  unfold tailWord_8091406
  simp only [CollatzResearch.WordTrace]
  refine ⟨36889727715528179871382759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196745214482816959314041381 36889727715528179871382759)
  ·
    refine ⟨55334591573292269807074139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36889727715528179871382759 55334591573292269807074139)
    ·
      refine ⟨83001887359938404710611209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55334591573292269807074139 83001887359938404710611209)
      ·
        refine ⟨62251415519953803532958407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83001887359938404710611209 62251415519953803532958407)
        ·
          refine ⟨93377123279930705299437611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62251415519953803532958407 93377123279930705299437611)
          ·
            refine ⟨140065684919896057949156417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93377123279930705299437611 140065684919896057949156417)
            ·
              refine ⟨105049263689922043461867313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140065684919896057949156417 105049263689922043461867313)
              ·
                refine ⟨78786947767441532596400485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105049263689922043461867313 78786947767441532596400485)
                ·
                  refine ⟨14772552706395287361825091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78786947767441532596400485 14772552706395287361825091)
                  ·
                    refine ⟨22158829059592931042737637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14772552706395287361825091 22158829059592931042737637)
                    ·
                      refine ⟨4154780448673674570513307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22158829059592931042737637 4154780448673674570513307)
                      ·
                        rfl

theorem cell23_8091406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_8091406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091406 prefixEnd_8091406 := by exact prefixLift 8091406
  have htrace : WordTrace (prefixWord ++ tailWord_8091406) baseStart_8091406 baseEnd_8091406 := by
    simpa [prefixWord, tailWord_8091406, baseEnd_8091406] using wordTrace_append hprefix tailTrace_8091406
  have hstable : (prefixWord ++ tailWord_8091406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091406).length < 2 ^ (prefixWord ++ tailWord_8091406).sum := by decide
  have hdescent : baseEnd_8091406 < baseStart_8091406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091416 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 5, 4]
def baseStart_8091416 : Nat := 118140960795 + 8091416 * 2 ^ 59
def prefixEnd_8091416 : Nat := 4983230072969 + 3 ^ 40 * 8091416 * 2
def baseEnd_8091416 : Nat := 1384928527826739843796087

theorem tailTrace_8091416 : CollatzResearch.WordTrace tailWord_8091416 prefixEnd_8091416 1384928527826739843796087 := by
  unfold tailWord_8091416
  simp only [CollatzResearch.WordTrace]
  refine ⟨147559093227094605339463051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196745457636126140452617401 147559093227094605339463051)
  ·
    refine ⟨221338639840641908009194577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147559093227094605339463051 221338639840641908009194577)
    ·
      refine ⟨166003979880481431006895933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221338639840641908009194577 166003979880481431006895933)
      ·
        refine ⟨62251492455180536627585975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166003979880481431006895933 62251492455180536627585975)
        ·
          refine ⟨93377238682770804941378963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62251492455180536627585975 93377238682770804941378963)
          ·
            refine ⟨140065858024156207412068445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93377238682770804941378963 140065858024156207412068445)
            ·
              refine ⟨52524696759058577779525667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140065858024156207412068445 52524696759058577779525667)
              ·
                refine ⟨78787045138587866669288501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52524696759058577779525667 78787045138587866669288501)
                ·
                  refine ⟨7386285481742612500245797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78787045138587866669288501 7386285481742612500245797)
                  ·
                    refine ⟨1384928527826739843796087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7386285481742612500245797 1384928527826739843796087)
                    ·
                      rfl

theorem cell23_8091416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_8091416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091416 prefixEnd_8091416 := by exact prefixLift 8091416
  have htrace : WordTrace (prefixWord ++ tailWord_8091416) baseStart_8091416 baseEnd_8091416 := by
    simpa [prefixWord, tailWord_8091416, baseEnd_8091416] using wordTrace_append hprefix tailTrace_8091416
  have hstable : (prefixWord ++ tailWord_8091416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091416).length < 2 ^ (prefixWord ++ tailWord_8091416).sum := by decide
  have hdescent : baseEnd_8091416 < baseStart_8091416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091419 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 4]
def baseStart_8091419 : Nat := 118140960795 + 8091419 * 2 ^ 59
def prefixEnd_8091419 : Nat := 4983230072969 + 3 ^ 40 * 8091419 * 2
def baseEnd_8091419 : Nat := 4154787123922183019650747

theorem tailTrace_8091419 : CollatzResearch.WordTrace tailWord_8091419 prefixEnd_8091419 4154787123922183019650747 := by
  unfold tailWord_8091419
  simp only [CollatzResearch.WordTrace]
  refine ⟨295118295873178342191285311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196745530582118894794190207 295118295873178342191285311)
  ·
    refine ⟨442677443809767513286927967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295118295873178342191285311 442677443809767513286927967)
    ·
      refine ⟨664016165714651269930391951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442677443809767513286927967 664016165714651269930391951)
      ·
        refine ⟨996024248571976904895587927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664016165714651269930391951 996024248571976904895587927)
        ·
          refine ⟨1494036372857965357343381891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996024248571976904895587927 1494036372857965357343381891)
          ·
            refine ⟨2241054559286948036015072837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494036372857965357343381891 2241054559286948036015072837)
            ·
              refine ⟨420197729866302756752826157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2241054559286948036015072837 420197729866302756752826157)
              ·
                refine ⟨157574148699863533782309809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420197729866302756752826157 157574148699863533782309809)
                ·
                  refine ⟨118180611524897650336732357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157574148699863533782309809 118180611524897650336732357)
                  ·
                    refine ⟨22158864660918309438137317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118180611524897650336732357 22158864660918309438137317)
                    ·
                      refine ⟨4154787123922183019650747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22158864660918309438137317 4154787123922183019650747)
                      ·
                        rfl

theorem cell23_8091419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 4].length) (baseStart_8091419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091419 prefixEnd_8091419 := by exact prefixLift 8091419
  have htrace : WordTrace (prefixWord ++ tailWord_8091419) baseStart_8091419 baseEnd_8091419 := by
    simpa [prefixWord, tailWord_8091419, baseEnd_8091419] using wordTrace_append hprefix tailTrace_8091419
  have hstable : (prefixWord ++ tailWord_8091419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091419).length < 2 ^ (prefixWord ++ tailWord_8091419).sum := by decide
  have hdescent : baseEnd_8091419 < baseStart_8091419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091450 : List Nat := [3, 1, 1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_8091450 : Nat := 118140960795 + 8091450 * 2 ^ 59
def prefixEnd_8091450 : Nat := 4983230072969 + 3 ^ 40 * 8091450 * 2
def baseEnd_8091450 : Nat := 1384934347274157466121035

theorem tailTrace_8091450 : CollatzResearch.WordTrace tailWord_8091450 prefixEnd_8091450 1384934347274157466121035 := by
  unfold tailWord_8091450
  simp only [CollatzResearch.WordTrace]
  refine ⟨73779856634016508621415951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196746284357377356323775869 73779856634016508621415951)
  ·
    refine ⟨110669784951024762932123927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73779856634016508621415951 110669784951024762932123927)
    ·
      refine ⟨166004677426537144398185891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110669784951024762932123927 166004677426537144398185891)
      ·
        refine ⟨249007016139805716597278837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166004677426537144398185891 249007016139805716597278837)
        ·
          refine ⟨23344407763106785930994891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249007016139805716597278837 23344407763106785930994891)
          ·
            refine ⟨35016611644660178896492337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23344407763106785930994891 35016611644660178896492337)
            ·
              refine ⟨26262458733495134172369253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35016611644660178896492337 26262458733495134172369253)
              ·
                refine ⟨4924211012530337657319235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26262458733495134172369253 4924211012530337657319235)
                ·
                  refine ⟨7386316518795506485978853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924211012530337657319235 7386316518795506485978853)
                  ·
                    refine ⟨1384934347274157466121035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7386316518795506485978853 1384934347274157466121035)
                    ·
                      rfl

theorem cell23_8091450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_8091450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091450 prefixEnd_8091450 := by exact prefixLift 8091450
  have htrace : WordTrace (prefixWord ++ tailWord_8091450) baseStart_8091450 baseEnd_8091450 := by
    simpa [prefixWord, tailWord_8091450, baseEnd_8091450] using wordTrace_append hprefix tailTrace_8091450
  have hstable : (prefixWord ++ tailWord_8091450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091450).length < 2 ^ (prefixWord ++ tailWord_8091450).sum := by decide
  have hdescent : baseEnd_8091450 < baseStart_8091450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091484 : List Nat := [2, 2, 4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_8091484 : Nat := 118140960795 + 8091484 * 2 ^ 59
def prefixEnd_8091484 : Nat := 4983230072969 + 3 ^ 40 * 8091484 * 2
def baseEnd_8091484 : Nat := 1384940166721575088445983

theorem tailTrace_8091484 : CollatzResearch.WordTrace tailWord_8091484 prefixEnd_8091484 1384940166721575088445983 := by
  unfold tailWord_8091484
  simp only [CollatzResearch.WordTrace]
  refine ⟨147560333308971429146200753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196747111078628572194934337 147560333308971429146200753)
  ·
    refine ⟨110670249981728571859650565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147560333308971429146200753 110670249981728571859650565)
    ·
      refine ⟨20750671871574107223684481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110670249981728571859650565 20750671871574107223684481)
      ·
        refine ⟨15563003903680580417763361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20750671871574107223684481 15563003903680580417763361)
        ·
          refine ⟨11672252927760435313322521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15563003903680580417763361 11672252927760435313322521)
          ·
            refine ⟨8754189695820326484991891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11672252927760435313322521 8754189695820326484991891)
            ·
              refine ⟨13131284543730489727487837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8754189695820326484991891 13131284543730489727487837)
              ·
                refine ⟨4924231703898933647807939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13131284543730489727487837 4924231703898933647807939)
                ·
                  refine ⟨7386347555848400471711909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924231703898933647807939 7386347555848400471711909)
                  ·
                    refine ⟨1384940166721575088445983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7386347555848400471711909 1384940166721575088445983)
                    ·
                      rfl

theorem cell23_8091484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_8091484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091484 prefixEnd_8091484 := by exact prefixLift 8091484
  have htrace : WordTrace (prefixWord ++ tailWord_8091484) baseStart_8091484 baseEnd_8091484 := by
    simpa [prefixWord, tailWord_8091484, baseEnd_8091484] using wordTrace_append hprefix tailTrace_8091484
  have hstable : (prefixWord ++ tailWord_8091484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091484).length < 2 ^ (prefixWord ++ tailWord_8091484).sum := by decide
  have hdescent : baseEnd_8091484 < baseStart_8091484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091500 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 2, 3, 2]
def baseStart_8091500 : Nat := 118140960795 + 8091500 * 2 ^ 59
def prefixEnd_8091500 : Nat := 4983230072969 + 3 ^ 40 * 8091500 * 2
def baseEnd_8091500 : Nat := 4154828715855197202737875

theorem tailTrace_8091500 : CollatzResearch.WordTrace tailWord_8091500 prefixEnd_8091500 4154828715855197202737875 := by
  unfold tailWord_8091500
  simp only [CollatzResearch.WordTrace]
  refine ⟨147560625092942446512491977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196747500123923262016655969 147560625092942446512491977)
  ·
    refine ⟨110670468819706834884368983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147560625092942446512491977 110670468819706834884368983)
    ·
      refine ⟨166005703229560252326553475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110670468819706834884368983 166005703229560252326553475)
      ·
        refine ⟨249008554844340378489830213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166005703229560252326553475 249008554844340378489830213)
        ·
          refine ⟨46689104033313820966843165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249008554844340378489830213 46689104033313820966843165)
          ·
            refine ⟨17508414012492682862566187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46689104033313820966843165 17508414012492682862566187)
            ·
              refine ⟨26262621018739024293849281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17508414012492682862566187 26262621018739024293849281)
              ·
                refine ⟨19696965764054268220386961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26262621018739024293849281 19696965764054268220386961)
                ·
                  refine ⟨14772724323040701165290221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19696965764054268220386961 14772724323040701165290221)
                  ·
                    refine ⟨5539771621140262936983833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14772724323040701165290221 5539771621140262936983833)
                    ·
                      refine ⟨4154828715855197202737875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539771621140262936983833 4154828715855197202737875)
                      ·
                        rfl

theorem cell23_8091500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_8091500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091500 prefixEnd_8091500 := by exact prefixLift 8091500
  have htrace : WordTrace (prefixWord ++ tailWord_8091500) baseStart_8091500 baseEnd_8091500 := by
    simpa [prefixWord, tailWord_8091500, baseEnd_8091500] using wordTrace_append hprefix tailTrace_8091500
  have hstable : (prefixWord ++ tailWord_8091500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091500).length < 2 ^ (prefixWord ++ tailWord_8091500).sum := by decide
  have hdescent : baseEnd_8091500 < baseStart_8091500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091516 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_8091516 : Nat := 118140960795 + 8091516 * 2 ^ 59
def prefixEnd_8091516 : Nat := 4983230072969 + 3 ^ 40 * 8091516 * 2
def baseEnd_8091516 : Nat := 4154836931545669140137801

theorem tailTrace_8091516 : CollatzResearch.WordTrace tailWord_8091516 prefixEnd_8091516 4154836931545669140137801 := by
  unfold tailWord_8091516
  simp only [CollatzResearch.WordTrace]
  refine ⟨147560916876913463878783201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196747889169217951838377601 147560916876913463878783201)
  ·
    refine ⟨110670687657685097909087401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147560916876913463878783201 110670687657685097909087401)
    ·
      refine ⟨83003015743263823431815551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110670687657685097909087401 83003015743263823431815551)
      ·
        refine ⟨124504523614895735147723327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83003015743263823431815551 124504523614895735147723327)
        ·
          refine ⟨186756785422343602721584991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124504523614895735147723327 186756785422343602721584991)
          ·
            refine ⟨280135178133515404082377487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186756785422343602721584991 280135178133515404082377487)
            ·
              refine ⟨420202767200273106123566231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280135178133515404082377487 420202767200273106123566231)
              ·
                refine ⟨630304150800409659185349347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420202767200273106123566231 630304150800409659185349347)
                ·
                  refine ⟨945456226200614488778024021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630304150800409659185349347 945456226200614488778024021)
                  ·
                    refine ⟨11079565150788451040367469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 945456226200614488778024021 11079565150788451040367469)
                    ·
                      refine ⟨4154836931545669140137801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11079565150788451040367469 4154836931545669140137801)
                      ·
                        rfl

theorem cell23_8091516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_8091516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091516 prefixEnd_8091516 := by exact prefixLift 8091516
  have htrace : WordTrace (prefixWord ++ tailWord_8091516) baseStart_8091516 baseEnd_8091516 := by
    simpa [prefixWord, tailWord_8091516, baseEnd_8091516] using wordTrace_append hprefix tailTrace_8091516
  have hstable : (prefixWord ++ tailWord_8091516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091516).length < 2 ^ (prefixWord ++ tailWord_8091516).sum := by decide
  have hdescent : baseEnd_8091516 < baseStart_8091516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091527 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 1, 5]
def baseStart_8091527 : Nat := 118140960795 + 8091527 * 2 ^ 59
def prefixEnd_8091527 : Nat := 4983230072969 + 3 ^ 40 * 8091527 * 2
def baseEnd_8091527 : Nat := 1384947526610956199033417

theorem tailTrace_8091527 : CollatzResearch.WordTrace tailWord_8091527 prefixEnd_8091527 1384947526610956199033417 := by
  unfold tailWord_8091527
  simp only [CollatzResearch.WordTrace]
  refine ⟨295122234956787076636216835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196748156637858051090811223 295122234956787076636216835)
  ·
    refine ⟨442683352435180614954325253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295122234956787076636216835 442683352435180614954325253)
    ·
      refine ⟨83003128581596365303935985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442683352435180614954325253 83003128581596365303935985)
      ·
        refine ⟨62252346436197273977951989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83003128581596365303935985 62252346436197273977951989)
        ·
          refine ⟨5836157478393494435432999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62252346436197273977951989 5836157478393494435432999)
          ·
            refine ⟨8754236217590241653149499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836157478393494435432999 8754236217590241653149499)
            ·
              refine ⟨13131354326385362479724249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8754236217590241653149499 13131354326385362479724249)
              ·
                refine ⟨9848515744789021859793187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13131354326385362479724249 9848515744789021859793187)
                ·
                  refine ⟨14772773617183532789689781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9848515744789021859793187 14772773617183532789689781)
                  ·
                    refine ⟨1384947526610956199033417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14772773617183532789689781 1384947526610956199033417)
                    ·
                      rfl

theorem cell23_8091527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_8091527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091527 prefixEnd_8091527 := by exact prefixLift 8091527
  have htrace : WordTrace (prefixWord ++ tailWord_8091527) baseStart_8091527 baseEnd_8091527 := by
    simpa [prefixWord, tailWord_8091527, baseEnd_8091527] using wordTrace_append hprefix tailTrace_8091527
  have hstable : (prefixWord ++ tailWord_8091527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091527).length < 2 ^ (prefixWord ++ tailWord_8091527).sum := by decide
  have hdescent : baseEnd_8091527 < baseStart_8091527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091530 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_8091530 : Nat := 118140960795 + 8091530 * 2 ^ 59
def prefixEnd_8091530 : Nat := 4983230072969 + 3 ^ 40 * 8091530 * 2
def baseEnd_8091530 : Nat := 4154844120274832085362737

theorem tailTrace_8091530 : CollatzResearch.WordTrace tailWord_8091530 prefixEnd_8091530 4154844120274832085362737 := by
  unfold tailWord_8091530
  simp only [CollatzResearch.WordTrace]
  refine ⟨73780586093944052037144011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196748229583850805432384029 73780586093944052037144011)
  ·
    refine ⟨110670879140916078055716017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73780586093944052037144011 110670879140916078055716017)
    ·
      refine ⟨83003159355687058541787013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110670879140916078055716017 83003159355687058541787013)
      ·
        refine ⟨15563092379191323476585065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83003159355687058541787013 15563092379191323476585065)
        ·
          refine ⟨11672319284393492607438799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15563092379191323476585065 11672319284393492607438799)
          ·
            refine ⟨17508478926590238911158199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672319284393492607438799 17508478926590238911158199)
            ·
              refine ⟨26262718389885358366737299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17508478926590238911158199 26262718389885358366737299)
              ·
                refine ⟨39394077584828037550105949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26262718389885358366737299 39394077584828037550105949)
                ·
                  refine ⟨14772779094310514081289731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39394077584828037550105949 14772779094310514081289731)
                  ·
                    refine ⟨22159168641465771121934597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14772779094310514081289731 22159168641465771121934597)
                    ·
                      refine ⟨4154844120274832085362737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22159168641465771121934597 4154844120274832085362737)
                      ·
                        rfl

theorem cell23_8091530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_8091530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091530 prefixEnd_8091530 := by exact prefixLift 8091530
  have htrace : WordTrace (prefixWord ++ tailWord_8091530) baseStart_8091530 baseEnd_8091530 := by
    simpa [prefixWord, tailWord_8091530, baseEnd_8091530] using wordTrace_append hprefix tailTrace_8091530
  have hstable : (prefixWord ++ tailWord_8091530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091530).length < 2 ^ (prefixWord ++ tailWord_8091530).sum := by decide
  have hdescent : baseEnd_8091530 < baseStart_8091530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091534 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_8091534 : Nat := 118140960795 + 8091534 * 2 ^ 59
def prefixEnd_8091534 : Nat := 4983230072969 + 3 ^ 40 * 8091534 * 2
def baseEnd_8091534 : Nat := 4154846174197450069712719

theorem tailTrace_8091534 : CollatzResearch.WordTrace tailWord_8091534 prefixEnd_8091534 4154846174197450069712719 := by
  unfold tailWord_8091534
  simp only [CollatzResearch.WordTrace]
  refine ⟨36890311283470214603965207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196748326845174477887814437 36890311283470214603965207)
  ·
    refine ⟨55335466925205321905947811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36890311283470214603965207 55335466925205321905947811)
    ·
      refine ⟨83003200387807982858921717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55335466925205321905947811 83003200387807982858921717)
      ·
        refine ⟨7781550036356998393023911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83003200387807982858921717 7781550036356998393023911)
        ·
          refine ⟨11672325054535497589535867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781550036356998393023911 11672325054535497589535867)
          ·
            refine ⟨17508487581803246384303801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672325054535497589535867 17508487581803246384303801)
            ·
              refine ⟨13131365686352434788227851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17508487581803246384303801 13131365686352434788227851)
              ·
                refine ⟨19697048529528652182341777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13131365686352434788227851 19697048529528652182341777)
                ·
                  refine ⟨14772786397146489136756333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19697048529528652182341777 14772786397146489136756333)
                  ·
                    refine ⟨5539794898929933426283625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14772786397146489136756333 5539794898929933426283625)
                    ·
                      refine ⟨4154846174197450069712719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539794898929933426283625 4154846174197450069712719)
                      ·
                        rfl

theorem cell23_8091534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_8091534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091534 prefixEnd_8091534 := by exact prefixLift 8091534
  have htrace : WordTrace (prefixWord ++ tailWord_8091534) baseStart_8091534 baseEnd_8091534 := by
    simpa [prefixWord, tailWord_8091534, baseEnd_8091534] using wordTrace_append hprefix tailTrace_8091534
  have hstable : (prefixWord ++ tailWord_8091534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091534).length < 2 ^ (prefixWord ++ tailWord_8091534).sum := by decide
  have hdescent : baseEnd_8091534 < baseStart_8091534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091543 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_8091543 : Nat := 118140960795 + 8091543 * 2 ^ 59
def prefixEnd_8091543 : Nat := 4983230072969 + 3 ^ 40 * 8091543 * 2
def baseEnd_8091543 : Nat := 4154850795523340534500177

theorem tailTrace_8091543 : CollatzResearch.WordTrace tailWord_8091543 prefixEnd_8091543 4154850795523340534500177 := by
  unfold tailWord_8091543
  simp only [CollatzResearch.WordTrace]
  refine ⟨295122818524729111368799283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196748545683152740912532855 295122818524729111368799283)
  ·
    refine ⟨442684227787093667053198925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295122818524729111368799283 442684227787093667053198925)
    ·
      refine ⟨166006585420160125144949597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442684227787093667053198925 166006585420160125144949597)
      ·
        refine ⟨62252469532560046929356099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166006585420160125144949597 62252469532560046929356099)
        ·
          refine ⟨93378704298840070394034149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62252469532560046929356099 93378704298840070394034149)
          ·
            refine ⟨17508507056032513198881403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93378704298840070394034149 17508507056032513198881403)
            ·
              refine ⟨26262760584048769798322105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17508507056032513198881403 26262760584048769798322105)
              ·
                refine ⟨19697070438036577348741579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26262760584048769798322105 19697070438036577348741579)
                ·
                  refine ⟨29545605657054866023112369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19697070438036577348741579 29545605657054866023112369)
                  ·
                    refine ⟨22159204242791149517334277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29545605657054866023112369 22159204242791149517334277)
                    ·
                      refine ⟨4154850795523340534500177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22159204242791149517334277 4154850795523340534500177)
                      ·
                        rfl

theorem cell23_8091543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_8091543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091543 prefixEnd_8091543 := by exact prefixLift 8091543
  have htrace : WordTrace (prefixWord ++ tailWord_8091543) baseStart_8091543 baseEnd_8091543 := by
    simpa [prefixWord, tailWord_8091543, baseEnd_8091543] using wordTrace_append hprefix tailTrace_8091543
  have hstable : (prefixWord ++ tailWord_8091543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091543).length < 2 ^ (prefixWord ++ tailWord_8091543).sum := by decide
  have hdescent : baseEnd_8091543 < baseStart_8091543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091553 : List Nat := [1, 2, 3, 4, 3, 10]
def baseStart_8091553 : Nat := 118140960795 + 8091553 * 2 ^ 59
def prefixEnd_8091553 : Nat := 4983230072969 + 3 ^ 40 * 8091553 * 2
def baseEnd_8091553 : Nat := 17098172552797882697017

theorem tailTrace_8091553 : CollatzResearch.WordTrace tailWord_8091553 prefixEnd_8091553 17098172552797882697017 := by
  unfold tailWord_8091553
  simp only [CollatzResearch.WordTrace]
  refine ⟨295123183254692883076663313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196748788836461922051108875 295123183254692883076663313)
  ·
    refine ⟨221342387441019662307497485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295123183254692883076663313 221342387441019662307497485)
    ·
      refine ⟨83003395290382373365311557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221342387441019662307497485 83003395290382373365311557)
      ·
        refine ⟨15563136616946695005995917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83003395290382373365311557 15563136616946695005995917)
        ·
          refine ⟨5836176231355010627248469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15563136616946695005995917 5836176231355010627248469)
          ·
            refine ⟨17098172552797882697017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5836176231355010627248469 17098172552797882697017)
            ·
              rfl

theorem cell23_8091553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 10].length) (baseStart_8091553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091553 prefixEnd_8091553 := by exact prefixLift 8091553
  have htrace : WordTrace (prefixWord ++ tailWord_8091553) baseStart_8091553 baseEnd_8091553 := by
    simpa [prefixWord, tailWord_8091553, baseEnd_8091553] using wordTrace_append hprefix tailTrace_8091553
  have hstable : (prefixWord ++ tailWord_8091553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091553).length < 2 ^ (prefixWord ++ tailWord_8091553).sum := by decide
  have hdescent : baseEnd_8091553 < baseStart_8091553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091683 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 5]
def baseStart_8091683 : Nat := 118140960795 + 8091683 * 2 ^ 59
def prefixEnd_8091683 : Nat := 4983230072969 + 3 ^ 40 * 8091683 * 2
def baseEnd_8091683 : Nat := 4154922682814969986749533

theorem tailTrace_8091683 : CollatzResearch.WordTrace tailWord_8091683 prefixEnd_8091683 4154922682814969986749533 := by
  unfold tailWord_8091683
  simp only [CollatzResearch.WordTrace]
  refine ⟨295127924744221915278895703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196751949829481276852597135 295127924744221915278895703)
  ·
    refine ⟨442691887116332872918343555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295127924744221915278895703 442691887116332872918343555)
    ·
      refine ⟨664037830674499309377515333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442691887116332872918343555 664037830674499309377515333)
      ·
        refine ⟨124507093251468620508284125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 664037830674499309377515333 124507093251468620508284125)
        ·
          refine ⟨46690159969300732690606547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124507093251468620508284125 46690159969300732690606547)
          ·
            refine ⟨70035239953951099035909821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46690159969300732690606547 70035239953951099035909821)
            ·
              refine ⟨26263214982731662138466183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70035239953951099035909821 26263214982731662138466183)
              ·
                refine ⟨39394822474097493207699275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26263214982731662138466183 39394822474097493207699275)
                ·
                  refine ⟨59092233711146239811548913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39394822474097493207699275 59092233711146239811548913)
                  ·
                    refine ⟨44319175283359679858661685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59092233711146239811548913 44319175283359679858661685)
                    ·
                      refine ⟨4154922682814969986749533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44319175283359679858661685 4154922682814969986749533)
                      ·
                        rfl

theorem cell23_8091683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_8091683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091683 prefixEnd_8091683 := by exact prefixLift 8091683
  have htrace : WordTrace (prefixWord ++ tailWord_8091683) baseStart_8091683 baseEnd_8091683 := by
    simpa [prefixWord, tailWord_8091683, baseEnd_8091683] using wordTrace_append hprefix tailTrace_8091683
  have hstable : (prefixWord ++ tailWord_8091683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091683).length < 2 ^ (prefixWord ++ tailWord_8091683).sum := by decide
  have hdescent : baseEnd_8091683 < baseStart_8091683 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091737 : List Nat := [1, 2, 1, 2, 2, 1, 5, 4, 1, 4]
def baseStart_8091737 : Nat := 118140960795 + 8091737 * 2 ^ 59
def prefixEnd_8091737 : Nat := 4983230072969 + 3 ^ 40 * 8091737 * 2
def baseEnd_8091737 : Nat := 1384983470256770925158095

theorem tailTrace_8091737 : CollatzResearch.WordTrace tailWord_8091737 prefixEnd_8091737 1384983470256770925158095 := by
  unfold tailWord_8091737
  simp only [CollatzResearch.WordTrace]
  refine ⟨295129894286026282501361465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196753262857350855000907643 295129894286026282501361465)
  ·
    refine ⟨221347420714519711876021099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295129894286026282501361465 221347420714519711876021099)
    ·
      refine ⟨332021131071779567814031649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221347420714519711876021099 332021131071779567814031649)
      ·
        refine ⟨249015848303834675860523737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332021131071779567814031649 249015848303834675860523737)
        ·
          refine ⟨186761886227876006895392803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249015848303834675860523737 186761886227876006895392803)
          ·
            refine ⟨280142829341814010343089205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186761886227876006895392803 280142829341814010343089205)
            ·
              refine ⟨26263390250795063469664613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280142829341814010343089205 26263390250795063469664613)
              ·
                refine ⟨4924385672024074400562115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26263390250795063469664613 4924385672024074400562115)
                ·
                  refine ⟨7386578508036111600843173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924385672024074400562115 7386578508036111600843173)
                  ·
                    refine ⟨1384983470256770925158095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7386578508036111600843173 1384983470256770925158095)
                    ·
                      rfl

theorem cell23_8091737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 4].length) (baseStart_8091737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091737 prefixEnd_8091737 := by exact prefixLift 8091737
  have htrace : WordTrace (prefixWord ++ tailWord_8091737) baseStart_8091737 baseEnd_8091737 := by
    simpa [prefixWord, tailWord_8091737, baseEnd_8091737] using wordTrace_append hprefix tailTrace_8091737
  have hstable : (prefixWord ++ tailWord_8091737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091737).length < 2 ^ (prefixWord ++ tailWord_8091737).sum := by decide
  have hdescent : baseEnd_8091737 < baseStart_8091737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091794 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_8091794 : Nat := 118140960795 + 8091794 * 2 ^ 59
def prefixEnd_8091794 : Nat := 4983230072969 + 3 ^ 40 * 8091794 * 2
def baseEnd_8091794 : Nat := 4154979679167619052461523

theorem tailTrace_8091794 : CollatzResearch.WordTrace tailWord_8091794 prefixEnd_8091794 4154979679167619052461523 := by
  unfold tailWord_8091794
  simp only [CollatzResearch.WordTrace]
  refine ⟨73782993311704945309046609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196754648831213187490790957 73782993311704945309046609)
  ·
    refine ⟨55337244983778708981784957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73782993311704945309046609 55337244983778708981784957)
    ·
      refine ⟨20751466868917015868169359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55337244983778708981784957 20751466868917015868169359)
      ·
        refine ⟨31127200303375523802254039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20751466868917015868169359 31127200303375523802254039)
        ·
          refine ⟨46690800455063285703381059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31127200303375523802254039 46690800455063285703381059)
          ·
            refine ⟨70036200682594928555071589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46690800455063285703381059 70036200682594928555071589)
            ·
              refine ⟨13131787627986549104075923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70036200682594928555071589 13131787627986549104075923)
              ·
                refine ⟨19697681441979823656113885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13131787627986549104075923 19697681441979823656113885)
                ·
                  refine ⟨7386630540742433871042707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19697681441979823656113885 7386630540742433871042707)
                  ·
                    refine ⟨11079945811113650806564061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7386630540742433871042707 11079945811113650806564061)
                    ·
                      refine ⟨4154979679167619052461523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11079945811113650806564061 4154979679167619052461523)
                      ·
                        rfl

theorem cell23_8091794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_8091794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091794 prefixEnd_8091794 := by exact prefixLift 8091794
  have htrace : WordTrace (prefixWord ++ tailWord_8091794) baseStart_8091794 baseEnd_8091794 := by
    simpa [prefixWord, tailWord_8091794, baseEnd_8091794] using wordTrace_append hprefix tailTrace_8091794
  have hstable : (prefixWord ++ tailWord_8091794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091794).length < 2 ^ (prefixWord ++ tailWord_8091794).sum := by decide
  have hdescent : baseEnd_8091794 < baseStart_8091794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091820 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_8091820 : Nat := 118140960795 + 8091820 * 2 ^ 59
def prefixEnd_8091820 : Nat := 4983230072969 + 3 ^ 40 * 8091820 * 2
def baseEnd_8091820 : Nat := 4154993029664635950736403

theorem tailTrace_8091820 : CollatzResearch.WordTrace tailWord_8091820 prefixEnd_8091820 4154993029664635950736403 := by
  unfold tailWord_8091820
  simp only [CollatzResearch.WordTrace]
  refine ⟨147566460772362793838316457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196755281029817058451088609 147566460772362793838316457)
  ·
    refine ⟨110674845579272095378737343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147566460772362793838316457 110674845579272095378737343)
    ·
      refine ⟨166012268368908143068106015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110674845579272095378737343 166012268368908143068106015)
      ·
        refine ⟨249018402553362214602159023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166012268368908143068106015 249018402553362214602159023)
        ·
          refine ⟨373527603830043321903238535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249018402553362214602159023 373527603830043321903238535)
          ·
            refine ⟨560291405745064982854857803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373527603830043321903238535 560291405745064982854857803)
            ·
              refine ⟨840437108617597474282286705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560291405745064982854857803 840437108617597474282286705)
              ·
                refine ⟨630327831463198105711715029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840437108617597474282286705 630327831463198105711715029)
                ·
                  refine ⟨14773308549918705602618321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 630327831463198105711715029 14773308549918705602618321)
                  ·
                    refine ⟨11079981412439029201963741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14773308549918705602618321 11079981412439029201963741)
                    ·
                      refine ⟨4154993029664635950736403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11079981412439029201963741 4154993029664635950736403)
                      ·
                        rfl

theorem cell23_8091820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_8091820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091820 prefixEnd_8091820 := by exact prefixLift 8091820
  have htrace : WordTrace (prefixWord ++ tailWord_8091820) baseStart_8091820 baseEnd_8091820 := by
    simpa [prefixWord, tailWord_8091820, baseEnd_8091820] using wordTrace_append hprefix tailTrace_8091820
  have hstable : (prefixWord ++ tailWord_8091820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091820).length < 2 ^ (prefixWord ++ tailWord_8091820).sum := by decide
  have hdescent : baseEnd_8091820 < baseStart_8091820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091840 : List Nat := [2, 1, 1, 2, 5, 3, 9]
def baseStart_8091840 : Nat := 118140960795 + 8091840 * 2 ^ 59
def prefixEnd_8091840 : Nat := 4983230072969 + 3 ^ 40 * 8091840 * 2
def baseEnd_8091840 : Nat := 51296337028120072499831

theorem tailTrace_8091840 : CollatzResearch.WordTrace tailWord_8091840 prefixEnd_8091840 51296337028120072499831 := by
  unfold tailWord_8091840
  simp only [CollatzResearch.WordTrace]
  refine ⟨147566825502326565546180487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196755767336435420728240649 147566825502326565546180487)
  ·
    refine ⟨221350238253489848319270731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147566825502326565546180487 221350238253489848319270731)
    ·
      refine ⟨332025357380234772478906097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221350238253489848319270731 332025357380234772478906097)
      ·
        refine ⟨249019018035176079359179573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332025357380234772478906097 249019018035176079359179573)
        ·
          refine ⟨23345532940797757439923085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249019018035176079359179573 23345532940797757439923085)
          ·
            refine ⟨8754574852799159039971157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23345532940797757439923085 8754574852799159039971157)
            ·
              refine ⟨51296337028120072499831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8754574852799159039971157 51296337028120072499831)
              ·
                rfl

theorem cell23_8091840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 9].length) (baseStart_8091840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091840 prefixEnd_8091840 := by exact prefixLift 8091840
  have htrace : WordTrace (prefixWord ++ tailWord_8091840) baseStart_8091840 baseEnd_8091840 := by
    simpa [prefixWord, tailWord_8091840, baseEnd_8091840] using wordTrace_append hprefix tailTrace_8091840
  have hstable : (prefixWord ++ tailWord_8091840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091840).length < 2 ^ (prefixWord ++ tailWord_8091840).sum := by decide
  have hdescent : baseEnd_8091840 < baseStart_8091840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091868 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_8091868 : Nat := 118140960795 + 8091868 * 2 ^ 59
def prefixEnd_8091868 : Nat := 4983230072969 + 3 ^ 40 * 8091868 * 2
def baseEnd_8091868 : Nat := 4155017676736051762936183

theorem tailTrace_8091868 : CollatzResearch.WordTrace tailWord_8091868 prefixEnd_8091868 4155017676736051762936183 := by
  unfold tailWord_8091868
  simp only [CollatzResearch.WordTrace]
  refine ⟨147567336124275845937190129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196756448165701127916253505 147567336124275845937190129)
  ·
    refine ⟨110675502093206884452892597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147567336124275845937190129 110675502093206884452892597)
    ·
      refine ⟨10375828321238145417458681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110675502093206884452892597 10375828321238145417458681)
      ·
        refine ⟨7781871240928609063094011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10375828321238145417458681 7781871240928609063094011)
        ·
          refine ⟨11672806861392913594641017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781871240928609063094011 11672806861392913594641017)
          ·
            refine ⟨8754605146044685195980763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11672806861392913594641017 8754605146044685195980763)
            ·
              refine ⟨13131907719067027793971145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8754605146044685195980763 13131907719067027793971145)
              ·
                refine ⟨9848930789300270845478359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13131907719067027793971145 9848930789300270845478359)
                ·
                  refine ⟨14773396183950406268217539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9848930789300270845478359 14773396183950406268217539)
                  ·
                    refine ⟨22160094275925609402326309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14773396183950406268217539 22160094275925609402326309)
                    ·
                      refine ⟨4155017676736051762936183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22160094275925609402326309 4155017676736051762936183)
                      ·
                        rfl

theorem cell23_8091868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_8091868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091868 prefixEnd_8091868 := by exact prefixLift 8091868
  have htrace : WordTrace (prefixWord ++ tailWord_8091868) baseStart_8091868 baseEnd_8091868 := by
    simpa [prefixWord, tailWord_8091868, baseEnd_8091868] using wordTrace_append hprefix tailTrace_8091868
  have hstable : (prefixWord ++ tailWord_8091868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091868).length < 2 ^ (prefixWord ++ tailWord_8091868).sum := by decide
  have hdescent : baseEnd_8091868 < baseStart_8091868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091907 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 3, 4, 2]
def baseStart_8091907 : Nat := 118140960795 + 8091907 * 2 ^ 59
def prefixEnd_8091907 : Nat := 4983230072969 + 3 ^ 40 * 8091907 * 2
def baseEnd_8091907 : Nat := 4155037702481577110348503

theorem tailTrace_8091907 : CollatzResearch.WordTrace tailWord_8091907 prefixEnd_8091907 4155037702481577110348503 := by
  unfold tailWord_8091907
  simp only [CollatzResearch.WordTrace]
  refine ⟨295136094695410401535049975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196757396463606934356699983 295136094695410401535049975)
  ·
    refine ⟨442704142043115602302574963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295136094695410401535049975 442704142043115602302574963)
    ·
      refine ⟨664056213064673403453862445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442704142043115602302574963 664056213064673403453862445)
      ·
        refine ⟨249021079899252526295198417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664056213064673403453862445 249021079899252526295198417)
        ·
          refine ⟨186765809924439394721398813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249021079899252526295198417 186765809924439394721398813)
          ·
            refine ⟨70037178721664773020524555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186765809924439394721398813 70037178721664773020524555)
            ·
              refine ⟨105055768082497159530786833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70037178721664773020524555 105055768082497159530786833)
              ·
                refine ⟨78791826061872869648090125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105055768082497159530786833 78791826061872869648090125)
                ·
                  refine ⟨29546934773202326118033797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78791826061872869648090125 29546934773202326118033797)
                  ·
                    refine ⟨5540050269975436147131337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29546934773202326118033797 5540050269975436147131337)
                    ·
                      refine ⟨4155037702481577110348503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540050269975436147131337 4155037702481577110348503)
                      ·
                        rfl

theorem cell23_8091907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_8091907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091907 prefixEnd_8091907 := by exact prefixLift 8091907
  have htrace : WordTrace (prefixWord ++ tailWord_8091907) baseStart_8091907 baseEnd_8091907 := by
    simpa [prefixWord, tailWord_8091907, baseEnd_8091907] using wordTrace_append hprefix tailTrace_8091907
  have hstable : (prefixWord ++ tailWord_8091907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091907).length < 2 ^ (prefixWord ++ tailWord_8091907).sum := by decide
  have hdescent : baseEnd_8091907 < baseStart_8091907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8091957 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_8091957 : Nat := 118140960795 + 8091957 * 2 ^ 59
def prefixEnd_8091957 : Nat := 4983230072969 + 3 ^ 40 * 8091957 * 2
def baseEnd_8091957 : Nat := 4155063376514301914723273

theorem tailTrace_8091957 : CollatzResearch.WordTrace tailWord_8091957 prefixEnd_8091957 4155063376514301914723273 := by
  unfold tailWord_8091957
  simp only [CollatzResearch.WordTrace]
  refine ⟨295137918345229260074370125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196758612230152840049580083 295137918345229260074370125)
  ·
    refine ⟨110676719379460972527888797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295137918345229260074370125 110676719379460972527888797)
    ·
      refine ⟨41503769767297864697958299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110676719379460972527888797 41503769767297864697958299)
      ·
        refine ⟨62255654650946797046937449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41503769767297864697958299 62255654650946797046937449)
        ·
          refine ⟨46691740988210097785203087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62255654650946797046937449 46691740988210097785203087)
          ·
            refine ⟨70037611482315146677804631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46691740988210097785203087 70037611482315146677804631)
            ·
              refine ⟨105056417223472720016706947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70037611482315146677804631 105056417223472720016706947)
              ·
                refine ⟨157584625835209080025060421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105056417223472720016706947 157584625835209080025060421)
                ·
                  refine ⟨29547117344101702504698829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157584625835209080025060421 29547117344101702504698829)
                  ·
                    refine ⟨11080169004038138439262061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29547117344101702504698829 11080169004038138439262061)
                    ·
                      refine ⟨4155063376514301914723273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11080169004038138439262061 4155063376514301914723273)
                      ·
                        rfl

theorem cell23_8091957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_8091957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8091957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8091957 prefixEnd_8091957 := by exact prefixLift 8091957
  have htrace : WordTrace (prefixWord ++ tailWord_8091957) baseStart_8091957 baseEnd_8091957 := by
    simpa [prefixWord, tailWord_8091957, baseEnd_8091957] using wordTrace_append hprefix tailTrace_8091957
  have hstable : (prefixWord ++ tailWord_8091957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8091957).length < 2 ^ (prefixWord ++ tailWord_8091957).sum := by decide
  have hdescent : baseEnd_8091957 < baseStart_8091957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8091957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092104 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_8092104 : Nat := 118140960795 + 8092104 * 2 ^ 59
def prefixEnd_8092104 : Nat := 4983230072969 + 3 ^ 40 * 8092104 * 2
def baseEnd_8092104 : Nat := 4155138858170512839585097

theorem tailTrace_8092104 : CollatzResearch.WordTrace tailWord_8092104 prefixEnd_8092104 4155138858170512839585097 := by
  unfold tailWord_8092104
  simp only [CollatzResearch.WordTrace]
  refine ⟨147571639937848352089985683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196762186583797802786647577 147571639937848352089985683)
  ·
    refine ⟨221357459906772528134978525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147571639937848352089985683 221357459906772528134978525)
    ·
      refine ⟨83009047465039698050616947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221357459906772528134978525 83009047465039698050616947)
      ·
        refine ⟨124513571197559547075925421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83009047465039698050616947 124513571197559547075925421)
        ·
          refine ⟨46692589199084830153472033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124513571197559547075925421 46692589199084830153472033)
          ·
            refine ⟨35019441899313622615104025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46692589199084830153472033 35019441899313622615104025)
            ·
              refine ⟨26264581424485216961328019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35019441899313622615104025 26264581424485216961328019)
              ·
                refine ⟨39396872136727825441992029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26264581424485216961328019 39396872136727825441992029)
                ·
                  refine ⟨14773827051272934540747011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39396872136727825441992029 14773827051272934540747011)
                  ·
                    refine ⟨22160740576909401811120517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14773827051272934540747011 22160740576909401811120517)
                    ·
                      refine ⟨4155138858170512839585097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22160740576909401811120517 4155138858170512839585097)
                      ·
                        rfl

theorem cell23_8092104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_8092104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092104 prefixEnd_8092104 := by exact prefixLift 8092104
  have htrace : WordTrace (prefixWord ++ tailWord_8092104) baseStart_8092104 baseEnd_8092104 := by
    simpa [prefixWord, tailWord_8092104, baseEnd_8092104] using wordTrace_append hprefix tailTrace_8092104
  have hstable : (prefixWord ++ tailWord_8092104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092104).length < 2 ^ (prefixWord ++ tailWord_8092104).sum := by decide
  have hdescent : baseEnd_8092104 < baseStart_8092104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092121 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 5, 2, 2]
def baseStart_8092121 : Nat := 118140960795 + 8092121 * 2 ^ 59
def prefixEnd_8092121 : Nat := 4983230072969 + 3 ^ 40 * 8092121 * 2
def baseEnd_8092121 : Nat := 4155147587341639273072519

theorem tailTrace_8092121 : CollatzResearch.WordTrace tailWord_8092121 prefixEnd_8092121 4155147587341639273072519 := by
  unfold tailWord_8092121
  simp only [CollatzResearch.WordTrace]
  refine ⟨295143899916635116083340217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196762599944423410722226811 295143899916635116083340217)
  ·
    refine ⟨221357924937476337062505163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295143899916635116083340217 221357924937476337062505163)
    ·
      refine ⟨332036887406214505593757745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221357924937476337062505163 332036887406214505593757745)
      ·
        refine ⟨249027665554660879195318309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332036887406214505593757745 249027665554660879195318309)
        ·
          refine ⟨46692687291498914849122183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249027665554660879195318309 46692687291498914849122183)
          ·
            refine ⟨70039030937248372273683275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46692687291498914849122183 70039030937248372273683275)
            ·
              refine ⟨105058546405872558410524913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70039030937248372273683275 105058546405872558410524913)
              ·
                refine ⟨78793909804404418807893685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105058546405872558410524913 78793909804404418807893685)
                ·
                  refine ⟨7386929044162914263240033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78793909804404418807893685 7386929044162914263240033)
                  ·
                    refine ⟨5540196783122185697430025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7386929044162914263240033 5540196783122185697430025)
                    ·
                      refine ⟨4155147587341639273072519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540196783122185697430025 4155147587341639273072519)
                      ·
                        rfl

theorem cell23_8092121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_8092121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092121 prefixEnd_8092121 := by exact prefixLift 8092121
  have htrace : WordTrace (prefixWord ++ tailWord_8092121) baseStart_8092121 baseEnd_8092121 := by
    simpa [prefixWord, tailWord_8092121, baseEnd_8092121] using wordTrace_append hprefix tailTrace_8092121
  have hstable : (prefixWord ++ tailWord_8092121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092121).length < 2 ^ (prefixWord ++ tailWord_8092121).sum := by decide
  have hdescent : baseEnd_8092121 < baseStart_8092121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092127 : List Nat := [1, 1, 2, 3, 3, 3, 10]
def baseStart_8092127 : Nat := 118140960795 + 8092127 * 2 ^ 59
def prefixEnd_8092127 : Nat := 4983230072969 + 3 ^ 40 * 8092127 * 2
def baseEnd_8092127 : Nat := 51298156397846496908611

theorem tailTrace_8092127 : CollatzResearch.WordTrace tailWord_8092127 prefixEnd_8092127 51298156397846496908611 := by
  unfold tailWord_8092127
  simp only [CollatzResearch.WordTrace]
  refine ⟨295144118754613379108058635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196762745836408919405372423 295144118754613379108058635)
  ·
    refine ⟨442716178131920068662087953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295144118754613379108058635 442716178131920068662087953)
    ·
      refine ⟨332037133598940051496565965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442716178131920068662087953 332037133598940051496565965)
      ·
        refine ⟨124513925099602519311212237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332037133598940051496565965 124513925099602519311212237)
        ·
          refine ⟨46692721912350944741704589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124513925099602519311212237 46692721912350944741704589)
          ·
            refine ⟨17509770717131604278139221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46692721912350944741704589 17509770717131604278139221)
            ·
              refine ⟨51298156397846496908611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17509770717131604278139221 51298156397846496908611)
              ·
                rfl

theorem cell23_8092127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 10].length) (baseStart_8092127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092127 prefixEnd_8092127 := by exact prefixLift 8092127
  have htrace : WordTrace (prefixWord ++ tailWord_8092127) baseStart_8092127 baseEnd_8092127 := by
    simpa [prefixWord, tailWord_8092127, baseEnd_8092127] using wordTrace_append hprefix tailTrace_8092127
  have hstable : (prefixWord ++ tailWord_8092127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092127).length < 2 ^ (prefixWord ++ tailWord_8092127).sum := by decide
  have hdescent : baseEnd_8092127 < baseStart_8092127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092131 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 4, 4]
def baseStart_8092131 : Nat := 118140960795 + 8092131 * 2 ^ 59
def prefixEnd_8092131 : Nat := 4983230072969 + 3 ^ 40 * 8092131 * 2
def baseEnd_8092131 : Nat := 1385050907382728077982491

theorem tailTrace_8092131 : CollatzResearch.WordTrace tailWord_8092131 prefixEnd_8092131 1385050907382728077982491 := by
  unfold tailWord_8092131
  simp only [CollatzResearch.WordTrace]
  refine ⟨295144264646598887791204247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196762843097732591860802831 295144264646598887791204247)
  ·
    refine ⟨442716396969898331686806371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295144264646598887791204247 442716396969898331686806371)
    ·
      refine ⟨664074595454847497530209557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442716396969898331686806371 664074595454847497530209557)
      ·
        refine ⟨31128496661945976446728573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 664074595454847497530209557 31128496661945976446728573)
        ·
          refine ⟨11673186248229741167523215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31128496661945976446728573 11673186248229741167523215)
          ·
            refine ⟨17509779372344611751284823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11673186248229741167523215 17509779372344611751284823)
            ·
              refine ⟨26264669058516917626927235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17509779372344611751284823 26264669058516917626927235)
              ·
                refine ⟨39397003587775376440390853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26264669058516917626927235 39397003587775376440390853)
                ·
                  refine ⟨7386938172707883082573285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39397003587775376440390853 7386938172707883082573285)
                  ·
                    refine ⟨1385050907382728077982491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7386938172707883082573285 1385050907382728077982491)
                    ·
                      rfl

theorem cell23_8092131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 4].length) (baseStart_8092131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092131 prefixEnd_8092131 := by exact prefixLift 8092131
  have htrace : WordTrace (prefixWord ++ tailWord_8092131) baseStart_8092131 baseEnd_8092131 := by
    simpa [prefixWord, tailWord_8092131, baseEnd_8092131] using wordTrace_append hprefix tailTrace_8092131
  have hstable : (prefixWord ++ tailWord_8092131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092131).length < 2 ^ (prefixWord ++ tailWord_8092131).sum := by decide
  have hdescent : baseEnd_8092131 < baseStart_8092131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092138 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_8092138 : Nat := 118140960795 + 8092138 * 2 ^ 59
def prefixEnd_8092138 : Nat := 4983230072969 + 3 ^ 40 * 8092138 * 2
def baseEnd_8092138 : Nat := 4155156316512765706559941

theorem tailTrace_8092138 : CollatzResearch.WordTrace tailWord_8092138 prefixEnd_8092138 4155156316512765706559941 := by
  unfold tailWord_8092138
  simp only [CollatzResearch.WordTrace]
  refine ⟨73786129989393381996677267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196763013305049018657806045 73786129989393381996677267)
  ·
    refine ⟨110679194984090072995015901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73786129989393381996677267 110679194984090072995015901)
    ·
      refine ⟨41504698119033777373130963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110679194984090072995015901 41504698119033777373130963)
      ·
        refine ⟨62257047178550666059696445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41504698119033777373130963 62257047178550666059696445)
        ·
          refine ⟨23346392691956499772386167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62257047178550666059696445 23346392691956499772386167)
          ·
            refine ⟨35019589037934749658579251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23346392691956499772386167 35019589037934749658579251)
            ·
              refine ⟨52529383556902124487868877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35019589037934749658579251 52529383556902124487868877)
              ·
                refine ⟨19698518833838296682950829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52529383556902124487868877 19698518833838296682950829)
                ·
                  refine ⟨7386944562689361256106561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19698518833838296682950829 7386944562689361256106561)
                  ·
                    refine ⟨5540208422017020942079921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7386944562689361256106561 5540208422017020942079921)
                    ·
                      refine ⟨4155156316512765706559941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540208422017020942079921 4155156316512765706559941)
                      ·
                        rfl

theorem cell23_8092138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_8092138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092138 prefixEnd_8092138 := by exact prefixLift 8092138
  have htrace : WordTrace (prefixWord ++ tailWord_8092138) baseStart_8092138 baseEnd_8092138 := by
    simpa [prefixWord, tailWord_8092138, baseEnd_8092138] using wordTrace_append hprefix tailTrace_8092138
  have hstable : (prefixWord ++ tailWord_8092138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092138).length < 2 ^ (prefixWord ++ tailWord_8092138).sum := by decide
  have hdescent : baseEnd_8092138 < baseStart_8092138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092141 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_8092141 : Nat := 118140960795 + 8092141 * 2 ^ 59
def prefixEnd_8092141 : Nat := 4983230072969 + 3 ^ 40 * 8092141 * 2
def baseEnd_8092141 : Nat := 4155157856954729194822427

theorem tailTrace_8092141 : CollatzResearch.WordTrace tailWord_8092141 prefixEnd_8092141 4155157856954729194822427 := by
  unfold tailWord_8092141
  simp only [CollatzResearch.WordTrace]
  refine ⟨295144629376562659499068277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196763086251041772999378851 295144629376562659499068277)
  ·
    refine ⟨27669809004052749328037651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295144629376562659499068277 27669809004052749328037651)
    ·
      refine ⟨41504713506079123992056477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27669809004052749328037651 41504713506079123992056477)
      ·
        refine ⟨15564267564779671497021179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41504713506079123992056477 15564267564779671497021179)
        ·
          refine ⟨23346401347169507245531769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15564267564779671497021179 23346401347169507245531769)
          ·
            refine ⟨17509801010377130434148827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23346401347169507245531769 17509801010377130434148827)
            ·
              refine ⟨26264701515565695651223241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17509801010377130434148827 26264701515565695651223241)
              ·
                refine ⟨19698526136674271738417431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26264701515565695651223241 19698526136674271738417431)
                ·
                  refine ⟨29547789205011407607626147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19698526136674271738417431 29547789205011407607626147)
                  ·
                    refine ⟨44321683807517111411439221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29547789205011407607626147 44321683807517111411439221)
                    ·
                      refine ⟨4155157856954729194822427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44321683807517111411439221 4155157856954729194822427)
                      ·
                        rfl

theorem cell23_8092141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_8092141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092141 prefixEnd_8092141 := by exact prefixLift 8092141
  have htrace : WordTrace (prefixWord ++ tailWord_8092141) baseStart_8092141 baseEnd_8092141 := by
    simpa [prefixWord, tailWord_8092141, baseEnd_8092141] using wordTrace_append hprefix tailTrace_8092141
  have hstable : (prefixWord ++ tailWord_8092141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092141).length < 2 ^ (prefixWord ++ tailWord_8092141).sum := by decide
  have hdescent : baseEnd_8092141 < baseStart_8092141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092154 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_8092154 : Nat := 118140960795 + 8092154 * 2 ^ 59
def prefixEnd_8092154 : Nat := 4983230072969 + 3 ^ 40 * 8092154 * 2
def baseEnd_8092154 : Nat := 4155164532203237643959867

theorem tailTrace_8092154 : CollatzResearch.WordTrace tailWord_8092154 prefixEnd_8092154 4155164532203237643959867 := by
  unfold tailWord_8092154
  simp only [CollatzResearch.WordTrace]
  refine ⟨73786275881378890679822879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196763402350343708479527677 73786275881378890679822879)
  ·
    refine ⟨110679413822068336019734319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73786275881378890679822879 110679413822068336019734319)
    ·
      refine ⟨166019120733102504029601479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110679413822068336019734319 166019120733102504029601479)
      ·
        refine ⟨249028681099653756044402219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166019120733102504029601479 249028681099653756044402219)
        ·
          refine ⟨373543021649480634066603329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249028681099653756044402219 373543021649480634066603329)
          ·
            refine ⟨280157266237110475549952497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373543021649480634066603329 280157266237110475549952497)
            ·
              refine ⟨210117949677832856662464373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280157266237110475549952497 210117949677832856662464373)
              ·
                refine ⟨19698557782296830312106035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210117949677832856662464373 19698557782296830312106035)
                ·
                  refine ⟨29547836673445245468159053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19698557782296830312106035 29547836673445245468159053)
                  ·
                    refine ⟨11080438752541967050559645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29547836673445245468159053 11080438752541967050559645)
                    ·
                      refine ⟨4155164532203237643959867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11080438752541967050559645 4155164532203237643959867)
                      ·
                        rfl

theorem cell23_8092154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_8092154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092154 prefixEnd_8092154 := by exact prefixLift 8092154
  have htrace : WordTrace (prefixWord ++ tailWord_8092154) baseStart_8092154 baseEnd_8092154 := by
    simpa [prefixWord, tailWord_8092154, baseEnd_8092154] using wordTrace_append hprefix tailTrace_8092154
  have hstable : (prefixWord ++ tailWord_8092154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092154).length < 2 ^ (prefixWord ++ tailWord_8092154).sum := by decide
  have hdescent : baseEnd_8092154 < baseStart_8092154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092161 : List Nat := [1, 2, 4, 1, 3, 3, 2, 7]
def baseStart_8092161 : Nat := 118140960795 + 8092161 * 2 ^ 59
def prefixEnd_8092161 : Nat := 4983230072969 + 3 ^ 40 * 8092161 * 2
def baseEnd_8092161 : Nat := 153895115798808115428605

theorem tailTrace_8092161 : CollatzResearch.WordTrace tailWord_8092161 prefixEnd_8092161 153895115798808115428605 := by
  unfold tailWord_8092161
  simp only [CollatzResearch.WordTrace]
  refine ⟨295145358836490202914796337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196763572557660135276530891 295145358836490202914796337)
  ·
    refine ⟨221359019127367652186097253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295145358836490202914796337 221359019127367652186097253)
    ·
      refine ⟨41504816086381434784893235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221359019127367652186097253 41504816086381434784893235)
      ·
        refine ⟨62257224129572152177339853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41504816086381434784893235 62257224129572152177339853)
        ·
          refine ⟨23346459048589557066502445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62257224129572152177339853 23346459048589557066502445)
          ·
            refine ⟨8754922143221083899938417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23346459048589557066502445 8754922143221083899938417)
            ·
              refine ⟨6566191607415812924953813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8754922143221083899938417 6566191607415812924953813)
              ·
                refine ⟨153895115798808115428605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6566191607415812924953813 153895115798808115428605)
                ·
                  rfl

theorem cell23_8092161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 7].length) (baseStart_8092161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092161 prefixEnd_8092161 := by exact prefixLift 8092161
  have htrace : WordTrace (prefixWord ++ tailWord_8092161) baseStart_8092161 baseEnd_8092161 := by
    simpa [prefixWord, tailWord_8092161, baseEnd_8092161] using wordTrace_append hprefix tailTrace_8092161
  have hstable : (prefixWord ++ tailWord_8092161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092161).length < 2 ^ (prefixWord ++ tailWord_8092161).sum := by decide
  have hdescent : baseEnd_8092161 < baseStart_8092161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092166 : List Nat := [6, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_8092166 : Nat := 118140960795 + 8092166 * 2 ^ 59
def prefixEnd_8092166 : Nat := 4983230072969 + 3 ^ 40 * 8092166 * 2
def baseEnd_8092166 : Nat := 4155170693971091597009813

theorem tailTrace_8092166 : CollatzResearch.WordTrace tailWord_8092166 prefixEnd_8092166 4155170693971091597009813 := by
  unfold tailWord_8092166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9223298162546002774022761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196763694134314725845818901 9223298162546002774022761)
  ·
    refine ⟨6917473621909502080517071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9223298162546002774022761 6917473621909502080517071)
    ·
      refine ⟨10376210432864253120775607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6917473621909502080517071 10376210432864253120775607)
      ·
        refine ⟨15564315649296379681163411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10376210432864253120775607 15564315649296379681163411)
        ·
          refine ⟨23346473473944569521745117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15564315649296379681163411 23346473473944569521745117)
          ·
            refine ⟨8754927552729213570654419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23346473473944569521745117 8754927552729213570654419)
            ·
              refine ⟨13132391329093820355981629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8754927552729213570654419 13132391329093820355981629)
              ·
                refine ⟨4924646748410182633493111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13132391329093820355981629 4924646748410182633493111)
                ·
                  refine ⟨7386970122615273950239667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924646748410182633493111 7386970122615273950239667)
                  ·
                    refine ⟨11080455183922910925359501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7386970122615273950239667 11080455183922910925359501)
                    ·
                      refine ⟨4155170693971091597009813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11080455183922910925359501 4155170693971091597009813)
                      ·
                        rfl

theorem cell23_8092166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_8092166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092166 prefixEnd_8092166 := by exact prefixLift 8092166
  have htrace : WordTrace (prefixWord ++ tailWord_8092166) baseStart_8092166 baseEnd_8092166 := by
    simpa [prefixWord, tailWord_8092166, baseEnd_8092166] using wordTrace_append hprefix tailTrace_8092166
  have hstable : (prefixWord ++ tailWord_8092166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092166).length < 2 ^ (prefixWord ++ tailWord_8092166).sum := by decide
  have hdescent : baseEnd_8092166 < baseStart_8092166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092171 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 3]
def baseStart_8092171 : Nat := 118140960795 + 8092171 * 2 ^ 59
def prefixEnd_8092171 : Nat := 4983230072969 + 3 ^ 40 * 8092171 * 2
def baseEnd_8092171 : Nat := 4155173261374364077447289

theorem tailTrace_8092171 : CollatzResearch.WordTrace tailWord_8092171 prefixEnd_8092171 4155173261374364077447289 := by
  unfold tailWord_8092171
  simp only [CollatzResearch.WordTrace]
  refine ⟨295145723566453974622660367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196763815710969316415106911 295145723566453974622660367)
  ·
    refine ⟨442718585349680961933990551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295145723566453974622660367 442718585349680961933990551)
    ·
      refine ⟨664077878024521442900985827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442718585349680961933990551 664077878024521442900985827)
      ·
        refine ⟨996116817036782164351478741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664077878024521442900985827 996116817036782164351478741)
        ·
          refine ⟨23346487899299581976987783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 996116817036782164351478741 23346487899299581976987783)
          ·
            refine ⟨35019731848949372965481675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23346487899299581976987783 35019731848949372965481675)
            ·
              refine ⟨52529597773424059448222513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35019731848949372965481675 52529597773424059448222513)
              ·
                refine ⟨39397198330068044586166885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52529597773424059448222513 39397198330068044586166885)
                ·
                  refine ⟨7386974686887758359906291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39397198330068044586166885 7386974686887758359906291)
                  ·
                    refine ⟨11080462030331637539859437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7386974686887758359906291 11080462030331637539859437)
                    ·
                      refine ⟨4155173261374364077447289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11080462030331637539859437 4155173261374364077447289)
                      ·
                        rfl

theorem cell23_8092171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 3].length) (baseStart_8092171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092171 prefixEnd_8092171 := by exact prefixLift 8092171
  have htrace : WordTrace (prefixWord ++ tailWord_8092171) baseStart_8092171 baseEnd_8092171 := by
    simpa [prefixWord, tailWord_8092171, baseEnd_8092171] using wordTrace_append hprefix tailTrace_8092171
  have hstable : (prefixWord ++ tailWord_8092171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092171).length < 2 ^ (prefixWord ++ tailWord_8092171).sum := by decide
  have hdescent : baseEnd_8092171 < baseStart_8092171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092172 : List Nat := [2, 2, 1, 2, 4, 3, 1, 3, 1, 2, 2]
def baseStart_8092172 : Nat := 118140960795 + 8092172 * 2 ^ 59
def prefixEnd_8092172 : Nat := 4983230072969 + 3 ^ 40 * 8092172 * 2
def baseEnd_8092172 : Nat := 4155173774855018573534785

theorem tailTrace_8092172 : CollatzResearch.WordTrace tailWord_8092172 prefixEnd_8092172 4155173774855018573534785 := by
  unfold tailWord_8092172
  simp only [CollatzResearch.WordTrace]
  refine ⟨147572880019725175896723385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196763840026300234528964513 147572880019725175896723385)
  ·
    refine ⟨110679660014793881922542539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147572880019725175896723385 110679660014793881922542539)
    ·
      refine ⟨166019490022190822883813809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110679660014793881922542539 166019490022190822883813809)
      ·
        refine ⟨124514617516643117162860357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166019490022190822883813809 124514617516643117162860357)
        ·
          refine ⟨23346490784370584468036317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124514617516643117162860357 23346490784370584468036317)
          ·
            refine ⟨8754934044138969175513619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23346490784370584468036317 8754934044138969175513619)
            ·
              refine ⟨13132401066208453763270429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8754934044138969175513619 13132401066208453763270429)
              ·
                refine ⟨4924650399828170161226411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13132401066208453763270429 4924650399828170161226411)
                ·
                  refine ⟨7386975599742255241839617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924650399828170161226411 7386975599742255241839617)
                  ·
                    refine ⟨5540231699806691431379713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7386975599742255241839617 5540231699806691431379713)
                    ·
                      refine ⟨4155173774855018573534785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540231699806691431379713 4155173774855018573534785)
                      ·
                        rfl

theorem cell23_8092172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_8092172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092172 prefixEnd_8092172 := by exact prefixLift 8092172
  have htrace : WordTrace (prefixWord ++ tailWord_8092172) baseStart_8092172 baseEnd_8092172 := by
    simpa [prefixWord, tailWord_8092172, baseEnd_8092172] using wordTrace_append hprefix tailTrace_8092172
  have hstable : (prefixWord ++ tailWord_8092172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092172).length < 2 ^ (prefixWord ++ tailWord_8092172).sum := by decide
  have hdescent : baseEnd_8092172 < baseStart_8092172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092194 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_8092194 : Nat := 118140960795 + 8092194 * 2 ^ 59
def prefixEnd_8092194 : Nat := 4983230072969 + 3 ^ 40 * 8092194 * 2
def baseEnd_8092194 : Nat := 4155185071429417487459683

theorem tailTrace_8092194 : CollatzResearch.WordTrace tailWord_8092194 prefixEnd_8092194 4155185071429417487459683 := by
  unfold tailWord_8092194
  simp only [CollatzResearch.WordTrace]
  refine ⟨73786640611342662387686909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196764374963580433033831757 73786640611342662387686909)
  ·
    refine ⟨27669990229253498395382591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73786640611342662387686909 27669990229253498395382591)
    ·
      refine ⟨41504985343880247593073887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27669990229253498395382591 41504985343880247593073887)
      ·
        refine ⟨62257478015820371389610831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41504985343880247593073887 62257478015820371389610831)
        ·
          refine ⟨93386217023730557084416247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62257478015820371389610831 93386217023730557084416247)
          ·
            refine ⟨140079325535595835626624371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93386217023730557084416247 140079325535595835626624371)
            ·
              refine ⟨210118988303393753439936557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140079325535595835626624371 210118988303393753439936557)
              ·
                refine ⟨78794620613772657539976209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210118988303393753439936557 78794620613772657539976209)
                ·
                  refine ⟨59095965460329493154982157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78794620613772657539976209 59095965460329493154982157)
                  ·
                    refine ⟨22160987047623559933118309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59095965460329493154982157 22160987047623559933118309)
                    ·
                      refine ⟨4155185071429417487459683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22160987047623559933118309 4155185071429417487459683)
                      ·
                        rfl

theorem cell23_8092194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_8092194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092194 prefixEnd_8092194 := by exact prefixLift 8092194
  have htrace : WordTrace (prefixWord ++ tailWord_8092194) baseStart_8092194 baseEnd_8092194 := by
    simpa [prefixWord, tailWord_8092194, baseEnd_8092194] using wordTrace_append hprefix tailTrace_8092194
  have hstable : (prefixWord ++ tailWord_8092194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092194).length < 2 ^ (prefixWord ++ tailWord_8092194).sum := by decide
  have hdescent : baseEnd_8092194 < baseStart_8092194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092199 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 2, 4]
def baseStart_8092199 : Nat := 118140960795 + 8092199 * 2 ^ 59
def prefixEnd_8092199 : Nat := 4983230072969 + 3 ^ 40 * 8092199 * 2
def baseEnd_8092199 : Nat := 1385062546277563322632387

theorem tailTrace_8092199 : CollatzResearch.WordTrace tailWord_8092199 prefixEnd_8092199 1385062546277563322632387 := by
  unfold tailWord_8092199
  simp only [CollatzResearch.WordTrace]
  refine ⟨295146744810352535404679651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196764496540235023603119767 295146744810352535404679651)
  ·
    refine ⟨442720117215528803107019477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295146744810352535404679651 442720117215528803107019477)
    ·
      refine ⟨10376252747238956322820769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 442720117215528803107019477 10376252747238956322820769)
      ·
        refine ⟨7782189560429217242115577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10376252747238956322820769 7782189560429217242115577)
        ·
          refine ⟨5836642170321912931586683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7782189560429217242115577 5836642170321912931586683)
          ·
            refine ⟨8754963255482869397380025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836642170321912931586683 8754963255482869397380025)
            ·
              refine ⟨6566222441612152048035019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8754963255482869397380025 6566222441612152048035019)
              ·
                refine ⟨9849333662418228072052529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6566222441612152048035019 9849333662418228072052529)
                ·
                  refine ⟨7387000246813671054039397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9849333662418228072052529 7387000246813671054039397)
                  ·
                    refine ⟨1385062546277563322632387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7387000246813671054039397 1385062546277563322632387)
                    ·
                      rfl

theorem cell23_8092199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_8092199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092199 prefixEnd_8092199 := by exact prefixLift 8092199
  have htrace : WordTrace (prefixWord ++ tailWord_8092199) baseStart_8092199 baseEnd_8092199 := by
    simpa [prefixWord, tailWord_8092199, baseEnd_8092199] using wordTrace_append hprefix tailTrace_8092199
  have hstable : (prefixWord ++ tailWord_8092199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092199).length < 2 ^ (prefixWord ++ tailWord_8092199).sum := by decide
  have hdescent : baseEnd_8092199 < baseStart_8092199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092207 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_8092207 : Nat := 118140960795 + 8092207 * 2 ^ 59
def prefixEnd_8092207 : Nat := 4983230072969 + 3 ^ 40 * 8092207 * 2
def baseEnd_8092207 : Nat := 4155191746677925936597123

theorem tailTrace_8092207 : CollatzResearch.WordTrace tailWord_8092207 prefixEnd_8092207 4155191746677925936597123 := by
  unfold tailWord_8092207
  simp only [CollatzResearch.WordTrace]
  refine ⟨295147036594323552770970875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196764691062882368513980583 295147036594323552770970875)
  ·
    refine ⟨442720554891485329156456313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295147036594323552770970875 442720554891485329156456313)
    ·
      refine ⟨332040416168613996867342235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442720554891485329156456313 332040416168613996867342235)
      ·
        refine ⟨498060624252920995301013353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332040416168613996867342235 498060624252920995301013353)
        ·
          refine ⟨373545468189690746475760015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498060624252920995301013353 373545468189690746475760015)
          ·
            refine ⟨560318202284536119713640023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373545468189690746475760015 560318202284536119713640023)
            ·
              refine ⟨840477303426804179570460035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560318202284536119713640023 840477303426804179570460035)
              ·
                refine ⟨1260715955140206269355690053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840477303426804179570460035 1260715955140206269355690053)
                ·
                  refine ⟨236384241588788675504191885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1260715955140206269355690053 236384241588788675504191885)
                  ·
                    refine ⟨88644090595795753314071957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236384241588788675504191885 88644090595795753314071957)
                    ·
                      refine ⟨4155191746677925936597123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88644090595795753314071957 4155191746677925936597123)
                      ·
                        rfl

theorem cell23_8092207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_8092207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092207 prefixEnd_8092207 := by exact prefixLift 8092207
  have htrace : WordTrace (prefixWord ++ tailWord_8092207) baseStart_8092207 baseEnd_8092207 := by
    simpa [prefixWord, tailWord_8092207, baseEnd_8092207] using wordTrace_append hprefix tailTrace_8092207
  have hstable : (prefixWord ++ tailWord_8092207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092207).length < 2 ^ (prefixWord ++ tailWord_8092207).sum := by decide
  have hdescent : baseEnd_8092207 < baseStart_8092207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092211 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 1, 4, 2]
def baseStart_8092211 : Nat := 118140960795 + 8092211 * 2 ^ 59
def prefixEnd_8092211 : Nat := 4983230072969 + 3 ^ 40 * 8092211 * 2
def baseEnd_8092211 : Nat := 4155193800600543920947105

theorem tailTrace_8092211 : CollatzResearch.WordTrace tailWord_8092211 prefixEnd_8092211 4155193800600543920947105 := by
  unfold tailWord_8092211
  simp only [CollatzResearch.WordTrace]
  refine ⟨295147182486309061454116487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196764788324206040969410991 295147182486309061454116487)
  ·
    refine ⟨442720773729463592181174731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295147182486309061454116487 442720773729463592181174731)
    ·
      refine ⟨664081160594195388271762097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442720773729463592181174731 664081160594195388271762097)
      ·
        refine ⟨498060870445646541203821573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664081160594195388271762097 498060870445646541203821573)
        ·
          refine ⟨93386413208558726475716545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 498060870445646541203821573 93386413208558726475716545)
          ·
            refine ⟨70039809906419044856787409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93386413208558726475716545 70039809906419044856787409)
            ·
              refine ⟨52529857429814283642590557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70039809906419044856787409 52529857429814283642590557)
              ·
                refine ⟨19698696536180356365971459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52529857429814283642590557 19698696536180356365971459)
                ·
                  refine ⟨29548044804270534548957189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19698696536180356365971459 29548044804270534548957189)
                  ·
                    refine ⟨5540258400800725227929473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29548044804270534548957189 5540258400800725227929473)
                    ·
                      refine ⟨4155193800600543920947105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540258400800725227929473 4155193800600543920947105)
                      ·
                        rfl

theorem cell23_8092211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 4, 2].length) (baseStart_8092211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092211 prefixEnd_8092211 := by exact prefixLift 8092211
  have htrace : WordTrace (prefixWord ++ tailWord_8092211) baseStart_8092211 baseEnd_8092211 := by
    simpa [prefixWord, tailWord_8092211, baseEnd_8092211] using wordTrace_append hprefix tailTrace_8092211
  have hstable : (prefixWord ++ tailWord_8092211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092211).length < 2 ^ (prefixWord ++ tailWord_8092211).sum := by decide
  have hdescent : baseEnd_8092211 < baseStart_8092211 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092281 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 2, 5]
def baseStart_8092281 : Nat := 118140960795 + 8092281 * 2 ^ 59
def prefixEnd_8092281 : Nat := 4983230072969 + 3 ^ 40 * 8092281 * 2
def baseEnd_8092281 : Nat := 1385076581415452882357261

theorem tailTrace_8092281 : CollatzResearch.WordTrace tailWord_8092281 prefixEnd_8092281 1385076581415452882357261 := by
  unfold tailWord_8092281
  simp only [CollatzResearch.WordTrace]
  refine ⟨295149735596055463409164697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196766490397370308939443131 295149735596055463409164697)
  ·
    refine ⟨221362301697041597556873523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295149735596055463409164697 221362301697041597556873523)
    ·
      refine ⟨332043452545562396335310285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221362301697041597556873523 332043452545562396335310285)
      ·
        refine ⟨124516294704585898625741357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332043452545562396335310285 124516294704585898625741357)
        ·
          refine ⟨46693610514219711984653009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124516294704585898625741357 46693610514219711984653009)
          ·
            refine ⟨35020207885664783988489757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46693610514219711984653009 35020207885664783988489757)
            ·
              refine ⟨13132577957124293995683659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35020207885664783988489757 13132577957124293995683659)
              ·
                refine ⟨19698866935686440993525489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13132577957124293995683659 19698866935686440993525489)
                ·
                  refine ⟨14774150201764830745144117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19698866935686440993525489 14774150201764830745144117)
                  ·
                    refine ⟨1385076581415452882357261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14774150201764830745144117 1385076581415452882357261)
                    ·
                      rfl

theorem cell23_8092281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_8092281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092281 prefixEnd_8092281 := by exact prefixLift 8092281
  have htrace : WordTrace (prefixWord ++ tailWord_8092281) baseStart_8092281 baseEnd_8092281 := by
    simpa [prefixWord, tailWord_8092281, baseEnd_8092281] using wordTrace_append hprefix tailTrace_8092281
  have hstable : (prefixWord ++ tailWord_8092281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092281).length < 2 ^ (prefixWord ++ tailWord_8092281).sum := by decide
  have hdescent : baseEnd_8092281 < baseStart_8092281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092341 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 8]
def baseStart_8092341 : Nat := 118140960795 + 8092341 * 2 ^ 59
def prefixEnd_8092341 : Nat := 4983230072969 + 3 ^ 40 * 8092341 * 2
def baseEnd_8092341 : Nat := 461695617009514268035723

theorem tailTrace_8092341 : CollatzResearch.WordTrace tailWord_8092341 prefixEnd_8092341 461695617009514268035723 := by
  unfold tailWord_8092341
  simp only [CollatzResearch.WordTrace]
  refine ⟨295151923975838093656348877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196767949317225395770899251 295151923975838093656348877)
  ·
    refine ⟨110681971490939285121130829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295151923975838093656348877 110681971490939285121130829)
    ·
      refine ⟨41505739309102231920424061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110681971490939285121130829 41505739309102231920424061)
      ·
        refine ⟨15564652240913336970159023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41505739309102231920424061 15564652240913336970159023)
        ·
          refine ⟨23346978361370005455238535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15564652240913336970159023 23346978361370005455238535)
          ·
            refine ⟨35020467542055008182857803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23346978361370005455238535 35020467542055008182857803)
            ·
              refine ⟨52530701313082512274286705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35020467542055008182857803 52530701313082512274286705)
              ·
                refine ⟨39398025984811884205715029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52530701313082512274286705 39398025984811884205715029)
                ·
                  refine ⟨461695617009514268035723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39398025984811884205715029 461695617009514268035723)
                  ·
                    rfl

theorem cell23_8092341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_8092341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092341 prefixEnd_8092341 := by exact prefixLift 8092341
  have htrace : WordTrace (prefixWord ++ tailWord_8092341) baseStart_8092341 baseEnd_8092341 := by
    simpa [prefixWord, tailWord_8092341, baseEnd_8092341] using wordTrace_append hprefix tailTrace_8092341
  have hstable : (prefixWord ++ tailWord_8092341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092341).length < 2 ^ (prefixWord ++ tailWord_8092341).sum := by decide
  have hdescent : baseEnd_8092341 < baseStart_8092341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092361 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 9, 2]
def baseStart_8092361 : Nat := 118140960795 + 8092361 * 2 ^ 59
def prefixEnd_8092361 : Nat := 4983230072969 + 3 ^ 40 * 8092361 * 2
def baseEnd_8092361 : Nat := 4155270822698718334071415

theorem tailTrace_8092361 : CollatzResearch.WordTrace tailWord_8092361 prefixEnd_8092361 4155270822698718334071415 := by
  unfold tailWord_8092361
  simp only [CollatzResearch.WordTrace]
  refine ⟨295152653435765637072076937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196768435623843758048051291 295152653435765637072076937)
  ·
    refine ⟨221364490076824227804057703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295152653435765637072076937 221364490076824227804057703)
    ·
      refine ⟨332046735115236341706086555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221364490076824227804057703 332046735115236341706086555)
      ·
        refine ⟨498070102672854512559129833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332046735115236341706086555 498070102672854512559129833)
        ·
          refine ⟨373552577004640884419347375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498070102672854512559129833 373552577004640884419347375)
          ·
            refine ⟨560328865506961326629021063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373552577004640884419347375 560328865506961326629021063)
            ·
              refine ⟨840493298260441989943531595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560328865506961326629021063 840493298260441989943531595)
              ·
                refine ⟨1260739947390662984915297393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840493298260441989943531595 1260739947390662984915297393)
                ·
                  refine ⟨945554960542997238686473045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1260739947390662984915297393 945554960542997238686473045)
                  ·
                    refine ⟨5540361096931624445428553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 945554960542997238686473045 5540361096931624445428553)
                    ·
                      refine ⟨4155270822698718334071415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540361096931624445428553 4155270822698718334071415)
                      ·
                        rfl

theorem cell23_8092361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 9, 2].length) (baseStart_8092361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092361 prefixEnd_8092361 := by exact prefixLift 8092361
  have htrace : WordTrace (prefixWord ++ tailWord_8092361) baseStart_8092361 baseEnd_8092361 := by
    simpa [prefixWord, tailWord_8092361, baseEnd_8092361] using wordTrace_append hprefix tailTrace_8092361
  have hstable : (prefixWord ++ tailWord_8092361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092361).length < 2 ^ (prefixWord ++ tailWord_8092361).sum := by decide
  have hdescent : baseEnd_8092361 < baseStart_8092361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092362 : List Nat := [3, 1, 2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_8092362 : Nat := 118140960795 + 8092362 * 2 ^ 59
def prefixEnd_8092362 : Nat := 4983230072969 + 3 ^ 40 * 8092362 * 2
def baseEnd_8092362 : Nat := 1385090445393124276719637

theorem tailTrace_8092362 : CollatzResearch.WordTrace tailWord_8092362 prefixEnd_8092362 1385090445393124276719637 := by
  unfold tailWord_8092362
  simp only [CollatzResearch.WordTrace]
  refine ⟨73788172477190503560715835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196768459939174676161908893 73788172477190503560715835)
  ·
    refine ⟨110682258715785755341073753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73788172477190503560715835 110682258715785755341073753)
    ·
      refine ⟨83011694036839316505805315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110682258715785755341073753 83011694036839316505805315)
      ·
        refine ⟨124517541055258974758707973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83011694036839316505805315 124517541055258974758707973)
        ·
          refine ⟨23347038947861057767257745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124517541055258974758707973 23347038947861057767257745)
          ·
            refine ⟨17510279210895793325443309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23347038947861057767257745 17510279210895793325443309)
            ·
              refine ⟨6566354704085922497041241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17510279210895793325443309 6566354704085922497041241)
              ·
                refine ⟨4924766028064441872780931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6566354704085922497041241 4924766028064441872780931)
                ·
                  refine ⟨7387149042096662809171397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924766028064441872780931 7387149042096662809171397)
                  ·
                    refine ⟨1385090445393124276719637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7387149042096662809171397 1385090445393124276719637)
                    ·
                      rfl

theorem cell23_8092362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_8092362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092362 prefixEnd_8092362 := by exact prefixLift 8092362
  have htrace : WordTrace (prefixWord ++ tailWord_8092362) baseStart_8092362 baseEnd_8092362 := by
    simpa [prefixWord, tailWord_8092362, baseEnd_8092362] using wordTrace_append hprefix tailTrace_8092362
  have hstable : (prefixWord ++ tailWord_8092362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092362).length < 2 ^ (prefixWord ++ tailWord_8092362).sum := by decide
  have hdescent : baseEnd_8092362 < baseStart_8092362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092378 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2]
def baseStart_8092378 : Nat := 118140960795 + 8092378 * 2 ^ 59
def prefixEnd_8092378 : Nat := 4983230072969 + 3 ^ 40 * 8092378 * 2
def baseEnd_8092378 : Nat := 4155279551869844767558837

theorem tailTrace_8092378 : CollatzResearch.WordTrace tailWord_8092378 prefixEnd_8092378 4155279551869844767558837 := by
  unfold tailWord_8092378
  simp only [CollatzResearch.WordTrace]
  refine ⟨73788318369176012243861447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196768848984469365983630525 73788318369176012243861447)
  ·
    refine ⟨110682477553764018365792171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73788318369176012243861447 110682477553764018365792171)
    ·
      refine ⟨166023716330646027548688257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110682477553764018365792171 166023716330646027548688257)
      ·
        refine ⟨124517787247984520661516193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166023716330646027548688257 124517787247984520661516193)
        ·
          refine ⟨93388340435988390496137145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124517787247984520661516193 93388340435988390496137145)
          ·
            refine ⟨70041255326991292872102859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93388340435988390496137145 70041255326991292872102859)
            ·
              refine ⟨105061882990486939308154289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70041255326991292872102859 105061882990486939308154289)
              ·
                refine ⟨78796412242865204481115717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105061882990486939308154289 78796412242865204481115717)
                ·
                  refine ⟨14774327295537225840209197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78796412242865204481115717 14774327295537225840209197)
                  ·
                    refine ⟨5540372735826459690078449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14774327295537225840209197 5540372735826459690078449)
                    ·
                      refine ⟨4155279551869844767558837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540372735826459690078449 4155279551869844767558837)
                      ·
                        rfl

theorem cell23_8092378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_8092378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092378 prefixEnd_8092378 := by exact prefixLift 8092378
  have htrace : WordTrace (prefixWord ++ tailWord_8092378) baseStart_8092378 baseEnd_8092378 := by
    simpa [prefixWord, tailWord_8092378, baseEnd_8092378] using wordTrace_append hprefix tailTrace_8092378
  have hstable : (prefixWord ++ tailWord_8092378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092378).length < 2 ^ (prefixWord ++ tailWord_8092378).sum := by decide
  have hdescent : baseEnd_8092378 < baseStart_8092378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092388 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_8092388 : Nat := 118140960795 + 8092388 * 2 ^ 59
def prefixEnd_8092388 : Nat := 4983230072969 + 3 ^ 40 * 8092388 * 2
def baseEnd_8092388 : Nat := 1385094895558796576144597

theorem tailTrace_8092388 : CollatzResearch.WordTrace tailWord_8092388 prefixEnd_8092388 1385094895558796576144597 := by
  unfold tailWord_8092388
  simp only [CollatzResearch.WordTrace]
  refine ⟨147576819103333910341654909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196769092137778547122206545 147576819103333910341654909)
  ·
    refine ⟨55341307163750216378120591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147576819103333910341654909 55341307163750216378120591)
    ·
      refine ⟨83011960745625324567180887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55341307163750216378120591 83011960745625324567180887)
      ·
        refine ⟨124517941118437986850771331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83011960745625324567180887 124517941118437986850771331)
        ·
          refine ⟨186776911677656980276156997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124517941118437986850771331 186776911677656980276156997)
          ·
            refine ⟨35020670939560683801779437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186776911677656980276156997 35020670939560683801779437)
            ·
              refine ⟨13132751602335256425667289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35020670939560683801779437 13132751602335256425667289)
              ·
                refine ⟨9849563701751442319250467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13132751602335256425667289 9849563701751442319250467)
                ·
                  refine ⟨14774345552627163478875701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9849563701751442319250467 14774345552627163478875701)
                  ·
                    refine ⟨1385094895558796576144597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14774345552627163478875701 1385094895558796576144597)
                    ·
                      rfl

theorem cell23_8092388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_8092388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092388 prefixEnd_8092388 := by exact prefixLift 8092388
  have htrace : WordTrace (prefixWord ++ tailWord_8092388) baseStart_8092388 baseEnd_8092388 := by
    simpa [prefixWord, tailWord_8092388, baseEnd_8092388] using wordTrace_append hprefix tailTrace_8092388
  have hstable : (prefixWord ++ tailWord_8092388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092388).length < 2 ^ (prefixWord ++ tailWord_8092388).sum := by decide
  have hdescent : baseEnd_8092388 < baseStart_8092388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092401 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 1, 6]
def baseStart_8092401 : Nat := 118140960795 + 8092401 * 2 ^ 59
def prefixEnd_8092401 : Nat := 4983230072969 + 3 ^ 40 * 8092401 * 2
def baseEnd_8092401 : Nat := 1385097120641632725857077

theorem tailTrace_8092401 : CollatzResearch.WordTrace tailWord_8092401 prefixEnd_8092401 1385097120641632725857077 := by
  unfold tailWord_8092401
  simp only [CollatzResearch.WordTrace]
  refine ⟨295154112355620723903533057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196769408237080482602355371 295154112355620723903533057)
  ·
    refine ⟨221365584266715542927649793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295154112355620723903533057 221365584266715542927649793)
    ·
      refine ⟨166024188200036657195737345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221365584266715542927649793 166024188200036657195737345)
      ·
        refine ⟨124518141150027492896803009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166024188200036657195737345 124518141150027492896803009)
        ·
          refine ⟨93388605862520619672602257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124518141150027492896803009 93388605862520619672602257)
          ·
            refine ⟨70041454396890464754451693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93388605862520619672602257 70041454396890464754451693)
            ·
              refine ⟨26265545398833924282919385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70041454396890464754451693 26265545398833924282919385)
              ·
                refine ⟨19699159049125443212189539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26265545398833924282919385 19699159049125443212189539)
                ·
                  refine ⟨29548738573688164818284309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19699159049125443212189539 29548738573688164818284309)
                  ·
                    refine ⟨1385097120641632725857077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29548738573688164818284309 1385097120641632725857077)
                    ·
                      rfl

theorem cell23_8092401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_8092401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092401 prefixEnd_8092401 := by exact prefixLift 8092401
  have htrace : WordTrace (prefixWord ++ tailWord_8092401) baseStart_8092401 baseEnd_8092401 := by
    simpa [prefixWord, tailWord_8092401, baseEnd_8092401] using wordTrace_append hprefix tailTrace_8092401
  have hstable : (prefixWord ++ tailWord_8092401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092401).length < 2 ^ (prefixWord ++ tailWord_8092401).sum := by decide
  have hdescent : baseEnd_8092401 < baseStart_8092401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092448 : List Nat := [2, 1, 1, 5, 1, 3, 3, 7]
def baseStart_8092448 : Nat := 118140960795 + 8092448 * 2 ^ 59
def prefixEnd_8092448 : Nat := 4983230072969 + 3 ^ 40 * 8092448 * 2
def baseEnd_8092448 : Nat := 153900573907987388654945

theorem tailTrace_8092448 : CollatzResearch.WordTrace tailWord_8092448 prefixEnd_8092448 153900573907987388654945 := by
  unfold tailWord_8092448
  simp only [CollatzResearch.WordTrace]
  refine ⟨147577913293225225465246999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196770551057633633953662665 147577913293225225465246999)
  ·
    refine ⟨221366869939837838197870499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147577913293225225465246999 221366869939837838197870499)
    ·
      refine ⟨332050304909756757296805749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221366869939837838197870499 332050304909756757296805749)
      ·
        refine ⟨31129716085289695996575539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332050304909756757296805749 31129716085289695996575539)
        ·
          refine ⟨46694574127934543994863309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31129716085289695996575539 46694574127934543994863309)
          ·
            refine ⟨17510465297975453998073741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46694574127934543994863309 17510465297975453998073741)
            ·
              refine ⟨6566424486740795249277653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17510465297975453998073741 6566424486740795249277653)
              ·
                refine ⟨153900573907987388654945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6566424486740795249277653 153900573907987388654945)
                ·
                  rfl

theorem cell23_8092448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 7].length) (baseStart_8092448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092448 prefixEnd_8092448 := by exact prefixLift 8092448
  have htrace : WordTrace (prefixWord ++ tailWord_8092448) baseStart_8092448 baseEnd_8092448 := by
    simpa [prefixWord, tailWord_8092448, baseEnd_8092448] using wordTrace_append hprefix tailTrace_8092448
  have hstable : (prefixWord ++ tailWord_8092448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092448).length < 2 ^ (prefixWord ++ tailWord_8092448).sum := by decide
  have hdescent : baseEnd_8092448 < baseStart_8092448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092462 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_8092462 : Nat := 118140960795 + 8092462 * 2 ^ 59
def prefixEnd_8092462 : Nat := 4983230072969 + 3 ^ 40 * 8092462 * 2
def baseEnd_8092462 : Nat := 4155322684244822438908451

theorem tailTrace_8092462 : CollatzResearch.WordTrace tailWord_8092462 prefixEnd_8092462 4155322684244822438908451 := by
  unfold tailWord_8092462
  simp only [CollatzResearch.WordTrace]
  refine ⟨36894542151049966415187955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196770891472266487547669093 36894542151049966415187955)
  ·
    refine ⟨55341813226574949622781933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36894542151049966415187955 55341813226574949622781933)
    ·
      refine ⟨20753179959965606108543225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55341813226574949622781933 20753179959965606108543225)
      ·
        refine ⟨15564884969974204581407419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20753179959965606108543225 15564884969974204581407419)
        ·
          refine ⟨23347327454961306872111129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15564884969974204581407419 23347327454961306872111129)
          ·
            refine ⟨17510495591220980154083347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23347327454961306872111129 17510495591220980154083347)
            ·
              refine ⟨26265743386831470231125021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17510495591220980154083347 26265743386831470231125021)
              ·
                refine ⟨9849653770061801336671883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26265743386831470231125021 9849653770061801336671883)
                ·
                  refine ⟨14774480655092702005007825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9849653770061801336671883 14774480655092702005007825)
                  ·
                    refine ⟨11080860491319526503755869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14774480655092702005007825 11080860491319526503755869)
                    ·
                      refine ⟨4155322684244822438908451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11080860491319526503755869 4155322684244822438908451)
                      ·
                        rfl

theorem cell23_8092462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_8092462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092462 prefixEnd_8092462 := by exact prefixLift 8092462
  have htrace : WordTrace (prefixWord ++ tailWord_8092462) baseStart_8092462 baseEnd_8092462 := by
    simpa [prefixWord, tailWord_8092462, baseEnd_8092462] using wordTrace_append hprefix tailTrace_8092462
  have hstable : (prefixWord ++ tailWord_8092462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092462).length < 2 ^ (prefixWord ++ tailWord_8092462).sum := by decide
  have hdescent : baseEnd_8092462 < baseStart_8092462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092486 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_8092486 : Nat := 118140960795 + 8092486 * 2 ^ 59
def prefixEnd_8092486 : Nat := 4983230072969 + 3 ^ 40 * 8092486 * 2
def baseEnd_8092486 : Nat := 1385111669260176781669447

theorem tailTrace_8092486 : CollatzResearch.WordTrace tailWord_8092486 prefixEnd_8092486 1385111669260176781669447 := by
  unfold tailWord_8092486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9223662892509774481886791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196771475040208522280251541 9223662892509774481886791)
  ·
    refine ⟨13835494338764661722830187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9223662892509774481886791 13835494338764661722830187)
    ·
      refine ⟨20753241508146992584245281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13835494338764661722830187 20753241508146992584245281)
      ·
        refine ⟨15564931131110244438183961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20753241508146992584245281 15564931131110244438183961)
        ·
          refine ⟨11673698348332683328637971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15564931131110244438183961 11673698348332683328637971)
          ·
            refine ⟨17510547522499024992956957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11673698348332683328637971 17510547522499024992956957)
            ·
              refine ⟨6566455320937134372358859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17510547522499024992956957 6566455320937134372358859)
              ·
                refine ⟨9849682981405701558538289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6566455320937134372358859 9849682981405701558538289)
                ·
                  refine ⟨7387262236054276168903717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9849682981405701558538289 7387262236054276168903717)
                  ·
                    refine ⟨1385111669260176781669447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7387262236054276168903717 1385111669260176781669447)
                    ·
                      rfl

theorem cell23_8092486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_8092486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092486 prefixEnd_8092486 := by exact prefixLift 8092486
  have htrace : WordTrace (prefixWord ++ tailWord_8092486) baseStart_8092486 baseEnd_8092486 := by
    simpa [prefixWord, tailWord_8092486, baseEnd_8092486] using wordTrace_append hprefix tailTrace_8092486
  have hstable : (prefixWord ++ tailWord_8092486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092486).length < 2 ^ (prefixWord ++ tailWord_8092486).sum := by decide
  have hdescent : baseEnd_8092486 < baseStart_8092486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092548 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_8092548 : Nat := 118140960795 + 8092548 * 2 ^ 59
def prefixEnd_8092548 : Nat := 4983230072969 + 3 ^ 40 * 8092548 * 2
def baseEnd_8092548 : Nat := 4155366843581109102433055

theorem tailTrace_8092548 : CollatzResearch.WordTrace tailWord_8092548 prefixEnd_8092548 4155366843581109102433055 := by
  unfold tailWord_8092548
  simp only [CollatzResearch.WordTrace]
  refine ⟨147579736943044084004567149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196772982590725445339422865 147579736943044084004567149)
  ·
    refine ⟨55342401353641531501712681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147579736943044084004567149 55342401353641531501712681)
    ·
      refine ⟨41506801015231148626284511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55342401353641531501712681 41506801015231148626284511)
      ·
        refine ⟨62260201522846722939426767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41506801015231148626284511 62260201522846722939426767)
        ·
          refine ⟨93390302284270084409140151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62260201522846722939426767 93390302284270084409140151)
          ·
            refine ⟨140085453426405126613710227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93390302284270084409140151 140085453426405126613710227)
            ·
              refine ⟨210128180139607689920565341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140085453426405126613710227 210128180139607689920565341)
              ·
                refine ⟨78798067552352883720212003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210128180139607689920565341 78798067552352883720212003)
                ·
                  refine ⟨118197101328529325580318005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78798067552352883720212003 118197101328529325580318005)
                  ·
                    refine ⟨11080978249549624273154813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118197101328529325580318005 11080978249549624273154813)
                    ·
                      refine ⟨4155366843581109102433055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11080978249549624273154813 4155366843581109102433055)
                      ·
                        rfl

theorem cell23_8092548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_8092548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092548 prefixEnd_8092548 := by exact prefixLift 8092548
  have htrace : WordTrace (prefixWord ++ tailWord_8092548) baseStart_8092548 baseEnd_8092548 := by
    simpa [prefixWord, tailWord_8092548, baseEnd_8092548] using wordTrace_append hprefix tailTrace_8092548
  have hstable : (prefixWord ++ tailWord_8092548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092548).length < 2 ^ (prefixWord ++ tailWord_8092548).sum := by decide
  have hdescent : baseEnd_8092548 < baseStart_8092548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092549 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 2, 2, 2]
def baseStart_8092549 : Nat := 118140960795 + 8092549 * 2 ^ 59
def prefixEnd_8092549 : Nat := 4983230072969 + 3 ^ 40 * 8092549 * 2
def baseEnd_8092549 : Nat := 4155367357061763598520551

theorem tailTrace_8092549 : CollatzResearch.WordTrace tailWord_8092549 prefixEnd_8092549 4155367357061763598520551 := by
  unfold tailWord_8092549
  simp only [CollatzResearch.WordTrace]
  refine ⟨295159510359084545179920701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196773006906056363453280467 295159510359084545179920701)
  ·
    refine ⟨110684816384656704442470263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295159510359084545179920701 110684816384656704442470263)
    ·
      refine ⟨166027224576985056663705395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110684816384656704442470263 166027224576985056663705395)
      ·
        refine ⟨249040836865477584995558093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166027224576985056663705395 249040836865477584995558093)
        ·
          refine ⟨93390313824554094373334285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249040836865477584995558093 93390313824554094373334285)
          ·
            refine ⟨35021367684207785390000357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93390313824554094373334285 35021367684207785390000357)
            ·
              refine ⟨6566506440788959760625067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35021367684207785390000357 6566506440788959760625067)
              ·
                refine ⟨9849759661183439640937601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6566506440788959760625067 9849759661183439640937601)
                ·
                  refine ⟨7387319745887579730703201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9849759661183439640937601 7387319745887579730703201)
                  ·
                    refine ⟨5540489809415684798027401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7387319745887579730703201 5540489809415684798027401)
                    ·
                      refine ⟨4155367357061763598520551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540489809415684798027401 4155367357061763598520551)
                      ·
                        rfl

theorem cell23_8092549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_8092549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092549 prefixEnd_8092549 := by exact prefixLift 8092549
  have htrace : WordTrace (prefixWord ++ tailWord_8092549) baseStart_8092549 baseEnd_8092549 := by
    simpa [prefixWord, tailWord_8092549, baseEnd_8092549] using wordTrace_append hprefix tailTrace_8092549
  have hstable : (prefixWord ++ tailWord_8092549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092549).length < 2 ^ (prefixWord ++ tailWord_8092549).sum := by decide
  have hdescent : baseEnd_8092549 < baseStart_8092549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092561 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_8092561 : Nat := 118140960795 + 8092561 * 2 ^ 59
def prefixEnd_8092561 : Nat := 4983230072969 + 3 ^ 40 * 8092561 * 2
def baseEnd_8092561 : Nat := 4155373518829617551570495

theorem tailTrace_8092561 : CollatzResearch.WordTrace tailWord_8092561 prefixEnd_8092561 4155373518829617551570495 := by
  unfold tailWord_8092561
  simp only [CollatzResearch.WordTrace]
  refine ⟨295159948035041071229357537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196773298690027380819571691 295159948035041071229357537)
  ·
    refine ⟨221369961026280803422018153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295159948035041071229357537 221369961026280803422018153)
    ·
      refine ⟨166027470769710602566513615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221369961026280803422018153 166027470769710602566513615)
      ·
        refine ⟨249041206154565903849770423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166027470769710602566513615 249041206154565903849770423)
        ·
          refine ⟨373561809231848855774655635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249041206154565903849770423 373561809231848855774655635)
          ·
            refine ⟨560342713847773283661983453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373561809231848855774655635 560342713847773283661983453)
            ·
              refine ⟨210128517692914981373243795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 560342713847773283661983453 210128517692914981373243795)
              ·
                refine ⟨315192776539372472059865693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210128517692914981373243795 315192776539372472059865693)
                ·
                  refine ⟨118197291202264677022449635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315192776539372472059865693 118197291202264677022449635)
                  ·
                    refine ⟨177295936803397015533674453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118197291202264677022449635 177295936803397015533674453)
                    ·
                      refine ⟨4155373518829617551570495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177295936803397015533674453 4155373518829617551570495)
                      ·
                        rfl

theorem cell23_8092561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_8092561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092561 prefixEnd_8092561 := by exact prefixLift 8092561
  have htrace : WordTrace (prefixWord ++ tailWord_8092561) baseStart_8092561 baseEnd_8092561 := by
    simpa [prefixWord, tailWord_8092561, baseEnd_8092561] using wordTrace_append hprefix tailTrace_8092561
  have hstable : (prefixWord ++ tailWord_8092561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092561).length < 2 ^ (prefixWord ++ tailWord_8092561).sum := by decide
  have hdescent : baseEnd_8092561 < baseStart_8092561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092566 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_8092566 : Nat := 118140960795 + 8092566 * 2 ^ 59
def prefixEnd_8092566 : Nat := 4983230072969 + 3 ^ 40 * 8092566 * 2
def baseEnd_8092566 : Nat := 4155376086232890032007973

theorem tailTrace_8092566 : CollatzResearch.WordTrace tailWord_8092566 prefixEnd_8092566 4155376086232890032007973 := by
  unfold tailWord_8092566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18447508150001434817705597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196773420266681971388859701 18447508150001434817705597)
  ·
    refine ⟨6917815556250538056639599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18447508150001434817705597 6917815556250538056639599)
    ·
      refine ⟨10376723334375807084959399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6917815556250538056639599 10376723334375807084959399)
      ·
        refine ⟨15565085001563710627439099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10376723334375807084959399 15565085001563710627439099)
        ·
          refine ⟨23347627502345565941158649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15565085001563710627439099 23347627502345565941158649)
          ·
            refine ⟨17510720626759174455868987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23347627502345565941158649 17510720626759174455868987)
            ·
              refine ⟨26266080940138761683803481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17510720626759174455868987 26266080940138761683803481)
              ·
                refine ⟨19699560705104071262852611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26266080940138761683803481 19699560705104071262852611)
                ·
                  refine ⟨29549341057656106894278917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19699560705104071262852611 29549341057656106894278917)
                  ·
                    refine ⟨5540501448310520042677297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29549341057656106894278917 5540501448310520042677297)
                    ·
                      refine ⟨4155376086232890032007973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540501448310520042677297 4155376086232890032007973)
                      ·
                        rfl

theorem cell23_8092566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_8092566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092566 prefixEnd_8092566 := by exact prefixLift 8092566
  have htrace : WordTrace (prefixWord ++ tailWord_8092566) baseStart_8092566 baseEnd_8092566 := by
    simpa [prefixWord, tailWord_8092566, baseEnd_8092566] using wordTrace_append hprefix tailTrace_8092566
  have hstable : (prefixWord ++ tailWord_8092566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092566).length < 2 ^ (prefixWord ++ tailWord_8092566).sum := by decide
  have hdescent : baseEnd_8092566 < baseStart_8092566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092589 : List Nat := [1, 5, 2, 3, 1, 1, 1, 4, 5]
def baseStart_8092589 : Nat := 118140960795 + 8092589 * 2 ^ 59
def prefixEnd_8092589 : Nat := 4983230072969 + 3 ^ 40 * 8092589 * 2
def baseEnd_8092589 : Nat := 461709766254215938002263

theorem tailTrace_8092589 : CollatzResearch.WordTrace tailWord_8092589 prefixEnd_8092589 461709766254215938002263 := by
  unfold tailWord_8092589
  simp only [CollatzResearch.WordTrace]
  refine ⟨295160969278939632011376821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196773979519293088007584547 295160969278939632011376821)
  ·
    refine ⟨27671340869900590501066577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295160969278939632011376821 27671340869900590501066577)
    ·
      refine ⟨20753505652425442875799933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27671340869900590501066577 20753505652425442875799933)
      ·
        refine ⟨7782564619659541078424975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20753505652425442875799933 7782564619659541078424975)
        ·
          refine ⟨11673846929489311617637463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7782564619659541078424975 11673846929489311617637463)
          ·
            refine ⟨17510770394233967426456195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11673846929489311617637463 17510770394233967426456195)
            ·
              refine ⟨26266155591350951139684293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17510770394233967426456195 26266155591350951139684293)
              ·
                refine ⟨4924904173378303338690805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26266155591350951139684293 4924904173378303338690805)
                ·
                  refine ⟨461709766254215938002263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4924904173378303338690805 461709766254215938002263)
                  ·
                    rfl

theorem cell23_8092589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_8092589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092589 prefixEnd_8092589 := by exact prefixLift 8092589
  have htrace : WordTrace (prefixWord ++ tailWord_8092589) baseStart_8092589 baseEnd_8092589 := by
    simpa [prefixWord, tailWord_8092589, baseEnd_8092589] using wordTrace_append hprefix tailTrace_8092589
  have hstable : (prefixWord ++ tailWord_8092589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092589).length < 2 ^ (prefixWord ++ tailWord_8092589).sum := by decide
  have hdescent : baseEnd_8092589 < baseStart_8092589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092622 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_8092622 : Nat := 118140960795 + 8092622 * 2 ^ 59
def prefixEnd_8092622 : Nat := 4983230072969 + 3 ^ 40 * 8092622 * 2
def baseEnd_8092622 : Nat := 4155404841149541812907715

theorem tailTrace_8092622 : CollatzResearch.WordTrace tailWord_8092622 prefixEnd_8092622 4155404841149541812907715 := by
  unfold tailWord_8092622
  simp only [CollatzResearch.WordTrace]
  refine ⟨36895271610977509830916015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196774781925213385764885413 36895271610977509830916015)
  ·
    refine ⟨55342907416466264746374023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36895271610977509830916015 55342907416466264746374023)
    ·
      refine ⟨83014361124699397119561035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55342907416466264746374023 83014361124699397119561035)
      ·
        refine ⟨124521541687049095679341553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83014361124699397119561035 124521541687049095679341553)
        ·
          refine ⟨93391156265286821759506165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124521541687049095679341553 93391156265286821759506165)
          ·
            refine ⟨8755420899870639539953703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93391156265286821759506165 8755420899870639539953703)
            ·
              refine ⟨13133131349805959309930555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755420899870639539953703 13133131349805959309930555)
              ·
                refine ⟨19699697024708938964895833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13133131349805959309930555 19699697024708938964895833)
                ·
                  refine ⟨14774772768531704223671875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19699697024708938964895833 14774772768531704223671875)
                  ·
                    refine ⟨22162159152797556335507813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14774772768531704223671875 22162159152797556335507813)
                    ·
                      refine ⟨4155404841149541812907715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22162159152797556335507813 4155404841149541812907715)
                      ·
                        rfl

theorem cell23_8092622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_8092622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092622 prefixEnd_8092622 := by exact prefixLift 8092622
  have htrace : WordTrace (prefixWord ++ tailWord_8092622) baseStart_8092622 baseEnd_8092622 := by
    simpa [prefixWord, tailWord_8092622, baseEnd_8092622] using wordTrace_append hprefix tailTrace_8092622
  have hstable : (prefixWord ++ tailWord_8092622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092622).length < 2 ^ (prefixWord ++ tailWord_8092622).sum := by decide
  have hdescent : baseEnd_8092622 < baseStart_8092622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092632 : List Nat := [2, 1, 2, 2, 2, 3, 1, 5, 1, 4]
def baseStart_8092632 : Nat := 118140960795 + 8092632 * 2 ^ 59
def prefixEnd_8092632 : Nat := 4983230072969 + 3 ^ 40 * 8092632 * 2
def baseEnd_8092632 : Nat := 1385136658652028924594223

theorem tailTrace_8092632 : CollatzResearch.WordTrace tailWord_8092632 prefixEnd_8092632 1385136658652028924594223 := by
  unfold tailWord_8092632
  simp only [CollatzResearch.WordTrace]
  refine ⟨147581268808891925177596075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196775025078522566903461433 147581268808891925177596075)
  ·
    refine ⟨221371903213337887766394113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147581268808891925177596075 221371903213337887766394113)
    ·
      refine ⟨166028927410003415824795585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221371903213337887766394113 166028927410003415824795585)
      ·
        refine ⟨124521695557502561868596689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166028927410003415824795585 124521695557502561868596689)
        ·
          refine ⟨93391271668126921401447517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124521695557502561868596689 93391271668126921401447517)
          ·
            refine ⟨35021726875547595525542819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93391271668126921401447517 35021726875547595525542819)
            ·
              refine ⟨52532590313321393288314229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35021726875547595525542819 52532590313321393288314229)
              ·
                refine ⟨4924930341873880620779459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52532590313321393288314229 4924930341873880620779459)
                ·
                  refine ⟨7387395512810820931169189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924930341873880620779459 7387395512810820931169189)
                  ·
                    refine ⟨1385136658652028924594223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7387395512810820931169189 1385136658652028924594223)
                    ·
                      rfl

theorem cell23_8092632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_8092632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092632 prefixEnd_8092632 := by exact prefixLift 8092632
  have htrace : WordTrace (prefixWord ++ tailWord_8092632) baseStart_8092632 baseEnd_8092632 := by
    simpa [prefixWord, tailWord_8092632, baseEnd_8092632] using wordTrace_append hprefix tailTrace_8092632
  have hstable : (prefixWord ++ tailWord_8092632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092632).length < 2 ^ (prefixWord ++ tailWord_8092632).sum := by decide
  have hdescent : baseEnd_8092632 < baseStart_8092632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092648 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_8092648 : Nat := 118140960795 + 8092648 * 2 ^ 59
def prefixEnd_8092648 : Nat := 4983230072969 + 3 ^ 40 * 8092648 * 2
def baseEnd_8092648 : Nat := 4155418191646558711182595

theorem tailTrace_8092648 : CollatzResearch.WordTrace tailWord_8092648 prefixEnd_8092648 4155418191646558711182595 := by
  unfold tailWord_8092648
  simp only [CollatzResearch.WordTrace]
  refine ⟨147581560592862942543887299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196775414123817256725183065 147581560592862942543887299)
  ·
    refine ⟨221372340889294413815830949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147581560592862942543887299 221372340889294413815830949)
    ·
      refine ⟨41507313916742702590468303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221372340889294413815830949 41507313916742702590468303)
      ·
        refine ⟨62260970875114053885702455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41507313916742702590468303 62260970875114053885702455)
        ·
          refine ⟨93391456312671080828553683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62260970875114053885702455 93391456312671080828553683)
          ·
            refine ⟨140087184469006621242830525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93391456312671080828553683 140087184469006621242830525)
            ·
              refine ⟨52532694175877482966061447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140087184469006621242830525 52532694175877482966061447)
              ·
                refine ⟨78799041263816224449092171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52532694175877482966061447 78799041263816224449092171)
                ·
                  refine ⟨118198561895724336673638257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78799041263816224449092171 118198561895724336673638257)
                  ·
                    refine ⟨88648921421793252505228693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118198561895724336673638257 88648921421793252505228693)
                    ·
                      refine ⟨4155418191646558711182595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88648921421793252505228693 4155418191646558711182595)
                      ·
                        rfl

theorem cell23_8092648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_8092648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092648 prefixEnd_8092648 := by exact prefixLift 8092648
  have htrace : WordTrace (prefixWord ++ tailWord_8092648) baseStart_8092648 baseEnd_8092648 := by
    simpa [prefixWord, tailWord_8092648, baseEnd_8092648] using wordTrace_append hprefix tailTrace_8092648
  have hstable : (prefixWord ++ tailWord_8092648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092648).length < 2 ^ (prefixWord ++ tailWord_8092648).sum := by decide
  have hdescent : baseEnd_8092648 < baseStart_8092648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092665 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 3, 5, 2]
def baseStart_8092665 : Nat := 118140960795 + 8092665 * 2 ^ 59
def prefixEnd_8092665 : Nat := 4983230072969 + 3 ^ 40 * 8092665 * 2
def baseEnd_8092665 : Nat := 4155426920817685144670017

theorem tailTrace_8092665 : CollatzResearch.WordTrace tailWord_8092665 prefixEnd_8092665 4155426920817685144670017 := by
  unfold tailWord_8092665
  simp only [CollatzResearch.WordTrace]
  refine ⟨295163741226664296991143449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196775827484442864660762299 295163741226664296991143449)
  ·
    refine ⟨221372805919998222743357587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295163741226664296991143449 221372805919998222743357587)
    ·
      refine ⟨332059208879997334115036381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221372805919998222743357587 332059208879997334115036381)
      ·
        refine ⟨124522203329999000293138643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332059208879997334115036381 124522203329999000293138643)
        ·
          refine ⟨186783304994998500439707965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124522203329999000293138643 186783304994998500439707965)
          ·
            refine ⟨70043739373124437664890487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186783304994998500439707965 70043739373124437664890487)
            ·
              refine ⟨105065609059686656497335731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70043739373124437664890487 105065609059686656497335731)
              ·
                refine ⟨157598413589529984746003597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105065609059686656497335731 157598413589529984746003597)
                ·
                  refine ⟨59099405096073744279751349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157598413589529984746003597 59099405096073744279751349)
                  ·
                    refine ⟨5540569227756913526226689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59099405096073744279751349 5540569227756913526226689)
                    ·
                      refine ⟨4155426920817685144670017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540569227756913526226689 4155426920817685144670017)
                      ·
                        rfl

theorem cell23_8092665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_8092665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092665 prefixEnd_8092665 := by exact prefixLift 8092665
  have htrace : WordTrace (prefixWord ++ tailWord_8092665) baseStart_8092665 baseEnd_8092665 := by
    simpa [prefixWord, tailWord_8092665, baseEnd_8092665] using wordTrace_append hprefix tailTrace_8092665
  have hstable : (prefixWord ++ tailWord_8092665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092665).length < 2 ^ (prefixWord ++ tailWord_8092665).sum := by decide
  have hdescent : baseEnd_8092665 < baseStart_8092665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092682 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_8092682 : Nat := 118140960795 + 8092682 * 2 ^ 59
def prefixEnd_8092682 : Nat := 4983230072969 + 3 ^ 40 * 8092682 * 2
def baseEnd_8092682 : Nat := 4155435649988811578157439

theorem tailTrace_8092682 : CollatzResearch.WordTrace tailWord_8092682 prefixEnd_8092682 4155435649988811578157439 := by
  unfold tailWord_8092682
  simp only [CollatzResearch.WordTrace]
  refine ⟨73791090316900677223628075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196776240845068472596341533 73791090316900677223628075)
  ·
    refine ⟨110686635475351015835442113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73791090316900677223628075 110686635475351015835442113)
    ·
      refine ⟨83014976606513261876581585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110686635475351015835442113 83014976606513261876581585)
      ·
        refine ⟨62261232454884946407436189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83014976606513261876581585 62261232454884946407436189)
        ·
          refine ⟨23347962170581854902788571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62261232454884946407436189 23347962170581854902788571)
          ·
            refine ⟨35021943255872782354182857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23347962170581854902788571 35021943255872782354182857)
            ·
              refine ⟨26266457441904586765637143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35021943255872782354182857 26266457441904586765637143)
              ·
                refine ⟨39399686162856880148455715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26266457441904586765637143 39399686162856880148455715)
                ·
                  refine ⟨59099529244285320222683573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39399686162856880148455715 59099529244285320222683573)
                  ·
                    refine ⟨5540580866651748770876585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59099529244285320222683573 5540580866651748770876585)
                    ·
                      refine ⟨4155435649988811578157439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540580866651748770876585 4155435649988811578157439)
                      ·
                        rfl

theorem cell23_8092682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_8092682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092682 prefixEnd_8092682 := by exact prefixLift 8092682
  have htrace : WordTrace (prefixWord ++ tailWord_8092682) baseStart_8092682 baseEnd_8092682 := by
    simpa [prefixWord, tailWord_8092682, baseEnd_8092682] using wordTrace_append hprefix tailTrace_8092682
  have hstable : (prefixWord ++ tailWord_8092682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092682).length < 2 ^ (prefixWord ++ tailWord_8092682).sum := by decide
  have hdescent : baseEnd_8092682 < baseStart_8092682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092715 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 3]
def baseStart_8092715 : Nat := 118140960795 + 8092715 * 2 ^ 59
def prefixEnd_8092715 : Nat := 4983230072969 + 3 ^ 40 * 8092715 * 2
def baseEnd_8092715 : Nat := 4155452594850409949044787

theorem tailTrace_8092715 : CollatzResearch.WordTrace tailWord_8092715 prefixEnd_8092715 4155452594850409949044787 := by
  unfold tailWord_8092715
  simp only [CollatzResearch.WordTrace]
  refine ⟨295165564876483155530463599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196777043250988770353642399 295165564876483155530463599)
  ·
    refine ⟨442748347314724733295695399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295165564876483155530463599 442748347314724733295695399)
    ·
      refine ⟨664122520972087099943543099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442748347314724733295695399 664122520972087099943543099)
      ·
        refine ⟨996183781458130649915314649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664122520972087099943543099 996183781458130649915314649)
        ·
          refine ⟨747137836093597987436485987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996183781458130649915314649 747137836093597987436485987)
          ·
            refine ⟨1120706754140396981154728981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747137836093597987436485987 1120706754140396981154728981)
            ·
              refine ⟨52533129100331108491627921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1120706754140396981154728981 52533129100331108491627921)
              ·
                refine ⟨39399846825248331368720941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52533129100331108491627921 39399846825248331368720941)
                ·
                  refine ⟨14774942559468124263270353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39399846825248331368720941 14774942559468124263270353)
                  ·
                    refine ⟨11081206919601093197452765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14774942559468124263270353 11081206919601093197452765)
                    ·
                      refine ⟨4155452594850409949044787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11081206919601093197452765 4155452594850409949044787)
                      ·
                        rfl

theorem cell23_8092715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 3].length) (baseStart_8092715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092715 prefixEnd_8092715 := by exact prefixLift 8092715
  have htrace : WordTrace (prefixWord ++ tailWord_8092715) baseStart_8092715 baseEnd_8092715 := by
    simpa [prefixWord, tailWord_8092715, baseEnd_8092715] using wordTrace_append hprefix tailTrace_8092715
  have hstable : (prefixWord ++ tailWord_8092715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092715).length < 2 ^ (prefixWord ++ tailWord_8092715).sum := by decide
  have hdescent : baseEnd_8092715 < baseStart_8092715 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092722 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_8092722 : Nat := 118140960795 + 8092722 * 2 ^ 59
def prefixEnd_8092722 : Nat := 4983230072969 + 3 ^ 40 * 8092722 * 2
def baseEnd_8092722 : Nat := 1385152063071663807219085

theorem tailTrace_8092722 : CollatzResearch.WordTrace tailWord_8092722 prefixEnd_8092722 1385152063071663807219085 := by
  unfold tailWord_8092722
  simp only [CollatzResearch.WordTrace]
  refine ⟨73791455046864448931492105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196777213458305197150645613 73791455046864448931492105)
  ·
    refine ⟨55343591285148336698619079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73791455046864448931492105 55343591285148336698619079)
    ·
      refine ⟨83015386927722505047928619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55343591285148336698619079 83015386927722505047928619)
      ·
        refine ⟨124523080391583757571892929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83015386927722505047928619 124523080391583757571892929)
        ·
          refine ⟨93392310293687818178919697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124523080391583757571892929 93392310293687818178919697)
          ·
            refine ⟨70044232720265863634189773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93392310293687818178919697 70044232720265863634189773)
            ·
              refine ⟨26266587270099698862821165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70044232720265863634189773 26266587270099698862821165)
              ·
                refine ⟨9849970226287387073557937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26266587270099698862821165 9849970226287387073557937)
                ·
                  refine ⟨7387477669715540305168453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9849970226287387073557937 7387477669715540305168453)
                  ·
                    refine ⟨1385152063071663807219085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7387477669715540305168453 1385152063071663807219085)
                    ·
                      rfl

theorem cell23_8092722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_8092722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092722 prefixEnd_8092722 := by exact prefixLift 8092722
  have htrace : WordTrace (prefixWord ++ tailWord_8092722) baseStart_8092722 baseEnd_8092722 := by
    simpa [prefixWord, tailWord_8092722, baseEnd_8092722] using wordTrace_append hprefix tailTrace_8092722
  have hstable : (prefixWord ++ tailWord_8092722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092722).length < 2 ^ (prefixWord ++ tailWord_8092722).sum := by decide
  have hdescent : baseEnd_8092722 < baseStart_8092722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092725 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_8092725 : Nat := 118140960795 + 8092725 * 2 ^ 59
def prefixEnd_8092725 : Nat := 4983230072969 + 3 ^ 40 * 8092725 * 2
def baseEnd_8092725 : Nat := 4155457729656954909919741

theorem tailTrace_8092725 : CollatzResearch.WordTrace tailWord_8092725 prefixEnd_8092725 4155457729656954909919741 := by
  unfold tailWord_8092725
  simp only [CollatzResearch.WordTrace]
  refine ⟨295165929606446927238327629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196777286404297951492218419 295165929606446927238327629)
  ·
    refine ⟨110687223602417597714372861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295165929606446927238327629 110687223602417597714372861)
    ·
      refine ⟨41507708850906599142889823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110687223602417597714372861 41507708850906599142889823)
      ·
        refine ⟨62261563276359898714334735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41507708850906599142889823 62261563276359898714334735)
        ·
          refine ⟨93392344914539848071502103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62261563276359898714334735 93392344914539848071502103)
          ·
            refine ⟨140088517371809772107253155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93392344914539848071502103 140088517371809772107253155)
            ·
              refine ⟨210132776057714658160879733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140088517371809772107253155 210132776057714658160879733)
              ·
                refine ⟨19699947755410749202582475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210132776057714658160879733 19699947755410749202582475)
                ·
                  refine ⟨29549921633116123803873713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19699947755410749202582475 29549921633116123803873713)
                  ·
                    refine ⟨22162441224837092852905285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29549921633116123803873713 22162441224837092852905285)
                    ·
                      refine ⟨4155457729656954909919741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22162441224837092852905285 4155457729656954909919741)
                      ·
                        rfl

theorem cell23_8092725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_8092725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092725 prefixEnd_8092725 := by exact prefixLift 8092725
  have htrace : WordTrace (prefixWord ++ tailWord_8092725) baseStart_8092725 baseEnd_8092725 := by
    simpa [prefixWord, tailWord_8092725, baseEnd_8092725] using wordTrace_append hprefix tailTrace_8092725
  have hstable : (prefixWord ++ tailWord_8092725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092725).length < 2 ^ (prefixWord ++ tailWord_8092725).sum := by decide
  have hdescent : baseEnd_8092725 < baseStart_8092725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092729 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 4]
def baseStart_8092729 : Nat := 118140960795 + 8092729 * 2 ^ 59
def prefixEnd_8092729 : Nat := 4983230072969 + 3 ^ 40 * 8092729 * 2
def baseEnd_8092729 : Nat := 4155459783579572894269723

theorem tailTrace_8092729 : CollatzResearch.WordTrace tailWord_8092729 prefixEnd_8092729 4155459783579572894269723 := by
  unfold tailWord_8092729
  simp only [CollatzResearch.WordTrace]
  refine ⟨295166075498432435921473241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196777383665621623947648827 295166075498432435921473241)
  ·
    refine ⟨221374556623824326941104931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295166075498432435921473241 221374556623824326941104931)
    ·
      refine ⟨332061834935736490411657397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221374556623824326941104931 332061834935736490411657397)
      ·
        refine ⟨31130797025225295976092881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332061834935736490411657397 31130797025225295976092881)
        ·
          refine ⟨23348097768918971982069661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31130797025225295976092881 23348097768918971982069661)
          ·
            refine ⟨8755536663344614493276123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23348097768918971982069661 8755536663344614493276123)
            ·
              refine ⟨13133304995016921739914185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755536663344614493276123 13133304995016921739914185)
              ·
                refine ⟨9849978746262691304935639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13133304995016921739914185 9849978746262691304935639)
                ·
                  refine ⟨14774968119394036957403459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9849978746262691304935639 14774968119394036957403459)
                  ·
                    refine ⟨22162452179091055436105189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14774968119394036957403459 22162452179091055436105189)
                    ·
                      refine ⟨4155459783579572894269723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22162452179091055436105189 4155459783579572894269723)
                      ·
                        rfl

theorem cell23_8092729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_8092729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092729 prefixEnd_8092729 := by exact prefixLift 8092729
  have htrace : WordTrace (prefixWord ++ tailWord_8092729) baseStart_8092729 baseEnd_8092729 := by
    simpa [prefixWord, tailWord_8092729, baseEnd_8092729] using wordTrace_append hprefix tailTrace_8092729
  have hstable : (prefixWord ++ tailWord_8092729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092729).length < 2 ^ (prefixWord ++ tailWord_8092729).sum := by decide
  have hdescent : baseEnd_8092729 < baseStart_8092729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092732 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_8092732 : Nat := 118140960795 + 8092732 * 2 ^ 59
def prefixEnd_8092732 : Nat := 4983230072969 + 3 ^ 40 * 8092732 * 2
def baseEnd_8092732 : Nat := 4155461324021536382532209

theorem tailTrace_8092732 : CollatzResearch.WordTrace tailWord_8092732 prefixEnd_8092732 4155461324021536382532209 := by
  unfold tailWord_8092732
  simp only [CollatzResearch.WordTrace]
  refine ⟨147583092458710783716916225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196777456611614378289221633 147583092458710783716916225)
  ·
    refine ⟨110687319344033087787687169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147583092458710783716916225 110687319344033087787687169)
    ·
      refine ⟨83015489508024815840765377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110687319344033087787687169 83015489508024815840765377)
      ·
        refine ⟨62261617131018611880574033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83015489508024815840765377 62261617131018611880574033)
        ·
          refine ⟨46696212848263958910430525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62261617131018611880574033 46696212848263958910430525)
          ·
            refine ⟨17511079818098984591411447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46696212848263958910430525 17511079818098984591411447)
            ·
              refine ⟨26266619727148476887117171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17511079818098984591411447 26266619727148476887117171)
              ·
                refine ⟨39399929590722715330675757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26266619727148476887117171 39399929590722715330675757)
                ·
                  refine ⟨14774973596521018249003409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39399929590722715330675757 14774973596521018249003409)
                  ·
                    refine ⟨11081230197390763686752557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14774973596521018249003409 11081230197390763686752557)
                    ·
                      refine ⟨4155461324021536382532209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11081230197390763686752557 4155461324021536382532209)
                      ·
                        rfl

theorem cell23_8092732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_8092732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092732 prefixEnd_8092732 := by exact prefixLift 8092732
  have htrace : WordTrace (prefixWord ++ tailWord_8092732) baseStart_8092732 baseEnd_8092732 := by
    simpa [prefixWord, tailWord_8092732, baseEnd_8092732] using wordTrace_append hprefix tailTrace_8092732
  have hstable : (prefixWord ++ tailWord_8092732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092732).length < 2 ^ (prefixWord ++ tailWord_8092732).sum := by decide
  have hdescent : baseEnd_8092732 < baseStart_8092732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092749 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_8092749 : Nat := 118140960795 + 8092749 * 2 ^ 59
def prefixEnd_8092749 : Nat := 4983230072969 + 3 ^ 40 * 8092749 * 2
def baseEnd_8092749 : Nat := 4155470053192662816019631

theorem tailTrace_8092749 : CollatzResearch.WordTrace tailWord_8092749 prefixEnd_8092749 4155470053192662816019631 := by
  unfold tailWord_8092749
  simp only [CollatzResearch.WordTrace]
  refine ⟨295166804958359979337201301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196777869972239986224800867 295166804958359979337201301)
  ·
    refine ⟨13835943982423124031431311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 295166804958359979337201301 13835943982423124031431311)
    ·
      refine ⟨20753915973634686047146967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13835943982423124031431311 20753915973634686047146967)
      ·
        refine ⟨31130873960452029070720451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20753915973634686047146967 31130873960452029070720451)
        ·
          refine ⟨46696310940678043606080677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31130873960452029070720451 46696310940678043606080677)
          ·
            refine ⟨8755558301377133176140127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46696310940678043606080677 8755558301377133176140127)
            ·
              refine ⟨13133337452065699764210191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755558301377133176140127 13133337452065699764210191)
              ·
                refine ⟨19700006178098549646315287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13133337452065699764210191 19700006178098549646315287)
                ·
                  refine ⟨29550009267147824469472931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19700006178098549646315287 29550009267147824469472931)
                  ·
                    refine ⟨44325013900721736704209397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29550009267147824469472931 44325013900721736704209397)
                    ·
                      refine ⟨4155470053192662816019631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44325013900721736704209397 4155470053192662816019631)
                      ·
                        rfl

theorem cell23_8092749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_8092749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092749 prefixEnd_8092749 := by exact prefixLift 8092749
  have htrace : WordTrace (prefixWord ++ tailWord_8092749) baseStart_8092749 baseEnd_8092749 := by
    simpa [prefixWord, tailWord_8092749, baseEnd_8092749] using wordTrace_append hprefix tailTrace_8092749
  have hstable : (prefixWord ++ tailWord_8092749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092749).length < 2 ^ (prefixWord ++ tailWord_8092749).sum := by decide
  have hdescent : baseEnd_8092749 < baseStart_8092749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092766 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_8092766 : Nat := 118140960795 + 8092766 * 2 ^ 59
def prefixEnd_8092766 : Nat := 4983230072969 + 3 ^ 40 * 8092766 * 2
def baseEnd_8092766 : Nat := 4155478782363789249507053

theorem tailTrace_8092766 : CollatzResearch.WordTrace tailWord_8092766 prefixEnd_8092766 4155478782363789249507053 := by
  unfold tailWord_8092766
  simp only [CollatzResearch.WordTrace]
  refine ⟨36895928124912298905071269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196778283332865594160380101 36895928124912298905071269)
  ·
    refine ⟨6917986523421056044700863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36895928124912298905071269 6917986523421056044700863)
    ·
      refine ⟨10376979785131584067051295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6917986523421056044700863 10376979785131584067051295)
      ·
        refine ⟨15565469677697376100576943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10376979785131584067051295 15565469677697376100576943)
        ·
          refine ⟨23348204516546064150865415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15565469677697376100576943 23348204516546064150865415)
          ·
            refine ⟨35022306774819096226298123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23348204516546064150865415 35022306774819096226298123)
            ·
              refine ⟨52533460162228644339447185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35022306774819096226298123 52533460162228644339447185)
              ·
                refine ⟨39400095121671483254585389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52533460162228644339447185 39400095121671483254585389)
                ·
                  refine ⟨14775035670626806220469521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39400095121671483254585389 14775035670626806220469521)
                  ·
                    refine ⟨11081276752970104665352141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14775035670626806220469521 11081276752970104665352141)
                    ·
                      refine ⟨4155478782363789249507053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11081276752970104665352141 4155478782363789249507053)
                      ·
                        rfl

theorem cell23_8092766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_8092766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092766 prefixEnd_8092766 := by exact prefixLift 8092766
  have htrace : WordTrace (prefixWord ++ tailWord_8092766) baseStart_8092766 baseEnd_8092766 := by
    simpa [prefixWord, tailWord_8092766, baseEnd_8092766] using wordTrace_append hprefix tailTrace_8092766
  have hstable : (prefixWord ++ tailWord_8092766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092766).length < 2 ^ (prefixWord ++ tailWord_8092766).sum := by decide
  have hdescent : baseEnd_8092766 < baseStart_8092766 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092836 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_8092836 : Nat := 118140960795 + 8092836 * 2 ^ 59
def prefixEnd_8092836 : Nat := 4983230072969 + 3 ^ 40 * 8092836 * 2
def baseEnd_8092836 : Nat := 4155514726009603975631731

theorem tailTrace_8092836 : CollatzResearch.WordTrace tailWord_8092836 prefixEnd_8092836 4155514726009603975631731 := by
  unfold tailWord_8092836
  simp only [CollatzResearch.WordTrace]
  refine ⟨147584989054522396597809181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196779985406029862130412241 147584989054522396597809181)
  ·
    refine ⟨55344370895445898724178443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147584989054522396597809181 55344370895445898724178443)
    ·
      refine ⟨83016556343168848086267665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55344370895445898724178443 83016556343168848086267665)
      ·
        refine ⟨62262417257376636064700749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83016556343168848086267665 62262417257376636064700749)
        ·
          refine ⟨23348406471516238524262781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62262417257376636064700749 23348406471516238524262781)
          ·
            refine ⟨8755652426818589446598543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23348406471516238524262781 8755652426818589446598543)
            ·
              refine ⟨13133478640227884169897815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755652426818589446598543 13133478640227884169897815)
              ·
                refine ⟨19700217960341826254846723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13133478640227884169897815 19700217960341826254846723)
                ·
                  refine ⟨29550326940512739382270085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19700217960341826254846723 29550326940512739382270085)
                  ·
                    refine ⟨5540686301346138634175641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29550326940512739382270085 5540686301346138634175641)
                    ·
                      refine ⟨4155514726009603975631731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540686301346138634175641 4155514726009603975631731)
                      ·
                        rfl

theorem cell23_8092836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_8092836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092836 prefixEnd_8092836 := by exact prefixLift 8092836
  have htrace : WordTrace (prefixWord ++ tailWord_8092836) baseStart_8092836 baseEnd_8092836 := by
    simpa [prefixWord, tailWord_8092836, baseEnd_8092836] using wordTrace_append hprefix tailTrace_8092836
  have hstable : (prefixWord ++ tailWord_8092836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092836).length < 2 ^ (prefixWord ++ tailWord_8092836).sum := by decide
  have hdescent : baseEnd_8092836 < baseStart_8092836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092855 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 1, 7]
def baseStart_8092855 : Nat := 118140960795 + 8092855 * 2 ^ 59
def prefixEnd_8092855 : Nat := 4983230072969 + 3 ^ 40 * 8092855 * 2
def baseEnd_8092855 : Nat := 1385174827380679800431381

theorem tailTrace_8092855 : CollatzResearch.WordTrace tailWord_8092855 prefixEnd_8092855 1385174827380679800431381 := by
  unfold tailWord_8092855
  simp only [CollatzResearch.WordTrace]
  refine ⟨295170671095975959440560019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196780447397317306293706679 295170671095975959440560019)
  ·
    refine ⟨442756006643963939160840029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295170671095975959440560019 442756006643963939160840029)
    ·
      refine ⟨166033502491486477185315011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442756006643963939160840029 166033502491486477185315011)
      ·
        refine ⟨249050253737229715777972517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166033502491486477185315011 249050253737229715777972517)
        ·
          refine ⟨46696922575730571708369847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249050253737229715777972517 46696922575730571708369847)
          ·
            refine ⟨70045383863595857562554771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46696922575730571708369847 70045383863595857562554771)
            ·
              refine ⟨105068075795393786343832157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70045383863595857562554771 105068075795393786343832157)
              ·
                refine ⟨39400528423272669878937059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105068075795393786343832157 39400528423272669878937059)
                ·
                  refine ⟨59100792634909004818405589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39400528423272669878937059 59100792634909004818405589)
                  ·
                    refine ⟨1385174827380679800431381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59100792634909004818405589 1385174827380679800431381)
                    ·
                      rfl

theorem cell23_8092855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_8092855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092855 prefixEnd_8092855 := by exact prefixLift 8092855
  have htrace : WordTrace (prefixWord ++ tailWord_8092855) baseStart_8092855 baseEnd_8092855 := by
    simpa [prefixWord, tailWord_8092855, baseEnd_8092855] using wordTrace_append hprefix tailTrace_8092855
  have hstable : (prefixWord ++ tailWord_8092855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092855).length < 2 ^ (prefixWord ++ tailWord_8092855).sum := by decide
  have hdescent : baseEnd_8092855 < baseStart_8092855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092875 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 4]
def baseStart_8092875 : Nat := 118140960795 + 8092875 * 2 ^ 59
def prefixEnd_8092875 : Nat := 4983230072969 + 3 ^ 40 * 8092875 * 2
def baseEnd_8092875 : Nat := 4155534751755129323044051

theorem tailTrace_8092875 : CollatzResearch.WordTrace tailWord_8092875 prefixEnd_8092875 4155534751755129323044051 := by
  unfold tailWord_8092875
  simp only [CollatzResearch.WordTrace]
  refine ⟨295171400555903502856288079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196780933703935668570858719 295171400555903502856288079)
  ·
    refine ⟨442757100833855254284432119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295171400555903502856288079 442757100833855254284432119)
    ·
      refine ⟨664135651250782881426648179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442757100833855254284432119 664135651250782881426648179)
      ·
        refine ⟨996203476876174322139972269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664135651250782881426648179 996203476876174322139972269)
        ·
          refine ⟨373576303828565370802489601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 996203476876174322139972269 373576303828565370802489601)
          ·
            refine ⟨280182227871424028101867201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373576303828565370802489601 280182227871424028101867201)
            ·
              refine ⟨210136670903568021076400401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280182227871424028101867201 210136670903568021076400401)
              ·
                refine ⟨157602503177676015807300301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210136670903568021076400401 157602503177676015807300301)
                ·
                  refine ⟨59100938691628505927737613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157602503177676015807300301 59100938691628505927737613)
                  ·
                    refine ⟨22162852009360689722901605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59100938691628505927737613 22162852009360689722901605)
                    ·
                      refine ⟨4155534751755129323044051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22162852009360689722901605 4155534751755129323044051)
                      ·
                        rfl

theorem cell23_8092875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 4].length) (baseStart_8092875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092875 prefixEnd_8092875 := by exact prefixLift 8092875
  have htrace : WordTrace (prefixWord ++ tailWord_8092875) baseStart_8092875 baseEnd_8092875 := by
    simpa [prefixWord, tailWord_8092875, baseEnd_8092875] using wordTrace_append hprefix tailTrace_8092875
  have hstable : (prefixWord ++ tailWord_8092875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092875).length < 2 ^ (prefixWord ++ tailWord_8092875).sum := by decide
  have hdescent : baseEnd_8092875 < baseStart_8092875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092882 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_8092882 : Nat := 118140960795 + 8092882 * 2 ^ 59
def prefixEnd_8092882 : Nat := 4983230072969 + 3 ^ 40 * 8092882 * 2
def baseEnd_8092882 : Nat := 4155538346119710795656519

theorem tailTrace_8092882 : CollatzResearch.WordTrace tailWord_8092882 prefixEnd_8092882 4155538346119710795656519 := by
  unfold tailWord_8092882
  simp only [CollatzResearch.WordTrace]
  refine ⟨73792913966719535762948225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196781103911252095367861933 73792913966719535762948225)
  ·
    refine ⟨55344685475039651822211169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73792913966719535762948225 55344685475039651822211169)
    ·
      refine ⟨41508514106279738866658377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55344685475039651822211169 41508514106279738866658377)
      ·
        refine ⟨31131385579709804149993783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41508514106279738866658377 31131385579709804149993783)
        ·
          refine ⟨46697078369564706224990675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31131385579709804149993783 46697078369564706224990675)
          ·
            refine ⟨70045617554347059337486013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46697078369564706224990675 70045617554347059337486013)
            ·
              refine ⟨26267106582880147251557255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70045617554347059337486013 26267106582880147251557255)
              ·
                refine ⟨39400659874320220877335883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26267106582880147251557255 39400659874320220877335883)
                ·
                  refine ⟨59100989811480331316003825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39400659874320220877335883 59100989811480331316003825)
                  ·
                    refine ⟨44325742358610248487002869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59100989811480331316003825 44325742358610248487002869)
                    ·
                      refine ⟨4155538346119710795656519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44325742358610248487002869 4155538346119710795656519)
                      ·
                        rfl

theorem cell23_8092882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_8092882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092882 prefixEnd_8092882 := by exact prefixLift 8092882
  have htrace : WordTrace (prefixWord ++ tailWord_8092882) baseStart_8092882 baseEnd_8092882 := by
    simpa [prefixWord, tailWord_8092882, baseEnd_8092882] using wordTrace_append hprefix tailTrace_8092882
  have hstable : (prefixWord ++ tailWord_8092882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092882).length < 2 ^ (prefixWord ++ tailWord_8092882).sum := by decide
  have hdescent : baseEnd_8092882 < baseStart_8092882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092909 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_8092909 : Nat := 118140960795 + 8092909 * 2 ^ 59
def prefixEnd_8092909 : Nat := 4983230072969 + 3 ^ 40 * 8092909 * 2
def baseEnd_8092909 : Nat := 4155552210097382190018895

theorem tailTrace_8092909 : CollatzResearch.WordTrace tailWord_8092909 prefixEnd_8092909 4155552210097382190018895 := by
  unfold tailWord_8092909
  simp only [CollatzResearch.WordTrace]
  refine ⟨295172640637780326663025781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196781760425186884442017187 295172640637780326663025781)
  ·
    refine ⟨27672435059791905624658667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295172640637780326663025781 27672435059791905624658667)
    ·
      refine ⟨41508652589687858436988001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27672435059791905624658667 41508652589687858436988001)
      ·
        refine ⟨31131489442265893827741001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41508652589687858436988001 31131489442265893827741001)
        ·
          refine ⟨23348617081699420370805751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31131489442265893827741001 23348617081699420370805751)
          ·
            refine ⟨35022925622549130556208627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23348617081699420370805751 35022925622549130556208627)
            ·
              refine ⟨52534388433823695834312941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35022925622549130556208627 52534388433823695834312941)
              ·
                refine ⟨19700395662683885937867353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52534388433823695834312941 19700395662683885937867353)
                ·
                  refine ⟨14775296747012914453400515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19700395662683885937867353 14775296747012914453400515)
                  ·
                    refine ⟨22162945120519371680100773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14775296747012914453400515 22162945120519371680100773)
                    ·
                      refine ⟨4155552210097382190018895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22162945120519371680100773 4155552210097382190018895)
                      ·
                        rfl

theorem cell23_8092909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_8092909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092909 prefixEnd_8092909 := by exact prefixLift 8092909
  have htrace : WordTrace (prefixWord ++ tailWord_8092909) baseStart_8092909 baseEnd_8092909 := by
    simpa [prefixWord, tailWord_8092909, baseEnd_8092909] using wordTrace_append hprefix tailTrace_8092909
  have hstable : (prefixWord ++ tailWord_8092909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092909).length < 2 ^ (prefixWord ++ tailWord_8092909).sum := by decide
  have hdescent : baseEnd_8092909 < baseStart_8092909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092929 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_8092929 : Nat := 118140960795 + 8092929 * 2 ^ 59
def prefixEnd_8092929 : Nat := 4983230072969 + 3 ^ 40 * 8092929 * 2
def baseEnd_8092929 : Nat := 4155562479710472111768803

theorem tailTrace_8092929 : CollatzResearch.WordTrace tailWord_8092929 prefixEnd_8092929 4155562479710472111768803 := by
  unfold tailWord_8092929
  simp only [CollatzResearch.WordTrace]
  refine ⟨295173370097707870078753841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196782246731805246719169227 295173370097707870078753841)
  ·
    refine ⟨221380027573280902559065381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295173370097707870078753841 221380027573280902559065381)
    ·
      refine ⟨41508755169990169229824759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221380027573280902559065381 41508755169990169229824759)
      ·
        refine ⟨62263132754985253844737139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41508755169990169229824759 62263132754985253844737139)
        ·
          refine ⟨93394699132477880767105709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62263132754985253844737139 93394699132477880767105709)
          ·
            refine ⟨35023012174679205287664641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93394699132477880767105709 35023012174679205287664641)
            ·
              refine ⟨26267259131009403965748481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35023012174679205287664641 26267259131009403965748481)
              ·
                refine ⟨19700444348257052974311361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26267259131009403965748481 19700444348257052974311361)
                ·
                  refine ⟨14775333261192789730733521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19700444348257052974311361 14775333261192789730733521)
                  ·
                    refine ⟨11081499945894592298050141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14775333261192789730733521 11081499945894592298050141)
                    ·
                      refine ⟨4155562479710472111768803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11081499945894592298050141 4155562479710472111768803)
                      ·
                        rfl

theorem cell23_8092929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_8092929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092929 prefixEnd_8092929 := by exact prefixLift 8092929
  have htrace : WordTrace (prefixWord ++ tailWord_8092929) baseStart_8092929 baseEnd_8092929 := by
    simpa [prefixWord, tailWord_8092929, baseEnd_8092929] using wordTrace_append hprefix tailTrace_8092929
  have hstable : (prefixWord ++ tailWord_8092929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092929).length < 2 ^ (prefixWord ++ tailWord_8092929).sum := by decide
  have hdescent : baseEnd_8092929 < baseStart_8092929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092955 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 7]
def baseStart_8092955 : Nat := 118140960795 + 8092955 * 2 ^ 59
def prefixEnd_8092955 : Nat := 4983230072969 + 3 ^ 40 * 8092955 * 2
def baseEnd_8092955 : Nat := 4155575830207489010043683

theorem tailTrace_8092955 : CollatzResearch.WordTrace tailWord_8092955 prefixEnd_8092955 4155575830207489010043683 := by
  unfold tailWord_8092955
  simp only [CollatzResearch.WordTrace]
  refine ⟨295174318395613676519200319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196782878930409117679466879 295174318395613676519200319)
  ·
    refine ⟨442761477593420514778800479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295174318395613676519200319 442761477593420514778800479)
    ·
      refine ⟨664142216390130772168200719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442761477593420514778800479 664142216390130772168200719)
      ·
        refine ⟨996213324585196158252301079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664142216390130772168200719 996213324585196158252301079)
        ·
          refine ⟨1494319986877794237378451619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996213324585196158252301079 1494319986877794237378451619)
          ·
            refine ⟨2241479980316691356067677429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494319986877794237378451619 2241479980316691356067677429)
            ·
              refine ⟨210138748154689814631344759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2241479980316691356067677429 210138748154689814631344759)
              ·
                refine ⟨315208122232034721947017139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210138748154689814631344759 315208122232034721947017139)
                ·
                  refine ⟨472812183348052082920525709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315208122232034721947017139 472812183348052082920525709)
                  ·
                    refine ⟨177304568755519531095197141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 472812183348052082920525709 177304568755519531095197141)
                    ·
                      refine ⟨4155575830207489010043683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177304568755519531095197141 4155575830207489010043683)
                      ·
                        rfl

theorem cell23_8092955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_8092955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092955 prefixEnd_8092955 := by exact prefixLift 8092955
  have htrace : WordTrace (prefixWord ++ tailWord_8092955) baseStart_8092955 baseEnd_8092955 := by
    simpa [prefixWord, tailWord_8092955, baseEnd_8092955] using wordTrace_append hprefix tailTrace_8092955
  have hstable : (prefixWord ++ tailWord_8092955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092955).length < 2 ^ (prefixWord ++ tailWord_8092955).sum := by decide
  have hdescent : baseEnd_8092955 < baseStart_8092955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092979 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 1, 5]
def baseStart_8092979 : Nat := 118140960795 + 8092979 * 2 ^ 59
def prefixEnd_8092979 : Nat := 4983230072969 + 3 ^ 40 * 8092979 * 2
def baseEnd_8092979 : Nat := 1385196051247732305381191

theorem tailTrace_8092979 : CollatzResearch.WordTrace tailWord_8092979 prefixEnd_8092979 1385196051247732305381191 := by
  unfold tailWord_8092979
  simp only [CollatzResearch.WordTrace]
  refine ⟨295175193747526728618073991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196783462498351152412049327 295175193747526728618073991)
  ·
    refine ⟨442762790621290092927110987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295175193747526728618073991 442762790621290092927110987)
    ·
      refine ⟨664144185931935139390666481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442762790621290092927110987 664144185931935139390666481)
      ·
        refine ⟨498108139448951354542999861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664144185931935139390666481 498108139448951354542999861)
        ·
          refine ⟨46697638073339189488406237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 498108139448951354542999861 46697638073339189488406237)
          ·
            refine ⟨17511614277502196058152339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46697638073339189488406237 17511614277502196058152339)
            ·
              refine ⟨26267421416253294087228509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17511614277502196058152339 26267421416253294087228509)
              ·
                refine ⟨9850283031094985282710691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26267421416253294087228509 9850283031094985282710691)
                ·
                  refine ⟨14775424546642477924066037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9850283031094985282710691 14775424546642477924066037)
                  ·
                    refine ⟨1385196051247732305381191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14775424546642477924066037 1385196051247732305381191)
                    ·
                      rfl

theorem cell23_8092979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 5].length) (baseStart_8092979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092979 prefixEnd_8092979 := by exact prefixLift 8092979
  have htrace : WordTrace (prefixWord ++ tailWord_8092979) baseStart_8092979 baseEnd_8092979 := by
    simpa [prefixWord, tailWord_8092979, baseEnd_8092979] using wordTrace_append hprefix tailTrace_8092979
  have hstable : (prefixWord ++ tailWord_8092979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092979).length < 2 ^ (prefixWord ++ tailWord_8092979).sum := by decide
  have hdescent : baseEnd_8092979 < baseStart_8092979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8092993 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_8092993 : Nat := 118140960795 + 8092993 * 2 ^ 59
def prefixEnd_8092993 : Nat := 4983230072969 + 3 ^ 40 * 8092993 * 2
def baseEnd_8092993 : Nat := 4155595342472359861368509

theorem tailTrace_8092993 : CollatzResearch.WordTrace tailWord_8092993 prefixEnd_8092993 4155595342472359861368509 := by
  unfold tailWord_8092993
  simp only [CollatzResearch.WordTrace]
  refine ⟨295175704369476009009083633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196783802912984006006055755 295175704369476009009083633)
  ·
    refine ⟨221381778277107006756812725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295175704369476009009083633 221381778277107006756812725)
    ·
      refine ⟨20754541713478781883451193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221381778277107006756812725 20754541713478781883451193)
      ·
        refine ⟨15565906285109086412588395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20754541713478781883451193 15565906285109086412588395)
        ·
          refine ⟨23348859427663629618882593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15565906285109086412588395 23348859427663629618882593)
          ·
            refine ⟨17511644570747722214161945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23348859427663629618882593 17511644570747722214161945)
            ·
              refine ⟨13133733428060791660621459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17511644570747722214161945 13133733428060791660621459)
              ·
                refine ⟨19700600142091187490932189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13133733428060791660621459 19700600142091187490932189)
                ·
                  refine ⟨7387725053284195309099571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19700600142091187490932189 7387725053284195309099571)
                  ·
                    refine ⟨11081587579926292963649357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7387725053284195309099571 11081587579926292963649357)
                    ·
                      refine ⟨4155595342472359861368509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11081587579926292963649357 4155595342472359861368509)
                      ·
                        rfl

theorem cell23_8092993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_8092993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8092993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8092993 prefixEnd_8092993 := by exact prefixLift 8092993
  have htrace : WordTrace (prefixWord ++ tailWord_8092993) baseStart_8092993 baseEnd_8092993 := by
    simpa [prefixWord, tailWord_8092993, baseEnd_8092993] using wordTrace_append hprefix tailTrace_8092993
  have hstable : (prefixWord ++ tailWord_8092993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8092993).length < 2 ^ (prefixWord ++ tailWord_8092993).sum := by decide
  have hdescent : baseEnd_8092993 < baseStart_8092993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8092993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093016 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 3, 2, 2]
def baseStart_8093016 : Nat := 118140960795 + 8093016 * 2 ^ 59
def prefixEnd_8093016 : Nat := 4983230072969 + 3 ^ 40 * 8093016 * 2
def baseEnd_8093016 : Nat := 4155607152527413271380903

theorem tailTrace_8093016 : CollatzResearch.WordTrace tailWord_8093016 prefixEnd_8093016 4155607152527413271380903 := by
  unfold tailWord_8093016
  simp only [CollatzResearch.WordTrace]
  refine ⟨147588271624196341968585451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196784362165595122624780601 147588271624196341968585451)
  ·
    refine ⟨221382407436294512952878177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147588271624196341968585451 221382407436294512952878177)
    ·
      refine ⟨166036805577220884714658633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221382407436294512952878177 166036805577220884714658633)
      ·
        refine ⟨124527604182915663535993975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166036805577220884714658633 124527604182915663535993975)
        ·
          refine ⟨186791406274373495303990963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124527604182915663535993975 186791406274373495303990963)
          ·
            refine ⟨280187109411560242955986445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186791406274373495303990963 280187109411560242955986445)
            ·
              refine ⟨105070166029335091108494917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280187109411560242955986445 105070166029335091108494917)
              ·
                refine ⟨19700656130500329582842797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105070166029335091108494917 19700656130500329582842797)
                ·
                  refine ⟨7387746048937623593566049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19700656130500329582842797 7387746048937623593566049)
                  ·
                    refine ⟨5540809536703217695174537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7387746048937623593566049 5540809536703217695174537)
                    ·
                      refine ⟨4155607152527413271380903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540809536703217695174537 4155607152527413271380903)
                      ·
                        rfl

theorem cell23_8093016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_8093016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093016 prefixEnd_8093016 := by exact prefixLift 8093016
  have htrace : WordTrace (prefixWord ++ tailWord_8093016) baseStart_8093016 baseEnd_8093016 := by
    simpa [prefixWord, tailWord_8093016, baseEnd_8093016] using wordTrace_append hprefix tailTrace_8093016
  have hstable : (prefixWord ++ tailWord_8093016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093016).length < 2 ^ (prefixWord ++ tailWord_8093016).sum := by decide
  have hdescent : baseEnd_8093016 < baseStart_8093016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093033 : List Nat := [1, 2, 1, 1, 1, 3, 2, 7, 1, 2, 2]
def baseStart_8093033 : Nat := 118140960795 + 8093033 * 2 ^ 59
def prefixEnd_8093033 : Nat := 4983230072969 + 3 ^ 40 * 8093033 * 2
def baseEnd_8093033 : Nat := 4155615881698539704868325

theorem tailTrace_8093033 : CollatzResearch.WordTrace tailWord_8093033 prefixEnd_8093033 4155615881698539704868325 := by
  unfold tailWord_8093033
  simp only [CollatzResearch.WordTrace]
  refine ⟨295177163289331095840539753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196784775526220730560359835 295177163289331095840539753)
  ·
    refine ⟨221382872466998321880404815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295177163289331095840539753 221382872466998321880404815)
    ·
      refine ⟨332074308700497482820607223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221382872466998321880404815 332074308700497482820607223)
      ·
        refine ⟨498111463050746224230910835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332074308700497482820607223 498111463050746224230910835)
        ·
          refine ⟨747167194576119336346366253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498111463050746224230910835 747167194576119336346366253)
          ·
            refine ⟨280187697966044751129887345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 747167194576119336346366253 280187697966044751129887345)
            ·
              refine ⟨210140773474533563347415509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280187697966044751129887345 210140773474533563347415509)
              ·
                refine ⟨4925174378309380390955051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 210140773474533563347415509 4925174378309380390955051)
                ·
                  refine ⟨7387761567464070586432577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925174378309380390955051 7387761567464070586432577)
                  ·
                    refine ⟨5540821175598052939824433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7387761567464070586432577 5540821175598052939824433)
                    ·
                      refine ⟨4155615881698539704868325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540821175598052939824433 4155615881698539704868325)
                      ·
                        rfl

theorem cell23_8093033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 2, 2].length) (baseStart_8093033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093033 prefixEnd_8093033 := by exact prefixLift 8093033
  have htrace : WordTrace (prefixWord ++ tailWord_8093033) baseStart_8093033 baseEnd_8093033 := by
    simpa [prefixWord, tailWord_8093033, baseEnd_8093033] using wordTrace_append hprefix tailTrace_8093033
  have hstable : (prefixWord ++ tailWord_8093033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093033).length < 2 ^ (prefixWord ++ tailWord_8093033).sum := by decide
  have hdescent : baseEnd_8093033 < baseStart_8093033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093036 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 3]
def baseStart_8093036 : Nat := 118140960795 + 8093036 * 2 ^ 59
def prefixEnd_8093036 : Nat := 4983230072969 + 3 ^ 40 * 8093036 * 2
def baseEnd_8093036 : Nat := 4155617422140503193130811

theorem tailTrace_8093036 : CollatzResearch.WordTrace tailWord_8093036 prefixEnd_8093036 4155617422140503193130811 := by
  unfold tailWord_8093036
  simp only [CollatzResearch.WordTrace]
  refine ⟨147588636354160113676449481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196784848472213484901932641 147588636354160113676449481)
  ·
    refine ⟨110691477265620085257337111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147588636354160113676449481 110691477265620085257337111)
    ·
      refine ⟨166037215898430127886005667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110691477265620085257337111 166037215898430127886005667)
      ·
        refine ⟨249055823847645191829008501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166037215898430127886005667 249055823847645191829008501)
        ·
          refine ⟨23348983485716736733969547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249055823847645191829008501 23348983485716736733969547)
          ·
            refine ⟨35023475228575105100954321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23348983485716736733969547 35023475228575105100954321)
            ·
              refine ⟨26267606421431328825715741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35023475228575105100954321 26267606421431328825715741)
              ·
                refine ⟨9850352408036748309643403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26267606421431328825715741 9850352408036748309643403)
                ·
                  refine ⟨14775528612055122464465105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9850352408036748309643403 14775528612055122464465105)
                  ·
                    refine ⟨11081646459041341848348829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14775528612055122464465105 11081646459041341848348829)
                    ·
                      refine ⟨4155617422140503193130811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11081646459041341848348829 4155617422140503193130811)
                      ·
                        rfl

theorem cell23_8093036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_8093036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093036 prefixEnd_8093036 := by exact prefixLift 8093036
  have htrace : WordTrace (prefixWord ++ tailWord_8093036) baseStart_8093036 baseEnd_8093036 := by
    simpa [prefixWord, tailWord_8093036, baseEnd_8093036] using wordTrace_append hprefix tailTrace_8093036
  have hstable : (prefixWord ++ tailWord_8093036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093036).length < 2 ^ (prefixWord ++ tailWord_8093036).sum := by decide
  have hdescent : baseEnd_8093036 < baseStart_8093036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093052 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_8093052 : Nat := 118140960795 + 8093052 * 2 ^ 59
def prefixEnd_8093052 : Nat := 4983230072969 + 3 ^ 40 * 8093052 * 2
def baseEnd_8093052 : Nat := 1385208545943658376843579

theorem tailTrace_8093052 : CollatzResearch.WordTrace tailWord_8093052 prefixEnd_8093052 1385208545943658376843579 := by
  unfold tailWord_8093052
  simp only [CollatzResearch.WordTrace]
  refine ⟨147588928138131131042740705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196785237517508174723654273 147588928138131131042740705)
  ·
    refine ⟨110691696103598348282055529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147588928138131131042740705 110691696103598348282055529)
    ·
      refine ⟨83018772077698761211541647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110691696103598348282055529 83018772077698761211541647)
      ·
        refine ⟨124528158116548141817312471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83018772077698761211541647 124528158116548141817312471)
        ·
          refine ⟨186792237174822212725968707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124528158116548141817312471 186792237174822212725968707)
          ·
            refine ⟨280188355762233319088953061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186792237174822212725968707 280188355762233319088953061)
            ·
              refine ⟨52535316705418747329178699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280188355762233319088953061 52535316705418747329178699)
              ·
                refine ⟨78802975058128120993768049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52535316705418747329178699 78802975058128120993768049)
                ·
                  refine ⟨59102231293596090745326037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78802975058128120993768049 59102231293596090745326037)
                  ·
                    refine ⟨1385208545943658376843579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59102231293596090745326037 1385208545943658376843579)
                    ·
                      rfl

theorem cell23_8093052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_8093052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093052 prefixEnd_8093052 := by exact prefixLift 8093052
  have htrace : WordTrace (prefixWord ++ tailWord_8093052) baseStart_8093052 baseEnd_8093052 := by
    simpa [prefixWord, tailWord_8093052, baseEnd_8093052] using wordTrace_append hprefix tailTrace_8093052
  have hstable : (prefixWord ++ tailWord_8093052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093052).length < 2 ^ (prefixWord ++ tailWord_8093052).sum := by decide
  have hdescent : baseEnd_8093052 < baseStart_8093052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093070 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_8093070 : Nat := 118140960795 + 8093070 * 2 ^ 59
def prefixEnd_8093070 : Nat := 4983230072969 + 3 ^ 40 * 8093070 * 2
def baseEnd_8093070 : Nat := 4155634880482756060105655

theorem tailTrace_8093070 : CollatzResearch.WordTrace tailWord_8093070 prefixEnd_8093070 4155634880482756060105655 := by
  unfold tailWord_8093070
  simp only [CollatzResearch.WordTrace]
  refine ⟨36897314098774631394954583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196785675193464700773091109 36897314098774631394954583)
  ·
    refine ⟨55345971148161947092431875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36897314098774631394954583 55345971148161947092431875)
    ·
      refine ⟨83018956722242920638647813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55345971148161947092431875 83018956722242920638647813)
      ·
        refine ⟨15566054385420547619746465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83018956722242920638647813 15566054385420547619746465)
        ·
          refine ⟨11674540789065410714809849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15566054385420547619746465 11674540789065410714809849)
          ·
            refine ⟨8755905591799058036107387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11674540789065410714809849 8755905591799058036107387)
            ·
              refine ⟨13133858387698587054161081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755905591799058036107387 13133858387698587054161081)
              ·
                refine ⟨9850393790773940290620811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13133858387698587054161081 9850393790773940290620811)
                ·
                  refine ⟨14775590686160910435931217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9850393790773940290620811 14775590686160910435931217)
                  ·
                    refine ⟨11081693014620682826948413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14775590686160910435931217 11081693014620682826948413)
                    ·
                      refine ⟨4155634880482756060105655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11081693014620682826948413 4155634880482756060105655)
                      ·
                        rfl

theorem cell23_8093070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_8093070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093070 prefixEnd_8093070 := by exact prefixLift 8093070
  have htrace : WordTrace (prefixWord ++ tailWord_8093070) baseStart_8093070 baseEnd_8093070 := by
    simpa [prefixWord, tailWord_8093070, baseEnd_8093070] using wordTrace_append hprefix tailTrace_8093070
  have hstable : (prefixWord ++ tailWord_8093070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093070).length < 2 ^ (prefixWord ++ tailWord_8093070).sum := by decide
  have hdescent : baseEnd_8093070 < baseStart_8093070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093116 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_8093116 : Nat := 118140960795 + 8093116 * 2 ^ 59
def prefixEnd_8093116 : Nat := 4983230072969 + 3 ^ 40 * 8093116 * 2
def baseEnd_8093116 : Nat := 1385219500197620960043481

theorem tailTrace_8093116 : CollatzResearch.WordTrace tailWord_8093116 prefixEnd_8093116 1385219500197620960043481 := by
  unfold tailWord_8093116
  simp only [CollatzResearch.WordTrace]
  refine ⟨147590095274015200507905601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196786793698686934010540801 147590095274015200507905601)
  ·
    refine ⟨110692571455511400380929201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147590095274015200507905601 110692571455511400380929201)
    ·
      refine ⟨83019428591633550285696901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110692571455511400380929201 83019428591633550285696901)
      ·
        refine ⟨15566142860931290678568169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83019428591633550285696901 15566142860931290678568169)
        ·
          refine ⟨11674607145698468008926127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15566142860931290678568169 11674607145698468008926127)
          ·
            refine ⟨17511910718547702013389191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11674607145698468008926127 17511910718547702013389191)
            ·
              refine ⟨26267866077821553020083787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17511910718547702013389191 26267866077821553020083787)
              ·
                refine ⟨39401799116732329530125681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26267866077821553020083787 39401799116732329530125681)
                ·
                  refine ⟨29551349337549247147594261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39401799116732329530125681 29551349337549247147594261)
                  ·
                    refine ⟨1385219500197620960043481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29551349337549247147594261 1385219500197620960043481)
                    ·
                      rfl

theorem cell23_8093116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_8093116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093116 prefixEnd_8093116 := by exact prefixLift 8093116
  have htrace : WordTrace (prefixWord ++ tailWord_8093116) baseStart_8093116 baseEnd_8093116 := by
    simpa [prefixWord, tailWord_8093116, baseEnd_8093116] using wordTrace_append hprefix tailTrace_8093116
  have hstable : (prefixWord ++ tailWord_8093116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093116).length < 2 ^ (prefixWord ++ tailWord_8093116).sum := by decide
  have hdescent : baseEnd_8093116 < baseStart_8093116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093123 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 2, 2, 2]
def baseStart_8093123 : Nat := 118140960795 + 8093123 * 2 ^ 59
def prefixEnd_8093123 : Nat := 4983230072969 + 3 ^ 40 * 8093123 * 2
def baseEnd_8093123 : Nat := 4155662094957444352742911

theorem tailTrace_8093123 : CollatzResearch.WordTrace tailWord_8093123 prefixEnd_8093123 4155662094957444352742911 := by
  unfold tailWord_8093123
  simp only [CollatzResearch.WordTrace]
  refine ⟨295180445859005041211316023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196786963906003360807544015 295180445859005041211316023)
  ·
    refine ⟨442770668788507561816974035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295180445859005041211316023 442770668788507561816974035)
    ·
      refine ⟨664156003182761342725461053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442770668788507561816974035 664156003182761342725461053)
      ·
        refine ⟨249058501193535503522047895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664156003182761342725461053 249058501193535503522047895)
        ·
          refine ⟨373587751790303255283071843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249058501193535503522047895 373587751790303255283071843)
          ·
            refine ⟨560381627685454882924607765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373587751790303255283071843 560381627685454882924607765)
            ·
              refine ⟨26267888797755697637090989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 560381627685454882924607765 26267888797755697637090989)
              ·
                refine ⟨9850458299158386613909121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26267888797755697637090989 9850458299158386613909121)
                ·
                  refine ⟨7387843724368789960431841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9850458299158386613909121 7387843724368789960431841)
                  ·
                    refine ⟨5540882793276592470323881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7387843724368789960431841 5540882793276592470323881)
                    ·
                      refine ⟨4155662094957444352742911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540882793276592470323881 4155662094957444352742911)
                      ·
                        rfl

theorem cell23_8093123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_8093123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093123 prefixEnd_8093123 := by exact prefixLift 8093123
  have htrace : WordTrace (prefixWord ++ tailWord_8093123) baseStart_8093123 baseEnd_8093123 := by
    simpa [prefixWord, tailWord_8093123, baseEnd_8093123] using wordTrace_append hprefix tailTrace_8093123
  have hstable : (prefixWord ++ tailWord_8093123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093123).length < 2 ^ (prefixWord ++ tailWord_8093123).sum := by decide
  have hdescent : baseEnd_8093123 < baseStart_8093123 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093146 : List Nat := [3, 1, 1, 2, 3, 2, 1, 5, 5]
def baseStart_8093146 : Nat := 118140960795 + 8093146 * 2 ^ 59
def prefixEnd_8093146 : Nat := 4983230072969 + 3 ^ 40 * 8093146 * 2
def baseEnd_8093146 : Nat := 461741545001388640306145

theorem tailTrace_8093146 : CollatzResearch.WordTrace tailWord_8093146 prefixEnd_8093146 461741545001388640306145 := by
  unfold tailWord_8093146
  simp only [CollatzResearch.WordTrace]
  refine ⟨73795321184480429034850823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196787523158614477426268861 73795321184480429034850823)
  ·
    refine ⟨110692981776720643552276235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73795321184480429034850823 110692981776720643552276235)
    ·
      refine ⟨166039472665080965328414353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110692981776720643552276235 166039472665080965328414353)
      ·
        refine ⟨124529604498810723996310765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166039472665080965328414353 124529604498810723996310765)
        ·
          refine ⟨46698601687054021498616537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124529604498810723996310765 46698601687054021498616537)
          ·
            refine ⟨35023951265290516123962403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46698601687054021498616537 35023951265290516123962403)
            ·
              refine ⟨52535926897935774185943605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35023951265290516123962403 52535926897935774185943605)
              ·
                refine ⟨4925243146681478829932213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52535926897935774185943605 4925243146681478829932213)
                ·
                  refine ⟨461741545001388640306145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4925243146681478829932213 461741545001388640306145)
                  ·
                    rfl

theorem cell23_8093146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_8093146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093146 prefixEnd_8093146 := by exact prefixLift 8093146
  have htrace : WordTrace (prefixWord ++ tailWord_8093146) baseStart_8093146 baseEnd_8093146 := by
    simpa [prefixWord, tailWord_8093146, baseEnd_8093146] using wordTrace_append hprefix tailTrace_8093146
  have hstable : (prefixWord ++ tailWord_8093146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093146).length < 2 ^ (prefixWord ++ tailWord_8093146).sum := by decide
  have hdescent : baseEnd_8093146 < baseStart_8093146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093157 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 2, 2, 2]
def baseStart_8093157 : Nat := 118140960795 + 8093157 * 2 ^ 59
def prefixEnd_8093157 : Nat := 4983230072969 + 3 ^ 40 * 8093157 * 2
def baseEnd_8093157 : Nat := 4155679553299697219717755

theorem tailTrace_8093157 : CollatzResearch.WordTrace tailWord_8093157 prefixEnd_8093157 4155679553299697219717755 := by
  unfold tailWord_8093157
  simp only [CollatzResearch.WordTrace]
  refine ⟨295181685940881865018053725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196787790627254576678702483 295181685940881865018053725)
  ·
    refine ⟨110693132227830699381770147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295181685940881865018053725 110693132227830699381770147)
    ·
      refine ⟨166039698341746049072655221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110693132227830699381770147 166039698341746049072655221)
      ·
        refine ⟨15566221719538692100561427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166039698341746049072655221 15566221719538692100561427)
        ·
          refine ⟨23349332579308038150842141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15566221719538692100561427 23349332579308038150842141)
          ·
            refine ⟨8755999717240514306565803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23349332579308038150842141 8755999717240514306565803)
            ·
              refine ⟨13133999575860771459848705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755999717240514306565803 13133999575860771459848705)
              ·
                refine ⟨9850499681895578594886529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13133999575860771459848705 9850499681895578594886529)
                ·
                  refine ⟨7387874761421683946164897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9850499681895578594886529 7387874761421683946164897)
                  ·
                    refine ⟨5540906071066262959623673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7387874761421683946164897 5540906071066262959623673)
                    ·
                      refine ⟨4155679553299697219717755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5540906071066262959623673 4155679553299697219717755)
                      ·
                        rfl

theorem cell23_8093157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_8093157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093157 prefixEnd_8093157 := by exact prefixLift 8093157
  have htrace : WordTrace (prefixWord ++ tailWord_8093157) baseStart_8093157 baseEnd_8093157 := by
    simpa [prefixWord, tailWord_8093157, baseEnd_8093157] using wordTrace_append hprefix tailTrace_8093157
  have hstable : (prefixWord ++ tailWord_8093157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093157).length < 2 ^ (prefixWord ++ tailWord_8093157).sum := by decide
  have hdescent : baseEnd_8093157 < baseStart_8093157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093173 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_8093173 : Nat := 118140960795 + 8093173 * 2 ^ 59
def prefixEnd_8093173 : Nat := 4983230072969 + 3 ^ 40 * 8093173 * 2
def baseEnd_8093173 : Nat := 4155687768990169157117681

theorem tailTrace_8093173 : CollatzResearch.WordTrace tailWord_8093173 prefixEnd_8093173 4155687768990169157117681 := by
  unfold tailWord_8093173
  simp only [CollatzResearch.WordTrace]
  refine ⟨295182269508823899750636173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196788179672549266500424115 295182269508823899750636173)
  ·
    refine ⟨110693351065808962406488565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295182269508823899750636173 110693351065808962406488565)
    ·
      refine ⟨10377501662419590225608303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110693351065808962406488565 10377501662419590225608303)
      ·
        refine ⟨15566252493629385338412455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10377501662419590225608303 15566252493629385338412455)
        ·
          refine ⟨23349378740444078007618683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15566252493629385338412455 23349378740444078007618683)
          ·
            refine ⟨35024068110666117011428025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23349378740444078007618683 35024068110666117011428025)
            ·
              refine ⟨26268051082999587758571019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35024068110666117011428025 26268051082999587758571019)
              ·
                refine ⟨39402076624499381637856529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26268051082999587758571019 39402076624499381637856529)
                ·
                  refine ⟨29551557468374536228392397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39402076624499381637856529 29551557468374536228392397)
                  ·
                    refine ⟨11081834050640451085647149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29551557468374536228392397 11081834050640451085647149)
                    ·
                      refine ⟨4155687768990169157117681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11081834050640451085647149 4155687768990169157117681)
                      ·
                        rfl

theorem cell23_8093173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_8093173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093173 prefixEnd_8093173 := by exact prefixLift 8093173
  have htrace : WordTrace (prefixWord ++ tailWord_8093173) baseStart_8093173 baseEnd_8093173 := by
    simpa [prefixWord, tailWord_8093173, baseEnd_8093173] using wordTrace_append hprefix tailTrace_8093173
  have hstable : (prefixWord ++ tailWord_8093173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093173).length < 2 ^ (prefixWord ++ tailWord_8093173).sum := by decide
  have hdescent : baseEnd_8093173 < baseStart_8093173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093179 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 4]
def baseStart_8093179 : Nat := 118140960795 + 8093179 * 2 ^ 59
def prefixEnd_8093179 : Nat := 4983230072969 + 3 ^ 40 * 8093179 * 2
def baseEnd_8093179 : Nat := 4155690849874096133642653

theorem tailTrace_8093179 : CollatzResearch.WordTrace tailWord_8093179 prefixEnd_8093179 4155690849874096133642653 := by
  unfold tailWord_8093179
  simp only [CollatzResearch.WordTrace]
  refine ⟨295182488346802162775354591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196788325564534775183569727 295182488346802162775354591)
  ·
    refine ⟨442773732520203244163031887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295182488346802162775354591 442773732520203244163031887)
    ·
      refine ⟨664160598780304866244547831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442773732520203244163031887 664160598780304866244547831)
      ·
        refine ⟨996240898170457299366821747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664160598780304866244547831 996240898170457299366821747)
        ·
          refine ⟨1494361347255685949050232621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996240898170457299366821747 1494361347255685949050232621)
          ·
            refine ⟨560385505220882230893837233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1494361347255685949050232621 560385505220882230893837233)
            ·
              refine ⟨420289128915661673170377925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560385505220882230893837233 420289128915661673170377925)
              ·
                refine ⟨78804211671686563719445861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420289128915661673170377925 78804211671686563719445861)
                ·
                  refine ⟨14775789688441230697396099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78804211671686563719445861 14775789688441230697396099)
                  ·
                    refine ⟨22163684532661846046094149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14775789688441230697396099 22163684532661846046094149)
                    ·
                      refine ⟨4155690849874096133642653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22163684532661846046094149 4155690849874096133642653)
                      ·
                        rfl

theorem cell23_8093179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 4].length) (baseStart_8093179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093179 prefixEnd_8093179 := by exact prefixLift 8093179
  have htrace : WordTrace (prefixWord ++ tailWord_8093179) baseStart_8093179 baseEnd_8093179 := by
    simpa [prefixWord, tailWord_8093179, baseEnd_8093179] using wordTrace_append hprefix tailTrace_8093179
  have hstable : (prefixWord ++ tailWord_8093179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093179).length < 2 ^ (prefixWord ++ tailWord_8093179).sum := by decide
  have hdescent : baseEnd_8093179 < baseStart_8093179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093199 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 3]
def baseStart_8093199 : Nat := 118140960795 + 8093199 * 2 ^ 59
def prefixEnd_8093199 : Nat := 4983230072969 + 3 ^ 40 * 8093199 * 2
def baseEnd_8093199 : Nat := 4155701119487186055392561

theorem tailTrace_8093199 : CollatzResearch.WordTrace tailWord_8093199 prefixEnd_8093199 4155701119487186055392561 := by
  unfold tailWord_8093199
  simp only [CollatzResearch.WordTrace]
  refine ⟨295183217806729706191082651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196788811871153137460721767 295183217806729706191082651)
  ·
    refine ⟨442774826710094559286623977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295183217806729706191082651 442774826710094559286623977)
    ·
      refine ⟨332081120032570919464967983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442774826710094559286623977 332081120032570919464967983)
      ·
        refine ⟨498121680048856379197451975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332081120032570919464967983 498121680048856379197451975)
        ·
          refine ⟨747182520073284568796177963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498121680048856379197451975 747182520073284568796177963)
          ·
            refine ⟨1120773780109926853194266945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747182520073284568796177963 1120773780109926853194266945)
            ·
              refine ⟨840580335082445139895700209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120773780109926853194266945 840580335082445139895700209)
              ·
                refine ⟨630435251311833854921775157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840580335082445139895700209 630435251311833854921775157)
                ·
                  refine ⟨59103304810484423898916421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 630435251311833854921775157 59103304810484423898916421)
                  ·
                    refine ⟨11081869651965829481046829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59103304810484423898916421 11081869651965829481046829)
                    ·
                      refine ⟨4155701119487186055392561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11081869651965829481046829 4155701119487186055392561)
                      ·
                        rfl

theorem cell23_8093199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_8093199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093199 prefixEnd_8093199 := by exact prefixLift 8093199
  have htrace : WordTrace (prefixWord ++ tailWord_8093199) baseStart_8093199 baseEnd_8093199 := by
    simpa [prefixWord, tailWord_8093199, baseEnd_8093199] using wordTrace_append hprefix tailTrace_8093199
  have hstable : (prefixWord ++ tailWord_8093199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093199).length < 2 ^ (prefixWord ++ tailWord_8093199).sum := by decide
  have hdescent : baseEnd_8093199 < baseStart_8093199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093214 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_8093214 : Nat := 118140960795 + 8093214 * 2 ^ 59
def prefixEnd_8093214 : Nat := 4983230072969 + 3 ^ 40 * 8093214 * 2
def baseEnd_8093214 : Nat := 461745424633000388522777

theorem tailTrace_8093214 : CollatzResearch.WordTrace tailWord_8093214 prefixEnd_8093214 461745424633000388522777 := by
  unfold tailWord_8093214
  simp only [CollatzResearch.WordTrace]
  refine ⟨36897970612709420469109837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196789176601116909168585797 36897970612709420469109837)
  ·
    refine ⟨13836738979766032675916189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36897970612709420469109837 13836738979766032675916189)
    ·
      refine ⟨5188777117412262253468571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13836738979766032675916189 5188777117412262253468571)
      ·
        refine ⟨7783165676118393380202857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5188777117412262253468571 7783165676118393380202857)
        ·
          refine ⟨5837374257088795035152143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7783165676118393380202857 5837374257088795035152143)
          ·
            refine ⟨8756061385633192552728215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837374257088795035152143 8756061385633192552728215)
            ·
              refine ⟨13134092078449788829092323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8756061385633192552728215 13134092078449788829092323)
              ·
                refine ⟨19701138117674683243638485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13134092078449788829092323 19701138117674683243638485)
                ·
                  refine ⟨461745424633000388522777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19701138117674683243638485 461745424633000388522777)
                  ·
                    rfl

theorem cell23_8093214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_8093214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093214 prefixEnd_8093214 := by exact prefixLift 8093214
  have htrace : WordTrace (prefixWord ++ tailWord_8093214) baseStart_8093214 baseEnd_8093214 := by
    simpa [prefixWord, tailWord_8093214, baseEnd_8093214] using wordTrace_append hprefix tailTrace_8093214
  have hstable : (prefixWord ++ tailWord_8093214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093214).length < 2 ^ (prefixWord ++ tailWord_8093214).sum := by decide
  have hdescent : baseEnd_8093214 < baseStart_8093214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093296 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 1, 6]
def baseStart_8093296 : Nat := 118140960795 + 8093296 * 2 ^ 59
def prefixEnd_8093296 : Nat := 4983230072969 + 3 ^ 40 * 8093296 * 2
def baseEnd_8093296 : Nat := 1385250309036890725293205

theorem tailTrace_8093296 : CollatzResearch.WordTrace tailWord_8093296 prefixEnd_8093296 1385250309036890725293205 := by
  unfold tailWord_8093296
  simp only [CollatzResearch.WordTrace]
  refine ⟨147593377843689145878681871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196791170458252194504909161 147593377843689145878681871)
  ·
    refine ⟨221390066765533718818022807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147593377843689145878681871 221390066765533718818022807)
    ·
      refine ⟨332085100148300578227034211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221390066765533718818022807 332085100148300578227034211)
      ·
        refine ⟨498127650222450867340551317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332085100148300578227034211 498127650222450867340551317)
        ·
          refine ⟨23349733604177384406588343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 498127650222450867340551317 23349733604177384406588343)
          ·
            refine ⟨35024600406266076609882515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23349733604177384406588343 35024600406266076609882515)
            ·
              refine ⟨52536900609399114914823773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35024600406266076609882515 52536900609399114914823773)
              ·
                refine ⟨19701337728524668093058915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52536900609399114914823773 19701337728524668093058915)
                ·
                  refine ⟨29552006592787002139588373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19701337728524668093058915 29552006592787002139588373)
                  ·
                    refine ⟨1385250309036890725293205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29552006592787002139588373 1385250309036890725293205)
                    ·
                      rfl

theorem cell23_8093296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_8093296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093296 prefixEnd_8093296 := by exact prefixLift 8093296
  have htrace : WordTrace (prefixWord ++ tailWord_8093296) baseStart_8093296 baseEnd_8093296 := by
    simpa [prefixWord, tailWord_8093296, baseEnd_8093296] using wordTrace_append hprefix tailTrace_8093296
  have hstable : (prefixWord ++ tailWord_8093296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093296).length < 2 ^ (prefixWord ++ tailWord_8093296).sum := by decide
  have hdescent : baseEnd_8093296 < baseStart_8093296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093299 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 6]
def baseStart_8093299 : Nat := 118140960795 + 8093299 * 2 ^ 59
def prefixEnd_8093299 : Nat := 4983230072969 + 3 ^ 40 * 8093299 * 2
def baseEnd_8093299 : Nat := 4155752467552635664142101

theorem tailTrace_8093299 : CollatzResearch.WordTrace tailWord_8093299 prefixEnd_8093299 4155752467552635664142101 := by
  unfold tailWord_8093299
  simp only [CollatzResearch.WordTrace]
  refine ⟨295186865106367423269722951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196791243404244948846481967 295186865106367423269722951)
  ·
    refine ⟨442780297659551134904584427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295186865106367423269722951 442780297659551134904584427)
    ·
      refine ⟨664170446489326702356876641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442780297659551134904584427 664170446489326702356876641)
      ·
        refine ⟨498127834866995026767657481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664170446489326702356876641 498127834866995026767657481)
        ·
          refine ⟨373595876150246270075743111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498127834866995026767657481 373595876150246270075743111)
          ·
            refine ⟨560393814225369405113614667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373595876150246270075743111 560393814225369405113614667)
            ·
              refine ⟨840590721338054107670422001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560393814225369405113614667 840590721338054107670422001)
              ·
                refine ⟨630443041003540580752816501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840590721338054107670422001 630443041003540580752816501)
                ·
                  refine ⟨59104035094081929445576547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 630443041003540580752816501 59104035094081929445576547)
                  ·
                    refine ⟨88656052641122894168364821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59104035094081929445576547 88656052641122894168364821)
                    ·
                      refine ⟨4155752467552635664142101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88656052641122894168364821 4155752467552635664142101)
                      ·
                        rfl

theorem cell23_8093299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_8093299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093299 prefixEnd_8093299 := by exact prefixLift 8093299
  have htrace : WordTrace (prefixWord ++ tailWord_8093299) baseStart_8093299 baseEnd_8093299 := by
    simpa [prefixWord, tailWord_8093299, baseEnd_8093299] using wordTrace_append hprefix tailTrace_8093299
  have hstable : (prefixWord ++ tailWord_8093299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093299).length < 2 ^ (prefixWord ++ tailWord_8093299).sum := by decide
  have hdescent : baseEnd_8093299 < baseStart_8093299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093323 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 3]
def baseStart_8093323 : Nat := 118140960795 + 8093323 * 2 ^ 59
def prefixEnd_8093323 : Nat := 4983230072969 + 3 ^ 40 * 8093323 * 2
def baseEnd_8093323 : Nat := 4155764791088343570241991

theorem tailTrace_8093323 : CollatzResearch.WordTrace tailWord_8093323 prefixEnd_8093323 4155764791088343570241991 := by
  unfold tailWord_8093323
  simp only [CollatzResearch.WordTrace]
  refine ⟨295187740458280475368596623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196791826972186983579064415 295187740458280475368596623)
  ·
    refine ⟨442781610687420713052894935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295187740458280475368596623 442781610687420713052894935)
    ·
      refine ⟨664172416031131069579342403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442781610687420713052894935 664172416031131069579342403)
      ·
        refine ⟨996258624046696604369013605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664172416031131069579342403 996258624046696604369013605)
        ·
          refine ⟨186798492008755613319190051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 996258624046696604369013605 186798492008755613319190051)
          ·
            refine ⟨280197738013133419978785077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186798492008755613319190051 280197738013133419978785077)
            ·
              refine ⟨26268537938731258123011101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280197738013133419978785077 26268537938731258123011101)
              ·
                refine ⟨9850701727024221796129163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26268537938731258123011101 9850701727024221796129163)
                ·
                  refine ⟨14776052590536332694193745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9850701727024221796129163 14776052590536332694193745)
                  ·
                    refine ⟨11082039442902249520645309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14776052590536332694193745 11082039442902249520645309)
                    ·
                      refine ⟨4155764791088343570241991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11082039442902249520645309 4155764791088343570241991)
                      ·
                        rfl

theorem cell23_8093323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 3].length) (baseStart_8093323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093323 prefixEnd_8093323 := by exact prefixLift 8093323
  have htrace : WordTrace (prefixWord ++ tailWord_8093323) baseStart_8093323 baseEnd_8093323 := by
    simpa [prefixWord, tailWord_8093323, baseEnd_8093323] using wordTrace_append hprefix tailTrace_8093323
  have hstable : (prefixWord ++ tailWord_8093323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093323).length < 2 ^ (prefixWord ++ tailWord_8093323).sum := by decide
  have hdescent : baseEnd_8093323 < baseStart_8093323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093326 : List Nat := [4, 1, 1, 3, 1, 3, 10]
def baseStart_8093326 : Nat := 118140960795 + 8093326 * 2 ^ 59
def prefixEnd_8093326 : Nat := 4983230072969 + 3 ^ 40 * 8093326 * 2
def baseEnd_8093326 : Nat := 51305757179386506895117

theorem tailTrace_8093326 : CollatzResearch.WordTrace tailWord_8093326 prefixEnd_8093326 51305757179386506895117 := by
  unfold tailWord_8093326
  simp only [CollatzResearch.WordTrace]
  refine ⟨36898481234658700860119479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196791899918179737920637221 36898481234658700860119479)
  ·
    refine ⟨55347721851988051290179219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36898481234658700860119479 55347721851988051290179219)
    ·
      refine ⟨83021582777982076935268829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55347721851988051290179219 83021582777982076935268829)
      ·
        refine ⟨31133093541743278850725811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83021582777982076935268829 31133093541743278850725811)
        ·
          refine ⟨46699640312614918276088717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31133093541743278850725811 46699640312614918276088717)
          ·
            refine ⟨17512365117230594353533269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46699640312614918276088717 17512365117230594353533269)
            ·
              refine ⟨51305757179386506895117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17512365117230594353533269 51305757179386506895117)
              ·
                rfl

theorem cell23_8093326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 10].length) (baseStart_8093326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093326 prefixEnd_8093326 := by exact prefixLift 8093326
  have htrace : WordTrace (prefixWord ++ tailWord_8093326) baseStart_8093326 baseEnd_8093326 := by
    simpa [prefixWord, tailWord_8093326, baseEnd_8093326] using wordTrace_append hprefix tailTrace_8093326
  have hstable : (prefixWord ++ tailWord_8093326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093326).length < 2 ^ (prefixWord ++ tailWord_8093326).sum := by decide
  have hdescent : baseEnd_8093326 < baseStart_8093326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093330 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_8093330 : Nat := 118140960795 + 8093330 * 2 ^ 59
def prefixEnd_8093330 : Nat := 4983230072969 + 3 ^ 40 * 8093330 * 2
def baseEnd_8093330 : Nat := 1385256128484308347618153

theorem tailTrace_8093330 : CollatzResearch.WordTrace tailWord_8093330 prefixEnd_8093330 1385256128484308347618153 := by
  unfold tailWord_8093330
  simp only [CollatzResearch.WordTrace]
  refine ⟨73796998942313778891025361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196791997179503410376067629 73796998942313778891025361)
  ·
    refine ⟨55347749206735334168269021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73796998942313778891025361 55347749206735334168269021)
    ·
      refine ⟨20755405952525750313100883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55347749206735334168269021 20755405952525750313100883)
      ·
        refine ⟨31133108928788625469651325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20755405952525750313100883 31133108928788625469651325)
        ·
          refine ⟨11674915848295734551119247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31133108928788625469651325 11674915848295734551119247)
          ·
            refine ⟨17512373772443601826678871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11674915848295734551119247 17512373772443601826678871)
            ·
              refine ⟨26268560658665402740018307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17512373772443601826678871 26268560658665402740018307)
              ·
                refine ⟨39402840987998104110027461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26268560658665402740018307 39402840987998104110027461)
                ·
                  refine ⟨7388032685249644520630149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39402840987998104110027461 7388032685249644520630149)
                  ·
                    refine ⟨1385256128484308347618153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7388032685249644520630149 1385256128484308347618153)
                    ·
                      rfl

theorem cell23_8093330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_8093330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093330 prefixEnd_8093330 := by exact prefixLift 8093330
  have htrace : WordTrace (prefixWord ++ tailWord_8093330) baseStart_8093330 baseEnd_8093330 := by
    simpa [prefixWord, tailWord_8093330, baseEnd_8093330] using wordTrace_append hprefix tailTrace_8093330
  have hstable : (prefixWord ++ tailWord_8093330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093330).length < 2 ^ (prefixWord ++ tailWord_8093330).sum := by decide
  have hdescent : baseEnd_8093330 < baseStart_8093330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093398 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_8093398 : Nat := 118140960795 + 8093398 * 2 ^ 59
def prefixEnd_8093398 : Nat := 4983230072969 + 3 ^ 40 * 8093398 * 2
def baseEnd_8093398 : Nat := 1385267767379143592268049

theorem tailTrace_8093398 : CollatzResearch.WordTrace tailWord_8093398 prefixEnd_8093398 1385267767379143592268049 := by
  unfold tailWord_8093398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18449404745813047698598553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196793650622005842118384565 18449404745813047698598553)
  ·
    refine ⟨13837053559359785773948915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18449404745813047698598553 13837053559359785773948915)
    ·
      refine ⟨20755580339039678660923373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13837053559359785773948915 20755580339039678660923373)
      ·
        refine ⟨7783342627139879497846265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20755580339039678660923373 7783342627139879497846265)
        ·
          refine ⟨5837506970354909623384699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7783342627139879497846265 5837506970354909623384699)
          ·
            refine ⟨8756260455532364435077049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837506970354909623384699 8756260455532364435077049)
            ·
              refine ⟨6567195341649273326307787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8756260455532364435077049 6567195341649273326307787)
              ·
                refine ⟨9850793012473909989461681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567195341649273326307787 9850793012473909989461681)
                ·
                  refine ⟨7388094759355432492096261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9850793012473909989461681 7388094759355432492096261)
                  ·
                    refine ⟨1385267767379143592268049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7388094759355432492096261 1385267767379143592268049)
                    ·
                      rfl

theorem cell23_8093398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_8093398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093398 prefixEnd_8093398 := by exact prefixLift 8093398
  have htrace : WordTrace (prefixWord ++ tailWord_8093398) baseStart_8093398 baseEnd_8093398 := by
    simpa [prefixWord, tailWord_8093398, baseEnd_8093398] using wordTrace_append hprefix tailTrace_8093398
  have hstable : (prefixWord ++ tailWord_8093398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093398).length < 2 ^ (prefixWord ++ tailWord_8093398).sum := by decide
  have hdescent : baseEnd_8093398 < baseStart_8093398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093404 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_8093404 : Nat := 118140960795 + 8093404 * 2 ^ 59
def prefixEnd_8093404 : Nat := 4983230072969 + 3 ^ 40 * 8093404 * 2
def baseEnd_8093404 : Nat := 4155806383021357753329119

theorem tailTrace_8093404 : CollatzResearch.WordTrace tailWord_8093404 prefixEnd_8093404 4155806383021357753329119 := by
  unfold tailWord_8093404
  simp only [CollatzResearch.WordTrace]
  refine ⟨147595347385493513101147633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196793796513991350801530177 147595347385493513101147633)
  ·
    refine ⟨110696510539120134825860725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147595347385493513101147633 110696510539120134825860725)
    ·
      refine ⟨10377797863042512639924443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110696510539120134825860725 10377797863042512639924443)
      ·
        refine ⟨15566696794563768959886665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10377797863042512639924443 15566696794563768959886665)
        ·
          refine ⟨11675022595922826719914999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15566696794563768959886665 11675022595922826719914999)
          ·
            refine ⟨17512533893884240079872499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11675022595922826719914999 17512533893884240079872499)
            ·
              refine ⟨26268800840826360119808749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17512533893884240079872499 26268800840826360119808749)
              ·
                refine ⟨9850800315309885044928281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26268800840826360119808749 9850800315309885044928281)
                ·
                  refine ⟨7388100236482413783696211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9850800315309885044928281 7388100236482413783696211)
                  ·
                    refine ⟨11082150354723620675544317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7388100236482413783696211 11082150354723620675544317)
                    ·
                      refine ⟨4155806383021357753329119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11082150354723620675544317 4155806383021357753329119)
                      ·
                        rfl

theorem cell23_8093404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_8093404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093404 prefixEnd_8093404 := by exact prefixLift 8093404
  have htrace : WordTrace (prefixWord ++ tailWord_8093404) baseStart_8093404 baseEnd_8093404 := by
    simpa [prefixWord, tailWord_8093404, baseEnd_8093404] using wordTrace_append hprefix tailTrace_8093404
  have hstable : (prefixWord ++ tailWord_8093404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093404).length < 2 ^ (prefixWord ++ tailWord_8093404).sum := by decide
  have hdescent : baseEnd_8093404 < baseStart_8093404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093444 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_8093444 : Nat := 118140960795 + 8093444 * 2 ^ 59
def prefixEnd_8093444 : Nat := 4983230072969 + 3 ^ 40 * 8093444 * 2
def baseEnd_8093444 : Nat := 4155826922247537596828935

theorem tailTrace_8093444 : CollatzResearch.WordTrace tailWord_8093444 prefixEnd_8093444 4155826922247537596828935 := by
  unfold tailWord_8093444
  simp only [CollatzResearch.WordTrace]
  refine ⟨147596076845421056516875693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196794769127228075355834257 147596076845421056516875693)
  ·
    refine ⟨55348528817032896193828385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147596076845421056516875693 55348528817032896193828385)
    ·
      refine ⟨41511396612774672145371289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55348528817032896193828385 41511396612774672145371289)
      ·
        refine ⟨31133547459581004109028467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41511396612774672145371289 31133547459581004109028467)
        ·
          refine ⟨46700321189371506163542701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31133547459581004109028467 46700321189371506163542701)
          ·
            refine ⟨17512620446014314811328513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46700321189371506163542701 17512620446014314811328513)
            ·
              refine ⟨13134465334510736108496385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17512620446014314811328513 13134465334510736108496385)
              ·
                refine ⟨9850849000883052081372289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13134465334510736108496385 9850849000883052081372289)
                ·
                  refine ⟨7388136750662289061029217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9850849000883052081372289 7388136750662289061029217)
                  ·
                    refine ⟨5541102562996716795771913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7388136750662289061029217 5541102562996716795771913)
                    ·
                      refine ⟨4155826922247537596828935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5541102562996716795771913 4155826922247537596828935)
                      ·
                        rfl

theorem cell23_8093444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_8093444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093444 prefixEnd_8093444 := by exact prefixLift 8093444
  have htrace : WordTrace (prefixWord ++ tailWord_8093444) baseStart_8093444 baseEnd_8093444 := by
    simpa [prefixWord, tailWord_8093444, baseEnd_8093444] using wordTrace_append hprefix tailTrace_8093444
  have hstable : (prefixWord ++ tailWord_8093444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093444).length < 2 ^ (prefixWord ++ tailWord_8093444).sum := by decide
  have hdescent : baseEnd_8093444 < baseStart_8093444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093450 : List Nat := [3, 1, 2, 2, 1, 4, 1, 4, 5]
def baseStart_8093450 : Nat := 118140960795 + 8093450 * 2 ^ 59
def prefixEnd_8093450 : Nat := 4983230072969 + 3 ^ 40 * 8093450 * 2
def baseEnd_8093450 : Nat := 461758889236829397039323

theorem tailTrace_8093450 : CollatzResearch.WordTrace tailWord_8093450 prefixEnd_8093450 461758889236829397039323 := by
  unfold tailWord_8093450
  simp only [CollatzResearch.WordTrace]
  refine ⟨73798093132205094014617451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196794915019213584038979869 73798093132205094014617451)
  ·
    refine ⟨110697139698307641021926177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73798093132205094014617451 110697139698307641021926177)
    ·
      refine ⟨83022854773730730766444633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110697139698307641021926177 83022854773730730766444633)
      ·
        refine ⟨62267141080298048074833475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83022854773730730766444633 62267141080298048074833475)
        ·
          refine ⟨93400711620447072112250213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62267141080298048074833475 93400711620447072112250213)
          ·
            refine ⟨17512633428833826021046915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93400711620447072112250213 17512633428833826021046915)
            ·
              refine ⟨26268950143250739031570373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17512633428833826021046915 26268950143250739031570373)
              ·
                refine ⟨4925428151859513568419445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26268950143250739031570373 4925428151859513568419445)
                ·
                  refine ⟨461758889236829397039323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4925428151859513568419445 461758889236829397039323)
                  ·
                    rfl

theorem cell23_8093450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_8093450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093450 prefixEnd_8093450 := by exact prefixLift 8093450
  have htrace : WordTrace (prefixWord ++ tailWord_8093450) baseStart_8093450 baseEnd_8093450 := by
    simpa [prefixWord, tailWord_8093450, baseEnd_8093450] using wordTrace_append hprefix tailTrace_8093450
  have hstable : (prefixWord ++ tailWord_8093450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093450).length < 2 ^ (prefixWord ++ tailWord_8093450).sum := by decide
  have hdescent : baseEnd_8093450 < baseStart_8093450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093480 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 2, 5]
def baseStart_8093480 : Nat := 118140960795 + 8093480 * 2 ^ 59
def prefixEnd_8093480 : Nat := 4983230072969 + 3 ^ 40 * 8093480 * 2
def baseEnd_8093480 : Nat := 1385281802517033151992923

theorem tailTrace_8093480 : CollatzResearch.WordTrace tailWord_8093480 prefixEnd_8093480 1385281802517033151992923 := by
  unfold tailWord_8093480
  simp only [CollatzResearch.WordTrace]
  refine ⟨147596733359355845591030947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196795644479141127454707929 147596733359355845591030947)
  ·
    refine ⟨221395100039033768386546421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147596733359355845591030947 221395100039033768386546421)
    ·
      refine ⟨20755790628659415786238727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221395100039033768386546421 20755790628659415786238727)
      ·
        refine ⟨31133685942989123679358091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20755790628659415786238727 31133685942989123679358091)
        ·
          refine ⟨46700528914483685519037137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31133685942989123679358091 46700528914483685519037137)
          ·
            refine ⟨35025396685862764139277853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46700528914483685519037137 35025396685862764139277853)
            ·
              refine ⟨13134523757198536552229195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35025396685862764139277853 13134523757198536552229195)
              ·
                refine ⟨19701785635797804828343793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13134523757198536552229195 19701785635797804828343793)
                ·
                  refine ⟨14776339226848353621257845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19701785635797804828343793 14776339226848353621257845)
                  ·
                    refine ⟨1385281802517033151992923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14776339226848353621257845 1385281802517033151992923)
                    ·
                      rfl

theorem cell23_8093480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_8093480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093480 prefixEnd_8093480 := by exact prefixLift 8093480
  have htrace : WordTrace (prefixWord ++ tailWord_8093480) baseStart_8093480 baseEnd_8093480 := by
    simpa [prefixWord, tailWord_8093480, baseEnd_8093480] using wordTrace_append hprefix tailTrace_8093480
  have hstable : (prefixWord ++ tailWord_8093480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093480).length < 2 ^ (prefixWord ++ tailWord_8093480).sum := by decide
  have hdescent : baseEnd_8093480 < baseStart_8093480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093500 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_8093500 : Nat := 118140960795 + 8093500 * 2 ^ 59
def prefixEnd_8093500 : Nat := 4983230072969 + 3 ^ 40 * 8093500 * 2
def baseEnd_8093500 : Nat := 4155855677164189377728677

theorem tailTrace_8093500 : CollatzResearch.WordTrace tailWord_8093500 prefixEnd_8093500 4155855677164189377728677 := by
  unfold tailWord_8093500
  simp only [CollatzResearch.WordTrace]
  refine ⟨147597098089319617298894977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196796130785759489731859969 147597098089319617298894977)
  ·
    refine ⟨110697823566989712974171233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147597098089319617298894977 110697823566989712974171233)
    ·
      refine ⟨83023367675242284730628425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110697823566989712974171233 83023367675242284730628425)
      ·
        refine ⟨62267525756431713547971319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83023367675242284730628425 62267525756431713547971319)
        ·
          refine ⟨93401288634647570321956979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62267525756431713547971319 93401288634647570321956979)
          ·
            refine ⟨140101932951971355482935469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93401288634647570321956979 140101932951971355482935469)
            ·
              refine ⟨52538224856989258306100801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140101932951971355482935469 52538224856989258306100801)
              ·
                refine ⟨39403668642741943729575601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52538224856989258306100801 39403668642741943729575601)
                ·
                  refine ⟨29552751482056457797181701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39403668642741943729575601 29552751482056457797181701)
                  ·
                    refine ⟨5541140902885585836971569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29552751482056457797181701 5541140902885585836971569)
                    ·
                      refine ⟨4155855677164189377728677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5541140902885585836971569 4155855677164189377728677)
                      ·
                        rfl

theorem cell23_8093500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_8093500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093500 prefixEnd_8093500 := by exact prefixLift 8093500
  have htrace : WordTrace (prefixWord ++ tailWord_8093500) baseStart_8093500 baseEnd_8093500 := by
    simpa [prefixWord, tailWord_8093500, baseEnd_8093500] using wordTrace_append hprefix tailTrace_8093500
  have hstable : (prefixWord ++ tailWord_8093500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093500).length < 2 ^ (prefixWord ++ tailWord_8093500).sum := by decide
  have hdescent : baseEnd_8093500 < baseStart_8093500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093593 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_8093593 : Nat := 118140960795 + 8093593 * 2 ^ 59
def prefixEnd_8093593 : Nat := 4983230072969 + 3 ^ 40 * 8093593 * 2
def baseEnd_8093593 : Nat := 4155903430865057513865749

theorem tailTrace_8093593 : CollatzResearch.WordTrace tailWord_8093593 prefixEnd_8093593 4155903430865057513865749 := by
  unfold tailWord_8093593
  simp only [CollatzResearch.WordTrace]
  refine ⟨295197588167302311480925433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196798392111534874320616955 295197588167302311480925433)
  ·
    refine ⟨221398191125476733610694075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295197588167302311480925433 221398191125476733610694075)
    ·
      refine ⟨332097286688215100416041113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221398191125476733610694075 332097286688215100416041113)
      ·
        refine ⟨249072965016161325312030835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332097286688215100416041113 249072965016161325312030835)
        ·
          refine ⟨373609447524241987968046253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249072965016161325312030835 373609447524241987968046253)
          ·
            refine ⟨140103542821590745488017345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373609447524241987968046253 140103542821590745488017345)
            ·
              refine ⟨105077657116193059116013009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140103542821590745488017345 105077657116193059116013009)
              ·
                refine ⟨78808242837144794337009757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105077657116193059116013009 78808242837144794337009757)
                ·
                  refine ⟨29553091063929297876378659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78808242837144794337009757 29553091063929297876378659)
                  ·
                    refine ⟨44329636595893946814567989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29553091063929297876378659 44329636595893946814567989)
                    ·
                      refine ⟨4155903430865057513865749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44329636595893946814567989 4155903430865057513865749)
                      ·
                        rfl

theorem cell23_8093593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_8093593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093593 prefixEnd_8093593 := by exact prefixLift 8093593
  have htrace : WordTrace (prefixWord ++ tailWord_8093593) baseStart_8093593 baseEnd_8093593 := by
    simpa [prefixWord, tailWord_8093593, baseEnd_8093593] using wordTrace_append hprefix tailTrace_8093593
  have hstable : (prefixWord ++ tailWord_8093593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093593).length < 2 ^ (prefixWord ++ tailWord_8093593).sum := by decide
  have hdescent : baseEnd_8093593 < baseStart_8093593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093594 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2]
def baseStart_8093594 : Nat := 118140960795 + 8093594 * 2 ^ 59
def prefixEnd_8093594 : Nat := 4983230072969 + 3 ^ 40 * 8093594 * 2
def baseEnd_8093594 : Nat := 4155903944345712009953245

theorem tailTrace_8093594 : CollatzResearch.WordTrace tailWord_8093594 prefixEnd_8093594 4155903944345712009953245 := by
  unfold tailWord_8093594
  simp only [CollatzResearch.WordTrace]
  refine ⟨73799406160074672162927959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196798416426865792434474557 73799406160074672162927959)
  ·
    refine ⟨110699109240112008244391939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73799406160074672162927959 110699109240112008244391939)
    ·
      refine ⟨166048663860168012366587909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110699109240112008244391939 166048663860168012366587909)
      ·
        refine ⟨31134124473781502318735233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166048663860168012366587909 31134124473781502318735233)
        ·
          refine ⟨23350593355336126739051425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31134124473781502318735233 23350593355336126739051425)
          ·
            refine ⟨17512945016502095054288569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23350593355336126739051425 17512945016502095054288569)
            ·
              refine ⟨13134708762376571290716427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17512945016502095054288569 13134708762376571290716427)
              ·
                refine ⟨19702063143564856936074641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13134708762376571290716427 19702063143564856936074641)
                ·
                  refine ⟨14776547357673642702055981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19702063143564856936074641 14776547357673642702055981)
                  ·
                    refine ⟨5541205259127616013270993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14776547357673642702055981 5541205259127616013270993)
                    ·
                      refine ⟨4155903944345712009953245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5541205259127616013270993 4155903944345712009953245)
                      ·
                        rfl

theorem cell23_8093594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_8093594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093594 prefixEnd_8093594 := by exact prefixLift 8093594
  have htrace : WordTrace (prefixWord ++ tailWord_8093594) baseStart_8093594 baseEnd_8093594 := by
    simpa [prefixWord, tailWord_8093594, baseEnd_8093594] using wordTrace_append hprefix tailTrace_8093594
  have hstable : (prefixWord ++ tailWord_8093594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093594).length < 2 ^ (prefixWord ++ tailWord_8093594).sum := by decide
  have hdescent : baseEnd_8093594 < baseStart_8093594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093613 : List Nat := [1, 5, 2, 15]
def baseStart_8093613 : Nat := 118140960795 + 8093613 * 2 ^ 59
def prefixEnd_8093613 : Nat := 4983230072969 + 3 ^ 40 * 8093613 * 2
def baseEnd_8093613 : Nat := 1900280612930108566811

theorem tailTrace_8093613 : CollatzResearch.WordTrace tailWord_8093613 prefixEnd_8093613 1900280612930108566811 := by
  unfold tailWord_8093613
  simp only [CollatzResearch.WordTrace]
  refine ⟨295198317627229854896653493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196798878418153236597768995 295198317627229854896653493)
  ·
    refine ⟨27674842277552798896561265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295198317627229854896653493 27674842277552798896561265)
    ·
      refine ⟨20756131708164599172420949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27674842277552798896561265 20756131708164599172420949)
      ·
        refine ⟨1900280612930108566811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 20756131708164599172420949 1900280612930108566811)
        ·
          rfl

theorem cell23_8093613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 15].length) (baseStart_8093613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093613 prefixEnd_8093613 := by exact prefixLift 8093613
  have htrace : WordTrace (prefixWord ++ tailWord_8093613) baseStart_8093613 baseEnd_8093613 := by
    simpa [prefixWord, tailWord_8093613, baseEnd_8093613] using wordTrace_append hprefix tailTrace_8093613
  have hstable : (prefixWord ++ tailWord_8093613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093613).length < 2 ^ (prefixWord ++ tailWord_8093613).sum := by decide
  have hdescent : baseEnd_8093613 < baseStart_8093613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093617 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 2, 4]
def baseStart_8093617 : Nat := 118140960795 + 8093617 * 2 ^ 59
def prefixEnd_8093617 : Nat := 4983230072969 + 3 ^ 40 * 8093617 * 2
def baseEnd_8093617 : Nat := 1385305251466921806655213

theorem tailTrace_8093617 : CollatzResearch.WordTrace tailWord_8093617 prefixEnd_8093617 1385305251466921806655213 := by
  unfold tailWord_8093617
  simp only [CollatzResearch.WordTrace]
  refine ⟨295198463519215363579799105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196798975679476909053199403 295198463519215363579799105)
  ·
    refine ⟨221398847639411522684849329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295198463519215363579799105 221398847639411522684849329)
    ·
      refine ⟨166049135729558642013636997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221398847639411522684849329 166049135729558642013636997)
      ·
        refine ⟨31134212949292245377556937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166049135729558642013636997 31134212949292245377556937)
        ·
          refine ⟨23350659711969184033167703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31134212949292245377556937 23350659711969184033167703)
          ·
            refine ⟨35025989567953776049751555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23350659711969184033167703 35025989567953776049751555)
            ·
              refine ⟨52538984351930664074627333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35025989567953776049751555 52538984351930664074627333)
              ·
                refine ⟨9851059565986999513992625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52538984351930664074627333 9851059565986999513992625)
                ·
                  refine ⟨7388294674490249635494469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9851059565986999513992625 7388294674490249635494469)
                  ·
                    refine ⟨1385305251466921806655213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7388294674490249635494469 1385305251466921806655213)
                    ·
                      rfl

theorem cell23_8093617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_8093617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093617 prefixEnd_8093617 := by exact prefixLift 8093617
  have htrace : WordTrace (prefixWord ++ tailWord_8093617) baseStart_8093617 baseEnd_8093617 := by
    simpa [prefixWord, tailWord_8093617, baseEnd_8093617] using wordTrace_append hprefix tailTrace_8093617
  have hstable : (prefixWord ++ tailWord_8093617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093617).length < 2 ^ (prefixWord ++ tailWord_8093617).sum := by decide
  have hdescent : baseEnd_8093617 < baseStart_8093617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093630 : List Nat := [4, 2, 1, 1, 1, 3, 3, 8]
def baseStart_8093630 : Nat := 118140960795 + 8093630 * 2 ^ 59
def prefixEnd_8093630 : Nat := 4983230072969 + 3 ^ 40 * 8093630 * 2
def baseEnd_8093630 : Nat := 153923052949973106263077

theorem tailTrace_8093630 : CollatzResearch.WordTrace tailWord_8093630 prefixEnd_8093630 153923052949973106263077 := by
  unfold tailWord_8093630
  simp only [CollatzResearch.WordTrace]
  refine ⟨36899867208521033350002793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196799291778778844533348229 36899867208521033350002793)
  ·
    refine ⟨27674900406390775012502095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36899867208521033350002793 27674900406390775012502095)
    ·
      refine ⟨41512350609586162518753143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27674900406390775012502095 41512350609586162518753143)
      ·
        refine ⟨62268525914379243778129715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41512350609586162518753143 62268525914379243778129715)
        ·
          refine ⟨93402788871568865667194573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62268525914379243778129715 93402788871568865667194573)
          ·
            refine ⟨35026045826838324625197965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93402788871568865667194573 35026045826838324625197965)
            ·
              refine ⟨13134767185064371734449237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35026045826838324625197965 13134767185064371734449237)
              ·
                refine ⟨153923052949973106263077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13134767185064371734449237 153923052949973106263077)
                ·
                  rfl

theorem cell23_8093630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_8093630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093630 prefixEnd_8093630 := by exact prefixLift 8093630
  have htrace : WordTrace (prefixWord ++ tailWord_8093630) baseStart_8093630 baseEnd_8093630 := by
    simpa [prefixWord, tailWord_8093630, baseEnd_8093630] using wordTrace_append hprefix tailTrace_8093630
  have hstable : (prefixWord ++ tailWord_8093630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093630).length < 2 ^ (prefixWord ++ tailWord_8093630).sum := by decide
  have hdescent : baseEnd_8093630 < baseStart_8093630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093643 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 2, 7]
def baseStart_8093643 : Nat := 118140960795 + 8093643 * 2 ^ 59
def prefixEnd_8093643 : Nat := 4983230072969 + 3 ^ 40 * 8093643 * 2
def baseEnd_8093643 : Nat := 1385309701632594106080173

theorem tailTrace_8093643 : CollatzResearch.WordTrace tailWord_8093643 prefixEnd_8093643 1385309701632594106080173 := by
  unfold tailWord_8093643
  simp only [CollatzResearch.WordTrace]
  refine ⟨295199411817121170020245583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196799607878080780013497055 295199411817121170020245583)
  ·
    refine ⟨442799117725681755030368375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295199411817121170020245583 442799117725681755030368375)
    ·
      refine ⟨664198676588522632545552563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442799117725681755030368375 664198676588522632545552563)
      ·
        refine ⟨996298014882783948818328845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664198676588522632545552563 996298014882783948818328845)
        ·
          refine ⟨373611755581043980806873317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 996298014882783948818328845 373611755581043980806873317)
          ·
            refine ⟨70052204171445746401288747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373611755581043980806873317 70052204171445746401288747)
            ·
              refine ⟨105078306257168619601933121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70052204171445746401288747 105078306257168619601933121)
              ·
                refine ⟨78808729692876464701449841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105078306257168619601933121 78808729692876464701449841)
                ·
                  refine ⟨59106547269657348526087381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78808729692876464701449841 59106547269657348526087381)
                  ·
                    refine ⟨1385309701632594106080173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59106547269657348526087381 1385309701632594106080173)
                    ·
                      rfl

theorem cell23_8093643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 7].length) (baseStart_8093643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093643 prefixEnd_8093643 := by exact prefixLift 8093643
  have htrace : WordTrace (prefixWord ++ tailWord_8093643) baseStart_8093643 baseEnd_8093643 := by
    simpa [prefixWord, tailWord_8093643, baseEnd_8093643] using wordTrace_append hprefix tailTrace_8093643
  have hstable : (prefixWord ++ tailWord_8093643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093643).length < 2 ^ (prefixWord ++ tailWord_8093643).sum := by decide
  have hdescent : baseEnd_8093643 < baseStart_8093643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093658 : List Nat := [3, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2]
def baseStart_8093658 : Nat := 118140960795 + 8093658 * 2 ^ 59
def prefixEnd_8093658 : Nat := 4983230072969 + 3 ^ 40 * 8093658 * 2
def baseEnd_8093658 : Nat := 4155936807107599759552951

theorem tailTrace_8093658 : CollatzResearch.WordTrace tailWord_8093658 prefixEnd_8093658 4155936807107599759552951 := by
  unfold tailWord_8093658
  simp only [CollatzResearch.WordTrace]
  refine ⟨73799989728016706895510407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196799972608044551721361085 73799989728016706895510407)
  ·
    refine ⟨110699984592025060343265611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73799989728016706895510407 110699984592025060343265611)
    ·
      refine ⟨166049976888037590514898417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110699984592025060343265611 166049976888037590514898417)
      ·
        refine ⟨124537482666028192886173813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166049976888037590514898417 124537482666028192886173813)
        ·
          refine ⟨11675388999940143083078795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124537482666028192886173813 11675388999940143083078795)
          ·
            refine ⟨17513083499910214624618193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11675388999940143083078795 17513083499910214624618193)
            ·
              refine ⟨13134812624932660968463645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17513083499910214624618193 13134812624932660968463645)
              ·
                refine ⟨4925554734349747863173867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13134812624932660968463645 4925554734349747863173867)
                ·
                  refine ⟨7388332101524621794760801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925554734349747863173867 7388332101524621794760801)
                  ·
                    refine ⟨5541249076143466346070601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7388332101524621794760801 5541249076143466346070601)
                    ·
                      refine ⟨4155936807107599759552951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5541249076143466346070601 4155936807107599759552951)
                      ·
                        rfl

theorem cell23_8093658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_8093658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093658 prefixEnd_8093658 := by exact prefixLift 8093658
  have htrace : WordTrace (prefixWord ++ tailWord_8093658) baseStart_8093658 baseEnd_8093658 := by
    simpa [prefixWord, tailWord_8093658, baseEnd_8093658] using wordTrace_append hprefix tailTrace_8093658
  have hstable : (prefixWord ++ tailWord_8093658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093658).length < 2 ^ (prefixWord ++ tailWord_8093658).sum := by decide
  have hdescent : baseEnd_8093658 < baseStart_8093658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093709 : List Nat := [1, 7, 1, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_8093709 : Nat := 118140960795 + 8093709 * 2 ^ 59
def prefixEnd_8093709 : Nat := 4983230072969 + 3 ^ 40 * 8093709 * 2
def baseEnd_8093709 : Nat := 4155962994620979060015217

theorem tailTrace_8093709 : CollatzResearch.WordTrace tailWord_8093709 prefixEnd_8093709 4155962994620979060015217 := by
  unfold tailWord_8093709
  simp only [CollatzResearch.WordTrace]
  refine ⟨295201819034882063292148181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196801212689921375528098787 295201819034882063292148181)
  ·
    refine ⟨6918792633630048358409723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 295201819034882063292148181 6918792633630048358409723)
    ·
      refine ⟨10378188950445072537614585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6918792633630048358409723 10378188950445072537614585)
      ·
        refine ⟨7783641712833804403210939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10378188950445072537614585 7783641712833804403210939)
        ·
          refine ⟨11675462569250706604816409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7783641712833804403210939 11675462569250706604816409)
          ·
            refine ⟨8756596926938029953612307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11675462569250706604816409 8756596926938029953612307)
            ·
              refine ⟨13134895390407044930418461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8756596926938029953612307 13134895390407044930418461)
              ·
                refine ⟨4925585771402641848906923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13134895390407044930418461 4925585771402641848906923)
                ·
                  refine ⟨7388378657103962773360385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925585771402641848906923 7388378657103962773360385)
                  ·
                    refine ⟨5541283992827972080020289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7388378657103962773360385 5541283992827972080020289)
                    ·
                      refine ⟨4155962994620979060015217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5541283992827972080020289 4155962994620979060015217)
                      ·
                        rfl

theorem cell23_8093709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_8093709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093709 prefixEnd_8093709 := by exact prefixLift 8093709
  have htrace : WordTrace (prefixWord ++ tailWord_8093709) baseStart_8093709 baseEnd_8093709 := by
    simpa [prefixWord, tailWord_8093709, baseEnd_8093709] using wordTrace_append hprefix tailTrace_8093709
  have hstable : (prefixWord ++ tailWord_8093709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093709).length < 2 ^ (prefixWord ++ tailWord_8093709).sum := by decide
  have hdescent : baseEnd_8093709 < baseStart_8093709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093717 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_8093717 : Nat := 118140960795 + 8093717 * 2 ^ 59
def prefixEnd_8093717 : Nat := 4983230072969 + 3 ^ 40 * 8093717 * 2
def baseEnd_8093717 : Nat := 4155967102466215028715179

theorem tailTrace_8093717 : CollatzResearch.WordTrace tailWord_8093717 prefixEnd_8093717 4155967102466215028715179 := by
  unfold tailWord_8093717
  simp only [CollatzResearch.WordTrace]
  refine ⟨295202110818853080658439405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196801407212568720438959603 295202110818853080658439405)
  ·
    refine ⟨110700791557069905246914777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295202110818853080658439405 110700791557069905246914777)
    ·
      refine ⟨83025593667802428935186083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110700791557069905246914777 83025593667802428935186083)
      ·
        refine ⟨124538390501703643402779125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83025593667802428935186083 124538390501703643402779125)
        ·
          refine ⟨11675474109534716569010543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124538390501703643402779125 11675474109534716569010543)
          ·
            refine ⟨17513211164302074853515815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11675474109534716569010543 17513211164302074853515815)
            ·
              refine ⟨26269816746453112280273723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17513211164302074853515815 26269816746453112280273723)
              ·
                refine ⟨39404725119679668420410585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26269816746453112280273723 39404725119679668420410585)
                ·
                  refine ⟨29553543839759751315307939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39404725119679668420410585 29553543839759751315307939)
                  ·
                    refine ⟨44330315759639626972961909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29553543839759751315307939 44330315759639626972961909)
                    ·
                      refine ⟨4155967102466215028715179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44330315759639626972961909 4155967102466215028715179)
                      ·
                        rfl

theorem cell23_8093717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_8093717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093717 prefixEnd_8093717 := by exact prefixLift 8093717
  have htrace : WordTrace (prefixWord ++ tailWord_8093717) baseStart_8093717 baseEnd_8093717 := by
    simpa [prefixWord, tailWord_8093717, baseEnd_8093717] using wordTrace_append hprefix tailTrace_8093717
  have hstable : (prefixWord ++ tailWord_8093717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093717).length < 2 ^ (prefixWord ++ tailWord_8093717).sum := by decide
  have hdescent : baseEnd_8093717 < baseStart_8093717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093730 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_8093730 : Nat := 118140960795 + 8093730 * 2 ^ 59
def prefixEnd_8093730 : Nat := 4983230072969 + 3 ^ 40 * 8093730 * 2
def baseEnd_8093730 : Nat := 4155973777714723477852619

theorem tailTrace_8093730 : CollatzResearch.WordTrace tailWord_8093730 prefixEnd_8093730 4155973777714723477852619 := by
  unfold tailWord_8093730
  simp only [CollatzResearch.WordTrace]
  refine ⟨73800646241951495969665661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196801723311870655919108429 73800646241951495969665661)
  ·
    refine ⟨27675242340731810988624623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73800646241951495969665661 27675242340731810988624623)
    ·
      refine ⟨41512863511097716482936935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27675242340731810988624623 41512863511097716482936935)
      ·
        refine ⟨62269295266646574724405403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41512863511097716482936935 62269295266646574724405403)
        ·
          refine ⟨93403942899969862086608105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62269295266646574724405403 93403942899969862086608105)
          ·
            refine ⟨70052957174977396564956079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93403942899969862086608105 70052957174977396564956079)
            ·
              refine ⟨105079435762466094847434119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70052957174977396564956079 105079435762466094847434119)
              ·
                refine ⟨157619153643699142271151179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105079435762466094847434119 157619153643699142271151179)
                ·
                  refine ⟨236428730465548713406726769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157619153643699142271151179 236428730465548713406726769)
                  ·
                    refine ⟨177321547849161535055045077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236428730465548713406726769 177321547849161535055045077)
                    ·
                      refine ⟨4155973777714723477852619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177321547849161535055045077 4155973777714723477852619)
                      ·
                        rfl

theorem cell23_8093730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_8093730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093730 prefixEnd_8093730 := by exact prefixLift 8093730
  have htrace : WordTrace (prefixWord ++ tailWord_8093730) baseStart_8093730 baseEnd_8093730 := by
    simpa [prefixWord, tailWord_8093730, baseEnd_8093730] using wordTrace_append hprefix tailTrace_8093730
  have hstable : (prefixWord ++ tailWord_8093730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093730).length < 2 ^ (prefixWord ++ tailWord_8093730).sum := by decide
  have hdescent : baseEnd_8093730 < baseStart_8093730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093767 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 2, 5]
def baseStart_8093767 : Nat := 118140960795 + 8093767 * 2 ^ 59
def prefixEnd_8093767 : Nat := 4983230072969 + 3 ^ 40 * 8093767 * 2
def baseEnd_8093767 : Nat := 1385330925499646611029983

theorem tailTrace_8093767 : CollatzResearch.WordTrace tailWord_8093767 prefixEnd_8093767 1385330925499646611029983 := by
  unfold tailWord_8093767
  simp only [CollatzResearch.WordTrace]
  refine ⟨295203934468671939197759555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196802622979114626131839703 295203934468671939197759555)
  ·
    refine ⟨442805901703007908796639333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295203934468671939197759555 442805901703007908796639333)
    ·
      refine ⟨83026106569313982899369875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442805901703007908796639333 83026106569313982899369875)
      ·
        refine ⟨124539159853970974349054813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83026106569313982899369875 124539159853970974349054813)
        ·
          refine ⟨46702184945239115380895555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124539159853970974349054813 46702184945239115380895555)
          ·
            refine ⟨70053277417858673071343333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46702184945239115380895555 70053277417858673071343333)
            ·
              refine ⟨13134989515848501200876875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70053277417858673071343333 13134989515848501200876875)
              ·
                refine ⟨19702484273772751801315313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13134989515848501200876875 19702484273772751801315313)
                ·
                  refine ⟨14776863205329563850986485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19702484273772751801315313 14776863205329563850986485)
                  ·
                    refine ⟨1385330925499646611029983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14776863205329563850986485 1385330925499646611029983)
                    ·
                      rfl

theorem cell23_8093767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_8093767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093767 prefixEnd_8093767 := by exact prefixLift 8093767
  have htrace : WordTrace (prefixWord ++ tailWord_8093767) baseStart_8093767 baseEnd_8093767 := by
    simpa [prefixWord, tailWord_8093767, baseEnd_8093767] using wordTrace_append hprefix tailTrace_8093767
  have hstable : (prefixWord ++ tailWord_8093767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093767).length < 2 ^ (prefixWord ++ tailWord_8093767).sum := by decide
  have hdescent : baseEnd_8093767 < baseStart_8093767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093804 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 2, 4, 2]
def baseStart_8093804 : Nat := 118140960795 + 8093804 * 2 ^ 59
def prefixEnd_8093804 : Nat := 4983230072969 + 3 ^ 40 * 8093804 * 2
def baseEnd_8093804 : Nat := 4156011775283156188327279

theorem tailTrace_8093804 : CollatzResearch.WordTrace tailWord_8093804 prefixEnd_8093804 4156011775283156188327279 := by
  unfold tailWord_8093804
  simp only [CollatzResearch.WordTrace]
  refine ⟨147602641984768947258428233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196803522646358596344570977 147602641984768947258428233)
  ·
    refine ⟨110701981488576710443821175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147602641984768947258428233 110701981488576710443821175)
    ·
      refine ⟨166052972232865065665731763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110701981488576710443821175 166052972232865065665731763)
      ·
        refine ⟨249079458349297598498597645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166052972232865065665731763 249079458349297598498597645)
        ·
          refine ⟨93404796880986599436974117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249079458349297598498597645 93404796880986599436974117)
          ·
            refine ⟨17513399415184987394432647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93404796880986599436974117 17513399415184987394432647)
            ·
              refine ⟨26270099122777481091648971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17513399415184987394432647 26270099122777481091648971)
              ·
                refine ⟨39405148684166221637473457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26270099122777481091648971 39405148684166221637473457)
                ·
                  refine ⟨29553861513124666228105093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39405148684166221637473457 29553861513124666228105093)
                  ·
                    refine ⟨5541349033710874917769705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29553861513124666228105093 5541349033710874917769705)
                    ·
                      refine ⟨4156011775283156188327279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5541349033710874917769705 4156011775283156188327279)
                      ·
                        rfl

theorem cell23_8093804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_8093804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093804 prefixEnd_8093804 := by exact prefixLift 8093804
  have htrace : WordTrace (prefixWord ++ tailWord_8093804) baseStart_8093804 baseEnd_8093804 := by
    simpa [prefixWord, tailWord_8093804, baseEnd_8093804] using wordTrace_append hprefix tailTrace_8093804
  have hstable : (prefixWord ++ tailWord_8093804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093804).length < 2 ^ (prefixWord ++ tailWord_8093804).sum := by decide
  have hdescent : baseEnd_8093804 < baseStart_8093804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093814 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_8093814 : Nat := 118140960795 + 8093814 * 2 ^ 59
def prefixEnd_8093814 : Nat := 4983230072969 + 3 ^ 40 * 8093814 * 2
def baseEnd_8093814 : Nat := 1385338970029900383067411

theorem tailTrace_8093814 : CollatzResearch.WordTrace tailWord_8093814 prefixEnd_8093814 1385338970029900383067411 := by
  unfold tailWord_8093814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18450353043718854139045031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196803765799667777483146997 18450353043718854139045031)
  ·
    refine ⟨27675529565578281208567547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18450353043718854139045031 27675529565578281208567547)
    ·
      refine ⟨41513294348367421812851321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27675529565578281208567547 41513294348367421812851321)
      ·
        refine ⟨31134970761275566359638491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41513294348367421812851321 31134970761275566359638491)
        ·
          refine ⟨46702456141913349539457737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31134970761275566359638491 46702456141913349539457737)
          ·
            refine ⟨35026842106435012154593303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46702456141913349539457737 35026842106435012154593303)
            ·
              refine ⟨52540263159652518231889955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35026842106435012154593303 52540263159652518231889955)
              ·
                refine ⟨78810394739478777347834933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52540263159652518231889955 78810394739478777347834933)
                ·
                  refine ⟨7388474506826135376359525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78810394739478777347834933 7388474506826135376359525)
                  ·
                    refine ⟨1385338970029900383067411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7388474506826135376359525 1385338970029900383067411)
                    ·
                      rfl

theorem cell23_8093814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_8093814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093814 prefixEnd_8093814 := by exact prefixLift 8093814
  have htrace : WordTrace (prefixWord ++ tailWord_8093814) baseStart_8093814 baseEnd_8093814 := by
    simpa [prefixWord, tailWord_8093814, baseEnd_8093814] using wordTrace_append hprefix tailTrace_8093814
  have hstable : (prefixWord ++ tailWord_8093814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093814).length < 2 ^ (prefixWord ++ tailWord_8093814).sum := by decide
  have hdescent : baseEnd_8093814 < baseStart_8093814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093874 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_8093874 : Nat := 118140960795 + 8093874 * 2 ^ 59
def prefixEnd_8093874 : Nat := 4983230072969 + 3 ^ 40 * 8093874 * 2
def baseEnd_8093874 : Nat := 1385349239642990304817319

theorem tailTrace_8093874 : CollatzResearch.WordTrace tailWord_8093874 prefixEnd_8093874 1385349239642990304817319 := by
  unfold tailWord_8093874
  simp only [CollatzResearch.WordTrace]
  refine ⟨73801959269821074117976169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196805224719522864314603117 73801959269821074117976169)
  ·
    refine ⟨55351469452365805588482127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73801959269821074117976169 55351469452365805588482127)
    ·
      refine ⟨83027204178548708382723191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55351469452365805588482127 83027204178548708382723191)
      ·
        refine ⟨124540806267823062574084787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83027204178548708382723191 124540806267823062574084787)
        ·
          refine ⟨186811209401734593861127181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124540806267823062574084787 186811209401734593861127181)
          ·
            refine ⟨70054203525650472697922693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186811209401734593861127181 70054203525650472697922693)
            ·
              refine ⟨13135163161059463630860505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70054203525650472697922693 13135163161059463630860505)
              ·
                refine ⟨9851372370794597723145379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13135163161059463630860505 9851372370794597723145379)
                ·
                  refine ⟨14777058556191896584718069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9851372370794597723145379 14777058556191896584718069)
                  ·
                    refine ⟨1385349239642990304817319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14777058556191896584718069 1385349239642990304817319)
                    ·
                      rfl

theorem cell23_8093874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_8093874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093874 prefixEnd_8093874 := by exact prefixLift 8093874
  have htrace : WordTrace (prefixWord ++ tailWord_8093874) baseStart_8093874 baseEnd_8093874 := by
    simpa [prefixWord, tailWord_8093874, baseEnd_8093874] using wordTrace_append hprefix tailTrace_8093874
  have hstable : (prefixWord ++ tailWord_8093874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093874).length < 2 ^ (prefixWord ++ tailWord_8093874).sum := by decide
  have hdescent : baseEnd_8093874 < baseStart_8093874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093888 : List Nat := [2, 1, 1, 2, 5, 1, 3, 3, 1, 1, 3]
def baseStart_8093888 : Nat := 118140960795 + 8093888 * 2 ^ 59
def prefixEnd_8093888 : Nat := 4983230072969 + 3 ^ 40 * 8093888 * 2
def baseEnd_8093888 : Nat := 4156054907658133859676893

theorem tailTrace_8093888 : CollatzResearch.WordTrace tailWord_8093888 prefixEnd_8093888 4156054907658133859676893 := by
  unfold tailWord_8093888
  simp only [CollatzResearch.WordTrace]
  refine ⟨147604173850616788431457159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196805565134155717908609545 147604173850616788431457159)
  ·
    refine ⟨221406260775925182647185739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147604173850616788431457159 221406260775925182647185739)
    ·
      refine ⟨332109391163887773970778609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221406260775925182647185739 332109391163887773970778609)
      ·
        refine ⟨249082043372915830478083957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332109391163887773970778609 249082043372915830478083957)
        ·
          refine ⟨23351441566210859107320371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249082043372915830478083957 23351441566210859107320371)
          ·
            refine ⟨35027162349316288660980557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23351441566210859107320371 35027162349316288660980557)
            ·
              refine ⟨13135185880993608247867709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35027162349316288660980557 13135185880993608247867709)
              ·
                refine ⟨4925694705372603092950391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13135185880993608247867709 4925694705372603092950391)
                ·
                  refine ⟨7388542058058904639425587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925694705372603092950391 7388542058058904639425587)
                  ·
                    refine ⟨11082813087088356959138381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7388542058058904639425587 11082813087088356959138381)
                    ·
                      refine ⟨4156054907658133859676893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11082813087088356959138381 4156054907658133859676893)
                      ·
                        rfl

theorem cell23_8093888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 1, 3].length) (baseStart_8093888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093888 prefixEnd_8093888 := by exact prefixLift 8093888
  have htrace : WordTrace (prefixWord ++ tailWord_8093888) baseStart_8093888 baseEnd_8093888 := by
    simpa [prefixWord, tailWord_8093888, baseEnd_8093888] using wordTrace_append hprefix tailTrace_8093888
  have hstable : (prefixWord ++ tailWord_8093888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093888).length < 2 ^ (prefixWord ++ tailWord_8093888).sum := by decide
  have hdescent : baseEnd_8093888 < baseStart_8093888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093944 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 6, 1, 3]
def baseStart_8093944 : Nat := 118140960795 + 8093944 * 2 ^ 59
def prefixEnd_8093944 : Nat := 4983230072969 + 3 ^ 40 * 8093944 * 2
def baseEnd_8093944 : Nat := 4156083662574785640576635

theorem tailTrace_8093944 : CollatzResearch.WordTrace tailWord_8093944 prefixEnd_8093944 4156083662574785640576635 := by
  unfold tailWord_8093944
  simp only [CollatzResearch.WordTrace]
  refine ⟨147605195094515349213476443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196806926792687132284635257 147605195094515349213476443)
  ·
    refine ⟨221407792641773023820214665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147605195094515349213476443 221407792641773023820214665)
    ·
      refine ⟨166055844481329767865160999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221407792641773023820214665 166055844481329767865160999)
      ·
        refine ⟨249083766721994651797741499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166055844481329767865160999 249083766721994651797741499)
        ·
          refine ⟨373625650082991977696612249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249083766721994651797741499 373625650082991977696612249)
          ·
            refine ⟨280219237562243983272459187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373625650082991977696612249 280219237562243983272459187)
            ·
              refine ⟨420328856343365974908688781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280219237562243983272459187 420328856343365974908688781)
              ·
                refine ⟨157623321128762240590758293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420328856343365974908688781 157623321128762240590758293)
                ·
                  refine ⟨7388593177910730027691795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157623321128762240590758293 7388593177910730027691795)
                  ·
                    refine ⟨11082889766866095041537693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7388593177910730027691795 11082889766866095041537693)
                    ·
                      refine ⟨4156083662574785640576635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11082889766866095041537693 4156083662574785640576635)
                      ·
                        rfl

theorem cell23_8093944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_8093944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093944 prefixEnd_8093944 := by exact prefixLift 8093944
  have htrace : WordTrace (prefixWord ++ tailWord_8093944) baseStart_8093944 baseEnd_8093944 := by
    simpa [prefixWord, tailWord_8093944, baseEnd_8093944] using wordTrace_append hprefix tailTrace_8093944
  have hstable : (prefixWord ++ tailWord_8093944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093944).length < 2 ^ (prefixWord ++ tailWord_8093944).sum := by decide
  have hdescent : baseEnd_8093944 < baseStart_8093944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093948 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_8093948 : Nat := 118140960795 + 8093948 * 2 ^ 59
def prefixEnd_8093948 : Nat := 4983230072969 + 3 ^ 40 * 8093948 * 2
def baseEnd_8093948 : Nat := 4156085716497403624926617

theorem tailTrace_8093948 : CollatzResearch.WordTrace tailWord_8093948 prefixEnd_8093948 4156085716497403624926617 := by
  unfold tailWord_8093948
  simp only [CollatzResearch.WordTrace]
  refine ⟨147605268040508103555049249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196807024054010804740065665 147605268040508103555049249)
  ·
    refine ⟨110703951030381077666286937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147605268040508103555049249 110703951030381077666286937)
    ·
      refine ⟨83027963272785808249715203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110703951030381077666286937 83027963272785808249715203)
      ·
        refine ⟨124541944909178712374572805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83027963272785808249715203 124541944909178712374572805)
        ·
          refine ⟨23351614670471008570232401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124541944909178712374572805 23351614670471008570232401)
          ·
            refine ⟨17513711002853256427674301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23351614670471008570232401 17513711002853256427674301)
            ·
              refine ⟨6567641626069971160377863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17513711002853256427674301 6567641626069971160377863)
              ·
                refine ⟨9851462439104956740566795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567641626069971160377863 9851462439104956740566795)
                ·
                  refine ⟨14777193658657435110850193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9851462439104956740566795 14777193658657435110850193)
                  ·
                    refine ⟨11082895243993076333137645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14777193658657435110850193 11082895243993076333137645)
                    ·
                      refine ⟨4156085716497403624926617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11082895243993076333137645 4156085716497403624926617)
                      ·
                        rfl

theorem cell23_8093948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_8093948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093948 prefixEnd_8093948 := by exact prefixLift 8093948
  have htrace : WordTrace (prefixWord ++ tailWord_8093948) baseStart_8093948 baseEnd_8093948 := by
    simpa [prefixWord, tailWord_8093948, baseEnd_8093948] using wordTrace_append hprefix tailTrace_8093948
  have hstable : (prefixWord ++ tailWord_8093948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093948).length < 2 ^ (prefixWord ++ tailWord_8093948).sum := by decide
  have hdescent : baseEnd_8093948 < baseStart_8093948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8093961 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 3]
def baseStart_8093961 : Nat := 118140960795 + 8093961 * 2 ^ 59
def prefixEnd_8093961 : Nat := 4983230072969 + 3 ^ 40 * 8093961 * 2
def baseEnd_8093961 : Nat := 4156092391745912074064057

theorem tailTrace_8093961 : CollatzResearch.WordTrace tailWord_8093961 prefixEnd_8093961 4156092391745912074064057 := by
  unfold tailWord_8093961
  simp only [CollatzResearch.WordTrace]
  refine ⟨295211010229969110330321737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196807340153312740220214491 295211010229969110330321737)
  ·
    refine ⟨221408257672476832747741303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295211010229969110330321737 221408257672476832747741303)
    ·
      refine ⟨332112386508715249121611955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221408257672476832747741303 332112386508715249121611955)
      ·
        refine ⟨498168579763072873682417933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332112386508715249121611955 498168579763072873682417933)
        ·
          refine ⟨186813217411152327630906725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498168579763072873682417933 186813217411152327630906725)
          ·
            refine ⟨35027478264591061430795011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186813217411152327630906725 35027478264591061430795011)
            ·
              refine ⟨52541217396886592146192517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35027478264591061430795011 52541217396886592146192517)
              ·
                refine ⟨9851478261916236027411097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52541217396886592146192517 9851478261916236027411097)
                ·
                  refine ⟨7388608696437177020558323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9851478261916236027411097 7388608696437177020558323)
                  ·
                    refine ⟨11082913044655765530837485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7388608696437177020558323 11082913044655765530837485)
                    ·
                      refine ⟨4156092391745912074064057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11082913044655765530837485 4156092391745912074064057)
                      ·
                        rfl

theorem cell23_8093961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 3].length) (baseStart_8093961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8093961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8093961 prefixEnd_8093961 := by exact prefixLift 8093961
  have htrace : WordTrace (prefixWord ++ tailWord_8093961) baseStart_8093961 baseEnd_8093961 := by
    simpa [prefixWord, tailWord_8093961, baseEnd_8093961] using wordTrace_append hprefix tailTrace_8093961
  have hstable : (prefixWord ++ tailWord_8093961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8093961).length < 2 ^ (prefixWord ++ tailWord_8093961).sum := by decide
  have hdescent : baseEnd_8093961 < baseStart_8093961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8093961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094058 : List Nat := [3, 1, 3, 3, 1, 1, 3, 3, 5]
def baseStart_8094058 : Nat := 118140960795 + 8094058 * 2 ^ 59
def prefixEnd_8094058 : Nat := 4983230072969 + 3 ^ 40 * 8094058 * 2
def baseEnd_8094058 : Nat := 461793577707710910505679

theorem tailTrace_8094058 : CollatzResearch.WordTrace tailWord_8094058 prefixEnd_8094058 461793577707710910505679 := by
  unfold tailWord_8094058
  simp only [CollatzResearch.WordTrace]
  refine ⟨73803637027654423974150707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196809698740411797264401885 73803637027654423974150707)
  ·
    refine ⟨110705455541481635961226061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73803637027654423974150707 110705455541481635961226061)
    ·
      refine ⟨41514545828055613485459773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110705455541481635961226061 41514545828055613485459773)
      ·
        refine ⟨15567954685520855057047415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41514545828055613485459773 15567954685520855057047415)
        ·
          refine ⟨23351932028281282585571123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15567954685520855057047415 23351932028281282585571123)
          ·
            refine ⟨35027898042421923878356685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23351932028281282585571123 35027898042421923878356685)
            ·
              refine ⟨13135461765908221454383757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35027898042421923878356685 13135461765908221454383757)
              ·
                refine ⟨4925798162215583045393909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13135461765908221454383757 4925798162215583045393909)
                ·
                  refine ⟨461793577707710910505679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4925798162215583045393909 461793577707710910505679)
                  ·
                    rfl

theorem cell23_8094058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_8094058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094058 prefixEnd_8094058 := by exact prefixLift 8094058
  have htrace : WordTrace (prefixWord ++ tailWord_8094058) baseStart_8094058 baseEnd_8094058 := by
    simpa [prefixWord, tailWord_8094058, baseEnd_8094058] using wordTrace_append hprefix tailTrace_8094058
  have hstable : (prefixWord ++ tailWord_8094058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094058).length < 2 ^ (prefixWord ++ tailWord_8094058).sum := by decide
  have hdescent : baseEnd_8094058 < baseStart_8094058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094067 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 1, 10]
def baseStart_8094067 : Nat := 118140960795 + 8094067 * 2 ^ 59
def prefixEnd_8094067 : Nat := 4983230072969 + 3 ^ 40 * 8094067 * 2
def baseEnd_8094067 : Nat := 1385382273565096219779523

theorem tailTrace_8094067 : CollatzResearch.WordTrace tailWord_8094067 prefixEnd_8094067 1385382273565096219779523 := by
  unfold tailWord_8094067
  simp only [CollatzResearch.WordTrace]
  refine ⟨295214876367585090433680455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196809917578390060289120303 295214876367585090433680455)
  ·
    refine ⟨442822314551377635650520683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295214876367585090433680455 442822314551377635650520683)
    ·
      refine ⟨664233471827066453475781025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442822314551377635650520683 664233471827066453475781025)
      ·
        refine ⟨498175103870299840106835769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664233471827066453475781025 498175103870299840106835769)
        ·
          refine ⟨373631327902724880080126827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498175103870299840106835769 373631327902724880080126827)
          ·
            refine ⟨560446991854087320120190241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373631327902724880080126827 560446991854087320120190241)
            ·
              refine ⟨420335243890565490090142681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560446991854087320120190241 420335243890565490090142681)
              ·
                refine ⟨315251432917924117567607011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420335243890565490090142681 315251432917924117567607011)
                ·
                  refine ⟨472877149376886176351410517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315251432917924117567607011 472877149376886176351410517)
                  ·
                    refine ⟨1385382273565096219779523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 472877149376886176351410517 1385382273565096219779523)
                    ·
                      rfl

theorem cell23_8094067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 10].length) (baseStart_8094067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094067 prefixEnd_8094067 := by exact prefixLift 8094067
  have htrace : WordTrace (prefixWord ++ tailWord_8094067) baseStart_8094067 baseEnd_8094067 := by
    simpa [prefixWord, tailWord_8094067, baseEnd_8094067] using wordTrace_append hprefix tailTrace_8094067
  have hstable : (prefixWord ++ tailWord_8094067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094067).length < 2 ^ (prefixWord ++ tailWord_8094067).sum := by decide
  have hdescent : baseEnd_8094067 < baseStart_8094067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094081 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_8094081 : Nat := 118140960795 + 8094081 * 2 ^ 59
def prefixEnd_8094081 : Nat := 4983230072969 + 3 ^ 40 * 8094081 * 2
def baseEnd_8094081 : Nat := 4156154009424451604563505

theorem tailTrace_8094081 : CollatzResearch.WordTrace tailWord_8094081 prefixEnd_8094081 4156154009424451604563505 := by
  unfold tailWord_8094081
  simp only [CollatzResearch.WordTrace]
  refine ⟨295215386989534370824690097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196810257993022913883126731 295215386989534370824690097)
  ·
    refine ⟨221411540242150778118517573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295215386989534370824690097 221411540242150778118517573)
    ·
      refine ⟨41514663795403270897222045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221411540242150778118517573 41514663795403270897222045)
      ·
        refine ⟨15567998923276226586458267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41514663795403270897222045 15567998923276226586458267)
        ·
          refine ⟨23351998384914339879687401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15567998923276226586458267 23351998384914339879687401)
          ·
            refine ⟨17513998788685754909765551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23351998384914339879687401 17513998788685754909765551)
            ·
              refine ⟨26270998183028632364648327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17513998788685754909765551 26270998183028632364648327)
              ·
                refine ⟨39406497274542948546972491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26270998183028632364648327 39406497274542948546972491)
                ·
                  refine ⟨59109745911814422820458737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39406497274542948546972491 59109745911814422820458737)
                  ·
                    refine ⟨44332309433860817115344053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59109745911814422820458737 44332309433860817115344053)
                    ·
                      refine ⟨4156154009424451604563505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44332309433860817115344053 4156154009424451604563505)
                      ·
                        rfl

theorem cell23_8094081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_8094081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094081 prefixEnd_8094081 := by exact prefixLift 8094081
  have htrace : WordTrace (prefixWord ++ tailWord_8094081) baseStart_8094081 baseEnd_8094081 := by
    simpa [prefixWord, tailWord_8094081, baseEnd_8094081] using wordTrace_append hprefix tailTrace_8094081
  have hstable : (prefixWord ++ tailWord_8094081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094081).length < 2 ^ (prefixWord ++ tailWord_8094081).sum := by decide
  have hdescent : baseEnd_8094081 < baseStart_8094081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094135 : List Nat := [1, 1, 3, 1, 3, 3, 4, 2, 1, 4]
def baseStart_8094135 : Nat := 118140960795 + 8094135 * 2 ^ 59
def prefixEnd_8094135 : Nat := 4983230072969 + 3 ^ 40 * 8094135 * 2
def baseEnd_8094135 : Nat := 1385393912459931464429419

theorem tailTrace_8094135 : CollatzResearch.WordTrace tailWord_8094135 prefixEnd_8094135 1385393912459931464429419 := by
  unfold tailWord_8094135
  simp only [CollatzResearch.WordTrace]
  refine ⟨295217356531338738047155859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196811571020892492031437239 295217356531338738047155859)
  ·
    refine ⟨442826034797008107070733789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295217356531338738047155859 442826034797008107070733789)
    ·
      refine ⟨166059763048878040151525171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442826034797008107070733789 166059763048878040151525171)
      ·
        refine ⟨249089644573317060227287757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166059763048878040151525171 249089644573317060227287757)
        ·
          refine ⟨93408616714993897585232909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249089644573317060227287757 93408616714993897585232909)
          ·
            refine ⟨35028231268122711594462341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93408616714993897585232909 35028231268122711594462341)
            ·
              refine ⟨6567793362773008423961689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35028231268122711594462341 6567793362773008423961689)
              ·
                refine ⟨4925845022079756317971267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6567793362773008423961689 4925845022079756317971267)
                ·
                  refine ⟨7388767533119634476956901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925845022079756317971267 7388767533119634476956901)
                  ·
                    refine ⟨1385393912459931464429419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7388767533119634476956901 1385393912459931464429419)
                    ·
                      rfl

theorem cell23_8094135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_8094135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094135 prefixEnd_8094135 := by exact prefixLift 8094135
  have htrace : WordTrace (prefixWord ++ tailWord_8094135) baseStart_8094135 baseEnd_8094135 := by
    simpa [prefixWord, tailWord_8094135, baseEnd_8094135] using wordTrace_append hprefix tailTrace_8094135
  have hstable : (prefixWord ++ tailWord_8094135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094135).length < 2 ^ (prefixWord ++ tailWord_8094135).sum := by decide
  have hdescent : baseEnd_8094135 < baseStart_8094135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094154 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_8094154 : Nat := 118140960795 + 8094154 * 2 ^ 59
def prefixEnd_8094154 : Nat := 4983230072969 + 3 ^ 40 * 8094154 * 2
def baseEnd_8094154 : Nat := 4156191493512229818950669

theorem tailTrace_8094154 : CollatzResearch.WordTrace tailWord_8094154 prefixEnd_8094154 4156191493512229818950669 := by
  unfold tailWord_8094154
  simp only [CollatzResearch.WordTrace]
  refine ⟨73804512379567476073024379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196812033012179936194731677 73804512379567476073024379)
  ·
    refine ⟨110706768569351214109536569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73804512379567476073024379 110706768569351214109536569)
    ·
      refine ⟨83030076427013410582152427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110706768569351214109536569 83030076427013410582152427)
      ·
        refine ⟨124545114640520115873228641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83030076427013410582152427 124545114640520115873228641)
        ·
          refine ⟨93408835980390086904921481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124545114640520115873228641 93408835980390086904921481)
          ·
            refine ⟨70056626985292565178691111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93408835980390086904921481 70056626985292565178691111)
            ·
              refine ⟨105084940477938847768036667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70056626985292565178691111 105084940477938847768036667)
              ·
                refine ⟨157627410716908271652055001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105084940477938847768036667 157627410716908271652055001)
                ·
                  refine ⟨118220558037681203739041251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157627410716908271652055001 118220558037681203739041251)
                  ·
                    refine ⟨177330837056521805608561877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118220558037681203739041251 177330837056521805608561877)
                    ·
                      refine ⟨4156191493512229818950669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177330837056521805608561877 4156191493512229818950669)
                      ·
                        rfl

theorem cell23_8094154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_8094154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094154 prefixEnd_8094154 := by exact prefixLift 8094154
  have htrace : WordTrace (prefixWord ++ tailWord_8094154) baseStart_8094154 baseEnd_8094154 := by
    simpa [prefixWord, tailWord_8094154, baseEnd_8094154] using wordTrace_append hprefix tailTrace_8094154
  have hstable : (prefixWord ++ tailWord_8094154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094154).length < 2 ^ (prefixWord ++ tailWord_8094154).sum := by decide
  have hdescent : baseEnd_8094154 < baseStart_8094154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094162 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_8094162 : Nat := 118140960795 + 8094162 * 2 ^ 59
def prefixEnd_8094162 : Nat := 4983230072969 + 3 ^ 40 * 8094162 * 2
def baseEnd_8094162 : Nat := 4156195601357465787650633

theorem tailTrace_8094162 : CollatzResearch.WordTrace tailWord_8094162 prefixEnd_8094162 4156195601357465787650633 := by
  unfold tailWord_8094162
  simp only [CollatzResearch.WordTrace]
  refine ⟨73804585325560230414597185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196812227534827281105592493 73804585325560230414597185)
  ·
    refine ⟨55353438994170172810947889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73804585325560230414597185 55353438994170172810947889)
    ·
      refine ⟨41515079245627629608210917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55353438994170172810947889 41515079245627629608210917)
      ·
        refine ⟨7784077358555180551539547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41515079245627629608210917 7784077358555180551539547)
        ·
          refine ⟨11676116037832770827309321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784077358555180551539547 11676116037832770827309321)
          ·
            refine ⟨8757087028374578120481991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11676116037832770827309321 8757087028374578120481991)
            ·
              refine ⟨13135630542561867180722987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757087028374578120481991 13135630542561867180722987)
              ·
                refine ⟨19703445813842800771084481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13135630542561867180722987 19703445813842800771084481)
                ·
                  refine ⟨14777584360382100578313361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19703445813842800771084481 14777584360382100578313361)
                  ·
                    refine ⟨11083188270286575433735021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14777584360382100578313361 11083188270286575433735021)
                    ·
                      refine ⟨4156195601357465787650633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11083188270286575433735021 4156195601357465787650633)
                      ·
                        rfl

theorem cell23_8094162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_8094162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094162 prefixEnd_8094162 := by exact prefixLift 8094162
  have htrace : WordTrace (prefixWord ++ tailWord_8094162) baseStart_8094162 baseEnd_8094162 := by
    simpa [prefixWord, tailWord_8094162, baseEnd_8094162] using wordTrace_append hprefix tailTrace_8094162
  have hstable : (prefixWord ++ tailWord_8094162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094162).length < 2 ^ (prefixWord ++ tailWord_8094162).sum := by decide
  have hdescent : baseEnd_8094162 < baseStart_8094162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094175 : List Nat := [1, 1, 2, 3, 3, 2, 1, 5, 1, 1, 3]
def baseStart_8094175 : Nat := 118140960795 + 8094175 * 2 ^ 59
def prefixEnd_8094175 : Nat := 4983230072969 + 3 ^ 40 * 8094175 * 2
def baseEnd_8094175 : Nat := 4156202276605974236788073

theorem tailTrace_8094175 : CollatzResearch.WordTrace tailWord_8094175 prefixEnd_8094175 4156202276605974236788073 := by
  unfold tailWord_8094175
  simp only [CollatzResearch.WordTrace]
  refine ⟨295218815451193824878611979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196812543634129216585741319 295218815451193824878611979)
  ·
    refine ⟨442828223176790737317917969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295218815451193824878611979 442828223176790737317917969)
    ·
      refine ⟨332121167382593052988438477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442828223176790737317917969 332121167382593052988438477)
      ·
        refine ⟨124545437768472394870664429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332121167382593052988438477 124545437768472394870664429)
        ·
          refine ⟨46704539163177148076499161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124545437768472394870664429 46704539163177148076499161)
          ·
            refine ⟨35028404372382861057374371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46704539163177148076499161 35028404372382861057374371)
            ·
              refine ⟨52542606558574291586061557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35028404372382861057374371 52542606558574291586061557)
              ·
                refine ⟨4925869364866339836193271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52542606558574291586061557 4925869364866339836193271)
                ·
                  refine ⟨7388804047299509754289907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925869364866339836193271 7388804047299509754289907)
                  ·
                    refine ⟨11083206070949264631434861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7388804047299509754289907 11083206070949264631434861)
                    ·
                      refine ⟨4156202276605974236788073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11083206070949264631434861 4156202276605974236788073)
                      ·
                        rfl

theorem cell23_8094175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_8094175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094175 prefixEnd_8094175 := by exact prefixLift 8094175
  have htrace : WordTrace (prefixWord ++ tailWord_8094175) baseStart_8094175 baseEnd_8094175 := by
    simpa [prefixWord, tailWord_8094175, baseEnd_8094175] using wordTrace_append hprefix tailTrace_8094175
  have hstable : (prefixWord ++ tailWord_8094175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094175).length < 2 ^ (prefixWord ++ tailWord_8094175).sum := by decide
  have hdescent : baseEnd_8094175 < baseStart_8094175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094201 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 3]
def baseStart_8094201 : Nat := 118140960795 + 8094201 * 2 ^ 59
def prefixEnd_8094201 : Nat := 4983230072969 + 3 ^ 40 * 8094201 * 2
def baseEnd_8094201 : Nat := 4156215627102991135062953

theorem tailTrace_8094201 : CollatzResearch.WordTrace tailWord_8094201 prefixEnd_8094201 4156215627102991135062953 := by
  unfold tailWord_8094201
  simp only [CollatzResearch.WordTrace]
  refine ⟨295219763749099631319058457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196813175832733087546038971 295219763749099631319058457)
  ·
    refine ⟨221414822811824723489293843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295219763749099631319058457 221414822811824723489293843)
    ·
      refine ⟨332122234217737085233940765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221414822811824723489293843 332122234217737085233940765)
      ·
        refine ⟨124545837831651406962727787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332122234217737085233940765 124545837831651406962727787)
        ·
          refine ⟨186818756747477110444091681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124545837831651406962727787 186818756747477110444091681)
          ·
            refine ⟨140114067560607832833068761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186818756747477110444091681 140114067560607832833068761)
            ·
              refine ⟨105085550670455874624801571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140114067560607832833068761 105085550670455874624801571)
              ·
                refine ⟨157628326005683811937202357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105085550670455874624801571 157628326005683811937202357)
                ·
                  refine ⟨14777655563032857369112721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157628326005683811937202357 14777655563032857369112721)
                  ·
                    refine ⟨11083241672274643026834541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14777655563032857369112721 11083241672274643026834541)
                    ·
                      refine ⟨4156215627102991135062953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11083241672274643026834541 4156215627102991135062953)
                      ·
                        rfl

theorem cell23_8094201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_8094201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094201 prefixEnd_8094201 := by exact prefixLift 8094201
  have htrace : WordTrace (prefixWord ++ tailWord_8094201) baseStart_8094201 baseEnd_8094201 := by
    simpa [prefixWord, tailWord_8094201, baseEnd_8094201] using wordTrace_append hprefix tailTrace_8094201
  have hstable : (prefixWord ++ tailWord_8094201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094201).length < 2 ^ (prefixWord ++ tailWord_8094201).sum := by decide
  have hdescent : baseEnd_8094201 < baseStart_8094201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094204 : List Nat := [2, 2, 2, 1, 2, 1, 1, 12]
def baseStart_8094204 : Nat := 118140960795 + 8094204 * 2 ^ 59
def prefixEnd_8094204 : Nat := 4983230072969 + 3 ^ 40 * 8094204 * 2
def baseEnd_8094204 : Nat := 153933969168331652715757

theorem tailTrace_8094204 : CollatzResearch.WordTrace tailWord_8094204 prefixEnd_8094204 153933969168331652715757 := by
  unfold tailWord_8094204
  simp only [CollatzResearch.WordTrace]
  refine ⟨147609936584044381415708833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196813248778725841887611777 147609936584044381415708833)
  ·
    refine ⟨110707452438033286061781625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147609936584044381415708833 110707452438033286061781625)
    ·
      refine ⟨83030589328524964546336219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110707452438033286061781625 83030589328524964546336219)
      ·
        refine ⟨124545883992787446819504329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83030589328524964546336219 124545883992787446819504329)
        ·
          refine ⟨93409412994590585114628247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124545883992787446819504329 93409412994590585114628247)
          ·
            refine ⟨140114119491885877671942371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93409412994590585114628247 140114119491885877671942371)
            ·
              refine ⟨210171179237828816507913557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140114119491885877671942371 210171179237828816507913557)
              ·
                refine ⟨153933969168331652715757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 210171179237828816507913557 153933969168331652715757)
                ·
                  rfl

theorem cell23_8094204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 12].length) (baseStart_8094204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094204 prefixEnd_8094204 := by exact prefixLift 8094204
  have htrace : WordTrace (prefixWord ++ tailWord_8094204) baseStart_8094204 baseEnd_8094204 := by
    simpa [prefixWord, tailWord_8094204, baseEnd_8094204] using wordTrace_append hprefix tailTrace_8094204
  have hstable : (prefixWord ++ tailWord_8094204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094204).length < 2 ^ (prefixWord ++ tailWord_8094204).sum := by decide
  have hdescent : baseEnd_8094204 < baseStart_8094204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094215 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_8094215 : Nat := 118140960795 + 8094215 * 2 ^ 59
def prefixEnd_8094215 : Nat := 4983230072969 + 3 ^ 40 * 8094215 * 2
def baseEnd_8094215 : Nat := 4156222815832154080287889

theorem tailTrace_8094215 : CollatzResearch.WordTrace tailWord_8094215 prefixEnd_8094215 4156222815832154080287889 := by
  unfold tailWord_8094215
  simp only [CollatzResearch.WordTrace]
  refine ⟨295220274371048911710068099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196813516247365941140045399 295220274371048911710068099)
  ·
    refine ⟨442830411556573367565102149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295220274371048911710068099 442830411556573367565102149)
    ·
      refine ⟨83030702166857506418456653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442830411556573367565102149 83030702166857506418456653)
      ·
        refine ⟨31136513312571564906921245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83030702166857506418456653 31136513312571564906921245)
        ·
          refine ⟨11676192492214336840095467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31136513312571564906921245 11676192492214336840095467)
          ·
            refine ⟨17514288738321505260143201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11676192492214336840095467 17514288738321505260143201)
            ·
              refine ⟨13135716553741128945107401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17514288738321505260143201 13135716553741128945107401)
              ·
                refine ⟨9851787415305846708830551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13135716553741128945107401 9851787415305846708830551)
                ·
                  refine ⟨14777681122958770063245827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9851787415305846708830551 14777681122958770063245827)
                  ·
                    refine ⟨22166521684438155094868741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14777681122958770063245827 22166521684438155094868741)
                    ·
                      refine ⟨4156222815832154080287889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22166521684438155094868741 4156222815832154080287889)
                      ·
                        rfl

theorem cell23_8094215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_8094215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094215 prefixEnd_8094215 := by exact prefixLift 8094215
  have htrace : WordTrace (prefixWord ++ tailWord_8094215) baseStart_8094215 baseEnd_8094215 := by
    simpa [prefixWord, tailWord_8094215, baseEnd_8094215] using wordTrace_append hprefix tailTrace_8094215
  have hstable : (prefixWord ++ tailWord_8094215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094215).length < 2 ^ (prefixWord ++ tailWord_8094215).sum := by decide
  have hdescent : baseEnd_8094215 < baseStart_8094215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094265 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 3]
def baseStart_8094265 : Nat := 118140960795 + 8094265 * 2 ^ 59
def prefixEnd_8094265 : Nat := 4983230072969 + 3 ^ 40 * 8094265 * 2
def baseEnd_8094265 : Nat := 4156248489864878884662659

theorem tailTrace_8094265 : CollatzResearch.WordTrace tailWord_8094265 prefixEnd_8094265 4156248489864878884662659 := by
  unfold tailWord_8094265
  simp only [CollatzResearch.WordTrace]
  refine ⟨295222098020867770249388249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196814732013911846832925499 295222098020867770249388249)
  ·
    refine ⟨221416573515650827687041187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295222098020867770249388249 221416573515650827687041187)
    ·
      refine ⟨332124860273476241530561781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221416573515650827687041187 332124860273476241530561781)
      ·
        refine ⟨31136705650638397643490167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332124860273476241530561781 31136705650638397643490167)
        ·
          refine ⟨46705058475957596465235251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31136705650638397643490167 46705058475957596465235251)
          ·
            refine ⟨70057587713936394697852877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46705058475957596465235251 70057587713936394697852877)
            ·
              refine ⟨26271595392726148011694829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70057587713936394697852877 26271595392726148011694829)
              ·
                refine ⟨9851848272272305504385561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26271595392726148011694829 9851848272272305504385561)
                ·
                  refine ⟨7388886204204229128289171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9851848272272305504385561 7388886204204229128289171)
                  ·
                    refine ⟨11083329306306343692433757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7388886204204229128289171 11083329306306343692433757)
                    ·
                      refine ⟨4156248489864878884662659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11083329306306343692433757 4156248489864878884662659)
                      ·
                        rfl

theorem cell23_8094265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_8094265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094265 prefixEnd_8094265 := by exact prefixLift 8094265
  have htrace : WordTrace (prefixWord ++ tailWord_8094265) baseStart_8094265 baseEnd_8094265 := by
    simpa [prefixWord, tailWord_8094265, baseEnd_8094265] using wordTrace_append hprefix tailTrace_8094265
  have hstable : (prefixWord ++ tailWord_8094265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094265).length < 2 ^ (prefixWord ++ tailWord_8094265).sum := by decide
  have hdescent : baseEnd_8094265 < baseStart_8094265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094311 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 7]
def baseStart_8094311 : Nat := 118140960795 + 8094311 * 2 ^ 59
def prefixEnd_8094311 : Nat := 4983230072969 + 3 ^ 40 * 8094311 * 2
def baseEnd_8094311 : Nat := 461808012219442856076383

theorem tailTrace_8094311 : CollatzResearch.WordTrace tailWord_8094311 prefixEnd_8094311 461808012219442856076383 := by
  unfold tailWord_8094311
  simp only [CollatzResearch.WordTrace]
  refine ⟨295223775778701120105562787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196815850519134080070375191 295223775778701120105562787)
  ·
    refine ⟨442835663668051680158344181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295223775778701120105562787 442835663668051680158344181)
    ·
      refine ⟨41515843468879845014844767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 442835663668051680158344181 41515843468879845014844767)
      ·
        refine ⟨62273765203319767522267151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41515843468879845014844767 62273765203319767522267151)
        ·
          refine ⟨93410647804979651283400727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62273765203319767522267151 93410647804979651283400727)
          ·
            refine ⟨140115971707469476925101091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93410647804979651283400727 140115971707469476925101091)
            ·
              refine ⟨210173957561204215387651637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140115971707469476925101091 210173957561204215387651637)
              ·
                refine ⟨19703808521362895192592341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210173957561204215387651637 19703808521362895192592341)
                ·
                  refine ⟨461808012219442856076383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19703808521362895192592341 461808012219442856076383)
                  ·
                    rfl

theorem cell23_8094311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 7].length) (baseStart_8094311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094311 prefixEnd_8094311 := by exact prefixLift 8094311
  have htrace : WordTrace (prefixWord ++ tailWord_8094311) baseStart_8094311 baseEnd_8094311 := by
    simpa [prefixWord, tailWord_8094311, baseEnd_8094311] using wordTrace_append hprefix tailTrace_8094311
  have hstable : (prefixWord ++ tailWord_8094311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094311).length < 2 ^ (prefixWord ++ tailWord_8094311).sum := by decide
  have hdescent : baseEnd_8094311 < baseStart_8094311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094318 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_8094318 : Nat := 118140960795 + 8094318 * 2 ^ 59
def prefixEnd_8094318 : Nat := 4983230072969 + 3 ^ 40 * 8094318 * 2
def baseEnd_8094318 : Nat := 4156275704339567177299915

theorem tailTrace_8094318 : CollatzResearch.WordTrace tailWord_8094318 prefixEnd_8094318 4156275704339567177299915 := by
  unfold tailWord_8094318
  simp only [CollatzResearch.WordTrace]
  refine ⟨36903003886209470037633451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196816020726450506867378405 36903003886209470037633451)
  ·
    refine ⟨55354505829314205056450177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36903003886209470037633451 55354505829314205056450177)
    ·
      refine ⟨41515879371985653792337633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55354505829314205056450177 41515879371985653792337633)
      ·
        refine ⟨31136909528989240344253225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41515879371985653792337633 31136909528989240344253225)
        ·
          refine ⟨23352682146741930258189919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31136909528989240344253225 23352682146741930258189919)
          ·
            refine ⟨35029023220112895387284879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23352682146741930258189919 35029023220112895387284879)
            ·
              refine ⟨52543534830169343080927319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35029023220112895387284879 52543534830169343080927319)
              ·
                refine ⟨78815302245254014621390979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52543534830169343080927319 78815302245254014621390979)
                ·
                  refine ⟨118222953367881021932086469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78815302245254014621390979 118222953367881021932086469)
                  ·
                    refine ⟨22166803756477691612266213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118222953367881021932086469 22166803756477691612266213)
                    ·
                      refine ⟨4156275704339567177299915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22166803756477691612266213 4156275704339567177299915)
                      ·
                        rfl

theorem cell23_8094318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_8094318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094318 prefixEnd_8094318 := by exact prefixLift 8094318
  have htrace : WordTrace (prefixWord ++ tailWord_8094318) baseStart_8094318 baseEnd_8094318 := by
    simpa [prefixWord, tailWord_8094318, baseEnd_8094318] using wordTrace_append hprefix tailTrace_8094318
  have hstable : (prefixWord ++ tailWord_8094318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094318).length < 2 ^ (prefixWord ++ tailWord_8094318).sum := by decide
  have hdescent : baseEnd_8094318 < baseStart_8094318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094322 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_8094322 : Nat := 118140960795 + 8094322 * 2 ^ 59
def prefixEnd_8094322 : Nat := 4983230072969 + 3 ^ 40 * 8094322 * 2
def baseEnd_8094322 : Nat := 4156277758262185161649897

theorem tailTrace_8094322 : CollatzResearch.WordTrace tailWord_8094322 prefixEnd_8094322 4156277758262185161649897 := by
  unfold tailWord_8094322
  simp only [CollatzResearch.WordTrace]
  refine ⟨73806044245415317246053305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196816117987774179322808813 73806044245415317246053305)
  ·
    refine ⟨55354533184061487934539979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73806044245415317246053305 55354533184061487934539979)
    ·
      refine ⟨83031799776092231901809969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55354533184061487934539979 83031799776092231901809969)
      ·
        refine ⟨62273849832069173926357477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83031799776092231901809969 62273849832069173926357477)
        ·
          refine ⟨11676346843512970111192027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62273849832069173926357477 11676346843512970111192027)
          ·
            refine ⟨17514520265269455166788041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11676346843512970111192027 17514520265269455166788041)
            ·
              refine ⟨13135890198952091375091031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17514520265269455166788041 13135890198952091375091031)
              ·
                refine ⟨19703835298428137062636547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13135890198952091375091031 19703835298428137062636547)
                ·
                  refine ⟨29555752947642205593954821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19703835298428137062636547 29555752947642205593954821)
                  ·
                    refine ⟨5541703677682913548866529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29555752947642205593954821 5541703677682913548866529)
                    ·
                      refine ⟨4156277758262185161649897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5541703677682913548866529 4156277758262185161649897)
                      ·
                        rfl

theorem cell23_8094322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_8094322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094322 prefixEnd_8094322 := by exact prefixLift 8094322
  have htrace : WordTrace (prefixWord ++ tailWord_8094322) baseStart_8094322 baseEnd_8094322 := by
    simpa [prefixWord, tailWord_8094322, baseEnd_8094322] using wordTrace_append hprefix tailTrace_8094322
  have hstable : (prefixWord ++ tailWord_8094322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094322).length < 2 ^ (prefixWord ++ tailWord_8094322).sum := by decide
  have hdescent : baseEnd_8094322 < baseStart_8094322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094348 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 1, 7, 2]
def baseStart_8094348 : Nat := 118140960795 + 8094348 * 2 ^ 59
def prefixEnd_8094348 : Nat := 4983230072969 + 3 ^ 40 * 8094348 * 2
def baseEnd_8094348 : Nat := 4156291108759202059924777

theorem tailTrace_8094348 : CollatzResearch.WordTrace tailWord_8094348 prefixEnd_8094348 4156291108759202059924777 := by
  unfold tailWord_8094348
  simp only [CollatzResearch.WordTrace]
  refine ⟨147612562639783537712329849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196816750186378050283106465 147612562639783537712329849)
  ·
    refine ⟨110709421979837653284247387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147612562639783537712329849 110709421979837653284247387)
    ·
      refine ⟨166064132969756479926371081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110709421979837653284247387 166064132969756479926371081)
      ·
        refine ⟨124548099727317359944778311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166064132969756479926371081 124548099727317359944778311)
        ·
          refine ⟨186822149590976039917167467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124548099727317359944778311 186822149590976039917167467)
          ·
            refine ⟨280233224386464059875751201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186822149590976039917167467 280233224386464059875751201)
            ·
              refine ⟨210174918289848044906813401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280233224386464059875751201 210174918289848044906813401)
              ·
                refine ⟨157631188717386033680110051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210174918289848044906813401 157631188717386033680110051)
                ·
                  refine ⟨236446783076079050520165077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157631188717386033680110051 236446783076079050520165077)
                  ·
                    refine ⟨5541721478345602746566369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 236446783076079050520165077 5541721478345602746566369)
                    ·
                      refine ⟨4156291108759202059924777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5541721478345602746566369 4156291108759202059924777)
                      ·
                        rfl

theorem cell23_8094348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_8094348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094348 prefixEnd_8094348 := by exact prefixLift 8094348
  have htrace : WordTrace (prefixWord ++ tailWord_8094348) baseStart_8094348 baseEnd_8094348 := by
    simpa [prefixWord, tailWord_8094348, baseEnd_8094348] using wordTrace_append hprefix tailTrace_8094348
  have hstable : (prefixWord ++ tailWord_8094348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094348).length < 2 ^ (prefixWord ++ tailWord_8094348).sum := by decide
  have hdescent : baseEnd_8094348 < baseStart_8094348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094356 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_8094356 : Nat := 118140960795 + 8094356 * 2 ^ 59
def prefixEnd_8094356 : Nat := 4983230072969 + 3 ^ 40 * 8094356 * 2
def baseEnd_8094356 : Nat := 4156295216604438028624741

theorem tailTrace_8094356 : CollatzResearch.WordTrace tailWord_8094356 prefixEnd_8094356 4156295216604438028624741 := by
  unfold tailWord_8094356
  simp only [CollatzResearch.WordTrace]
  refine ⟨147612708531769046395475461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196816944709025395193967281 147612708531769046395475461)
  ·
    refine ⟨27677382849706696199151649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147612708531769046395475461 27677382849706696199151649)
    ·
      refine ⟨20758037137280022149363737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27677382849706696199151649 20758037137280022149363737)
      ·
        refine ⟨15568527852960016612022803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20758037137280022149363737 15568527852960016612022803)
        ·
          refine ⟨23352791779440024918034205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15568527852960016612022803 23352791779440024918034205)
          ·
            refine ⟨8757296917290009344262827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23352791779440024918034205 8757296917290009344262827)
            ·
              refine ⟨13135945375935014016394241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757296917290009344262827 13135945375935014016394241)
              ·
                refine ⟨9851959031951260512295681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13135945375935014016394241 9851959031951260512295681)
                ·
                  refine ⟨7388969273963445384221761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9851959031951260512295681 7388969273963445384221761)
                  ·
                    refine ⟨5541726955472584038166321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7388969273963445384221761 5541726955472584038166321)
                    ·
                      refine ⟨4156295216604438028624741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5541726955472584038166321 4156295216604438028624741)
                      ·
                        rfl

theorem cell23_8094356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_8094356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094356 prefixEnd_8094356 := by exact prefixLift 8094356
  have htrace : WordTrace (prefixWord ++ tailWord_8094356) baseStart_8094356 baseEnd_8094356 := by
    simpa [prefixWord, tailWord_8094356, baseEnd_8094356] using wordTrace_append hprefix tailTrace_8094356
  have hstable : (prefixWord ++ tailWord_8094356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094356).length < 2 ^ (prefixWord ++ tailWord_8094356).sum := by decide
  have hdescent : baseEnd_8094356 < baseStart_8094356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094435 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 6]
def baseStart_8094435 : Nat := 118140960795 + 8094435 * 2 ^ 59
def prefixEnd_8094435 : Nat := 4983230072969 + 3 ^ 40 * 8094435 * 2
def baseEnd_8094435 : Nat := 461815086841793691059653

theorem tailTrace_8094435 : CollatzResearch.WordTrace tailWord_8094435 prefixEnd_8094435 461815086841793691059653 := by
  unfold tailWord_8094435
  simp only [CollatzResearch.WordTrace]
  refine ⟨295228298430251889283076759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196818865620167926188717839 295228298430251889283076759)
  ·
    refine ⟨442842447645377833924615139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295228298430251889283076759 442842447645377833924615139)
    ·
      refine ⟨664263671468066750886922709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442842447645377833924615139 664263671468066750886922709)
      ·
        refine ⟨15568679800032814473912251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 664263671468066750886922709 15568679800032814473912251)
        ·
          refine ⟨23353019700049221710868377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15568679800032814473912251 23353019700049221710868377)
          ·
            refine ⟨17514764775036916283151283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23353019700049221710868377 17514764775036916283151283)
            ·
              refine ⟨26272147162555374424726925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17514764775036916283151283 26272147162555374424726925)
              ·
                refine ⟨9852055185958265409272597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26272147162555374424726925 9852055185958265409272597)
                ·
                  refine ⟨461815086841793691059653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9852055185958265409272597 461815086841793691059653)
                  ·
                    rfl

theorem cell23_8094435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 6].length) (baseStart_8094435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094435 prefixEnd_8094435 := by exact prefixLift 8094435
  have htrace : WordTrace (prefixWord ++ tailWord_8094435) baseStart_8094435 baseEnd_8094435 := by
    simpa [prefixWord, tailWord_8094435, baseEnd_8094435] using wordTrace_append hprefix tailTrace_8094435
  have hstable : (prefixWord ++ tailWord_8094435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094435).length < 2 ^ (prefixWord ++ tailWord_8094435).sum := by decide
  have hdescent : baseEnd_8094435 < baseStart_8094435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094448 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 3, 5]
def baseStart_8094448 : Nat := 118140960795 + 8094448 * 2 ^ 59
def prefixEnd_8094448 : Nat := 4983230072969 + 3 ^ 40 * 8094448 * 2
def baseEnd_8094448 : Nat := 1385447485608217222891439

theorem tailTrace_8094448 : CollatzResearch.WordTrace tailWord_8094448 prefixEnd_8094448 1385447485608217222891439 := by
  unfold tailWord_8094448
  simp only [CollatzResearch.WordTrace]
  refine ⟨147614386289602396251649999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196819181719469861668866665 147614386289602396251649999)
  ·
    refine ⟨221421579434403594377474999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147614386289602396251649999 221421579434403594377474999)
    ·
      refine ⟨332132369151605391566212499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221421579434403594377474999 332132369151605391566212499)
      ·
        refine ⟨498198553727408087349318749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332132369151605391566212499 498198553727408087349318749)
        ·
          refine ⟨186824457647778032755994531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498198553727408087349318749 186824457647778032755994531)
          ·
            refine ⟨280236686471667049133991797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186824457647778032755994531 280236686471667049133991797)
            ·
              refine ⟨26272189356718785856311731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280236686471667049133991797 26272189356718785856311731)
              ·
                refine ⟨39408284035078178784467597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26272189356718785856311731 39408284035078178784467597)
                ·
                  refine ⟨14778106513154317044175349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39408284035078178784467597 14778106513154317044175349)
                  ·
                    refine ⟨1385447485608217222891439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14778106513154317044175349 1385447485608217222891439)
                    ·
                      rfl

theorem cell23_8094448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_8094448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094448 prefixEnd_8094448 := by exact prefixLift 8094448
  have htrace : WordTrace (prefixWord ++ tailWord_8094448) baseStart_8094448 baseEnd_8094448 := by
    simpa [prefixWord, tailWord_8094448, baseEnd_8094448] using wordTrace_append hprefix tailTrace_8094448
  have hstable : (prefixWord ++ tailWord_8094448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094448).length < 2 ^ (prefixWord ++ tailWord_8094448).sum := by decide
  have hdescent : baseEnd_8094448 < baseStart_8094448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094472 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_8094472 : Nat := 118140960795 + 8094472 * 2 ^ 59
def prefixEnd_8094472 : Nat := 4983230072969 + 3 ^ 40 * 8094472 * 2
def baseEnd_8094472 : Nat := 4156354780360359574774207

theorem tailTrace_8094472 : CollatzResearch.WordTrace tailWord_8094472 prefixEnd_8094472 4156354780360359574774207 := by
  unfold tailWord_8094472
  simp only [CollatzResearch.WordTrace]
  refine ⟨147614823965558922301086835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196819765287411896401449113 147614823965558922301086835)
  ·
    refine ⟨221422235948338383451630253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147614823965558922301086835 221422235948338383451630253)
    ·
      refine ⟨83033338480626893794361345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221422235948338383451630253 83033338480626893794361345)
      ·
        refine ⟨62275003860470170345771009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83033338480626893794361345 62275003860470170345771009)
        ·
          refine ⟨46706252895352627759328257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62275003860470170345771009 46706252895352627759328257)
          ·
            refine ⟨35029689671514470819496193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46706252895352627759328257 35029689671514470819496193)
            ·
              refine ⟨26272267253635853114622145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35029689671514470819496193 26272267253635853114622145)
              ·
                refine ⟨19704200440226889835966609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26272267253635853114622145 19704200440226889835966609)
                ·
                  refine ⟨14778150330170167376974957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19704200440226889835966609 14778150330170167376974957)
                  ·
                    refine ⟨5541806373813812766365609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14778150330170167376974957 5541806373813812766365609)
                    ·
                      refine ⟨4156354780360359574774207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5541806373813812766365609 4156354780360359574774207)
                      ·
                        rfl

theorem cell23_8094472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_8094472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094472 prefixEnd_8094472 := by exact prefixLift 8094472
  have htrace : WordTrace (prefixWord ++ tailWord_8094472) baseStart_8094472 baseEnd_8094472 := by
    simpa [prefixWord, tailWord_8094472, baseEnd_8094472] using wordTrace_append hprefix tailTrace_8094472
  have hstable : (prefixWord ++ tailWord_8094472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094472).length < 2 ^ (prefixWord ++ tailWord_8094472).sum := by decide
  have hdescent : baseEnd_8094472 < baseStart_8094472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094478 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_8094478 : Nat := 118140960795 + 8094478 * 2 ^ 59
def prefixEnd_8094478 : Nat := 4983230072969 + 3 ^ 40 * 8094478 * 2
def baseEnd_8094478 : Nat := 1385452620414762183766393

theorem tailTrace_8094478 : CollatzResearch.WordTrace tailWord_8094478 prefixEnd_8094478 1385452620414762183766393 := by
  unfold tailWord_8094478
  simp only [CollatzResearch.WordTrace]
  refine ⟨36903733346137013453361511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196819911179397405084594725 36903733346137013453361511)
  ·
    refine ⟨55355600019205520180042267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36903733346137013453361511 55355600019205520180042267)
    ·
      refine ⟨83033400028808280270063401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55355600019205520180042267 83033400028808280270063401)
      ·
        refine ⟨62275050021606210202547551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83033400028808280270063401 62275050021606210202547551)
        ·
          refine ⟨93412575032409315303821327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62275050021606210202547551 93412575032409315303821327)
          ·
            refine ⟨140118862548613972955731991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93412575032409315303821327 140118862548613972955731991)
            ·
              refine ⟨210178293822920959433597987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140118862548613972955731991 210178293822920959433597987)
              ·
                refine ⟨315267440734381439150396981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210178293822920959433597987 315267440734381439150396981)
                ·
                  refine ⟨29556322568848259920349717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315267440734381439150396981 29556322568848259920349717)
                  ·
                    refine ⟨1385452620414762183766393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29556322568848259920349717 1385452620414762183766393)
                    ·
                      rfl

theorem cell23_8094478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_8094478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094478 prefixEnd_8094478 := by exact prefixLift 8094478
  have htrace : WordTrace (prefixWord ++ tailWord_8094478) baseStart_8094478 baseEnd_8094478 := by
    simpa [prefixWord, tailWord_8094478, baseEnd_8094478] using wordTrace_append hprefix tailTrace_8094478
  have hstable : (prefixWord ++ tailWord_8094478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094478).length < 2 ^ (prefixWord ++ tailWord_8094478).sum := by decide
  have hdescent : baseEnd_8094478 < baseStart_8094478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094488 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_8094488 : Nat := 118140960795 + 8094488 * 2 ^ 59
def prefixEnd_8094488 : Nat := 4983230072969 + 3 ^ 40 * 8094488 * 2
def baseEnd_8094488 : Nat := 4156362996050831512174133

theorem tailTrace_8094488 : CollatzResearch.WordTrace tailWord_8094488 prefixEnd_8094488 4156362996050831512174133 := by
  unfold tailWord_8094488
  simp only [CollatzResearch.WordTrace]
  refine ⟨147615115749529939667378059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196820154332706586223170745 147615115749529939667378059)
  ·
    refine ⟨221422673624294909501067089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147615115749529939667378059 221422673624294909501067089)
    ·
      refine ⟨166067005218221182125800317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221422673624294909501067089 166067005218221182125800317)
      ·
        refine ⟨62275126956832943297175119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166067005218221182125800317 62275126956832943297175119)
        ·
          refine ⟨93412690435249414945762679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62275126956832943297175119 93412690435249414945762679)
          ·
            refine ⟨140119035652874122418644019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93412690435249414945762679 140119035652874122418644019)
            ·
              refine ⟨210178553479311183627966029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140119035652874122418644019 210178553479311183627966029)
              ·
                refine ⟨78816957554741693860487261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210178553479311183627966029 78816957554741693860487261)
                ·
                  refine ⟨29556359083028135197682723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78816957554741693860487261 29556359083028135197682723)
                  ·
                    refine ⟨44334538624542202796524085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29556359083028135197682723 44334538624542202796524085)
                    ·
                      refine ⟨4156362996050831512174133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44334538624542202796524085 4156362996050831512174133)
                      ·
                        rfl

theorem cell23_8094488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_8094488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094488 prefixEnd_8094488 := by exact prefixLift 8094488
  have htrace : WordTrace (prefixWord ++ tailWord_8094488) baseStart_8094488 baseEnd_8094488 := by
    simpa [prefixWord, tailWord_8094488, baseEnd_8094488] using wordTrace_append hprefix tailTrace_8094488
  have hstable : (prefixWord ++ tailWord_8094488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094488).length < 2 ^ (prefixWord ++ tailWord_8094488).sum := by decide
  have hdescent : baseEnd_8094488 < baseStart_8094488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094495 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 1, 6]
def baseStart_8094495 : Nat := 118140960795 + 8094495 * 2 ^ 59
def prefixEnd_8094495 : Nat := 4983230072969 + 3 ^ 40 * 8094495 * 2
def baseEnd_8094495 : Nat := 1385455530138470994928867

theorem tailTrace_8094495 : CollatzResearch.WordTrace tailWord_8094495 prefixEnd_8094495 1385455530138470994928867 := by
  unfold tailWord_8094495
  simp only [CollatzResearch.WordTrace]
  refine ⟨295230486810034519530260939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196820324540023013020173959 295230486810034519530260939)
  ·
    refine ⟨442845730215051779295391409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295230486810034519530260939 442845730215051779295391409)
    ·
      refine ⟨332134297661288834471543557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442845730215051779295391409 332134297661288834471543557)
      ·
        refine ⟨62275180811491656463414417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332134297661288834471543557 62275180811491656463414417)
        ·
          refine ⟨46706385608618742347560813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62275180811491656463414417 46706385608618742347560813)
          ·
            refine ⟨17514894603232028380335305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46706385608618742347560813 17514894603232028380335305)
            ·
              refine ⟨13136170952424021285251479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17514894603232028380335305 13136170952424021285251479)
              ·
                refine ⟨19704256428636031927877219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13136170952424021285251479 19704256428636031927877219)
                ·
                  refine ⟨29556384642954047891815829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19704256428636031927877219 29556384642954047891815829)
                  ·
                    refine ⟨1385455530138470994928867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29556384642954047891815829 1385455530138470994928867)
                    ·
                      rfl

theorem cell23_8094495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_8094495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094495 prefixEnd_8094495 := by exact prefixLift 8094495
  have htrace : WordTrace (prefixWord ++ tailWord_8094495) baseStart_8094495 baseEnd_8094495 := by
    simpa [prefixWord, tailWord_8094495, baseEnd_8094495] using wordTrace_append hprefix tailTrace_8094495
  have hstable : (prefixWord ++ tailWord_8094495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094495).length < 2 ^ (prefixWord ++ tailWord_8094495).sum := by decide
  have hdescent : baseEnd_8094495 < baseStart_8094495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094515 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 4]
def baseStart_8094515 : Nat := 118140960795 + 8094515 * 2 ^ 59
def prefixEnd_8094515 : Nat := 4983230072969 + 3 ^ 40 * 8094515 * 2
def baseEnd_8094515 : Nat := 4156376860028502906536509

theorem tailTrace_8094515 : CollatzResearch.WordTrace tailWord_8094515 prefixEnd_8094515 4156376860028502906536509 := by
  unfold tailWord_8094515
  simp only [CollatzResearch.WordTrace]
  refine ⟨295231216269962062945988999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196820810846641375297325999 295231216269962062945988999)
  ·
    refine ⟨442846824404943094418983499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295231216269962062945988999 442846824404943094418983499)
    ·
      refine ⟨664270236607414641628475249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442846824404943094418983499 664270236607414641628475249)
      ·
        refine ⟨498202677455560981221356437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664270236607414641628475249 498202677455560981221356437)
        ·
          refine ⟨23353250505729420994751083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 498202677455560981221356437 23353250505729420994751083)
          ·
            refine ⟨35029875758594131492126625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23353250505729420994751083 35029875758594131492126625)
            ·
              refine ⟨26272406818945598619094969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35029875758594131492126625 26272406818945598619094969)
              ·
                refine ⟨19704305114209198964321227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26272406818945598619094969 19704305114209198964321227)
                ·
                  refine ⟨29556457671313798446481841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19704305114209198964321227 29556457671313798446481841)
                  ·
                    refine ⟨22167343253485348834861381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29556457671313798446481841 22167343253485348834861381)
                    ·
                      refine ⟨4156376860028502906536509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22167343253485348834861381 4156376860028502906536509)
                      ·
                        rfl

theorem cell23_8094515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_8094515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094515 prefixEnd_8094515 := by exact prefixLift 8094515
  have htrace : WordTrace (prefixWord ++ tailWord_8094515) baseStart_8094515 baseEnd_8094515 := by
    simpa [prefixWord, tailWord_8094515, baseEnd_8094515] using wordTrace_append hprefix tailTrace_8094515
  have hstable : (prefixWord ++ tailWord_8094515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094515).length < 2 ^ (prefixWord ++ tailWord_8094515).sum := by decide
  have hdescent : baseEnd_8094515 < baseStart_8094515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094516 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_8094516 : Nat := 118140960795 + 8094516 * 2 ^ 59
def prefixEnd_8094516 : Nat := 4983230072969 + 3 ^ 40 * 8094516 * 2
def baseEnd_8094516 : Nat := 1385459124503052467541335

theorem tailTrace_8094516 : CollatzResearch.WordTrace tailWord_8094516 prefixEnd_8094516 1385459124503052467541335 := by
  unfold tailWord_8094516
  simp only [CollatzResearch.WordTrace]
  refine ⟨147615626371479220058387701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196820835161972293411183601 147615626371479220058387701)
  ·
    refine ⟨13838964972326176880473847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147615626371479220058387701 13838964972326176880473847)
    ·
      refine ⟨20758447458489265320710771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13838964972326176880473847 20758447458489265320710771)
      ·
        refine ⟨31137671187733897981066157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20758447458489265320710771 31137671187733897981066157)
        ·
          refine ⟨11676626695400211742899809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31137671187733897981066157 11676626695400211742899809)
          ·
            refine ⟨8757470021550158807174857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11676626695400211742899809 8757470021550158807174857)
            ·
              refine ⟨6568102516162619105381143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8757470021550158807174857 6568102516162619105381143)
              ·
                refine ⟨9852153774243928658071715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568102516162619105381143 9852153774243928658071715)
                ·
                  refine ⟨14778230661365892987107573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9852153774243928658071715 14778230661365892987107573)
                  ·
                    refine ⟨1385459124503052467541335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14778230661365892987107573 1385459124503052467541335)
                    ·
                      rfl

theorem cell23_8094516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_8094516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094516 prefixEnd_8094516 := by exact prefixLift 8094516
  have htrace : WordTrace (prefixWord ++ tailWord_8094516) baseStart_8094516 baseEnd_8094516 := by
    simpa [prefixWord, tailWord_8094516, baseEnd_8094516] using wordTrace_append hprefix tailTrace_8094516
  have hstable : (prefixWord ++ tailWord_8094516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094516).length < 2 ^ (prefixWord ++ tailWord_8094516).sum := by decide
  have hdescent : baseEnd_8094516 < baseStart_8094516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094525 : List Nat := [1, 4, 1, 4, 2, 1, 10]
def baseStart_8094525 : Nat := 118140960795 + 8094525 * 2 ^ 59
def prefixEnd_8094525 : Nat := 4983230072969 + 3 ^ 40 * 8094525 * 2
def baseEnd_8094525 : Nat := 51313357960926516881623

theorem tailTrace_8094525 : CollatzResearch.WordTrace tailWord_8094525 prefixEnd_8094525 51313357960926516881623 := by
  unfold tailWord_8094525
  simp only [CollatzResearch.WordTrace]
  refine ⟨295231580999925834653853029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196821053999950556435902019 295231580999925834653853029)
  ·
    refine ⟨55355921437486093997597443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295231580999925834653853029 55355921437486093997597443)
    ·
      refine ⟨83033882156229140996396165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55355921437486093997597443 83033882156229140996396165)
      ·
        refine ⟨15568852904292963936824281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83033882156229140996396165 15568852904292963936824281)
        ·
          refine ⟨11676639678219722952618211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15568852904292963936824281 11676639678219722952618211)
          ·
            refine ⟨17514959517329584428927317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11676639678219722952618211 17514959517329584428927317)
            ·
              refine ⟨51313357960926516881623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17514959517329584428927317 51313357960926516881623)
              ·
                rfl

theorem cell23_8094525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 10].length) (baseStart_8094525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094525 prefixEnd_8094525 := by exact prefixLift 8094525
  have htrace : WordTrace (prefixWord ++ tailWord_8094525) baseStart_8094525 baseEnd_8094525 := by
    simpa [prefixWord, tailWord_8094525, baseEnd_8094525] using wordTrace_append hprefix tailTrace_8094525
  have hstable : (prefixWord ++ tailWord_8094525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094525).length < 2 ^ (prefixWord ++ tailWord_8094525).sum := by decide
  have hdescent : baseEnd_8094525 < baseStart_8094525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094529 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 4, 4]
def baseStart_8094529 : Nat := 118140960795 + 8094529 * 2 ^ 59
def prefixEnd_8094529 : Nat := 4983230072969 + 3 ^ 40 * 8094529 * 2
def baseEnd_8094529 : Nat := 1385461349585888617253815

theorem tailTrace_8094529 : CollatzResearch.WordTrace tailWord_8094529 prefixEnd_8094529 1385461349585888617253815 := by
  unfold tailWord_8094529
  simp only [CollatzResearch.WordTrace]
  refine ⟨295231726891911343336998641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196821151261274228891332427 295231726891911343336998641)
  ·
    refine ⟨221423795168933507502748981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295231726891911343336998641 221423795168933507502748981)
    ·
      refine ⟨20758480797087516328382717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221423795168933507502748981 20758480797087516328382717)
      ·
        refine ⟨7784430298907818623143519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20758480797087516328382717 7784430298907818623143519)
        ·
          refine ⟨11676645448361727934715279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784430298907818623143519 11676645448361727934715279)
          ·
            refine ⟨17514968172542591902072919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11676645448361727934715279 17514968172542591902072919)
            ·
              refine ⟨26272452258813887853109379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17514968172542591902072919 26272452258813887853109379)
              ·
                refine ⟨39408678388220831779664069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26272452258813887853109379 39408678388220831779664069)
                ·
                  refine ⟨7389127197791405958687013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39408678388220831779664069 7389127197791405958687013)
                  ·
                    refine ⟨1385461349585888617253815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7389127197791405958687013 1385461349585888617253815)
                    ·
                      rfl

theorem cell23_8094529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_8094529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094529 prefixEnd_8094529 := by exact prefixLift 8094529
  have htrace : WordTrace (prefixWord ++ tailWord_8094529) baseStart_8094529 baseEnd_8094529 := by
    simpa [prefixWord, tailWord_8094529, baseEnd_8094529] using wordTrace_append hprefix tailTrace_8094529
  have hstable : (prefixWord ++ tailWord_8094529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094529).length < 2 ^ (prefixWord ++ tailWord_8094529).sum := by decide
  have hdescent : baseEnd_8094529 < baseStart_8094529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094538 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_8094538 : Nat := 118140960795 + 8094538 * 2 ^ 59
def prefixEnd_8094538 : Nat := 4983230072969 + 3 ^ 40 * 8094538 * 2
def baseEnd_8094538 : Nat := 1385462890027852105516301

theorem tailTrace_8094538 : CollatzResearch.WordTrace tailWord_8094538 prefixEnd_8094538 1385462890027852105516301 := by
  unfold tailWord_8094538
  simp only [CollatzResearch.WordTrace]
  refine ⟨73808013787219684468519067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196821370099252491916050845 73808013787219684468519067)
  ·
    refine ⟨110712020680829526702778601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73808013787219684468519067 110712020680829526702778601)
    ·
      refine ⟨83034015510622145027083951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110712020680829526702778601 83034015510622145027083951)
      ·
        refine ⟨124551023265933217540625927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83034015510622145027083951 124551023265933217540625927)
        ·
          refine ⟨186826534898899826310938891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124551023265933217540625927 186826534898899826310938891)
          ·
            refine ⟨280239802348349739466408337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186826534898899826310938891 280239802348349739466408337)
            ·
              refine ⟨210179851761262304599806253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280239802348349739466408337 210179851761262304599806253)
              ·
                refine ⟨78817444410473364224927345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210179851761262304599806253 78817444410473364224927345)
                ·
                  refine ⟨59113083307855023168695509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78817444410473364224927345 59113083307855023168695509)
                  ·
                    refine ⟨1385462890027852105516301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59113083307855023168695509 1385462890027852105516301)
                    ·
                      rfl

theorem cell23_8094538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_8094538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094538 prefixEnd_8094538 := by exact prefixLift 8094538
  have htrace : WordTrace (prefixWord ++ tailWord_8094538) baseStart_8094538 baseEnd_8094538 := by
    simpa [prefixWord, tailWord_8094538, baseEnd_8094538] using wordTrace_append hprefix tailTrace_8094538
  have hstable : (prefixWord ++ tailWord_8094538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094538).length < 2 ^ (prefixWord ++ tailWord_8094538).sum := by decide
  have hdescent : baseEnd_8094538 < baseStart_8094538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094552 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 2, 1, 3]
def baseStart_8094552 : Nat := 118140960795 + 8094552 * 2 ^ 59
def prefixEnd_8094552 : Nat := 4983230072969 + 3 ^ 40 * 8094552 * 2
def baseEnd_8094552 : Nat := 4156395858812719261773839

theorem tailTrace_8094552 : CollatzResearch.WordTrace tailWord_8094552 prefixEnd_8094552 4156395858812719261773839 := by
  unfold tailWord_8094552
  simp only [CollatzResearch.WordTrace]
  refine ⟨147616282885414009132542955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196821710513885345510057273 147616282885414009132542955)
  ·
    refine ⟨221424424328121013698814433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147616282885414009132542955 221424424328121013698814433)
    ·
      refine ⟨166068318246090760274110825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221424424328121013698814433 166068318246090760274110825)
      ·
        refine ⟨124551238684568070205583119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166068318246090760274110825 124551238684568070205583119)
        ·
          refine ⟨186826858026852105308374679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124551238684568070205583119 186826858026852105308374679)
          ·
            refine ⟨280240287040278157962562019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186826858026852105308374679 280240287040278157962562019)
            ·
              refine ⟨420360430560417236943843029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280240287040278157962562019 420360430560417236943843029)
              ·
                refine ⟨9852197591259778990871321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 420360430560417236943843029 9852197591259778990871321)
                ·
                  refine ⟨7389148193444834243153491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9852197591259778990871321 7389148193444834243153491)
                  ·
                    refine ⟨11083722290167251364730237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7389148193444834243153491 11083722290167251364730237)
                    ·
                      refine ⟨4156395858812719261773839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11083722290167251364730237 4156395858812719261773839)
                      ·
                        rfl

theorem cell23_8094552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_8094552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094552 prefixEnd_8094552 := by exact prefixLift 8094552
  have htrace : WordTrace (prefixWord ++ tailWord_8094552) baseStart_8094552 baseEnd_8094552 := by
    simpa [prefixWord, tailWord_8094552, baseEnd_8094552] using wordTrace_append hprefix tailTrace_8094552
  have hstable : (prefixWord ++ tailWord_8094552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094552).length < 2 ^ (prefixWord ++ tailWord_8094552).sum := by decide
  have hdescent : baseEnd_8094552 < baseStart_8094552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094595 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 3]
def baseStart_8094595 : Nat := 118140960795 + 8094595 * 2 ^ 59
def prefixEnd_8094595 : Nat := 4983230072969 + 3 ^ 40 * 8094595 * 2
def baseEnd_8094595 : Nat := 4156417938480862593536141

theorem tailTrace_8094595 : CollatzResearch.WordTrace tailWord_8094595 prefixEnd_8094595 4156417938480862593536141 := by
  unfold tailWord_8094595
  simp only [CollatzResearch.WordTrace]
  refine ⟨295234134109672236608901239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196822756073114824405934159 295234134109672236608901239)
  ·
    refine ⟨442851201164508354913351859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295234134109672236608901239 442851201164508354913351859)
    ·
      refine ⟨664276801746762532370027789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442851201164508354913351859 664276801746762532370027789)
      ·
        refine ⟨249103800655035949638760421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664276801746762532370027789 249103800655035949638760421)
        ·
          refine ⟨46706962622819240557267579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249103800655035949638760421 46706962622819240557267579)
          ·
            refine ⟨70060443934228860835901369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46706962622819240557267579 70060443934228860835901369)
            ·
              refine ⟨52545332950671645626926027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70060443934228860835901369 52545332950671645626926027)
              ·
                refine ⟨78817999426007468440389041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52545332950671645626926027 78817999426007468440389041)
                ·
                  refine ⟨59113499569505601330291781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78817999426007468440389041 59113499569505601330291781)
                  ·
                    refine ⟨11083781169282300249429709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59113499569505601330291781 11083781169282300249429709)
                    ·
                      refine ⟨4156417938480862593536141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11083781169282300249429709 4156417938480862593536141)
                      ·
                        rfl

theorem cell23_8094595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_8094595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094595 prefixEnd_8094595 := by exact prefixLift 8094595
  have htrace : WordTrace (prefixWord ++ tailWord_8094595) baseStart_8094595 baseEnd_8094595 := by
    simpa [prefixWord, tailWord_8094595, baseEnd_8094595] using wordTrace_append hprefix tailTrace_8094595
  have hstable : (prefixWord ++ tailWord_8094595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094595).length < 2 ^ (prefixWord ++ tailWord_8094595).sum := by decide
  have hdescent : baseEnd_8094595 < baseStart_8094595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094608 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_8094608 : Nat := 118140960795 + 8094608 * 2 ^ 59
def prefixEnd_8094608 : Nat := 4983230072969 + 3 ^ 40 * 8094608 * 2
def baseEnd_8094608 : Nat := 4156424613729371042673581

theorem tailTrace_8094608 : CollatzResearch.WordTrace tailWord_8094608 prefixEnd_8094608 4156424613729371042673581 := by
  unfold tailWord_8094608
  simp only [CollatzResearch.WordTrace]
  refine ⟨147617304129312569914562239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196823072172416759886082985 147617304129312569914562239)
  ·
    refine ⟨221425956193968854871843359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147617304129312569914562239 221425956193968854871843359)
    ·
      refine ⟨332138934290953282307765039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221425956193968854871843359 332138934290953282307765039)
      ·
        refine ⟨498208401436429923461647559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332138934290953282307765039 498208401436429923461647559)
        ·
          refine ⟨747312602154644885192471339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498208401436429923461647559 747312602154644885192471339)
          ·
            refine ⟨1120968903231967327788707009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747312602154644885192471339 1120968903231967327788707009)
            ·
              refine ⟨840726677423975495841530257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120968903231967327788707009 840726677423975495841530257)
              ·
                refine ⟨630545008067981621881147693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840726677423975495841530257 630545008067981621881147693)
                ·
                  refine ⟨236454378025493108205430385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630545008067981621881147693 236454378025493108205430385)
                  ·
                    refine ⟨177340783519119831154072789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236454378025493108205430385 177340783519119831154072789)
                    ·
                      refine ⟨4156424613729371042673581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177340783519119831154072789 4156424613729371042673581)
                      ·
                        rfl

theorem cell23_8094608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_8094608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094608 prefixEnd_8094608 := by exact prefixLift 8094608
  have htrace : WordTrace (prefixWord ++ tailWord_8094608) baseStart_8094608 baseEnd_8094608 := by
    simpa [prefixWord, tailWord_8094608, baseEnd_8094608] using wordTrace_append hprefix tailTrace_8094608
  have hstable : (prefixWord ++ tailWord_8094608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094608).length < 2 ^ (prefixWord ++ tailWord_8094608).sum := by decide
  have hdescent : baseEnd_8094608 < baseStart_8094608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094649 : List Nat := [1, 2, 1, 4, 2, 2, 4, 2, 5]
def baseStart_8094649 : Nat := 118140960795 + 8094649 * 2 ^ 59
def prefixEnd_8094649 : Nat := 4983230072969 + 3 ^ 40 * 8094649 * 2
def baseEnd_8094649 : Nat := 461827296270689486917877

theorem tailTrace_8094649 : CollatzResearch.WordTrace tailWord_8094649 prefixEnd_8094649 461827296270689486917877 := by
  unfold tailWord_8094649
  simp only [CollatzResearch.WordTrace]
  refine ⟨295236103651476603831367001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196824069100984402554244667 295236103651476603831367001)
  ·
    refine ⟨221427077738607452873525251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295236103651476603831367001 221427077738607452873525251)
    ·
      refine ⟨332140616607911179310287877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221427077738607452873525251 332140616607911179310287877)
      ·
        refine ⟨62276365613983346120678977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332140616607911179310287877 62276365613983346120678977)
        ·
          refine ⟨46707274210487509590509233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62276365613983346120678977 46707274210487509590509233)
          ·
            refine ⟨35030455657865632192881925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46707274210487509590509233 35030455657865632192881925)
            ·
              refine ⟨6568210435849806036165361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35030455657865632192881925 6568210435849806036165361)
              ·
                refine ⟨4926157826887354527124021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6568210435849806036165361 4926157826887354527124021)
                ·
                  refine ⟨461827296270689486917877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4926157826887354527124021 461827296270689486917877)
                  ·
                    rfl

theorem cell23_8094649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 5].length) (baseStart_8094649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094649 prefixEnd_8094649 := by exact prefixLift 8094649
  have htrace : WordTrace (prefixWord ++ tailWord_8094649) baseStart_8094649 baseEnd_8094649 := by
    simpa [prefixWord, tailWord_8094649, baseEnd_8094649] using wordTrace_append hprefix tailTrace_8094649
  have hstable : (prefixWord ++ tailWord_8094649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094649).length < 2 ^ (prefixWord ++ tailWord_8094649).sum := by decide
  have hdescent : baseEnd_8094649 < baseStart_8094649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094682 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_8094682 : Nat := 118140960795 + 8094682 * 2 ^ 59
def prefixEnd_8094682 : Nat := 4983230072969 + 3 ^ 40 * 8094682 * 2
def baseEnd_8094682 : Nat := 4156462611297803753148241

theorem tailTrace_8094682 : CollatzResearch.WordTrace tailWord_8094682 prefixEnd_8094682 4156462611297803753148241 := by
  unfold tailWord_8094682
  simp only [CollatzResearch.WordTrace]
  refine ⟨73809326815089262616829575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196824871506904700311545533 73809326815089262616829575)
  ·
    refine ⟨110713990222633893925244363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73809326815089262616829575 110713990222633893925244363)
    ·
      refine ⟨166070985333950840887866545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110713990222633893925244363 166070985333950840887866545)
      ·
        refine ⟨124553239000463130665899909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166070985333950840887866545 124553239000463130665899909)
        ·
          refine ⟨23353732312586836999856233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124553239000463130665899909 23353732312586836999856233)
          ·
            refine ⟨17515299234440127749892175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23353732312586836999856233 17515299234440127749892175)
            ·
              refine ⟨26272948851660191624838263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17515299234440127749892175 26272948851660191624838263)
              ·
                refine ⟨39409423277490287437257395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26272948851660191624838263 39409423277490287437257395)
                ·
                  refine ⟨59114134916235431155886093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39409423277490287437257395 59114134916235431155886093)
                  ·
                    refine ⟨22167800593588286683457285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59114134916235431155886093 22167800593588286683457285)
                    ·
                      refine ⟨4156462611297803753148241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22167800593588286683457285 4156462611297803753148241)
                      ·
                        rfl

theorem cell23_8094682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_8094682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094682 prefixEnd_8094682 := by exact prefixLift 8094682
  have htrace : WordTrace (prefixWord ++ tailWord_8094682) baseStart_8094682 baseEnd_8094682 := by
    simpa [prefixWord, tailWord_8094682, baseEnd_8094682] using wordTrace_append hprefix tailTrace_8094682
  have hstable : (prefixWord ++ tailWord_8094682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094682).length < 2 ^ (prefixWord ++ tailWord_8094682).sum := by decide
  have hdescent : baseEnd_8094682 < baseStart_8094682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094725 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_8094725 : Nat := 118140960795 + 8094725 * 2 ^ 59
def prefixEnd_8094725 : Nat := 4983230072969 + 3 ^ 40 * 8094725 * 2
def baseEnd_8094725 : Nat := 4156484690965947084910543

theorem tailTrace_8094725 : CollatzResearch.WordTrace tailWord_8094725 prefixEnd_8094725 4156484690965947084910543 := by
  unfold tailWord_8094725
  simp only [CollatzResearch.WordTrace]
  refine ⟨295238875599201268811133629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196825917066134179207422419 295238875599201268811133629)
  ·
    refine ⟨110714578349700475804175111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295238875599201268811133629 110714578349700475804175111)
    ·
      refine ⟨166071867524550713706262667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110714578349700475804175111 166071867524550713706262667)
      ·
        refine ⟨249107801286826070559394001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166071867524550713706262667 249107801286826070559394001)
        ·
          refine ⟨186830850965119552919545501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249107801286826070559394001 186830850965119552919545501)
          ·
            refine ⟨70061569111919832344829563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186830850965119552919545501 70061569111919832344829563)
            ·
              refine ⟨105092353667879748517244345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70061569111919832344829563 105092353667879748517244345)
              ·
                refine ⟨78819265250909811387933259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105092353667879748517244345 78819265250909811387933259)
                ·
                  refine ⟨118228897876364717081899889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78819265250909811387933259 118228897876364717081899889)
                  ·
                    refine ⟨88671673407273537811424917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118228897876364717081899889 88671673407273537811424917)
                    ·
                      refine ⟨4156484690965947084910543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88671673407273537811424917 4156484690965947084910543)
                      ·
                        rfl

theorem cell23_8094725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_8094725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094725 prefixEnd_8094725 := by exact prefixLift 8094725
  have htrace : WordTrace (prefixWord ++ tailWord_8094725) baseStart_8094725 baseEnd_8094725 := by
    simpa [prefixWord, tailWord_8094725, baseEnd_8094725] using wordTrace_append hprefix tailTrace_8094725
  have hstable : (prefixWord ++ tailWord_8094725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094725).length < 2 ^ (prefixWord ++ tailWord_8094725).sum := by decide
  have hdescent : baseEnd_8094725 < baseStart_8094725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094743 : List Nat := [1, 1, 3, 5, 1, 3, 1, 3, 1, 4]
def baseStart_8094743 : Nat := 118140960795 + 8094743 * 2 ^ 59
def prefixEnd_8094743 : Nat := 4983230072969 + 3 ^ 40 * 8094743 * 2
def baseEnd_8094743 : Nat := 1385497977872576004828487

theorem tailTrace_8094743 : CollatzResearch.WordTrace tailWord_8094743 prefixEnd_8094743 1385497977872576004828487 := by
  unfold tailWord_8094743
  simp only [CollatzResearch.WordTrace]
  refine ⟨295239532113136057885288883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196826354742090705256859255 295239532113136057885288883)
  ·
    refine ⟨442859298169704086827933325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295239532113136057885288883 442859298169704086827933325)
    ·
      refine ⟨166072236813639032560474997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442859298169704086827933325 166072236813639032560474997)
      ·
        refine ⟨15569272201278659302544531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166072236813639032560474997 15569272201278659302544531)
        ·
          refine ⟨23353908301917988953816797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15569272201278659302544531 23353908301917988953816797)
          ·
            refine ⟨8757715613219245857681299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23353908301917988953816797 8757715613219245857681299)
            ·
              refine ⟨13136573419828868786521949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757715613219245857681299 13136573419828868786521949)
              ·
                refine ⟨4926215032435825794945731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13136573419828868786521949 4926215032435825794945731)
                ·
                  refine ⟨7389322548653738692418597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926215032435825794945731 7389322548653738692418597)
                  ·
                    refine ⟨1385497977872576004828487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7389322548653738692418597 1385497977872576004828487)
                    ·
                      rfl

theorem cell23_8094743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_8094743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094743 prefixEnd_8094743 := by exact prefixLift 8094743
  have htrace : WordTrace (prefixWord ++ tailWord_8094743) baseStart_8094743 baseEnd_8094743 := by
    simpa [prefixWord, tailWord_8094743, baseEnd_8094743] using wordTrace_append hprefix tailTrace_8094743
  have hstable : (prefixWord ++ tailWord_8094743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094743).length < 2 ^ (prefixWord ++ tailWord_8094743).sum := by decide
  have hdescent : baseEnd_8094743 < baseStart_8094743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094789 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 4]
def baseStart_8094789 : Nat := 118140960795 + 8094789 * 2 ^ 59
def prefixEnd_8094789 : Nat := 4983230072969 + 3 ^ 40 * 8094789 * 2
def baseEnd_8094789 : Nat := 4156517553727834834510249

theorem tailTrace_8094789 : CollatzResearch.WordTrace tailWord_8094789 prefixEnd_8094789 4156517553727834834510249 := by
  unfold tailWord_8094789
  simp only [CollatzResearch.WordTrace]
  refine ⟨295241209870969407741463421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196827473247312938494308947 295241209870969407741463421)
  ·
    refine ⟨110715453701613527903048783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295241209870969407741463421 110715453701613527903048783)
    ·
      refine ⟨166073180552420291854573175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110715453701613527903048783 166073180552420291854573175)
      ·
        refine ⟨249109770828630437781859763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166073180552420291854573175 249109770828630437781859763)
        ·
          refine ⟨373664656242945656672789645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249109770828630437781859763 373664656242945656672789645)
          ·
            refine ⟨140124246091104621252296117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373664656242945656672789645 140124246091104621252296117)
            ·
              refine ⟨13136648071041058242402761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140124246091104621252296117 13136648071041058242402761)
              ·
                refine ⟨9852486053280793681802071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13136648071041058242402761 9852486053280793681802071)
                ·
                  refine ⟨14778729079921190522703107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9852486053280793681802071 14778729079921190522703107)
                  ·
                    refine ⟨22168093619881785784054661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14778729079921190522703107 22168093619881785784054661)
                    ·
                      refine ⟨4156517553727834834510249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22168093619881785784054661 4156517553727834834510249)
                      ·
                        rfl

theorem cell23_8094789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_8094789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094789 prefixEnd_8094789 := by exact prefixLift 8094789
  have htrace : WordTrace (prefixWord ++ tailWord_8094789) baseStart_8094789 baseEnd_8094789 := by
    simpa [prefixWord, tailWord_8094789, baseEnd_8094789] using wordTrace_append hprefix tailTrace_8094789
  have hstable : (prefixWord ++ tailWord_8094789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094789).length < 2 ^ (prefixWord ++ tailWord_8094789).sum := by decide
  have hdescent : baseEnd_8094789 < baseStart_8094789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094829 : List Nat := [1, 5, 1, 1, 2, 4, 1, 8]
def baseStart_8094829 : Nat := 118140960795 + 8094829 * 2 ^ 59
def prefixEnd_8094829 : Nat := 4983230072969 + 3 ^ 40 * 8094829 * 2
def baseEnd_8094829 : Nat := 153945855294593136222595

theorem tailTrace_8094829 : CollatzResearch.WordTrace tailWord_8094829 prefixEnd_8094829 153945855294593136222595 := by
  unfold tailWord_8094829
  simp only [CollatzResearch.WordTrace]
  refine ⟨295242668790824494572919541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196828445860549663048613027 295242668790824494572919541)
  ·
    refine ⟨27679000199139796366211207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295242668790824494572919541 27679000199139796366211207)
    ·
      refine ⟨41518500298709694549316811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27679000199139796366211207 41518500298709694549316811)
      ·
        refine ⟨62277750448064541823975217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41518500298709694549316811 62277750448064541823975217)
        ·
          refine ⟨46708312836048406367981413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62277750448064541823975217 46708312836048406367981413)
          ·
            refine ⟨8757808656759076193996515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46708312836048406367981413 8757808656759076193996515)
            ·
              refine ⟨13136712985138614290994773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757808656759076193996515 13136712985138614290994773)
              ·
                refine ⟨153945855294593136222595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13136712985138614290994773 153945855294593136222595)
                ·
                  rfl

theorem cell23_8094829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 8].length) (baseStart_8094829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094829 prefixEnd_8094829 := by exact prefixLift 8094829
  have htrace : WordTrace (prefixWord ++ tailWord_8094829) baseStart_8094829 baseEnd_8094829 := by
    simpa [prefixWord, tailWord_8094829, baseEnd_8094829] using wordTrace_append hprefix tailTrace_8094829
  have hstable : (prefixWord ++ tailWord_8094829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094829).length < 2 ^ (prefixWord ++ tailWord_8094829).sum := by decide
  have hdescent : baseEnd_8094829 < baseStart_8094829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094839 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_8094839 : Nat := 118140960795 + 8094839 * 2 ^ 59
def prefixEnd_8094839 : Nat := 4983230072969 + 3 ^ 40 * 8094839 * 2
def baseEnd_8094839 : Nat := 4156543227760559638885019

theorem tailTrace_8094839 : CollatzResearch.WordTrace tailWord_8094839 prefixEnd_8094839 4156543227760559638885019 := by
  unfold tailWord_8094839
  simp only [CollatzResearch.WordTrace]
  refine ⟨295243033520788266280783571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196828689013858844187189047 295243033520788266280783571)
  ·
    refine ⟨442864550281182399421175357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295243033520788266280783571 442864550281182399421175357)
    ·
      refine ⟨166074206355443399782940759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442864550281182399421175357 166074206355443399782940759)
      ·
        refine ⟨249111309533165099674411139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166074206355443399782940759 249111309533165099674411139)
        ·
          refine ⟨373666964299747649511616709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249111309533165099674411139 373666964299747649511616709)
          ·
            refine ⟨70062555806202684283428133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373666964299747649511616709 70062555806202684283428133)
            ·
              refine ⟨13136729213663003303142775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70062555806202684283428133 13136729213663003303142775)
              ·
                refine ⟨19705093820494504954714163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13136729213663003303142775 19705093820494504954714163)
                ·
                  refine ⟨29557640730741757432071245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19705093820494504954714163 29557640730741757432071245)
                  ·
                    refine ⟨11084115274028159037026717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29557640730741757432071245 11084115274028159037026717)
                    ·
                      refine ⟨4156543227760559638885019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11084115274028159037026717 4156543227760559638885019)
                      ·
                        rfl

theorem cell23_8094839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_8094839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094839 prefixEnd_8094839 := by exact prefixLift 8094839
  have htrace : WordTrace (prefixWord ++ tailWord_8094839) baseStart_8094839 baseEnd_8094839 := by
    simpa [prefixWord, tailWord_8094839, baseEnd_8094839] using wordTrace_append hprefix tailTrace_8094839
  have hstable : (prefixWord ++ tailWord_8094839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094839).length < 2 ^ (prefixWord ++ tailWord_8094839).sum := by decide
  have hdescent : baseEnd_8094839 < baseStart_8094839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094892 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_8094892 : Nat := 118140960795 + 8094892 * 2 ^ 59
def prefixEnd_8094892 : Nat := 4983230072969 + 3 ^ 40 * 8094892 * 2
def baseEnd_8094892 : Nat := 4156570442235247931522275

theorem tailTrace_8094892 : CollatzResearch.WordTrace tailWord_8094892 prefixEnd_8094892 4156570442235247931522275 := by
  unfold tailWord_8094892
  simp only [CollatzResearch.WordTrace]
  refine ⟨147622483294798128166231465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196829977726397504221641953 147622483294798128166231465)
  ·
    refine ⟨110716862471098596124673599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147622483294798128166231465 110716862471098596124673599)
    ·
      refine ⟨166075293706647894187010399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110716862471098596124673599 166075293706647894187010399)
      ·
        refine ⟨249112940559971841280515599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166075293706647894187010399 249112940559971841280515599)
        ·
          refine ⟨373669410839957761920773399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249112940559971841280515599 373669410839957761920773399)
          ·
            refine ⟨560504116259936642881160099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373669410839957761920773399 560504116259936642881160099)
            ·
              refine ⟨840756174389904964321740149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560504116259936642881160099 840756174389904964321740149)
              ·
                refine ⟨78820891349053590405163139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 840756174389904964321740149 78820891349053590405163139)
                ·
                  refine ⟨118231337023580385607744709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78820891349053590405163139 118231337023580385607744709)
                  ·
                    refine ⟨22168375691921322301452133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118231337023580385607744709 22168375691921322301452133)
                    ·
                      refine ⟨4156570442235247931522275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22168375691921322301452133 4156570442235247931522275)
                      ·
                        rfl

theorem cell23_8094892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_8094892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094892 prefixEnd_8094892 := by exact prefixLift 8094892
  have htrace : WordTrace (prefixWord ++ tailWord_8094892) baseStart_8094892 baseEnd_8094892 := by
    simpa [prefixWord, tailWord_8094892, baseEnd_8094892] using wordTrace_append hprefix tailTrace_8094892
  have hstable : (prefixWord ++ tailWord_8094892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094892).length < 2 ^ (prefixWord ++ tailWord_8094892).sum := by decide
  have hdescent : baseEnd_8094892 < baseStart_8094892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094916 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_8094916 : Nat := 118140960795 + 8094916 * 2 ^ 59
def prefixEnd_8094916 : Nat := 4983230072969 + 3 ^ 40 * 8094916 * 2
def baseEnd_8094916 : Nat := 4156582765770955837622165

theorem tailTrace_8094916 : CollatzResearch.WordTrace tailWord_8094916 prefixEnd_8094916 4156582765770955837622165 := by
  unfold tailWord_8094916
  simp only [CollatzResearch.WordTrace]
  refine ⟨147622920970754654215668301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196830561294339538954224401 147622920970754654215668301)
  ·
    refine ⟨55358595364032995330875613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147622920970754654215668301 55358595364032995330875613)
    ·
      refine ⟨20759473261512373249078355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55358595364032995330875613 20759473261512373249078355)
      ·
        refine ⟨31139209892268559873617533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20759473261512373249078355 31139209892268559873617533)
        ·
          refine ⟨11677203709600709952606575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31139209892268559873617533 11677203709600709952606575)
          ·
            refine ⟨17515805564401064928909863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11677203709600709952606575 17515805564401064928909863)
            ·
              refine ⟨26273708346601597393364795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17515805564401064928909863 26273708346601597393364795)
              ·
                refine ⟨39410562519902396090047193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26273708346601597393364795 39410562519902396090047193)
                ·
                  refine ⟨29557921889926797067535395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39410562519902396090047193 29557921889926797067535395)
                  ·
                    refine ⟨44336882834890195601303093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29557921889926797067535395 44336882834890195601303093)
                    ·
                      refine ⟨4156582765770955837622165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44336882834890195601303093 4156582765770955837622165)
                      ·
                        rfl

theorem cell23_8094916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_8094916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094916 prefixEnd_8094916 := by exact prefixLift 8094916
  have htrace : WordTrace (prefixWord ++ tailWord_8094916) baseStart_8094916 baseEnd_8094916 := by
    simpa [prefixWord, tailWord_8094916, baseEnd_8094916] using wordTrace_append hprefix tailTrace_8094916
  have hstable : (prefixWord ++ tailWord_8094916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094916).length < 2 ^ (prefixWord ++ tailWord_8094916).sum := by decide
  have hdescent : baseEnd_8094916 < baseStart_8094916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094936 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 7]
def baseStart_8094936 : Nat := 118140960795 + 8094936 * 2 ^ 59
def prefixEnd_8094936 : Nat := 4983230072969 + 3 ^ 40 * 8094936 * 2
def baseEnd_8094936 : Nat := 461843670598227306596897

theorem tailTrace_8094936 : CollatzResearch.WordTrace tailWord_8094936 prefixEnd_8094936 461843670598227306596897 := by
  unfold tailWord_8094936
  simp only [CollatzResearch.WordTrace]
  refine ⟨147623285700718425923532331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196831047600957901231376441 147623285700718425923532331)
  ·
    refine ⟨221434928551077638885298497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147623285700718425923532331 221434928551077638885298497)
    ·
      refine ⟨166076196413308229163973873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221434928551077638885298497 166076196413308229163973873)
      ·
        refine ⟨124557147309981171872980405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166076196413308229163973873 124557147309981171872980405)
        ·
          refine ⟨11677232560310734863091913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124557147309981171872980405 11677232560310734863091913)
          ·
            refine ⟨8757924420233051147318935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11677232560310734863091913 8757924420233051147318935)
            ·
              refine ⟨13136886630349576720978403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757924420233051147318935 13136886630349576720978403)
              ·
                refine ⟨19705329945524365081467605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13136886630349576720978403 19705329945524365081467605)
                ·
                  refine ⟨461843670598227306596897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19705329945524365081467605 461843670598227306596897)
                  ·
                    rfl

theorem cell23_8094936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 7].length) (baseStart_8094936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094936 prefixEnd_8094936 := by exact prefixLift 8094936
  have htrace : WordTrace (prefixWord ++ tailWord_8094936) baseStart_8094936 baseEnd_8094936 := by
    simpa [prefixWord, tailWord_8094936, baseEnd_8094936] using wordTrace_append hprefix tailTrace_8094936
  have hstable : (prefixWord ++ tailWord_8094936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094936).length < 2 ^ (prefixWord ++ tailWord_8094936).sum := by decide
  have hdescent : baseEnd_8094936 < baseStart_8094936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094986 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_8094986 : Nat := 118140960795 + 8094986 * 2 ^ 59
def prefixEnd_8094986 : Nat := 4983230072969 + 3 ^ 40 * 8094986 * 2
def baseEnd_8094986 : Nat := 4156618709416770563746843

theorem tailTrace_8094986 : CollatzResearch.WordTrace tailWord_8094986 prefixEnd_8094986 4156618709416770563746843 := by
  unfold tailWord_8094986
  simp only [CollatzResearch.WordTrace]
  refine ⟨73812098762813927596596203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196832263367503806924256541 73812098762813927596596203)
  ·
    refine ⟨110718148144220891394894305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73812098762813927596596203 110718148144220891394894305)
    ·
      refine ⟨83038611108165668546170729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110718148144220891394894305 83038611108165668546170729)
      ·
        refine ⟨62278958331124251409628047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83038611108165668546170729 62278958331124251409628047)
        ·
          refine ⟨93418437496686377114442071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62278958331124251409628047 93418437496686377114442071)
          ·
            refine ⟨140127656245029565671663107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93418437496686377114442071 140127656245029565671663107)
            ·
              refine ⟨210191484367544348507494661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140127656245029565671663107 210191484367544348507494661)
              ·
                refine ⟨39410903318914565345155249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210191484367544348507494661 39410903318914565345155249)
                ·
                  refine ⟨29558177489185924008866437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39410903318914565345155249 29558177489185924008866437)
                  ·
                    refine ⟨5542158279222360751662457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29558177489185924008866437 5542158279222360751662457)
                    ·
                      refine ⟨4156618709416770563746843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542158279222360751662457 4156618709416770563746843)
                      ·
                        rfl

theorem cell23_8094986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_8094986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094986 prefixEnd_8094986 := by exact prefixLift 8094986
  have htrace : WordTrace (prefixWord ++ tailWord_8094986) baseStart_8094986 baseEnd_8094986 := by
    simpa [prefixWord, tailWord_8094986, baseEnd_8094986] using wordTrace_append hprefix tailTrace_8094986
  have hstable : (prefixWord ++ tailWord_8094986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094986).length < 2 ^ (prefixWord ++ tailWord_8094986).sum := by decide
  have hdescent : baseEnd_8094986 < baseStart_8094986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094992 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 14]
def baseStart_8094992 : Nat := 118140960795 + 8094992 * 2 ^ 59
def prefixEnd_8094992 : Nat := 4983230072969 + 3 ^ 40 * 8094992 * 2
def baseEnd_8094992 : Nat := 461846865588966393363535

theorem tailTrace_8094992 : CollatzResearch.WordTrace tailWord_8094992 prefixEnd_8094992 461846865588966393363535 := by
  unfold tailWord_8094992
  simp only [CollatzResearch.WordTrace]
  refine ⟨147624306944616986705551615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196832409259489315607402153 147624306944616986705551615)
  ·
    refine ⟨221436460416925480058327423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147624306944616986705551615 221436460416925480058327423)
    ·
      refine ⟨332154690625388220087491135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221436460416925480058327423 332154690625388220087491135)
      ·
        refine ⟨498232035938082330131236703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332154690625388220087491135 498232035938082330131236703)
        ·
          refine ⟨747348053907123495196855055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498232035938082330131236703 747348053907123495196855055)
          ·
            refine ⟨1121022080860685242795282583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747348053907123495196855055 1121022080860685242795282583)
            ·
              refine ⟨1681533121291027864192923875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121022080860685242795282583 1681533121291027864192923875)
              ·
                refine ⟨2522299681936541796289385813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681533121291027864192923875 2522299681936541796289385813)
                ·
                  refine ⟨461846865588966393363535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 14 2522299681936541796289385813 461846865588966393363535)
                  ·
                    rfl

theorem cell23_8094992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 14].length) (baseStart_8094992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094992 prefixEnd_8094992 := by exact prefixLift 8094992
  have htrace : WordTrace (prefixWord ++ tailWord_8094992) baseStart_8094992 baseEnd_8094992 := by
    simpa [prefixWord, tailWord_8094992, baseEnd_8094992] using wordTrace_append hprefix tailTrace_8094992
  have hstable : (prefixWord ++ tailWord_8094992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094992).length < 2 ^ (prefixWord ++ tailWord_8094992).sum := by decide
  have hdescent : baseEnd_8094992 < baseStart_8094992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095143 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_8095143 : Nat := 118140960795 + 8095143 * 2 ^ 59
def prefixEnd_8095143 : Nat := 4983230072969 + 3 ^ 40 * 8095143 * 2
def baseEnd_8095143 : Nat := 4156699325879526449483621

theorem tailTrace_8095143 : CollatzResearch.WordTrace tailWord_8095143 prefixEnd_8095143 4156699325879526449483621 := by
  unfold tailWord_8095143
  simp only [CollatzResearch.WordTrace]
  refine ⟨295254121311686926199850083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196836080874457950799900055 295254121311686926199850083)
  ·
    refine ⟨442881181967530389299775125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295254121311686926199850083 442881181967530389299775125)
    ·
      refine ⟨20760055404727986998426959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 442881181967530389299775125 20760055404727986998426959)
      ·
        refine ⟨31140083107091980497640439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20760055404727986998426959 31140083107091980497640439)
        ·
          refine ⟨46710124660637970746460659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31140083107091980497640439 46710124660637970746460659)
          ·
            refine ⟨70065186990956956119690989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46710124660637970746460659 70065186990956956119690989)
            ·
              refine ⟨26274445121608858544884121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70065186990956956119690989 26274445121608858544884121)
              ·
                refine ⟨19705833841206643908663091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26274445121608858544884121 19705833841206643908663091)
                ·
                  refine ⟨29558750761809965862994637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19705833841206643908663091 29558750761809965862994637)
                  ·
                    refine ⟨11084531535678737198622989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29558750761809965862994637 11084531535678737198622989)
                    ·
                      refine ⟨4156699325879526449483621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11084531535678737198622989 4156699325879526449483621)
                      ·
                        rfl

theorem cell23_8095143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_8095143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095143 prefixEnd_8095143 := by exact prefixLift 8095143
  have htrace : WordTrace (prefixWord ++ tailWord_8095143) baseStart_8095143 baseEnd_8095143 := by
    simpa [prefixWord, tailWord_8095143, baseEnd_8095143] using wordTrace_append hprefix tailTrace_8095143
  have hstable : (prefixWord ++ tailWord_8095143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095143).length < 2 ^ (prefixWord ++ tailWord_8095143).sum := by decide
  have hdescent : baseEnd_8095143 < baseStart_8095143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095161 : List Nat := [1, 2, 1, 4, 4, 2, 2, 2, 1, 2, 2]
def baseStart_8095161 : Nat := 118140960795 + 8095161 * 2 ^ 59
def prefixEnd_8095161 : Nat := 4983230072969 + 3 ^ 40 * 8095161 * 2
def baseEnd_8095161 : Nat := 4156708568531307379058539

theorem tailTrace_8095161 : CollatzResearch.WordTrace tailWord_8095161 prefixEnd_8095161 4156708568531307379058539 := by
  unfold tailWord_8095161
  simp only [CollatzResearch.WordTrace]
  refine ⟨295254777825621715274005337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196836518550414476849336891 295254777825621715274005337)
  ·
    refine ⟨221441083369216286455504003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295254777825621715274005337 221441083369216286455504003)
    ·
      refine ⟨332161625053824429683256005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221441083369216286455504003 332161625053824429683256005)
      ·
        refine ⟨62280304697592080565610501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332161625053824429683256005 62280304697592080565610501)
        ·
          refine ⟨11677557130798515106051969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62280304697592080565610501 11677557130798515106051969)
          ·
            refine ⟨8758167848098886329538977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11677557130798515106051969 8758167848098886329538977)
            ·
              refine ⟨6568625886074164747154233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8758167848098886329538977 6568625886074164747154233)
              ·
                refine ⟨4926469414555623560365675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6568625886074164747154233 4926469414555623560365675)
                ·
                  refine ⟨7389704121833435340548513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926469414555623560365675 7389704121833435340548513)
                  ·
                    refine ⟨5542278091375076505411385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7389704121833435340548513 5542278091375076505411385)
                    ·
                      refine ⟨4156708568531307379058539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542278091375076505411385 4156708568531307379058539)
                      ·
                        rfl

theorem cell23_8095161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_8095161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095161 prefixEnd_8095161 := by exact prefixLift 8095161
  have htrace : WordTrace (prefixWord ++ tailWord_8095161) baseStart_8095161 baseEnd_8095161 := by
    simpa [prefixWord, tailWord_8095161, baseEnd_8095161] using wordTrace_append hprefix tailTrace_8095161
  have hstable : (prefixWord ++ tailWord_8095161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095161).length < 2 ^ (prefixWord ++ tailWord_8095161).sum := by decide
  have hdescent : baseEnd_8095161 < baseStart_8095161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095176 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 2, 6]
def baseStart_8095176 : Nat := 118140960795 + 8095176 * 2 ^ 59
def prefixEnd_8095176 : Nat := 4983230072969 + 3 ^ 40 * 8095176 * 2
def baseEnd_8095176 : Nat := 1385572090247041606790323

theorem tailTrace_8095176 : CollatzResearch.WordTrace tailWord_8095176 prefixEnd_8095176 1385572090247041606790323 := by
  unfold tailWord_8095176
  simp only [CollatzResearch.WordTrace]
  refine ⟨147627662460283686417900691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196836883280378248557200921 147627662460283686417900691)
  ·
    refine ⟨221441493690425529626851037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147627662460283686417900691 221441493690425529626851037)
    ·
      refine ⟨83040560133909573610069139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221441493690425529626851037 83040560133909573610069139)
      ·
        refine ⟨124560840200864360415103709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83040560133909573610069139 124560840200864360415103709)
        ·
          refine ⟨46710315075324135155663891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124560840200864360415103709 46710315075324135155663891)
          ·
            refine ⟨70065472612986202733495837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46710315075324135155663891 70065472612986202733495837)
            ·
              refine ⟨26274552229869826025060939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70065472612986202733495837 26274552229869826025060939)
              ·
                refine ⟨39411828344804739037591409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26274552229869826025060939 39411828344804739037591409)
                ·
                  refine ⟨29558871258603554278193557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39411828344804739037591409 29558871258603554278193557)
                  ·
                    refine ⟨1385572090247041606790323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29558871258603554278193557 1385572090247041606790323)
                    ·
                      rfl

theorem cell23_8095176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_8095176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095176 prefixEnd_8095176 := by exact prefixLift 8095176
  have htrace : WordTrace (prefixWord ++ tailWord_8095176) baseStart_8095176 baseEnd_8095176 := by
    simpa [prefixWord, tailWord_8095176, baseEnd_8095176] using wordTrace_append hprefix tailTrace_8095176
  have hstable : (prefixWord ++ tailWord_8095176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095176).length < 2 ^ (prefixWord ++ tailWord_8095176).sum := by decide
  have hdescent : baseEnd_8095176 < baseStart_8095176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095183 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 1, 4, 2]
def baseStart_8095183 : Nat := 118140960795 + 8095183 * 2 ^ 59
def prefixEnd_8095183 : Nat := 4983230072969 + 3 ^ 40 * 8095183 * 2
def baseEnd_8095183 : Nat := 4156719865105706292983437

theorem tailTrace_8095183 : CollatzResearch.WordTrace tailWord_8095183 prefixEnd_8095183 4156719865105706292983437 := by
  unfold tailWord_8095183
  simp only [CollatzResearch.WordTrace]
  refine ⟨295255580231542013031306203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196837053487694675354204135 295255580231542013031306203)
  ·
    refine ⟨442883370347313019546959305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295255580231542013031306203 442883370347313019546959305)
    ·
      refine ⟨332162527760484764660219479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442883370347313019546959305 332162527760484764660219479)
      ·
        refine ⟨498243791640727146990329219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332162527760484764660219479 498243791640727146990329219)
        ·
          refine ⟨747365687461090720485493829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498243791640727146990329219 747365687461090720485493829)
          ·
            refine ⟨140131066398954510091030093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 747365687461090720485493829 140131066398954510091030093)
            ·
              refine ⟨52549149899607941284136285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140131066398954510091030093 52549149899607941284136285)
              ·
                refine ⟨19705931212352977981551107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52549149899607941284136285 19705931212352977981551107)
                ·
                  refine ⟨29558896818529466972326661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19705931212352977981551107 29558896818529466972326661)
                  ·
                    refine ⟨5542293153474275057311249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29558896818529466972326661 5542293153474275057311249)
                    ·
                      refine ⟨4156719865105706292983437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542293153474275057311249 4156719865105706292983437)
                      ·
                        rfl

theorem cell23_8095183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 4, 2].length) (baseStart_8095183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095183 prefixEnd_8095183 := by exact prefixLift 8095183
  have htrace : WordTrace (prefixWord ++ tailWord_8095183) baseStart_8095183 baseEnd_8095183 := by
    simpa [prefixWord, tailWord_8095183, baseEnd_8095183] using wordTrace_append hprefix tailTrace_8095183
  have hstable : (prefixWord ++ tailWord_8095183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095183).length < 2 ^ (prefixWord ++ tailWord_8095183).sum := by decide
  have hdescent : baseEnd_8095183 < baseStart_8095183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095217 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 2, 2, 2]
def baseStart_8095217 : Nat := 118140960795 + 8095217 * 2 ^ 59
def prefixEnd_8095217 : Nat := 4983230072969 + 3 ^ 40 * 8095217 * 2
def baseEnd_8095217 : Nat := 4156737323447959159958281

theorem tailTrace_8095217 : CollatzResearch.WordTrace tailWord_8095217 prefixEnd_8095217 4156737323447959159958281 := by
  unfold tailWord_8095217
  simp only [CollatzResearch.WordTrace]
  refine ⟨295256820313418836838043905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196837880208945891225362603 295256820313418836838043905)
  ·
    refine ⟨221442615235064127628532929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295256820313418836838043905 221442615235064127628532929)
    ·
      refine ⟨166081961426298095721399697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221442615235064127628532929 166081961426298095721399697)
      ·
        refine ⟨124561471069723571791049773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166081961426298095721399697 124561471069723571791049773)
        ·
          refine ⟨46710551651146339421643665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124561471069723571791049773 46710551651146339421643665)
          ·
            refine ⟨35032913738359754566232749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46710551651146339421643665 35032913738359754566232749)
            ·
              refine ⟨13137342651884907962337281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35032913738359754566232749 13137342651884907962337281)
              ·
                refine ⟨9853006988913680971752961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13137342651884907962337281 9853006988913680971752961)
                ·
                  refine ⟨7389755241685260728814721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9853006988913680971752961 7389755241685260728814721)
                  ·
                    refine ⟨5542316431263945546611041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7389755241685260728814721 5542316431263945546611041)
                    ·
                      refine ⟨4156737323447959159958281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542316431263945546611041 4156737323447959159958281)
                      ·
                        rfl

theorem cell23_8095217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_8095217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095217 prefixEnd_8095217 := by exact prefixLift 8095217
  have htrace : WordTrace (prefixWord ++ tailWord_8095217) baseStart_8095217 baseEnd_8095217 := by
    simpa [prefixWord, tailWord_8095217, baseEnd_8095217] using wordTrace_append hprefix tailTrace_8095217
  have hstable : (prefixWord ++ tailWord_8095217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095217).length < 2 ^ (prefixWord ++ tailWord_8095217).sum := by decide
  have hdescent : baseEnd_8095217 < baseStart_8095217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095234 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_8095234 : Nat := 118140960795 + 8095234 * 2 ^ 59
def prefixEnd_8095234 : Nat := 4983230072969 + 3 ^ 40 * 8095234 * 2
def baseEnd_8095234 : Nat := 4156746052619085593445703

theorem tailTrace_8095234 : CollatzResearch.WordTrace tailWord_8095234 prefixEnd_8095234 4156746052619085593445703 := by
  unfold tailWord_8095234
  simp only [CollatzResearch.WordTrace]
  refine ⟨73814360088589312185353189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196838293569571499160941837 73814360088589312185353189)
  ·
    refine ⟨13840192516610496034753723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73814360088589312185353189 13840192516610496034753723)
    ·
      refine ⟨20760288774915744052130585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13840192516610496034753723 20760288774915744052130585)
      ·
        refine ⟨15570216581186808039097939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20760288774915744052130585 15570216581186808039097939)
        ·
          refine ⟨23355324871780212058646909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15570216581186808039097939 23355324871780212058646909)
          ·
            refine ⟨8758246826917579521992591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23355324871780212058646909 8758246826917579521992591)
            ·
              refine ⟨13137370240376369282988887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8758246826917579521992591 13137370240376369282988887)
              ·
                refine ⟨19706055360564553924483331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13137370240376369282988887 19706055360564553924483331)
                ·
                  refine ⟨29559083040846830886724997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19706055360564553924483331 29559083040846830886724997)
                  ·
                    refine ⟨5542328070158780791260937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29559083040846830886724997 5542328070158780791260937)
                    ·
                      refine ⟨4156746052619085593445703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542328070158780791260937 4156746052619085593445703)
                      ·
                        rfl

theorem cell23_8095234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_8095234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095234 prefixEnd_8095234 := by exact prefixLift 8095234
  have htrace : WordTrace (prefixWord ++ tailWord_8095234) baseStart_8095234 baseEnd_8095234 := by
    simpa [prefixWord, tailWord_8095234, baseEnd_8095234] using wordTrace_append hprefix tailTrace_8095234
  have hstable : (prefixWord ++ tailWord_8095234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095234).length < 2 ^ (prefixWord ++ tailWord_8095234).sum := by decide
  have hdescent : baseEnd_8095234 < baseStart_8095234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095238 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_8095238 : Nat := 118140960795 + 8095238 * 2 ^ 59
def prefixEnd_8095238 : Nat := 4983230072969 + 3 ^ 40 * 8095238 * 2
def baseEnd_8095238 : Nat := 4156748106541703577795685

theorem tailTrace_8095238 : CollatzResearch.WordTrace tailWord_8095238 prefixEnd_8095238 4156748106541703577795685 := by
  unfold tailWord_8095238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226799570198211169517449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196838390830895171616372245 9226799570198211169517449)
  ·
    refine ⟨6920099677648658377138087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9226799570198211169517449 6920099677648658377138087)
    ·
      refine ⟨10380149516472987565707131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6920099677648658377138087 10380149516472987565707131)
      ·
        refine ⟨15570224274709481348560697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10380149516472987565707131 15570224274709481348560697)
        ·
          refine ⟨11677668206032111011420523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15570224274709481348560697 11677668206032111011420523)
          ·
            refine ⟨17516502309048166517130785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11677668206032111011420523 17516502309048166517130785)
            ·
              refine ⟨13137376731786124887848089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17516502309048166517130785 13137376731786124887848089)
              ·
                refine ⟨9853032548839593665886067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13137376731786124887848089 9853032548839593665886067)
                ·
                  refine ⟨14779548823259390498829101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9853032548839593665886067 14779548823259390498829101)
                  ·
                    refine ⟨5542330808722271437060913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14779548823259390498829101 5542330808722271437060913)
                    ·
                      refine ⟨4156748106541703577795685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542330808722271437060913 4156748106541703577795685)
                      ·
                        rfl

theorem cell23_8095238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_8095238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095238 prefixEnd_8095238 := by exact prefixLift 8095238
  have htrace : WordTrace (prefixWord ++ tailWord_8095238) baseStart_8095238 baseEnd_8095238 := by
    simpa [prefixWord, tailWord_8095238, baseEnd_8095238] using wordTrace_append hprefix tailTrace_8095238
  have hstable : (prefixWord ++ tailWord_8095238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095238).length < 2 ^ (prefixWord ++ tailWord_8095238).sum := by decide
  have hdescent : baseEnd_8095238 < baseStart_8095238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095340 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 3]
def baseStart_8095340 : Nat := 118140960795 + 8095340 * 2 ^ 59
def prefixEnd_8095340 : Nat := 4983230072969 + 3 ^ 40 * 8095340 * 2
def baseEnd_8095340 : Nat := 4156800481568462178720215

theorem tailTrace_8095340 : CollatzResearch.WordTrace tailWord_8095340 prefixEnd_8095340 4156800481568462178720215 := by
  unfold tailWord_8095340
  simp only [CollatzResearch.WordTrace]
  refine ⟨147630653245986614422385737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196840870994648819229847649 147630653245986614422385737)
  ·
    refine ⟨110722989934489960816789303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147630653245986614422385737 110722989934489960816789303)
    ·
      refine ⟨166084484901734941225183955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110722989934489960816789303 166084484901734941225183955)
      ·
        refine ⟨249126727352602411837775933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166084484901734941225183955 249126727352602411837775933)
        ·
          refine ⟨93422522757225904439165975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249126727352602411837775933 93422522757225904439165975)
          ·
            refine ⟨140133784135838856658748963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93422522757225904439165975 140133784135838856658748963)
            ·
              refine ⟨210200676203758284988123445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140133784135838856658748963 210200676203758284988123445)
              ·
                refine ⟨19706313394102339217636573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210200676203758284988123445 19706313394102339217636573)
                ·
                  refine ⟨7389867522788377206613715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19706313394102339217636573 7389867522788377206613715)
                  ·
                    refine ⟨11084801284182565809920573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7389867522788377206613715 11084801284182565809920573)
                    ·
                      refine ⟨4156800481568462178720215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11084801284182565809920573 4156800481568462178720215)
                      ·
                        rfl

theorem cell23_8095340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_8095340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095340 prefixEnd_8095340 := by exact prefixLift 8095340
  have htrace : WordTrace (prefixWord ++ tailWord_8095340) baseStart_8095340 baseEnd_8095340 := by
    simpa [prefixWord, tailWord_8095340, baseEnd_8095340] using wordTrace_append hprefix tailTrace_8095340
  have hstable : (prefixWord ++ tailWord_8095340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095340).length < 2 ^ (prefixWord ++ tailWord_8095340).sum := by decide
  have hdescent : baseEnd_8095340 < baseStart_8095340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095357 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_8095357 : Nat := 118140960795 + 8095357 * 2 ^ 59
def prefixEnd_8095357 : Nat := 4983230072969 + 3 ^ 40 * 8095357 * 2
def baseEnd_8095357 : Nat := 4156809210739588612207637

theorem tailTrace_8095357 : CollatzResearch.WordTrace tailWord_8095357 prefixEnd_8095357 4156809210739588612207637 := by
  unfold tailWord_8095357
  simp only [CollatzResearch.WordTrace]
  refine ⟨295261926532911640748140325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196841284355274427165426883 295261926532911640748140325)
  ·
    refine ⟨55361611224920932640276311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295261926532911640748140325 55361611224920932640276311)
    ·
      refine ⟨83042416837381398960414467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55361611224920932640276311 83042416837381398960414467)
      ·
        refine ⟨124563625256072098440621701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83042416837381398960414467 124563625256072098440621701)
        ·
          refine ⟨23355679735513518457616569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124563625256072098440621701 23355679735513518457616569)
          ·
            refine ⟨17516759801635138843212427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23355679735513518457616569 17516759801635138843212427)
            ·
              refine ⟨26275139702452708264818641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17516759801635138843212427 26275139702452708264818641)
              ·
                refine ⟨19706354776839531198613981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26275139702452708264818641 19706354776839531198613981)
                ·
                  refine ⟨7389883041314824199480243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19706354776839531198613981 7389883041314824199480243)
                  ·
                    refine ⟨11084824561972236299220365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7389883041314824199480243 11084824561972236299220365)
                    ·
                      refine ⟨4156809210739588612207637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11084824561972236299220365 4156809210739588612207637)
                      ·
                        rfl

theorem cell23_8095357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_8095357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095357 prefixEnd_8095357 := by exact prefixLift 8095357
  have htrace : WordTrace (prefixWord ++ tailWord_8095357) baseStart_8095357 baseEnd_8095357 := by
    simpa [prefixWord, tailWord_8095357, baseEnd_8095357] using wordTrace_append hprefix tailTrace_8095357
  have hstable : (prefixWord ++ tailWord_8095357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095357).length < 2 ^ (prefixWord ++ tailWord_8095357).sum := by decide
  have hdescent : baseEnd_8095357 < baseStart_8095357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095367 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_8095367 : Nat := 118140960795 + 8095367 * 2 ^ 59
def prefixEnd_8095367 : Nat := 4983230072969 + 3 ^ 40 * 8095367 * 2
def baseEnd_8095367 : Nat := 4156814345546133573082591

theorem tailTrace_8095367 : CollatzResearch.WordTrace tailWord_8095367 prefixEnd_8095367 4156814345546133573082591 := by
  unfold tailWord_8095367
  simp only [CollatzResearch.WordTrace]
  refine ⟨295262291262875412456004355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196841527508583608304002903 295262291262875412456004355)
  ·
    refine ⟨442893436894313118684006533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295262291262875412456004355 442893436894313118684006533)
    ·
      refine ⟨83042519417683709753251225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442893436894313118684006533 83042519417683709753251225)
      ·
        refine ⟨62281889563262782314938419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83042519417683709753251225 62281889563262782314938419)
        ·
          refine ⟨93422834344894173472407629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62281889563262782314938419 93422834344894173472407629)
          ·
            refine ⟨35033562879335315052152861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93422834344894173472407629 35033562879335315052152861)
            ·
              refine ⟨13137586079750743144557323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35033562879335315052152861 13137586079750743144557323)
              ·
                refine ⟨19706379119626114716835985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13137586079750743144557323 19706379119626114716835985)
                ·
                  refine ⟨14779784339719586037626989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19706379119626114716835985 14779784339719586037626989)
                  ·
                    refine ⟨5542419127394844764110121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14779784339719586037626989 5542419127394844764110121)
                    ·
                      refine ⟨4156814345546133573082591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542419127394844764110121 4156814345546133573082591)
                      ·
                        rfl

theorem cell23_8095367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_8095367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095367 prefixEnd_8095367 := by exact prefixLift 8095367
  have htrace : WordTrace (prefixWord ++ tailWord_8095367) baseStart_8095367 baseEnd_8095367 := by
    simpa [prefixWord, tailWord_8095367, baseEnd_8095367] using wordTrace_append hprefix tailTrace_8095367
  have hstable : (prefixWord ++ tailWord_8095367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095367).length < 2 ^ (prefixWord ++ tailWord_8095367).sum := by decide
  have hdescent : baseEnd_8095367 < baseStart_8095367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095374 : List Nat := [4, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3]
def baseStart_8095374 : Nat := 118140960795 + 8095374 * 2 ^ 59
def prefixEnd_8095374 : Nat := 4983230072969 + 3 ^ 40 * 8095374 * 2
def baseEnd_8095374 : Nat := 4156817939910715045695059

theorem tailTrace_8095374 : CollatzResearch.WordTrace tailWord_8095374 prefixEnd_8095374 4156817939910715045695059 := by
  unfold tailWord_8095374
  simp only [CollatzResearch.WordTrace]
  refine ⟨36907818321731256581438647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196841697715900035101006117 36907818321731256581438647)
  ·
    refine ⟨55361727482596884872157971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36907818321731256581438647 55361727482596884872157971)
    ·
      refine ⟨83042591223895327308236957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55361727482596884872157971 83042591223895327308236957)
      ·
        refine ⟨31140971708960747740588859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83042591223895327308236957 31140971708960747740588859)
        ·
          refine ⟨46711457563441121610883289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31140971708960747740588859 46711457563441121610883289)
          ·
            refine ⟨35033593172580841208162467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46711457563441121610883289 35033593172580841208162467)
            ·
              refine ⟨52550389758871261812243701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35033593172580841208162467 52550389758871261812243701)
              ·
                refine ⟨4926599039894180794897847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52550389758871261812243701 4926599039894180794897847)
                ·
                  refine ⟨7389898559841271192346771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926599039894180794897847 7389898559841271192346771)
                  ·
                    refine ⟨11084847839761906788520157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7389898559841271192346771 11084847839761906788520157)
                    ·
                      refine ⟨4156817939910715045695059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11084847839761906788520157 4156817939910715045695059)
                      ·
                        rfl

theorem cell23_8095374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_8095374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095374 prefixEnd_8095374 := by exact prefixLift 8095374
  have htrace : WordTrace (prefixWord ++ tailWord_8095374) baseStart_8095374 baseEnd_8095374 := by
    simpa [prefixWord, tailWord_8095374, baseEnd_8095374] using wordTrace_append hprefix tailTrace_8095374
  have hstable : (prefixWord ++ tailWord_8095374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095374).length < 2 ^ (prefixWord ++ tailWord_8095374).sum := by decide
  have hdescent : baseEnd_8095374 < baseStart_8095374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095397 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 3, 2, 2]
def baseStart_8095397 : Nat := 118140960795 + 8095397 * 2 ^ 59
def prefixEnd_8095397 : Nat := 4983230072969 + 3 ^ 40 * 8095397 * 2
def baseEnd_8095397 : Nat := 4156829749965768455707453

theorem tailTrace_8095397 : CollatzResearch.WordTrace tailWord_8095397 prefixEnd_8095397 4156829749965768455707453 := by
  unfold tailWord_8095397
  simp only [CollatzResearch.WordTrace]
  refine ⟨295263385452766727579596445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196842256968511151719730963 295263385452766727579596445)
  ·
    refine ⟨110723769544787522842348667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295263385452766727579596445 110723769544787522842348667)
    ·
      refine ⟨166085654317181284263523001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110723769544787522842348667 166085654317181284263523001)
      ·
        refine ⟨124564240737885963197642251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166085654317181284263523001 124564240737885963197642251)
        ·
          refine ⟨186846361106828944796463377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124564240737885963197642251 186846361106828944796463377)
          ·
            refine ⟨140134770830121708597347533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186846361106828944796463377 140134770830121708597347533)
            ·
              refine ⟨52550539061295640724005325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140134770830121708597347533 52550539061295640724005325)
              ·
                refine ⟨19706452147985865271501997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52550539061295640724005325 19706452147985865271501997)
                ·
                  refine ⟨7389919555494699476813249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19706452147985865271501997 7389919555494699476813249)
                  ·
                    refine ⟨5542439666621024607609937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7389919555494699476813249 5542439666621024607609937)
                    ·
                      refine ⟨4156829749965768455707453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542439666621024607609937 4156829749965768455707453)
                      ·
                        rfl

theorem cell23_8095397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_8095397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095397 prefixEnd_8095397 := by exact prefixLift 8095397
  have htrace : WordTrace (prefixWord ++ tailWord_8095397) baseStart_8095397 baseEnd_8095397 := by
    simpa [prefixWord, tailWord_8095397, baseEnd_8095397] using wordTrace_append hprefix tailTrace_8095397
  have hstable : (prefixWord ++ tailWord_8095397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095397).length < 2 ^ (prefixWord ++ tailWord_8095397).sum := by decide
  have hdescent : baseEnd_8095397 < baseStart_8095397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095407 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 2, 4]
def baseStart_8095407 : Nat := 118140960795 + 8095407 * 2 ^ 59
def prefixEnd_8095407 : Nat := 4983230072969 + 3 ^ 40 * 8095407 * 2
def baseEnd_8095407 : Nat := 1385611628257437805527469

theorem tailTrace_8095407 : CollatzResearch.WordTrace tailWord_8095407 prefixEnd_8095407 1385611628257437805527469 := by
  unfold tailWord_8095407
  simp only [CollatzResearch.WordTrace]
  refine ⟨295263750182730499287460475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196842500121820332858306983 295263750182730499287460475)
  ·
    refine ⟨442895625274095748931190713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295263750182730499287460475 442895625274095748931190713)
    ·
      refine ⟨332171718955571811698393035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442895625274095748931190713 332171718955571811698393035)
      ·
        refine ⟨498257578433357717547589553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332171718955571811698393035 498257578433357717547589553)
        ·
          refine ⟨373693183825018288160692165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498257578433357717547589553 373693183825018288160692165)
          ·
            refine ⟨70067471967190929030129781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373693183825018288160692165 70067471967190929030129781)
            ·
              refine ⟨6568825496924149596574667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70067471967190929030129781 6568825496924149596574667)
              ·
                refine ⟨9853238245386224394862001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568825496924149596574667 9853238245386224394862001)
                ·
                  refine ⟨7389928684039668296146501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9853238245386224394862001 7389928684039668296146501)
                  ·
                    refine ⟨1385611628257437805527469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7389928684039668296146501 1385611628257437805527469)
                    ·
                      rfl

theorem cell23_8095407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 4].length) (baseStart_8095407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095407 prefixEnd_8095407 := by exact prefixLift 8095407
  have htrace : WordTrace (prefixWord ++ tailWord_8095407) baseStart_8095407 baseEnd_8095407 := by
    simpa [prefixWord, tailWord_8095407, baseEnd_8095407] using wordTrace_append hprefix tailTrace_8095407
  have hstable : (prefixWord ++ tailWord_8095407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095407).length < 2 ^ (prefixWord ++ tailWord_8095407).sum := by decide
  have hdescent : baseEnd_8095407 < baseStart_8095407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095410 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_8095410 : Nat := 118140960795 + 8095410 * 2 ^ 59
def prefixEnd_8095410 : Nat := 4983230072969 + 3 ^ 40 * 8095410 * 2
def baseEnd_8095410 : Nat := 4156836425214276904844893

theorem tailTrace_8095410 : CollatzResearch.WordTrace tailWord_8095410 prefixEnd_8095410 4156836425214276904844893 := by
  unfold tailWord_8095410
  simp only [CollatzResearch.WordTrace]
  refine ⟨73815964900429907699954921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196842573067813087199879789 73815964900429907699954921)
  ·
    refine ⟨55361973675322430774966191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73815964900429907699954921 55361973675322430774966191)
    ·
      refine ⟨83042960512983646162449287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55361973675322430774966191 83042960512983646162449287)
      ·
        refine ⟨124564440769475469243673931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83042960512983646162449287 124564440769475469243673931)
        ·
          refine ⟨186846661154213203865510897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124564440769475469243673931 186846661154213203865510897)
          ·
            refine ⟨140134995865659902899133173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186846661154213203865510897 140134995865659902899133173)
            ·
              refine ⟨13137655862405615896793735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140134995865659902899133173 13137655862405615896793735)
              ·
                refine ⟨19706483793608423845190603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13137655862405615896793735 19706483793608423845190603)
                ·
                  refine ⟨29559725690412635767785905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19706483793608423845190603 29559725690412635767785905)
                  ·
                    refine ⟨22169794267809476825839429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29559725690412635767785905 22169794267809476825839429)
                    ·
                      refine ⟨4156836425214276904844893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22169794267809476825839429 4156836425214276904844893)
                      ·
                        rfl

theorem cell23_8095410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_8095410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095410 prefixEnd_8095410 := by exact prefixLift 8095410
  have htrace : WordTrace (prefixWord ++ tailWord_8095410) baseStart_8095410 baseEnd_8095410 := by
    simpa [prefixWord, tailWord_8095410, baseEnd_8095410] using wordTrace_append hprefix tailTrace_8095410
  have hstable : (prefixWord ++ tailWord_8095410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095410).length < 2 ^ (prefixWord ++ tailWord_8095410).sum := by decide
  have hdescent : baseEnd_8095410 < baseStart_8095410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095414 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_8095414 : Nat := 118140960795 + 8095414 * 2 ^ 59
def prefixEnd_8095414 : Nat := 4983230072969 + 3 ^ 40 * 8095414 * 2
def baseEnd_8095414 : Nat := 4156838479136894889194875

theorem tailTrace_8095414 : CollatzResearch.WordTrace tailWord_8095414 prefixEnd_8095414 4156838479136894889194875 := by
  unfold tailWord_8095414
  simp only [CollatzResearch.WordTrace]
  refine ⟨18454000343356571217685331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196842670329136759655310197 18454000343356571217685331)
  ·
    refine ⟨27681000515034856826527997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18454000343356571217685331 27681000515034856826527997)
    ·
      refine ⟨10380375193138071309947999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27681000515034856826527997 10380375193138071309947999)
      ·
        refine ⟨15570562789707106964921999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10380375193138071309947999 15570562789707106964921999)
        ·
          refine ⟨23355844184560660447382999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15570562789707106964921999 23355844184560660447382999)
          ·
            refine ⟨35033766276840990671074499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23355844184560660447382999 35033766276840990671074499)
            ·
              refine ⟨52550649415261486006611749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35033766276840990671074499 52550649415261486006611749)
              ·
                refine ⟨9853246765361528626239703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52550649415261486006611749 9853246765361528626239703)
                ·
                  refine ⟨14779870148042292939359555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9853246765361528626239703 14779870148042292939359555)
                  ·
                    refine ⟨22169805222063439409039333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14779870148042292939359555 22169805222063439409039333)
                    ·
                      refine ⟨4156838479136894889194875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22169805222063439409039333 4156838479136894889194875)
                      ·
                        rfl

theorem cell23_8095414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_8095414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095414 prefixEnd_8095414 := by exact prefixLift 8095414
  have htrace : WordTrace (prefixWord ++ tailWord_8095414) baseStart_8095414 baseEnd_8095414 := by
    simpa [prefixWord, tailWord_8095414, baseEnd_8095414] using wordTrace_append hprefix tailTrace_8095414
  have hstable : (prefixWord ++ tailWord_8095414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095414).length < 2 ^ (prefixWord ++ tailWord_8095414).sum := by decide
  have hdescent : baseEnd_8095414 < baseStart_8095414 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095420 : List Nat := [2, 2, 2, 3, 1, 2, 4, 7]
def baseStart_8095420 : Nat := 118140960795 + 8095420 * 2 ^ 59
def prefixEnd_8095420 : Nat := 4983230072969 + 3 ^ 40 * 8095420 * 2
def baseEnd_8095420 : Nat := 153957094815585995026661

theorem tailTrace_8095420 : CollatzResearch.WordTrace tailWord_8095420 prefixEnd_8095420 153957094815585995026661 := by
  unfold tailWord_8095420
  simp only [CollatzResearch.WordTrace]
  refine ⟨147632112165841701253841857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196842816221122268338455809 147632112165841701253841857)
  ·
    refine ⟨110724084124381275940381393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147632112165841701253841857 110724084124381275940381393)
    ·
      refine ⟨83043063093285956955286045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110724084124381275940381393 83043063093285956955286045)
      ·
        refine ⟨31141148659982233858232267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83043063093285956955286045 31141148659982233858232267)
        ·
          refine ⟨46711722989973350787348401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31141148659982233858232267 46711722989973350787348401)
          ·
            refine ⟨35033792242480013090511301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46711722989973350787348401 35033792242480013090511301)
            ·
              refine ⟨6568836045465002454470869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35033792242480013090511301 6568836045465002454470869)
              ·
                refine ⟨153957094815585995026661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6568836045465002454470869 153957094815585995026661)
                ·
                  rfl

theorem cell23_8095420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 7].length) (baseStart_8095420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095420 prefixEnd_8095420 := by exact prefixLift 8095420
  have htrace : WordTrace (prefixWord ++ tailWord_8095420) baseStart_8095420 baseEnd_8095420 := by
    simpa [prefixWord, tailWord_8095420, baseEnd_8095420] using wordTrace_append hprefix tailTrace_8095420
  have hstable : (prefixWord ++ tailWord_8095420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095420).length < 2 ^ (prefixWord ++ tailWord_8095420).sum := by decide
  have hdescent : baseEnd_8095420 < baseStart_8095420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095437 : List Nat := [1, 6, 2, 1, 1, 3, 9]
def baseStart_8095437 : Nat := 118140960795 + 8095437 * 2 ^ 59
def prefixEnd_8095437 : Nat := 4983230072969 + 3 ^ 40 * 8095437 * 2
def baseEnd_8095437 : Nat := 51319139372740102459349

theorem tailTrace_8095437 : CollatzResearch.WordTrace tailWord_8095437 prefixEnd_8095437 51319139372740102459349 := by
  unfold tailWord_8095437
  simp only [CollatzResearch.WordTrace]
  refine ⟨295264844372621814411052565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196843229581747876274035043 295264844372621814411052565)
  ·
    refine ⟨13840539579966647550518089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 295264844372621814411052565 13840539579966647550518089)
    ·
      refine ⟨10380404684974985662888567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13840539579966647550518089 10380404684974985662888567)
      ·
        refine ⟨15570607027462478494332851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10380404684974985662888567 15570607027462478494332851)
        ·
          refine ⟨23355910541193717741499277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15570607027462478494332851 23355910541193717741499277)
          ·
            refine ⟨8758466452947644153062229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23355910541193717741499277 8758466452947644153062229)
            ·
              refine ⟨51319139372740102459349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8758466452947644153062229 51319139372740102459349)
              ·
                rfl

theorem cell23_8095437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 9].length) (baseStart_8095437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095437 prefixEnd_8095437 := by exact prefixLift 8095437
  have htrace : WordTrace (prefixWord ++ tailWord_8095437) baseStart_8095437 baseEnd_8095437 := by
    simpa [prefixWord, tailWord_8095437, baseEnd_8095437] using wordTrace_append hprefix tailTrace_8095437
  have hstable : (prefixWord ++ tailWord_8095437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095437).length < 2 ^ (prefixWord ++ tailWord_8095437).sum := by decide
  have hdescent : baseEnd_8095437 < baseStart_8095437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095447 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 3]
def baseStart_8095447 : Nat := 118140960795 + 8095447 * 2 ^ 59
def prefixEnd_8095447 : Nat := 4983230072969 + 3 ^ 40 * 8095447 * 2
def baseEnd_8095447 : Nat := 4156855423998493260082223

theorem tailTrace_8095447 : CollatzResearch.WordTrace tailWord_8095447 prefixEnd_8095447 4156855423998493260082223 := by
  unfold tailWord_8095447
  simp only [CollatzResearch.WordTrace]
  refine ⟨295265209102585586118916595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196843472735057057412611063 295265209102585586118916595)
  ·
    refine ⟨442897813653878379178374893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295265209102585586118916595 442897813653878379178374893)
    ·
      refine ⟨166086680120204392191890585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442897813653878379178374893 166086680120204392191890585)
      ·
        refine ⟨124565010090153294143917939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166086680120204392191890585 124565010090153294143917939)
        ·
          refine ⟨186847515135229941215876909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124565010090153294143917939 186847515135229941215876909)
          ·
            refine ⟨70067818175711227955953841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186847515135229941215876909 70067818175711227955953841)
            ·
              refine ⟨52550863631783420966965381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70067818175711227955953841 52550863631783420966965381)
              ·
                refine ⟨9853286930959391431306009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52550863631783420966965381 9853286930959391431306009)
                ·
                  refine ⟨7389965198219543573479507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9853286930959391431306009 7389965198219543573479507)
                  ·
                    refine ⟨11084947797329315360219261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7389965198219543573479507 11084947797329315360219261)
                    ·
                      refine ⟨4156855423998493260082223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11084947797329315360219261 4156855423998493260082223)
                      ·
                        rfl

theorem cell23_8095447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_8095447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095447 prefixEnd_8095447 := by exact prefixLift 8095447
  have htrace : WordTrace (prefixWord ++ tailWord_8095447) baseStart_8095447 baseEnd_8095447 := by
    simpa [prefixWord, tailWord_8095447, baseEnd_8095447] using wordTrace_append hprefix tailTrace_8095447
  have hstable : (prefixWord ++ tailWord_8095447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095447).length < 2 ^ (prefixWord ++ tailWord_8095447).sum := by decide
  have hdescent : baseEnd_8095447 < baseStart_8095447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095464 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_8095464 : Nat := 118140960795 + 8095464 * 2 ^ 59
def prefixEnd_8095464 : Nat := 4983230072969 + 3 ^ 40 * 8095464 * 2
def baseEnd_8095464 : Nat := 4156864153169619693569645

theorem tailTrace_8095464 : CollatzResearch.WordTrace tailWord_8095464 prefixEnd_8095464 4156864153169619693569645 := by
  unfold tailWord_8095464
  simp only [CollatzResearch.WordTrace]
  refine ⟨147632914571761999011142723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196843886095682665348190297 147632914571761999011142723)
  ·
    refine ⟨221449371857642998516714085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147632914571761999011142723 221449371857642998516714085)
    ·
      refine ⟨41521757223308062221883891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221449371857642998516714085 41521757223308062221883891)
      ·
        refine ⟨62282635834962093332825837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41521757223308062221883891 62282635834962093332825837)
        ·
          refine ⟨23355988438110784999809689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62282635834962093332825837 23355988438110784999809689)
          ·
            refine ⟨17516991328583088749857267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23355988438110784999809689 17516991328583088749857267)
            ·
              refine ⟨26275486992874633124785901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17516991328583088749857267 26275486992874633124785901)
              ·
                refine ⟨9853307622327987421794713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26275486992874633124785901 9853307622327987421794713)
                ·
                  refine ⟨7389980716745990566346035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9853307622327987421794713 7389980716745990566346035)
                  ·
                    refine ⟨11084971075118985849519053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7389980716745990566346035 11084971075118985849519053)
                    ·
                      refine ⟨4156864153169619693569645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11084971075118985849519053 4156864153169619693569645)
                      ·
                        rfl

theorem cell23_8095464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_8095464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095464 prefixEnd_8095464 := by exact prefixLift 8095464
  have htrace : WordTrace (prefixWord ++ tailWord_8095464) baseStart_8095464 baseEnd_8095464 := by
    simpa [prefixWord, tailWord_8095464, baseEnd_8095464] using wordTrace_append hprefix tailTrace_8095464
  have hstable : (prefixWord ++ tailWord_8095464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095464).length < 2 ^ (prefixWord ++ tailWord_8095464).sum := by decide
  have hdescent : baseEnd_8095464 < baseStart_8095464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095483 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 4]
def baseStart_8095483 : Nat := 118140960795 + 8095483 * 2 ^ 59
def prefixEnd_8095483 : Nat := 4983230072969 + 3 ^ 40 * 8095483 * 2
def baseEnd_8095483 : Nat := 4156873909302055119232057

theorem tailTrace_8095483 : CollatzResearch.WordTrace tailWord_8095483 prefixEnd_8095483 4156873909302055119232057 := by
  unfold tailWord_8095483
  simp only [CollatzResearch.WordTrace]
  refine ⟨295266522130455164267227103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196844348086970109511484735 295266522130455164267227103)
  ·
    refine ⟨442899783195682746400840655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295266522130455164267227103 442899783195682746400840655)
    ·
      refine ⟨664349674793524119601260983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442899783195682746400840655 664349674793524119601260983)
      ·
        refine ⟨996524512190286179401891475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664349674793524119601260983 996524512190286179401891475)
        ·
          refine ⟨1494786768285429269102837213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996524512190286179401891475 1494786768285429269102837213)
          ·
            refine ⟨560545038107035975913563955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1494786768285429269102837213 560545038107035975913563955)
            ·
              refine ⟨840817557160553963870345933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560545038107035975913563955 840817557160553963870345933)
              ·
                refine ⟨315306583935207736451379725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 840817557160553963870345933 315306583935207736451379725)
                ·
                  refine ⟨118239968975702901169267397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 315306583935207736451379725 118239968975702901169267397)
                  ·
                    refine ⟨22169994182944293969237637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118239968975702901169267397 22169994182944293969237637)
                    ·
                      refine ⟨4156873909302055119232057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22169994182944293969237637 4156873909302055119232057)
                      ·
                        rfl

theorem cell23_8095483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 4].length) (baseStart_8095483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095483 prefixEnd_8095483 := by exact prefixLift 8095483
  have htrace : WordTrace (prefixWord ++ tailWord_8095483) baseStart_8095483 baseEnd_8095483 := by
    simpa [prefixWord, tailWord_8095483, baseEnd_8095483] using wordTrace_append hprefix tailTrace_8095483
  have hstable : (prefixWord ++ tailWord_8095483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095483).length < 2 ^ (prefixWord ++ tailWord_8095483).sum := by decide
  have hdescent : baseEnd_8095483 < baseStart_8095483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095487 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 6, 2, 2]
def baseStart_8095487 : Nat := 118140960795 + 8095487 * 2 ^ 59
def prefixEnd_8095487 : Nat := 4983230072969 + 3 ^ 40 * 8095487 * 2
def baseEnd_8095487 : Nat := 4156875963224673103582039

theorem tailTrace_8095487 : CollatzResearch.WordTrace tailWord_8095487 prefixEnd_8095487 4156875963224673103582039 := by
  unfold tailWord_8095487
  simp only [CollatzResearch.WordTrace]
  refine ⟨295266668022440672950372715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196844445348293781966915143 295266668022440672950372715)
  ·
    refine ⟨442900002033661009425559073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295266668022440672950372715 442900002033661009425559073)
    ·
      refine ⟨332175001525245757069169305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442900002033661009425559073 332175001525245757069169305)
      ·
        refine ⟨249131251143934317801876979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332175001525245757069169305 249131251143934317801876979)
        ·
          refine ⟨373696876715901476702815469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249131251143934317801876979 373696876715901476702815469)
          ·
            refine ⟨140136328768463053763555801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373696876715901476702815469 140136328768463053763555801)
            ·
              refine ⟨105102246576347290322666851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140136328768463053763555801 105102246576347290322666851)
              ·
                refine ⟨157653369864520935484000277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105102246576347290322666851 157653369864520935484000277)
                ·
                  refine ⟨7390001712399418850812513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157653369864520935484000277 7390001712399418850812513)
                  ·
                    refine ⟨5542501284299564138109385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7390001712399418850812513 5542501284299564138109385)
                    ·
                      refine ⟨4156875963224673103582039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542501284299564138109385 4156875963224673103582039)
                      ·
                        rfl

theorem cell23_8095487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_8095487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095487 prefixEnd_8095487 := by exact prefixLift 8095487
  have htrace : WordTrace (prefixWord ++ tailWord_8095487) baseStart_8095487 baseEnd_8095487 := by
    simpa [prefixWord, tailWord_8095487, baseEnd_8095487] using wordTrace_append hprefix tailTrace_8095487
  have hstable : (prefixWord ++ tailWord_8095487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095487).length < 2 ^ (prefixWord ++ tailWord_8095487).sum := by decide
  have hdescent : baseEnd_8095487 < baseStart_8095487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095577 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 2, 4, 2]
def baseStart_8095577 : Nat := 118140960795 + 8095577 * 2 ^ 59
def prefixEnd_8095577 : Nat := 4983230072969 + 3 ^ 40 * 8095577 * 2
def baseEnd_8095577 : Nat := 4156922176483577751456625

theorem tailTrace_8095577 : CollatzResearch.WordTrace tailWord_8095577 prefixEnd_8095577 4156922176483577751456625 := by
  unfold tailWord_8095577
  simp only [CollatzResearch.WordTrace]
  refine ⟨295269950592114618321148985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196846633728076412214099323 295269950592114618321148985)
  ·
    refine ⟨221452462944085963740861739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295269950592114618321148985 221452462944085963740861739)
    ·
      refine ⟨332178694416128945611292609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221452462944085963740861739 332178694416128945611292609)
      ·
        refine ⟨249134020812096709208469457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332178694416128945611292609 249134020812096709208469457)
        ·
          refine ⟨186850515609072531906352093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249134020812096709208469457 186850515609072531906352093)
          ·
            refine ⟨70068943353402199464882035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186850515609072531906352093 70068943353402199464882035)
            ·
              refine ⟨105103415030103299197323053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70068943353402199464882035 105103415030103299197323053)
              ·
                refine ⟨39413780636288737198996145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105103415030103299197323053 39413780636288737198996145)
                ·
                  refine ⟨29560335477216552899247109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39413780636288737198996145 29560335477216552899247109)
                  ·
                    refine ⟨5542562901978103668608833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29560335477216552899247109 5542562901978103668608833)
                    ·
                      refine ⟨4156922176483577751456625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542562901978103668608833 4156922176483577751456625)
                      ·
                        rfl

theorem cell23_8095577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_8095577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095577 prefixEnd_8095577 := by exact prefixLift 8095577
  have htrace : WordTrace (prefixWord ++ tailWord_8095577) baseStart_8095577 baseEnd_8095577 := by
    simpa [prefixWord, tailWord_8095577, baseEnd_8095577] using wordTrace_append hprefix tailTrace_8095577
  have hstable : (prefixWord ++ tailWord_8095577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095577).length < 2 ^ (prefixWord ++ tailWord_8095577).sum := by decide
  have hdescent : baseEnd_8095577 < baseStart_8095577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095597 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_8095597 : Nat := 118140960795 + 8095597 * 2 ^ 59
def prefixEnd_8095597 : Nat := 4983230072969 + 3 ^ 40 * 8095597 * 2
def baseEnd_8095597 : Nat := 4156932446096667673206533

theorem tailTrace_8095597 : CollatzResearch.WordTrace tailWord_8095597 prefixEnd_8095597 4156932446096667673206533 := by
  unfold tailWord_8095597
  simp only [CollatzResearch.WordTrace]
  refine ⟨295270680052042161736877045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196847120034694774491251363 295270680052042161736877045)
  ·
    refine ⟨27681626254878952662832223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295270680052042161736877045 27681626254878952662832223)
    ·
      refine ⟨41522439382318428994248335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27681626254878952662832223 41522439382318428994248335)
      ·
        refine ⟨62283659073477643491372503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41522439382318428994248335 62283659073477643491372503)
        ·
          refine ⟨93425488610216465237058755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62283659073477643491372503 93425488610216465237058755)
          ·
            refine ⟨140138232915324697855588133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93425488610216465237058755 140138232915324697855588133)
            ·
              refine ⟨26275918671623380847922775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140138232915324697855588133 26275918671623380847922775)
              ·
                refine ⟨39413878007435071271884163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26275918671623380847922775 39413878007435071271884163)
                ·
                  refine ⟨59120817011152606907826245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39413878007435071271884163 59120817011152606907826245)
                  ·
                    refine ⟨11085153189591113795217421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59120817011152606907826245 11085153189591113795217421)
                    ·
                      refine ⟨4156932446096667673206533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11085153189591113795217421 4156932446096667673206533)
                      ·
                        rfl

theorem cell23_8095597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_8095597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095597 prefixEnd_8095597 := by exact prefixLift 8095597
  have htrace : WordTrace (prefixWord ++ tailWord_8095597) baseStart_8095597 baseEnd_8095597 := by
    simpa [prefixWord, tailWord_8095597, baseEnd_8095597] using wordTrace_append hprefix tailTrace_8095597
  have hstable : (prefixWord ++ tailWord_8095597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095597).length < 2 ^ (prefixWord ++ tailWord_8095597).sum := by decide
  have hdescent : baseEnd_8095597 < baseStart_8095597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095620 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_8095620 : Nat := 118140960795 + 8095620 * 2 ^ 59
def prefixEnd_8095620 : Nat := 4983230072969 + 3 ^ 40 * 8095620 * 2
def baseEnd_8095620 : Nat := 4156944256151721083218927

theorem tailTrace_8095620 : CollatzResearch.WordTrace tailWord_8095620 prefixEnd_8095620 4156944256151721083218927 := by
  unfold tailWord_8095620
  simp only [CollatzResearch.WordTrace]
  refine ⟨147635759465479418332482157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196847679287305891109976209 147635759465479418332482157)
  ·
    refine ⟨55363409799554781874680809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147635759465479418332482157 55363409799554781874680809)
    ·
      refine ⟨41522557349666086406010607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55363409799554781874680809 41522557349666086406010607)
      ·
        refine ⟨62283836024499129609015911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41522557349666086406010607 62283836024499129609015911)
        ·
          refine ⟨93425754036748694413523867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62283836024499129609015911 93425754036748694413523867)
          ·
            refine ⟨140138631055123041620285801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93425754036748694413523867 140138631055123041620285801)
            ·
              refine ⟨105103973291342281215214351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140138631055123041620285801 105103973291342281215214351)
              ·
                refine ⟨157655959937013421822821527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105103973291342281215214351 157655959937013421822821527)
                ·
                  refine ⟨236483939905520132734232291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157655959937013421822821527 236483939905520132734232291)
                  ·
                    refine ⟨354725909858280199101348437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 236483939905520132734232291 354725909858280199101348437)
                    ·
                      refine ⟨4156944256151721083218927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 354725909858280199101348437 4156944256151721083218927)
                      ·
                        rfl

theorem cell23_8095620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_8095620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095620 prefixEnd_8095620 := by exact prefixLift 8095620
  have htrace : WordTrace (prefixWord ++ tailWord_8095620) baseStart_8095620 baseEnd_8095620 := by
    simpa [prefixWord, tailWord_8095620, baseEnd_8095620] using wordTrace_append hprefix tailTrace_8095620
  have hstable : (prefixWord ++ tailWord_8095620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095620).length < 2 ^ (prefixWord ++ tailWord_8095620).sum := by decide
  have hdescent : baseEnd_8095620 < baseStart_8095620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095621 : List Nat := [1, 3, 1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_8095621 : Nat := 118140960795 + 8095621 * 2 ^ 59
def prefixEnd_8095621 : Nat := 4983230072969 + 3 ^ 40 * 8095621 * 2
def baseEnd_8095621 : Nat := 1385648256544125193102141

theorem tailTrace_8095621 : CollatzResearch.WordTrace tailWord_8095621 prefixEnd_8095621 1385648256544125193102141 := by
  unfold tailWord_8095621
  simp only [CollatzResearch.WordTrace]
  refine ⟨295271555403955213835750717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196847703602636809223833811 295271555403955213835750717)
  ·
    refine ⟨110726833276483205188406519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295271555403955213835750717 110726833276483205188406519)
    ·
      refine ⟨166090249914724807782609779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110726833276483205188406519 166090249914724807782609779)
      ·
        refine ⟨249135374872087211673914669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166090249914724807782609779 249135374872087211673914669)
        ·
          refine ⟨93425765577032704377718001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249135374872087211673914669 93425765577032704377718001)
          ·
            refine ⟨70069324182774528283288501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93425765577032704377718001 70069324182774528283288501)
            ·
              refine ⟨6568999142135112026558297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70069324182774528283288501 6568999142135112026558297)
              ·
                refine ⟨4926749356601334019918723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6568999142135112026558297 4926749356601334019918723)
                ·
                  refine ⟨7390124034902001029878085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926749356601334019918723 7390124034902001029878085)
                  ·
                    refine ⟨1385648256544125193102141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7390124034902001029878085 1385648256544125193102141)
                    ·
                      rfl

theorem cell23_8095621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_8095621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095621 prefixEnd_8095621 := by exact prefixLift 8095621
  have htrace : WordTrace (prefixWord ++ tailWord_8095621) baseStart_8095621 baseEnd_8095621 := by
    simpa [prefixWord, tailWord_8095621, baseEnd_8095621] using wordTrace_append hprefix tailTrace_8095621
  have hstable : (prefixWord ++ tailWord_8095621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095621).length < 2 ^ (prefixWord ++ tailWord_8095621).sum := by decide
  have hdescent : baseEnd_8095621 < baseStart_8095621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095634 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 6]
def baseStart_8095634 : Nat := 118140960795 + 8095634 * 2 ^ 59
def prefixEnd_8095634 : Nat := 4983230072969 + 3 ^ 40 * 8095634 * 2
def baseEnd_8095634 : Nat := 461883493875653780938207

theorem tailTrace_8095634 : CollatzResearch.WordTrace tailWord_8095634 prefixEnd_8095634 461883493875653780938207 := by
  unfold tailWord_8095634
  simp only [CollatzResearch.WordTrace]
  refine ⟨73818007388227029263993489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196848019701938744703982637 73818007388227029263993489)
  ·
    refine ⟨55363505541170271947995117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73818007388227029263993489 55363505541170271947995117)
    ·
      refine ⟨20761314577938851980498169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55363505541170271947995117 20761314577938851980498169)
      ·
        refine ⟨15570985933454138985373627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20761314577938851980498169 15570985933454138985373627)
        ·
          refine ⟨23356478900181208478060441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15570985933454138985373627 23356478900181208478060441)
          ·
            refine ⟨17517359175135906358545331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23356478900181208478060441 17517359175135906358545331)
            ·
              refine ⟨26276038762703859537817997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17517359175135906358545331 26276038762703859537817997)
              ·
                refine ⟨9853514536013947326681749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26276038762703859537817997 9853514536013947326681749)
                ·
                  refine ⟨461883493875653780938207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9853514536013947326681749 461883493875653780938207)
                  ·
                    rfl

theorem cell23_8095634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_8095634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095634 prefixEnd_8095634 := by exact prefixLift 8095634
  have htrace : WordTrace (prefixWord ++ tailWord_8095634) baseStart_8095634 baseEnd_8095634 := by
    simpa [prefixWord, tailWord_8095634, baseEnd_8095634] using wordTrace_append hprefix tailTrace_8095634
  have hstable : (prefixWord ++ tailWord_8095634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095634).length < 2 ^ (prefixWord ++ tailWord_8095634).sum := by decide
  have hdescent : baseEnd_8095634 < baseStart_8095634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095678 : List Nat := [4, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_8095678 : Nat := 118140960795 + 8095678 * 2 ^ 59
def prefixEnd_8095678 : Nat := 4983230072969 + 3 ^ 40 * 8095678 * 2
def baseEnd_8095678 : Nat := 4156974038029681856293661

theorem tailTrace_8095678 : CollatzResearch.WordTrace tailWord_8095678 prefixEnd_8095678 4156974038029681856293661 := by
  unfold tailWord_8095678
  simp only [CollatzResearch.WordTrace]
  refine ⟨36909204295593589071321961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196849089576499141713717125 36909204295593589071321961)
  ·
    refine ⟨27681903221695191803491471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36909204295593589071321961 27681903221695191803491471)
    ·
      refine ⟨41522854832542787705237207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27681903221695191803491471 41522854832542787705237207)
      ·
        refine ⟨62284282248814181557855811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41522854832542787705237207 62284282248814181557855811)
        ·
          refine ⟨93426423373221272336783717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62284282248814181557855811 93426423373221272336783717)
          ·
            refine ⟨17517454382478988563146947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93426423373221272336783717 17517454382478988563146947)
            ·
              refine ⟨26276181573718482844720421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17517454382478988563146947 26276181573718482844720421)
              ·
                refine ⟨4926784045072215533385079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26276181573718482844720421 4926784045072215533385079)
                ·
                  refine ⟨7390176067608323300077619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926784045072215533385079 7390176067608323300077619)
                  ·
                    refine ⟨11085264101412484950116429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7390176067608323300077619 11085264101412484950116429)
                    ·
                      refine ⟨4156974038029681856293661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11085264101412484950116429 4156974038029681856293661)
                      ·
                        rfl

theorem cell23_8095678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_8095678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095678 prefixEnd_8095678 := by exact prefixLift 8095678
  have htrace : WordTrace (prefixWord ++ tailWord_8095678) baseStart_8095678 baseEnd_8095678 := by
    simpa [prefixWord, tailWord_8095678, baseEnd_8095678] using wordTrace_append hprefix tailTrace_8095678
  have hstable : (prefixWord ++ tailWord_8095678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095678).length < 2 ^ (prefixWord ++ tailWord_8095678).sum := by decide
  have hdescent : baseEnd_8095678 < baseStart_8095678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095694 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_8095694 : Nat := 118140960795 + 8095694 * 2 ^ 59
def prefixEnd_8095694 : Nat := 4983230072969 + 3 ^ 40 * 8095694 * 2
def baseEnd_8095694 : Nat := 1385660751240051264564529

theorem tailTrace_8095694 : CollatzResearch.WordTrace tailWord_8095694 prefixEnd_8095694 1385660751240051264564529 := by
  unfold tailWord_8095694
  simp only [CollatzResearch.WordTrace]
  refine ⟨36909277241586343412894767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196849478621793831535438757 36909277241586343412894767)
  ·
    refine ⟨55363915862379515119342151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36909277241586343412894767 55363915862379515119342151)
    ·
      refine ⟨83045873793569272679013227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55363915862379515119342151 83045873793569272679013227)
      ·
        refine ⟨124568810690353909018519841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83045873793569272679013227 124568810690353909018519841)
        ·
          refine ⟨93426608017765431763889881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124568810690353909018519841 93426608017765431763889881)
          ·
            refine ⟨70069956013324073822917411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93426608017765431763889881 70069956013324073822917411)
            ·
              refine ⟨105104934019986110734376117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70069956013324073822917411 105104934019986110734376117)
              ·
                refine ⟨9853587564373697881347761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105104934019986110734376117 9853587564373697881347761)
                ·
                  refine ⟨7390190673280273411010821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9853587564373697881347761 7390190673280273411010821)
                  ·
                    refine ⟨1385660751240051264564529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7390190673280273411010821 1385660751240051264564529)
                    ·
                      rfl

theorem cell23_8095694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_8095694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095694 prefixEnd_8095694 := by exact prefixLift 8095694
  have htrace : WordTrace (prefixWord ++ tailWord_8095694) baseStart_8095694 baseEnd_8095694 := by
    simpa [prefixWord, tailWord_8095694, baseEnd_8095694] using wordTrace_append hprefix tailTrace_8095694
  have hstable : (prefixWord ++ tailWord_8095694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095694).length < 2 ^ (prefixWord ++ tailWord_8095694).sum := by decide
  have hdescent : baseEnd_8095694 < baseStart_8095694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095701 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_8095701 : Nat := 118140960795 + 8095701 * 2 ^ 59
def prefixEnd_8095701 : Nat := 4983230072969 + 3 ^ 40 * 8095701 * 2
def baseEnd_8095701 : Nat := 4156985848084735266306055

theorem tailTrace_8095701 : CollatzResearch.WordTrace tailWord_8095701 prefixEnd_8095701 4156985848084735266306055 := by
  unfold tailWord_8095701
  simp only [CollatzResearch.WordTrace]
  refine ⟨295274473243665387498662957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196849648829110258332441971 295274473243665387498662957)
  ·
    refine ⟨110727927466374520311998609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295274473243665387498662957 110727927466374520311998609)
    ·
      refine ⟨83045945599780890233998957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110727927466374520311998609 83045945599780890233998957)
      ·
        refine ⟨31142229599917833837749609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83045945599780890233998957 31142229599917833837749609)
        ·
          refine ⟨23356672199938375378312207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31142229599917833837749609 23356672199938375378312207)
          ·
            refine ⟨35035008299907563067468311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23356672199938375378312207 35035008299907563067468311)
            ·
              refine ⟨52552512449861344601202467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35035008299907563067468311 52552512449861344601202467)
              ·
                refine ⟨78828768674792016901803701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52552512449861344601202467 78828768674792016901803701)
                ·
                  refine ⟨7390197063261751584544097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78828768674792016901803701 7390197063261751584544097)
                  ·
                    refine ⟨5542647797446313688408073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7390197063261751584544097 5542647797446313688408073)
                    ·
                      refine ⟨4156985848084735266306055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542647797446313688408073 4156985848084735266306055)
                      ·
                        rfl

theorem cell23_8095701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_8095701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095701 prefixEnd_8095701 := by exact prefixLift 8095701
  have htrace : WordTrace (prefixWord ++ tailWord_8095701) baseStart_8095701 baseEnd_8095701 := by
    simpa [prefixWord, tailWord_8095701, baseEnd_8095701] using wordTrace_append hprefix tailTrace_8095701
  have hstable : (prefixWord ++ tailWord_8095701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095701).length < 2 ^ (prefixWord ++ tailWord_8095701).sum := by decide
  have hdescent : baseEnd_8095701 < baseStart_8095701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095704 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 1, 2, 3]
def baseStart_8095704 : Nat := 118140960795 + 8095704 * 2 ^ 59
def prefixEnd_8095704 : Nat := 4983230072969 + 3 ^ 40 * 8095704 * 2
def baseEnd_8095704 : Nat := 4156987388526698754568541

theorem tailTrace_8095704 : CollatzResearch.WordTrace tailWord_8095704 prefixEnd_8095704 4156987388526698754568541 := by
  unfold tailWord_8095704
  simp only [CollatzResearch.WordTrace]
  refine ⟨147637291331327259505511083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196849721775103012674014777 147637291331327259505511083)
  ·
    refine ⟨221455936996990889258266625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147637291331327259505511083 221455936996990889258266625)
    ·
      refine ⟨166091952747743166943699969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221455936996990889258266625 166091952747743166943699969)
      ·
        refine ⟨124568964560807375207774977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166091952747743166943699969 124568964560807375207774977)
        ·
          refine ⟨93426723420605531405831233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124568964560807375207774977 93426723420605531405831233)
          ·
            refine ⟨70070042565454148554373425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93426723420605531405831233 70070042565454148554373425)
            ·
              refine ⟨52552531924090611415780069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70070042565454148554373425 52552531924090611415780069)
              ·
                refine ⟨9853599735766989640458763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52552531924090611415780069 9853599735766989640458763)
                ·
                  refine ⟨14780399603650484460688145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9853599735766989640458763 14780399603650484460688145)
                  ·
                    refine ⟨11085299702737863345516109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14780399603650484460688145 11085299702737863345516109)
                    ·
                      refine ⟨4156987388526698754568541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11085299702737863345516109 4156987388526698754568541)
                      ·
                        rfl

theorem cell23_8095704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_8095704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095704 prefixEnd_8095704 := by exact prefixLift 8095704
  have htrace : WordTrace (prefixWord ++ tailWord_8095704) baseStart_8095704 baseEnd_8095704 := by
    simpa [prefixWord, tailWord_8095704, baseEnd_8095704] using wordTrace_append hprefix tailTrace_8095704
  have hstable : (prefixWord ++ tailWord_8095704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095704).length < 2 ^ (prefixWord ++ tailWord_8095704).sum := by decide
  have hdescent : baseEnd_8095704 < baseStart_8095704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095744 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 3, 3, 2]
def baseStart_8095744 : Nat := 118140960795 + 8095744 * 2 ^ 59
def prefixEnd_8095744 : Nat := 4983230072969 + 3 ^ 40 * 8095744 * 2
def baseEnd_8095744 : Nat := 4157007927752878598068357

theorem tailTrace_8095744 : CollatzResearch.WordTrace tailWord_8095744 prefixEnd_8095744 4157007927752878598068357 := by
  unfold tailWord_8095744
  simp only [CollatzResearch.WordTrace]
  refine ⟨147638020791254802921239143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196850694388339737228318857 147638020791254802921239143)
  ·
    refine ⟨221457031186882204381858715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147638020791254802921239143 221457031186882204381858715)
    ·
      refine ⟨332185546780323306572788073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221457031186882204381858715 332185546780323306572788073)
      ·
        refine ⟨249139160085242479929591055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332185546780323306572788073 249139160085242479929591055)
        ·
          refine ⟨373708740127863719894386583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249139160085242479929591055 373708740127863719894386583)
          ·
            refine ⟨560563110191795579841579875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373708740127863719894386583 560563110191795579841579875)
            ·
              refine ⟨840844665287693369762369813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560563110191795579841579875 840844665287693369762369813)
              ·
                refine ⟨39414593685360626707611085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 840844665287693369762369813 39414593685360626707611085)
                ·
                  refine ⟨14780472632010235015354157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39414593685360626707611085 14780472632010235015354157)
                  ·
                    refine ⟨5542677237003838130757809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14780472632010235015354157 5542677237003838130757809)
                    ·
                      refine ⟨4157007927752878598068357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542677237003838130757809 4157007927752878598068357)
                      ·
                        rfl

theorem cell23_8095744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_8095744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095744 prefixEnd_8095744 := by exact prefixLift 8095744
  have htrace : WordTrace (prefixWord ++ tailWord_8095744) baseStart_8095744 baseEnd_8095744 := by
    simpa [prefixWord, tailWord_8095744, baseEnd_8095744] using wordTrace_append hprefix tailTrace_8095744
  have hstable : (prefixWord ++ tailWord_8095744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095744).length < 2 ^ (prefixWord ++ tailWord_8095744).sum := by decide
  have hdescent : baseEnd_8095744 < baseStart_8095744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095748 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_8095748 : Nat := 118140960795 + 8095748 * 2 ^ 59
def prefixEnd_8095748 : Nat := 4983230072969 + 3 ^ 40 * 8095748 * 2
def baseEnd_8095748 : Nat := 4157009981675496582418339

theorem tailTrace_8095748 : CollatzResearch.WordTrace tailWord_8095748 prefixEnd_8095748 4157009981675496582418339 := by
  unfold tailWord_8095748
  simp only [CollatzResearch.WordTrace]
  refine ⟨147638093737247557262811949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196850791649663409683749265 147638093737247557262811949)
  ·
    refine ⟨55364285151467833973554481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147638093737247557262811949 55364285151467833973554481)
    ·
      refine ⟨41523213863600875480165861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55364285151467833973554481 41523213863600875480165861)
      ·
        refine ⟨7785602599425164152531099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41523213863600875480165861 7785602599425164152531099)
        ·
          refine ⟨11678403899137746228796649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7785602599425164152531099 11678403899137746228796649)
          ·
            refine ⟨8758802924353309671597487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11678403899137746228796649 8758802924353309671597487)
            ·
              refine ⟨13138204386529964507396231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8758802924353309671597487 13138204386529964507396231)
              ·
                refine ⟨19707306579794946761094347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13138204386529964507396231 19707306579794946761094347)
                ·
                  refine ⟨29560959869692420141641521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19707306579794946761094347 29560959869692420141641521)
                  ·
                    refine ⟨22170719902269315106231141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29560959869692420141641521 22170719902269315106231141)
                    ·
                      refine ⟨4157009981675496582418339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22170719902269315106231141 4157009981675496582418339)
                      ·
                        rfl

theorem cell23_8095748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_8095748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095748 prefixEnd_8095748 := by exact prefixLift 8095748
  have htrace : WordTrace (prefixWord ++ tailWord_8095748) baseStart_8095748 baseEnd_8095748 := by
    simpa [prefixWord, tailWord_8095748, baseEnd_8095748] using wordTrace_append hprefix tailTrace_8095748
  have hstable : (prefixWord ++ tailWord_8095748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095748).length < 2 ^ (prefixWord ++ tailWord_8095748).sum := by decide
  have hdescent : baseEnd_8095748 < baseStart_8095748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095751 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_8095751 : Nat := 118140960795 + 8095751 * 2 ^ 59
def prefixEnd_8095751 : Nat := 4983230072969 + 3 ^ 40 * 8095751 * 2
def baseEnd_8095751 : Nat := 4157011522117460070680825

theorem tailTrace_8095751 : CollatzResearch.WordTrace tailWord_8095751 prefixEnd_8095751 4157011522117460070680825 := by
  unfold tailWord_8095751
  simp only [CollatzResearch.WordTrace]
  refine ⟨295276296893484246037983107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196850864595656164025322071 295276296893484246037983107)
  ·
    refine ⟨442914445340226369056974661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295276296893484246037983107 442914445340226369056974661)
    ·
      refine ⟨83046458501292444198182749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442914445340226369056974661 83046458501292444198182749)
      ·
        refine ⟨31142421937984666574318531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83046458501292444198182749 31142421937984666574318531)
        ·
          refine ⟨46713632906976999861477797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31142421937984666574318531 46713632906976999861477797)
          ·
            refine ⟨8758806170058187474027087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46713632906976999861477797 8758806170058187474027087)
            ·
              refine ⟨13138209255087281211040631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8758806170058187474027087 13138209255087281211040631)
              ·
                refine ⟨19707313882630921816560947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13138209255087281211040631 19707313882630921816560947)
                ·
                  refine ⟨29560970823946382724841421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19707313882630921816560947 29560970823946382724841421)
                  ·
                    refine ⟨11085364058979893521815533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29560970823946382724841421 11085364058979893521815533)
                    ·
                      refine ⟨4157011522117460070680825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11085364058979893521815533 4157011522117460070680825)
                      ·
                        rfl

theorem cell23_8095751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_8095751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095751 prefixEnd_8095751 := by exact prefixLift 8095751
  have htrace : WordTrace (prefixWord ++ tailWord_8095751) baseStart_8095751 baseEnd_8095751 := by
    simpa [prefixWord, tailWord_8095751, baseEnd_8095751] using wordTrace_append hprefix tailTrace_8095751
  have hstable : (prefixWord ++ tailWord_8095751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095751).length < 2 ^ (prefixWord ++ tailWord_8095751).sum := by decide
  have hdescent : baseEnd_8095751 < baseStart_8095751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095787 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 4]
def baseStart_8095787 : Nat := 118140960795 + 8095787 * 2 ^ 59
def prefixEnd_8095787 : Nat := 4983230072969 + 3 ^ 40 * 8095787 * 2
def baseEnd_8095787 : Nat := 4157030007421021929830659

theorem tailTrace_8095787 : CollatzResearch.WordTrace tailWord_8095787 prefixEnd_8095787 4157030007421021929830659 := by
  unfold tailWord_8095787
  simp only [CollatzResearch.WordTrace]
  refine ⟨295277609921353824186293615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196851739947569216124195743 295277609921353824186293615)
  ·
    refine ⟨442916414882030736279440423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295277609921353824186293615 442916414882030736279440423)
    ·
      refine ⟨664374622323046104419160635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442916414882030736279440423 664374622323046104419160635)
      ·
        refine ⟨996561933484569156628740953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664374622323046104419160635 996561933484569156628740953)
        ·
          refine ⟨747421450113426867471555715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996561933484569156628740953 747421450113426867471555715)
          ·
            refine ⟨1121132175170140301207333573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747421450113426867471555715 1121132175170140301207333573)
            ·
              refine ⟨210212282844401306476375045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1121132175170140301207333573 210212282844401306476375045)
              ·
                refine ⟨39414803033325244964320321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210212282844401306476375045 39414803033325244964320321)
                ·
                  refine ⟨29561102274993933723240241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39414803033325244964320321 29561102274993933723240241)
                  ·
                    refine ⟨22170826706245450292430181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29561102274993933723240241 22170826706245450292430181)
                    ·
                      refine ⟨4157030007421021929830659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22170826706245450292430181 4157030007421021929830659)
                      ·
                        rfl

theorem cell23_8095787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 4].length) (baseStart_8095787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095787 prefixEnd_8095787 := by exact prefixLift 8095787
  have htrace : WordTrace (prefixWord ++ tailWord_8095787) baseStart_8095787 baseEnd_8095787 := by
    simpa [prefixWord, tailWord_8095787, baseEnd_8095787] using wordTrace_append hprefix tailTrace_8095787
  have hstable : (prefixWord ++ tailWord_8095787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095787).length < 2 ^ (prefixWord ++ tailWord_8095787).sum := by decide
  have hdescent : baseEnd_8095787 < baseStart_8095787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095808 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 2, 2, 2]
def baseStart_8095808 : Nat := 118140960795 + 8095808 * 2 ^ 59
def prefixEnd_8095808 : Nat := 4983230072969 + 3 ^ 40 * 8095808 * 2
def baseEnd_8095808 : Nat := 4157040790514766347668063

theorem tailTrace_8095808 : CollatzResearch.WordTrace tailWord_8095808 prefixEnd_8095808 4157040790514766347668063 := by
  unfold tailWord_8095808
  simp only [CollatzResearch.WordTrace]
  refine ⟨147639187927138872386404039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196852250569518496515205385 147639187927138872386404039)
  ·
    refine ⟨221458781890708308579606059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147639187927138872386404039 221458781890708308579606059)
    ·
      refine ⟨332188172836062462869409089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221458781890708308579606059 332188172836062462869409089)
      ·
        refine ⟨249141129627046847152056817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332188172836062462869409089 249141129627046847152056817)
        ·
          refine ⟨186855847220285135364042613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249141129627046847152056817 186855847220285135364042613)
          ·
            refine ⟨17517735676901731440378995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186855847220285135364042613 17517735676901731440378995)
            ·
              refine ⟨26276603515352597160568493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17517735676901731440378995 26276603515352597160568493)
              ·
                refine ⟨9853726318257223935213185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26276603515352597160568493 9853726318257223935213185)
                ·
                  refine ⟨7390294738692917951409889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9853726318257223935213185 7390294738692917951409889)
                  ·
                    refine ⟨5542721054019688463557417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7390294738692917951409889 5542721054019688463557417)
                    ·
                      refine ⟨4157040790514766347668063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542721054019688463557417 4157040790514766347668063)
                      ·
                        rfl

theorem cell23_8095808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_8095808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095808 prefixEnd_8095808 := by exact prefixLift 8095808
  have htrace : WordTrace (prefixWord ++ tailWord_8095808) baseStart_8095808 baseEnd_8095808 := by
    simpa [prefixWord, tailWord_8095808, baseEnd_8095808] using wordTrace_append hprefix tailTrace_8095808
  have hstable : (prefixWord ++ tailWord_8095808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095808).length < 2 ^ (prefixWord ++ tailWord_8095808).sum := by decide
  have hdescent : baseEnd_8095808 < baseStart_8095808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095842 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_8095842 : Nat := 118140960795 + 8095842 * 2 ^ 59
def prefixEnd_8095842 : Nat := 4983230072969 + 3 ^ 40 * 8095842 * 2
def baseEnd_8095842 : Nat := 4157058248857019214642907

theorem tailTrace_8095842 : CollatzResearch.WordTrace tailWord_8095842 prefixEnd_8095842 4157058248857019214642907 := by
  unfold tailWord_8095842
  simp only [CollatzResearch.WordTrace]
  refine ⟨73819903984038642144886445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196853077290769712386363853 73819903984038642144886445)
  ·
    refine ⟨27682463994014490804332417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73819903984038642144886445 27682463994014490804332417)
    ·
      refine ⟨20761847995510868103249313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27682463994014490804332417 20761847995510868103249313)
      ·
        refine ⟨15571385996633151077436985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20761847995510868103249313 15571385996633151077436985)
        ·
          refine ⟨11678539497474863308077739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15571385996633151077436985 11678539497474863308077739)
          ·
            refine ⟨17517809246212294962116609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11678539497474863308077739 17517809246212294962116609)
            ·
              refine ⟨13138356934659221221587457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17517809246212294962116609 13138356934659221221587457)
              ·
                refine ⟨9853767700994415916190593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13138356934659221221587457 9853767700994415916190593)
                ·
                  refine ⟨7390325775745811937142945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9853767700994415916190593 7390325775745811937142945)
                  ·
                    refine ⟨5542744331809358952857209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7390325775745811937142945 5542744331809358952857209)
                    ·
                      refine ⟨4157058248857019214642907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542744331809358952857209 4157058248857019214642907)
                      ·
                        rfl

theorem cell23_8095842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_8095842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095842 prefixEnd_8095842 := by exact prefixLift 8095842
  have htrace : WordTrace (prefixWord ++ tailWord_8095842) baseStart_8095842 baseEnd_8095842 := by
    simpa [prefixWord, tailWord_8095842, baseEnd_8095842] using wordTrace_append hprefix tailTrace_8095842
  have hstable : (prefixWord ++ tailWord_8095842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095842).length < 2 ^ (prefixWord ++ tailWord_8095842).sum := by decide
  have hdescent : baseEnd_8095842 < baseStart_8095842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095844 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_8095844 : Nat := 118140960795 + 8095844 * 2 ^ 59
def prefixEnd_8095844 : Nat := 4983230072969 + 3 ^ 40 * 8095844 * 2
def baseEnd_8095844 : Nat := 1385686425272776068939299

theorem tailTrace_8095844 : CollatzResearch.WordTrace tailWord_8095844 prefixEnd_8095844 1385686425272776068939299 := by
  unfold tailWord_8095844
  simp only [CollatzResearch.WordTrace]
  refine ⟨147639844441073661460559293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196853125921431548614079057 147639844441073661460559293)
  ·
    refine ⟨55364941665402623047709735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147639844441073661460559293 55364941665402623047709735)
    ·
      refine ⟨83047412498103934571564603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55364941665402623047709735 83047412498103934571564603)
      ·
        refine ⟨124571118747155901857346905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83047412498103934571564603 124571118747155901857346905)
        ·
          refine ⟨93428339060366926393010179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124571118747155901857346905 93428339060366926393010179)
          ·
            refine ⟨140142508590550389589515269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93428339060366926393010179 140142508590550389589515269)
            ·
              refine ⟨26276720360728198048034113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140142508590550389589515269 26276720360728198048034113)
              ·
                refine ⟨19707540270546148536025585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26276720360728198048034113 19707540270546148536025585)
                ·
                  refine ⟨14780655202909611402019189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19707540270546148536025585 14780655202909611402019189)
                  ·
                    refine ⟨1385686425272776068939299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14780655202909611402019189 1385686425272776068939299)
                    ·
                      rfl

theorem cell23_8095844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_8095844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095844 prefixEnd_8095844 := by exact prefixLift 8095844
  have htrace : WordTrace (prefixWord ++ tailWord_8095844) baseStart_8095844 baseEnd_8095844 := by
    simpa [prefixWord, tailWord_8095844, baseEnd_8095844] using wordTrace_append hprefix tailTrace_8095844
  have hstable : (prefixWord ++ tailWord_8095844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095844).length < 2 ^ (prefixWord ++ tailWord_8095844).sum := by decide
  have hdescent : baseEnd_8095844 < baseStart_8095844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095854 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_8095854 : Nat := 118140960795 + 8095854 * 2 ^ 59
def prefixEnd_8095854 : Nat := 4983230072969 + 3 ^ 40 * 8095854 * 2
def baseEnd_8095854 : Nat := 4157064410624873167692851

theorem tailTrace_8095854 : CollatzResearch.WordTrace tailWord_8095854 prefixEnd_8095854 4157064410624873167692851 := by
  unfold tailWord_8095854
  simp only [CollatzResearch.WordTrace]
  refine ⟨36910006701513886828622827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196853369074740729752655077 36910006701513886828622827)
  ·
    refine ⟨55365010052270830242934241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36910006701513886828622827 55365010052270830242934241)
    ·
      refine ⟨41523757539203122682200681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55365010052270830242934241 41523757539203122682200681)
      ·
        refine ⟨31142818154402342011650511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41523757539203122682200681 31142818154402342011650511)
        ·
          refine ⟨46714227231603513017475767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31142818154402342011650511 46714227231603513017475767)
          ·
            refine ⟨70071340847405269526213651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46714227231603513017475767 70071340847405269526213651)
            ·
              refine ⟨105107011271107904289320477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70071340847405269526213651 105107011271107904289320477)
              ·
                refine ⟨39415129226665464108495179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105107011271107904289320477 39415129226665464108495179)
                ·
                  refine ⟨59122693839998196162742769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39415129226665464108495179 59122693839998196162742769)
                  ·
                    refine ⟨44342020379998647122057077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59122693839998196162742769 44342020379998647122057077)
                    ·
                      refine ⟨4157064410624873167692851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44342020379998647122057077 4157064410624873167692851)
                      ·
                        rfl

theorem cell23_8095854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_8095854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095854 prefixEnd_8095854 := by exact prefixLift 8095854
  have htrace : WordTrace (prefixWord ++ tailWord_8095854) baseStart_8095854 baseEnd_8095854 := by
    simpa [prefixWord, tailWord_8095854, baseEnd_8095854] using wordTrace_append hprefix tailTrace_8095854
  have hstable : (prefixWord ++ tailWord_8095854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095854).length < 2 ^ (prefixWord ++ tailWord_8095854).sum := by decide
  have hdescent : baseEnd_8095854 < baseStart_8095854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095904 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 8]
def baseStart_8095904 : Nat := 118140960795 + 8095904 * 2 ^ 59
def prefixEnd_8095904 : Nat := 4983230072969 + 3 ^ 40 * 8095904 * 2
def baseEnd_8095904 : Nat := 461898898295288663563069

theorem tailTrace_8095904 : CollatzResearch.WordTrace tailWord_8095904 prefixEnd_8095904 461898898295288663563069 := by
  unfold tailWord_8095904
  simp only [CollatzResearch.WordTrace]
  refine ⟨147640938630964976584151383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196854584841286635445535177 147640938630964976584151383)
  ·
    refine ⟨221461407946447464876227075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147640938630964976584151383 221461407946447464876227075)
    ·
      refine ⟨332192111919671197314340613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221461407946447464876227075 332192111919671197314340613)
      ·
        refine ⟨62286020984938349496438865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332192111919671197314340613 62286020984938349496438865)
        ·
          refine ⟨46714515738703762122329149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62286020984938349496438865 46714515738703762122329149)
          ·
            refine ⟨17517943402013910795873431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46714515738703762122329149 17517943402013910795873431)
            ·
              refine ⟨26276915103020866193810147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17517943402013910795873431 26276915103020866193810147)
              ·
                refine ⟨39415372654531299290715221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26276915103020866193810147 39415372654531299290715221)
                ·
                  refine ⟨461898898295288663563069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39415372654531299290715221 461898898295288663563069)
                  ·
                    rfl

theorem cell23_8095904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 8].length) (baseStart_8095904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095904 prefixEnd_8095904 := by exact prefixLift 8095904
  have htrace : WordTrace (prefixWord ++ tailWord_8095904) baseStart_8095904 baseEnd_8095904 := by
    simpa [prefixWord, tailWord_8095904, baseEnd_8095904] using wordTrace_append hprefix tailTrace_8095904
  have hstable : (prefixWord ++ tailWord_8095904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095904).length < 2 ^ (prefixWord ++ tailWord_8095904).sum := by decide
  have hdescent : baseEnd_8095904 < baseStart_8095904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095908 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_8095908 : Nat := 118140960795 + 8095908 * 2 ^ 59
def prefixEnd_8095908 : Nat := 4983230072969 + 3 ^ 40 * 8095908 * 2
def baseEnd_8095908 : Nat := 1385697379526738652139201

theorem tailTrace_8095908 : CollatzResearch.WordTrace tailWord_8095908 prefixEnd_8095908 1385697379526738652139201 := by
  unfold tailWord_8095908
  simp only [CollatzResearch.WordTrace]
  refine ⟨147641011576957730925724189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196854682102610307900965585 147641011576957730925724189)
  ·
    refine ⟨55365379341359149097146571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147641011576957730925724189 55365379341359149097146571)
    ·
      refine ⟨83048069012038723645719857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55365379341359149097146571 83048069012038723645719857)
      ·
        refine ⟨62286051759029042734289893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83048069012038723645719857 62286051759029042734289893)
        ·
          refine ⟨11678634704817945512679355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62286051759029042734289893 11678634704817945512679355)
          ·
            refine ⟨17517952057226918269019033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11678634704817945512679355 17517952057226918269019033)
            ·
              refine ⟨13138464042920188701764275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17517952057226918269019033 13138464042920188701764275)
              ·
                refine ⟨19707696064380283052646413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13138464042920188701764275 19707696064380283052646413)
                ·
                  refine ⟨7390386024142606144742405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19707696064380283052646413 7390386024142606144742405)
                  ·
                    refine ⟨1385697379526738652139201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7390386024142606144742405 1385697379526738652139201)
                    ·
                      rfl

theorem cell23_8095908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_8095908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095908 prefixEnd_8095908 := by exact prefixLift 8095908
  have htrace : WordTrace (prefixWord ++ tailWord_8095908) baseStart_8095908 baseEnd_8095908 := by
    simpa [prefixWord, tailWord_8095908, baseEnd_8095908] using wordTrace_append hprefix tailTrace_8095908
  have hstable : (prefixWord ++ tailWord_8095908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095908).length < 2 ^ (prefixWord ++ tailWord_8095908).sum := by decide
  have hdescent : baseEnd_8095908 < baseStart_8095908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095931 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 3]
def baseStart_8095931 : Nat := 118140960795 + 8095931 * 2 ^ 59
def prefixEnd_8095931 : Nat := 4983230072969 + 3 ^ 40 * 8095931 * 2
def baseEnd_8095931 : Nat := 4157103948635269366429997

theorem tailTrace_8095931 : CollatzResearch.WordTrace tailWord_8095931 prefixEnd_8095931 4157103948635269366429997 := by
  unfold tailWord_8095931
  simp only [CollatzResearch.WordTrace]
  refine ⟨295282862032832136779535647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196855241355221424519690431 295282862032832136779535647)
  ·
    refine ⟨442924293049248205169303471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295282862032832136779535647 442924293049248205169303471)
    ·
      refine ⟨664386439573872307753955207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442924293049248205169303471 664386439573872307753955207)
      ·
        refine ⟨996579659360808461630932811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664386439573872307753955207 996579659360808461630932811)
        ·
          refine ⟨1494869489041212692446399217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996579659360808461630932811 1494869489041212692446399217)
          ·
            refine ⟨1121152116780909519334799413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1494869489041212692446399217 1121152116780909519334799413)
            ·
              refine ⟨105108010948210267437637445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1121152116780909519334799413 105108010948210267437637445)
              ·
                refine ⟨19707752052789425144557021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105108010948210267437637445 19707752052789425144557021)
                ·
                  refine ⟨7390407019796034429208883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19707752052789425144557021 7390407019796034429208883)
                  ·
                    refine ⟨11085610529694051643813325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7390407019796034429208883 11085610529694051643813325)
                    ·
                      refine ⟨4157103948635269366429997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11085610529694051643813325 4157103948635269366429997)
                      ·
                        rfl

theorem cell23_8095931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 3].length) (baseStart_8095931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095931 prefixEnd_8095931 := by exact prefixLift 8095931
  have htrace : WordTrace (prefixWord ++ tailWord_8095931) baseStart_8095931 baseEnd_8095931 := by
    simpa [prefixWord, tailWord_8095931, baseEnd_8095931] using wordTrace_append hprefix tailTrace_8095931
  have hstable : (prefixWord ++ tailWord_8095931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095931).length < 2 ^ (prefixWord ++ tailWord_8095931).sum := by decide
  have hdescent : baseEnd_8095931 < baseStart_8095931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095938 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 8]
def baseStart_8095938 : Nat := 118140960795 + 8095938 * 2 ^ 59
def prefixEnd_8095938 : Nat := 4983230072969 + 3 ^ 40 * 8095938 * 2
def baseEnd_8095938 : Nat := 461900838111094537671385

theorem tailTrace_8095938 : CollatzResearch.WordTrace tailWord_8095938 prefixEnd_8095938 461900838111094537671385 := by
  unfold tailWord_8095938
  simp only [CollatzResearch.WordTrace]
  refine ⟨73820779335951694243760117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196855411562537851316693645 73820779335951694243760117)
  ·
    refine ⟨6920698062745471335352511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73820779335951694243760117 6920698062745471335352511)
    ·
      refine ⟨10381047094118207003028767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6920698062745471335352511 10381047094118207003028767)
      ·
        refine ⟨15571570641177310504543151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10381047094118207003028767 15571570641177310504543151)
        ·
          refine ⟨23357355961765965756814727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15571570641177310504543151 23357355961765965756814727)
          ·
            refine ⟨35036033942648948635222091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23357355961765965756814727 35036033942648948635222091)
            ·
              refine ⟨52554050913973422952833137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35036033942648948635222091 52554050913973422952833137)
              ·
                refine ⟨39415538185480067214624853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52554050913973422952833137 39415538185480067214624853)
                ·
                  refine ⟨461900838111094537671385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39415538185480067214624853 461900838111094537671385)
                  ·
                    rfl

theorem cell23_8095938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_8095938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095938 prefixEnd_8095938 := by exact prefixLift 8095938
  have htrace : WordTrace (prefixWord ++ tailWord_8095938) baseStart_8095938 baseEnd_8095938 := by
    simpa [prefixWord, tailWord_8095938, baseEnd_8095938] using wordTrace_append hprefix tailTrace_8095938
  have hstable : (prefixWord ++ tailWord_8095938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095938).length < 2 ^ (prefixWord ++ tailWord_8095938).sum := by decide
  have hdescent : baseEnd_8095938 < baseStart_8095938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095941 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 1, 5, 2]
def baseStart_8095941 : Nat := 118140960795 + 8095941 * 2 ^ 59
def prefixEnd_8095941 : Nat := 4983230072969 + 3 ^ 40 * 8095941 * 2
def baseEnd_8095941 : Nat := 4157109083441814327304951

theorem tailTrace_8095941 : CollatzResearch.WordTrace tailWord_8095941 prefixEnd_8095941 4157109083441814327304951 := by
  unfold tailWord_8095941
  simp only [CollatzResearch.WordTrace]
  refine ⟨295283226762795908487399677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196855484508530605658266451 295283226762795908487399677)
  ·
    refine ⟨110731210036048465682774879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295283226762795908487399677 110731210036048465682774879)
    ·
      refine ⟨166096815054072698524162319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110731210036048465682774879 166096815054072698524162319)
      ·
        refine ⟨249145222581109047786243479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166096815054072698524162319 249145222581109047786243479)
        ·
          refine ⟨373717833871663571679365219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249145222581109047786243479 373717833871663571679365219)
          ·
            refine ⟨560576750807495357519047829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373717833871663571679365219 560576750807495357519047829)
            ·
              refine ⟨26277035194101344883705367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 560576750807495357519047829 26277035194101344883705367)
              ·
                refine ⟨39415552791152017325558051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26277035194101344883705367 39415552791152017325558051)
                ·
                  refine ⟨59123329186728025988337077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39415552791152017325558051 59123329186728025988337077)
                  ·
                    refine ⟨5542812111255752436406601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59123329186728025988337077 5542812111255752436406601)
                    ·
                      refine ⟨4157109083441814327304951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542812111255752436406601 4157109083441814327304951)
                      ·
                        rfl

theorem cell23_8095941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_8095941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095941 prefixEnd_8095941 := by exact prefixLift 8095941
  have htrace : WordTrace (prefixWord ++ tailWord_8095941) baseStart_8095941 baseEnd_8095941 := by
    simpa [prefixWord, tailWord_8095941, baseEnd_8095941] using wordTrace_append hprefix tailTrace_8095941
  have hstable : (prefixWord ++ tailWord_8095941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095941).length < 2 ^ (prefixWord ++ tailWord_8095941).sum := by decide
  have hdescent : baseEnd_8095941 < baseStart_8095941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095965 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_8095965 : Nat := 118140960795 + 8095965 * 2 ^ 59
def prefixEnd_8095965 : Nat := 4983230072969 + 3 ^ 40 * 8095965 * 2
def baseEnd_8095965 : Nat := 4157121406977522233404841

theorem tailTrace_8095965 : CollatzResearch.WordTrace tailWord_8095965 prefixEnd_8095965 4157121406977522233404841 := by
  unfold tailWord_8095965
  simp only [CollatzResearch.WordTrace]
  refine ⟨295284102114708960586273349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196856068076472640390848899 295284102114708960586273349)
  ·
    refine ⟨55365769146507930109926253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295284102114708960586273349 55365769146507930109926253)
    ·
      refine ⟨20762163429940473791222345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55365769146507930109926253 20762163429940473791222345)
      ·
        refine ⟨15571622572455355343416759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20762163429940473791222345 15571622572455355343416759)
        ·
          refine ⟨23357433858683033015125139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15571622572455355343416759 23357433858683033015125139)
          ·
            refine ⟨35036150788024549522687709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23357433858683033015125139 35036150788024549522687709)
            ·
              refine ⟨13138556545509206071007891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35036150788024549522687709 13138556545509206071007891)
              ·
                refine ⟨19707834818263809106511837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13138556545509206071007891 19707834818263809106511837)
                ·
                  refine ⟨7390438056848928414941939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19707834818263809106511837 7390438056848928414941939)
                  ·
                    refine ⟨11085657085273392622412909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7390438056848928414941939 11085657085273392622412909)
                    ·
                      refine ⟨4157121406977522233404841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11085657085273392622412909 4157121406977522233404841)
                      ·
                        rfl

theorem cell23_8095965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_8095965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095965 prefixEnd_8095965 := by exact prefixLift 8095965
  have htrace : WordTrace (prefixWord ++ tailWord_8095965) baseStart_8095965 baseEnd_8095965 := by
    simpa [prefixWord, tailWord_8095965, baseEnd_8095965] using wordTrace_append hprefix tailTrace_8095965
  have hstable : (prefixWord ++ tailWord_8095965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095965).length < 2 ^ (prefixWord ++ tailWord_8095965).sum := by decide
  have hdescent : baseEnd_8095965 < baseStart_8095965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095984 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_8095984 : Nat := 118140960795 + 8095984 * 2 ^ 59
def prefixEnd_8095984 : Nat := 4983230072969 + 3 ^ 40 * 8095984 * 2
def baseEnd_8095984 : Nat := 4157131163109957659067253

theorem tailTrace_8095984 : CollatzResearch.WordTrace tailWord_8095984 prefixEnd_8095984 4157131163109957659067253 := by
  unfold tailWord_8095984
  simp only [CollatzResearch.WordTrace]
  refine ⟨147642397550820063415607503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196856530067760084554143337 147642397550820063415607503)
  ·
    refine ⟨221463596326230095123411255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147642397550820063415607503 221463596326230095123411255)
    ·
      refine ⟨332195394489345142685116883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221463596326230095123411255 332195394489345142685116883)
      ·
        refine ⟨498293091734017714027675325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332195394489345142685116883 498293091734017714027675325)
        ·
          refine ⟨186859909400256642760378247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498293091734017714027675325 186859909400256642760378247)
          ·
            refine ⟨280289864100384964140567371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186859909400256642760378247 280289864100384964140567371)
            ·
              refine ⟨420434796150577446210851057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280289864100384964140567371 420434796150577446210851057)
              ·
                refine ⟨315326097112933084658138293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420434796150577446210851057 315326097112933084658138293)
                ·
                  refine ⟨29561821604337476686700465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315326097112933084658138293 29561821604337476686700465)
                  ·
                    refine ⟨22171366203253107515025349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29561821604337476686700465 22171366203253107515025349)
                    ·
                      refine ⟨4157131163109957659067253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22171366203253107515025349 4157131163109957659067253)
                      ·
                        rfl

theorem cell23_8095984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_8095984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095984 prefixEnd_8095984 := by exact prefixLift 8095984
  have htrace : WordTrace (prefixWord ++ tailWord_8095984) baseStart_8095984 baseEnd_8095984 := by
    simpa [prefixWord, tailWord_8095984, baseEnd_8095984] using wordTrace_append hprefix tailTrace_8095984
  have hstable : (prefixWord ++ tailWord_8095984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095984).length < 2 ^ (prefixWord ++ tailWord_8095984).sum := by decide
  have hdescent : baseEnd_8095984 < baseStart_8095984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8095994 : List Nat := [3, 1, 1, 1, 1, 5, 2, 9]
def baseStart_8095994 : Nat := 118140960795 + 8095994 * 2 ^ 59
def prefixEnd_8095994 : Nat := 4983230072969 + 3 ^ 40 * 8095994 * 2
def baseEnd_8095994 : Nat := 153968011033944541479341

theorem tailTrace_8095994 : CollatzResearch.WordTrace tailWord_8095994 prefixEnd_8095994 153968011033944541479341 := by
  unfold tailWord_8095994
  simp only [CollatzResearch.WordTrace]
  refine ⟨73821289957900974634769759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196856773221069265692719357 73821289957900974634769759)
  ·
    refine ⟨110731934936851461952154639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73821289957900974634769759 110731934936851461952154639)
    ·
      refine ⟨166097902405277192928231959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110731934936851461952154639 166097902405277192928231959)
      ·
        refine ⟨249146853607915789392347939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166097902405277192928231959 249146853607915789392347939)
        ·
          refine ⟨373720280411873684088521909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249146853607915789392347939 373720280411873684088521909)
          ·
            refine ⟨35036276288613157883298929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373720280411873684088521909 35036276288613157883298929)
            ·
              refine ⟨26277207216459868412474197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35036276288613157883298929 26277207216459868412474197)
              ·
                refine ⟨153968011033944541479341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26277207216459868412474197 153968011033944541479341)
                ·
                  rfl

theorem cell23_8095994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 9].length) (baseStart_8095994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8095994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8095994 prefixEnd_8095994 := by exact prefixLift 8095994
  have htrace : WordTrace (prefixWord ++ tailWord_8095994) baseStart_8095994 baseEnd_8095994 := by
    simpa [prefixWord, tailWord_8095994, baseEnd_8095994] using wordTrace_append hprefix tailTrace_8095994
  have hstable : (prefixWord ++ tailWord_8095994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8095994).length < 2 ^ (prefixWord ++ tailWord_8095994).sum := by decide
  have hdescent : baseEnd_8095994 < baseStart_8095994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8095994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096001 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_8096001 : Nat := 118140960795 + 8096001 * 2 ^ 59
def prefixEnd_8096001 : Nat := 4983230072969 + 3 ^ 40 * 8096001 * 2
def baseEnd_8096001 : Nat := 4157139892281084092554675

theorem tailTrace_8096001 : CollatzResearch.WordTrace tailWord_8096001 prefixEnd_8096001 4157139892281084092554675 := by
  unfold tailWord_8096001
  simp only [CollatzResearch.WordTrace]
  refine ⟨295285415142578538734583857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196856943428385692489722571 295285415142578538734583857)
  ·
    refine ⟨221464061356933904050937893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295285415142578538734583857 221464061356933904050937893)
    ·
      refine ⟨41524511504425107009550855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221464061356933904050937893 41524511504425107009550855)
      ·
        refine ⟨62286767256637660514326283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41524511504425107009550855 62286767256637660514326283)
        ·
          refine ⟨93430150884956490771489425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62286767256637660514326283 93430150884956490771489425)
          ·
            refine ⟨70072613163717368078617069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93430150884956490771489425 70072613163717368078617069)
            ·
              refine ⟨26277229936394013029481401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70072613163717368078617069 26277229936394013029481401)
              ·
                refine ⟨19707922452295509772111051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26277229936394013029481401 19707922452295509772111051)
                ·
                  refine ⟨29561883678443264658166577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19707922452295509772111051 29561883678443264658166577)
                  ·
                    refine ⟨22171412758832448493624933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29561883678443264658166577 22171412758832448493624933)
                    ·
                      refine ⟨4157139892281084092554675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22171412758832448493624933 4157139892281084092554675)
                      ·
                        rfl

theorem cell23_8096001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_8096001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096001 prefixEnd_8096001 := by exact prefixLift 8096001
  have htrace : WordTrace (prefixWord ++ tailWord_8096001) baseStart_8096001 baseEnd_8096001 := by
    simpa [prefixWord, tailWord_8096001, baseEnd_8096001] using wordTrace_append hprefix tailTrace_8096001
  have hstable : (prefixWord ++ tailWord_8096001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096001).length < 2 ^ (prefixWord ++ tailWord_8096001).sum := by decide
  have hdescent : baseEnd_8096001 < baseStart_8096001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096008 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_8096008 : Nat := 118140960795 + 8096008 * 2 ^ 59
def prefixEnd_8096008 : Nat := 4983230072969 + 3 ^ 40 * 8096008 * 2
def baseEnd_8096008 : Nat := 4157143486645665565167143

theorem tailTrace_8096008 : CollatzResearch.WordTrace tailWord_8096008 prefixEnd_8096008 4157143486645665565167143 := by
  unfold tailWord_8096008
  simp only [CollatzResearch.WordTrace]
  refine ⟨147642835226776589465044339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196857113635702119286725785 147642835226776589465044339)
  ·
    refine ⟨221464252840164884197566509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147642835226776589465044339 221464252840164884197566509)
    ·
      refine ⟨83049094815061831574087441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221464252840164884197566509 83049094815061831574087441)
      ·
        refine ⟨62286821111296373680565581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83049094815061831574087441 62286821111296373680565581)
        ·
          refine ⟨23357557916736140130212093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62286821111296373680565581 23357557916736140130212093)
          ·
            refine ⟨8759084218776052548829535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23357557916736140130212093 8759084218776052548829535)
            ·
              refine ⟨13138626328164078823244303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759084218776052548829535 13138626328164078823244303)
              ·
                refine ⟨19707939492246118234866455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13138626328164078823244303 19707939492246118234866455)
                ·
                  refine ⟨29561909238369177352299683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19707939492246118234866455 29561909238369177352299683)
                  ·
                    refine ⟨44342863857553766028449525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29561909238369177352299683 44342863857553766028449525)
                    ·
                      refine ⟨4157143486645665565167143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44342863857553766028449525 4157143486645665565167143)
                      ·
                        rfl

theorem cell23_8096008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_8096008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096008 prefixEnd_8096008 := by exact prefixLift 8096008
  have htrace : WordTrace (prefixWord ++ tailWord_8096008) baseStart_8096008 baseEnd_8096008 := by
    simpa [prefixWord, tailWord_8096008, baseEnd_8096008] using wordTrace_append hprefix tailTrace_8096008
  have hstable : (prefixWord ++ tailWord_8096008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096008).length < 2 ^ (prefixWord ++ tailWord_8096008).sum := by decide
  have hdescent : baseEnd_8096008 < baseStart_8096008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096024 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 1, 9]
def baseStart_8096024 : Nat := 118140960795 + 8096024 * 2 ^ 59
def prefixEnd_8096024 : Nat := 4983230072969 + 3 ^ 40 * 8096024 * 2
def baseEnd_8096024 : Nat := 1385717234112045834189023

theorem tailTrace_8096024 : CollatzResearch.WordTrace tailWord_8096024 prefixEnd_8096024 1385717234112045834189023 := by
  unfold tailWord_8096024
  simp only [CollatzResearch.WordTrace]
  refine ⟨147643127010747606831335563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196857502680996809108447417 147643127010747606831335563)
  ·
    refine ⟨221464690516121410247003345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147643127010747606831335563 221464690516121410247003345)
    ·
      refine ⟨166098517887091057685252509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221464690516121410247003345 166098517887091057685252509)
      ·
        refine ⟨62286944207659146631969691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166098517887091057685252509 62286944207659146631969691)
        ·
          refine ⟨93430416311488719947954537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62286944207659146631969691 93430416311488719947954537)
          ·
            refine ⟨70072812233616539960965903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93430416311488719947954537 70072812233616539960965903)
            ·
              refine ⟨105109218350424809941448855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70072812233616539960965903 105109218350424809941448855)
              ·
                refine ⟨157663827525637214912173283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105109218350424809941448855 157663827525637214912173283)
                ·
                  refine ⟨236495741288455822368259925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157663827525637214912173283 236495741288455822368259925)
                  ·
                    refine ⟨1385717234112045834189023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 236495741288455822368259925 1385717234112045834189023)
                    ·
                      rfl

theorem cell23_8096024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_8096024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096024 prefixEnd_8096024 := by exact prefixLift 8096024
  have htrace : WordTrace (prefixWord ++ tailWord_8096024) baseStart_8096024 baseEnd_8096024 := by
    simpa [prefixWord, tailWord_8096024, baseEnd_8096024] using wordTrace_append hprefix tailTrace_8096024
  have hstable : (prefixWord ++ tailWord_8096024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096024).length < 2 ^ (prefixWord ++ tailWord_8096024).sum := by decide
  have hdescent : baseEnd_8096024 < baseStart_8096024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096045 : List Nat := [1, 5, 3, 1, 2, 1, 3, 7]
def baseStart_8096045 : Nat := 118140960795 + 8096045 * 2 ^ 59
def prefixEnd_8096045 : Nat := 4983230072969 + 3 ^ 40 * 8096045 * 2
def baseEnd_8096045 : Nat := 153968980941847478533499

theorem tailTrace_8096045 : CollatzResearch.WordTrace tailWord_8096045 prefixEnd_8096045 153968980941847478533499 := by
  unfold tailWord_8096045
  simp only [CollatzResearch.WordTrace]
  refine ⟨295287019954419134249185589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196858013302946089499457059 295287019954419134249185589)
  ·
    refine ⟨27683158120726793835861149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295287019954419134249185589 27683158120726793835861149)
    ·
      refine ⟨10381184295272547688447931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27683158120726793835861149 10381184295272547688447931)
      ·
        refine ⟨15571776442908821532671897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10381184295272547688447931 15571776442908821532671897)
        ·
          refine ⟨11678832332181616149503923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15571776442908821532671897 11678832332181616149503923)
          ·
            refine ⟨17518248498272424224255885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11678832332181616149503923 17518248498272424224255885)
            ·
              refine ⟨6569343186852159084095957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17518248498272424224255885 6569343186852159084095957)
              ·
                refine ⟨153968980941847478533499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6569343186852159084095957 153968980941847478533499)
                ·
                  rfl

theorem cell23_8096045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 7].length) (baseStart_8096045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096045 prefixEnd_8096045 := by exact prefixLift 8096045
  have htrace : WordTrace (prefixWord ++ tailWord_8096045) baseStart_8096045 baseEnd_8096045 := by
    simpa [prefixWord, tailWord_8096045, baseEnd_8096045] using wordTrace_append hprefix tailTrace_8096045
  have hstable : (prefixWord ++ tailWord_8096045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096045).length < 2 ^ (prefixWord ++ tailWord_8096045).sum := by decide
  have hdescent : baseEnd_8096045 < baseStart_8096045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096095 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 2, 2, 2]
def baseStart_8096095 : Nat := 118140960795 + 8096095 * 2 ^ 59
def prefixEnd_8096095 : Nat := 4983230072969 + 3 ^ 40 * 8096095 * 2
def baseEnd_8096095 : Nat := 4157188159462606724779243

theorem tailTrace_8096095 : CollatzResearch.WordTrace tailWord_8096095 prefixEnd_8096095 4157188159462606724779243 := by
  unfold tailWord_8096095
  simp only [CollatzResearch.WordTrace]
  refine ⟨295288843604237992788505739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196859229069491995192337159 295288843604237992788505739)
  ·
    refine ⟨442933265406356989182758609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295288843604237992788505739 442933265406356989182758609)
    ·
      refine ⟨332199949054767741887068957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442933265406356989182758609 332199949054767741887068957)
      ·
        refine ⟨124574980895537903207650859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332199949054767741887068957 124574980895537903207650859)
        ·
          refine ⟨186862471343306854811476289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124574980895537903207650859 186862471343306854811476289)
          ·
            refine ⟨140146853507480141108607217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186862471343306854811476289 140146853507480141108607217)
            ·
              refine ⟨105110140130610105831455413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140146853507480141108607217 105110140130610105831455413)
              ·
                refine ⟨9854075637244697421698945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105110140130610105831455413 9854075637244697421698945)
                ·
                  refine ⟨7390556727933523066274209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9854075637244697421698945 7390556727933523066274209)
                  ·
                    refine ⟨5542917545950142299705657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7390556727933523066274209 5542917545950142299705657)
                    ·
                      refine ⟨4157188159462606724779243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542917545950142299705657 4157188159462606724779243)
                      ·
                        rfl

theorem cell23_8096095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_8096095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096095 prefixEnd_8096095 := by exact prefixLift 8096095
  have htrace : WordTrace (prefixWord ++ tailWord_8096095) baseStart_8096095 baseEnd_8096095 := by
    simpa [prefixWord, tailWord_8096095, baseEnd_8096095] using wordTrace_append hprefix tailTrace_8096095
  have hstable : (prefixWord ++ tailWord_8096095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096095).length < 2 ^ (prefixWord ++ tailWord_8096095).sum := by decide
  have hdescent : baseEnd_8096095 < baseStart_8096095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096101 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 7]
def baseStart_8096101 : Nat := 118140960795 + 8096101 * 2 ^ 59
def prefixEnd_8096101 : Nat := 4983230072969 + 3 ^ 40 * 8096101 * 2
def baseEnd_8096101 : Nat := 461910137816281522367135

theorem tailTrace_8096101 : CollatzResearch.WordTrace tailWord_8096101 prefixEnd_8096101 461910137816281522367135 := by
  unfold tailWord_8096101
  simp only [CollatzResearch.WordTrace]
  refine ⟨295289062442216255813224157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196859374961477503875482771 295289062442216255813224157)
  ·
    refine ⟨110733398415831095929959059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295289062442216255813224157 110733398415831095929959059)
    ·
      refine ⟨166100097623746643894938589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110733398415831095929959059 166100097623746643894938589)
      ·
        refine ⟨62287536608904991460601971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166100097623746643894938589 62287536608904991460601971)
        ·
          refine ⟨93431304913357487190902957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62287536608904991460601971 93431304913357487190902957)
          ·
            refine ⟨35036739342509057696588609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93431304913357487190902957 35036739342509057696588609)
            ·
              refine ⟨26277554506881793272441457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35036739342509057696588609 26277554506881793272441457)
              ·
                refine ⟨19708165880161344954331093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26277554506881793272441457 19708165880161344954331093)
                ·
                  refine ⟨461910137816281522367135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19708165880161344954331093 461910137816281522367135)
                  ·
                    rfl

theorem cell23_8096101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_8096101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096101 prefixEnd_8096101 := by exact prefixLift 8096101
  have htrace : WordTrace (prefixWord ++ tailWord_8096101) baseStart_8096101 baseEnd_8096101 := by
    simpa [prefixWord, tailWord_8096101, baseEnd_8096101] using wordTrace_append hprefix tailTrace_8096101
  have hstable : (prefixWord ++ tailWord_8096101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096101).length < 2 ^ (prefixWord ++ tailWord_8096101).sum := by decide
  have hdescent : baseEnd_8096101 < baseStart_8096101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096111 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 3]
def baseStart_8096111 : Nat := 118140960795 + 8096111 * 2 ^ 59
def prefixEnd_8096111 : Nat := 4983230072969 + 3 ^ 40 * 8096111 * 2
def baseEnd_8096111 : Nat := 4157196375153078662179169

theorem tailTrace_8096111 : CollatzResearch.WordTrace tailWord_8096111 prefixEnd_8096111 4157196375153078662179169 := by
  unfold tailWord_8096111
  simp only [CollatzResearch.WordTrace]
  refine ⟨295289427172180027521088187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196859618114786685014058791 295289427172180027521088187)
  ·
    refine ⟨442934140758270041281632281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295289427172180027521088187 442934140758270041281632281)
    ·
      refine ⟨332200605568702530961224211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442934140758270041281632281 332200605568702530961224211)
      ·
        refine ⟨498300908353053796441836317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332200605568702530961224211 498300908353053796441836317)
        ·
          refine ⟨186862840632395173665688619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498300908353053796441836317 186862840632395173665688619)
          ·
            refine ⟨280294260948592760498532929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186862840632395173665688619 280294260948592760498532929)
            ·
              refine ⟨210220695711444570373899697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280294260948592760498532929 210220695711444570373899697)
              ·
                refine ⟨157665521783583427780424773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210220695711444570373899697 157665521783583427780424773)
                ·
                  refine ⟨29562285334421892708829645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157665521783583427780424773 29562285334421892708829645)
                  ·
                    refine ⟨11085857000408209765811117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29562285334421892708829645 11085857000408209765811117)
                    ·
                      refine ⟨4157196375153078662179169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11085857000408209765811117 4157196375153078662179169)
                      ·
                        rfl

theorem cell23_8096111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_8096111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096111 prefixEnd_8096111 := by exact prefixLift 8096111
  have htrace : WordTrace (prefixWord ++ tailWord_8096111) baseStart_8096111 baseEnd_8096111 := by
    simpa [prefixWord, tailWord_8096111, baseEnd_8096111] using wordTrace_append hprefix tailTrace_8096111
  have hstable : (prefixWord ++ tailWord_8096111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096111).length < 2 ^ (prefixWord ++ tailWord_8096111).sum := by decide
  have hdescent : baseEnd_8096111 < baseStart_8096111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096135 : List Nat := [1, 1, 4, 2, 2, 1, 5, 2, 5]
def baseStart_8096135 : Nat := 118140960795 + 8096135 * 2 ^ 59
def prefixEnd_8096135 : Nat := 4983230072969 + 3 ^ 40 * 8096135 * 2
def baseEnd_8096135 : Nat := 461912077632087396475451

theorem tailTrace_8096135 : CollatzResearch.WordTrace tailWord_8096135 prefixEnd_8096135 461912077632087396475451 := by
  unfold tailWord_8096135
  simp only [CollatzResearch.WordTrace]
  refine ⟨295290302524093079619961859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196860201682728719746641239 295290302524093079619961859)
  ·
    refine ⟨442935453786139619429942789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295290302524093079619961859 442935453786139619429942789)
    ·
      refine ⟨83050397584901178643114273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442935453786139619429942789 83050397584901178643114273)
      ·
        refine ⟨62287798188675883982335705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83050397584901178643114273 62287798188675883982335705)
        ·
          refine ⟨46715848641506912986751779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62287798188675883982335705 46715848641506912986751779)
          ·
            refine ⟨70073772962260369480127669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46715848641506912986751779 70073772962260369480127669)
            ·
              refine ⟨6569416215211909638761969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70073772962260369480127669 6569416215211909638761969)
              ·
                refine ⟨4927062161408932229071477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6569416215211909638761969 4927062161408932229071477)
                ·
                  refine ⟨461912077632087396475451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4927062161408932229071477 461912077632087396475451)
                  ·
                    rfl

theorem cell23_8096135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 5].length) (baseStart_8096135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096135 prefixEnd_8096135 := by exact prefixLift 8096135
  have htrace : WordTrace (prefixWord ++ tailWord_8096135) baseStart_8096135 baseEnd_8096135 := by
    simpa [prefixWord, tailWord_8096135, baseEnd_8096135] using wordTrace_append hprefix tailTrace_8096135
  have hstable : (prefixWord ++ tailWord_8096135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096135).length < 2 ^ (prefixWord ++ tailWord_8096135).sum := by decide
  have hdescent : baseEnd_8096135 < baseStart_8096135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096150 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_8096150 : Nat := 118140960795 + 8096150 * 2 ^ 59
def prefixEnd_8096150 : Nat := 4983230072969 + 3 ^ 40 * 8096150 * 2
def baseEnd_8096150 : Nat := 4157216400898604009591491

theorem tailTrace_8096150 : CollatzResearch.WordTrace tailWord_8096150 prefixEnd_8096150 4157216400898604009591491 := by
  unfold tailWord_8096150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455678101189921073859869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196860566412692491454505269 18455678101189921073859869)
  ·
    refine ⟨6920879287946220402697451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18455678101189921073859869 6920879287946220402697451)
    ·
      refine ⟨10381318931919330604046177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6920879287946220402697451 10381318931919330604046177)
      ·
        refine ⟨7785989198939497953034633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10381318931919330604046177 7785989198939497953034633)
        ·
          refine ⟨5839491899204623464775975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7785989198939497953034633 5839491899204623464775975)
          ·
            refine ⟨8759237848806935197163963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5839491899204623464775975 8759237848806935197163963)
            ·
              refine ⟨13138856773210402795745945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759237848806935197163963 13138856773210402795745945)
              ·
                refine ⟨9854142579907802096809459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13138856773210402795745945 9854142579907802096809459)
                ·
                  refine ⟨14781213869861703145214189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9854142579907802096809459 14781213869861703145214189)
                  ·
                    refine ⟨5542955201198138679455321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14781213869861703145214189 5542955201198138679455321)
                    ·
                      refine ⟨4157216400898604009591491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5542955201198138679455321 4157216400898604009591491)
                      ·
                        rfl

theorem cell23_8096150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_8096150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096150 prefixEnd_8096150 := by exact prefixLift 8096150
  have htrace : WordTrace (prefixWord ++ tailWord_8096150) baseStart_8096150 baseEnd_8096150 := by
    simpa [prefixWord, tailWord_8096150, baseEnd_8096150] using wordTrace_append hprefix tailTrace_8096150
  have hstable : (prefixWord ++ tailWord_8096150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096150).length < 2 ^ (prefixWord ++ tailWord_8096150).sum := by decide
  have hdescent : baseEnd_8096150 < baseStart_8096150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096151 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_8096151 : Nat := 118140960795 + 8096151 * 2 ^ 59
def prefixEnd_8096151 : Nat := 4983230072969 + 3 ^ 40 * 8096151 * 2
def baseEnd_8096151 : Nat := 4157216914379258505678985

theorem tailTrace_8096151 : CollatzResearch.WordTrace tailWord_8096151 prefixEnd_8096151 4157216914379258505678985 := by
  unfold tailWord_8096151
  simp only [CollatzResearch.WordTrace]
  refine ⟨295290886092035114352544307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196860590728023409568362871 295290886092035114352544307)
  ·
    refine ⟨442936329138052671528816461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295290886092035114352544307 442936329138052671528816461)
    ·
      refine ⟨166101123426769751823306173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442936329138052671528816461 166101123426769751823306173)
      ·
        refine ⟨62287921285038656933739815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166101123426769751823306173 62287921285038656933739815)
        ·
          refine ⟨93431881927557985400609723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62287921285038656933739815 93431881927557985400609723)
          ·
            refine ⟨140147822891336978100914585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93431881927557985400609723 140147822891336978100914585)
            ·
              refine ⟨105110867168502733575685939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140147822891336978100914585 105110867168502733575685939)
              ·
                refine ⟨157666300752754100363528909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105110867168502733575685939 157666300752754100363528909)
                ·
                  refine ⟨59124862782282787636323341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157666300752754100363528909 59124862782282787636323341)
                  ·
                    refine ⟨22171823543356045363621253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59124862782282787636323341 22171823543356045363621253)
                    ·
                      refine ⟨4157216914379258505678985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22171823543356045363621253 4157216914379258505678985)
                      ·
                        rfl

theorem cell23_8096151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_8096151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096151 prefixEnd_8096151 := by exact prefixLift 8096151
  have htrace : WordTrace (prefixWord ++ tailWord_8096151) baseStart_8096151 baseEnd_8096151 := by
    simpa [prefixWord, tailWord_8096151, baseEnd_8096151] using wordTrace_append hprefix tailTrace_8096151
  have hstable : (prefixWord ++ tailWord_8096151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096151).length < 2 ^ (prefixWord ++ tailWord_8096151).sum := by decide
  have hdescent : baseEnd_8096151 < baseStart_8096151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096229 : List Nat := [1, 3, 1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_8096229 : Nat := 118140960795 + 8096229 * 2 ^ 59
def prefixEnd_8096229 : Nat := 4983230072969 + 3 ^ 40 * 8096229 * 2
def baseEnd_8096229 : Nat := 1385752321956769733501209

theorem tailTrace_8096229 : CollatzResearch.WordTrace tailWord_8096229 prefixEnd_8096229 1385752321956769733501209 := by
  unfold tailWord_8096229
  simp only [CollatzResearch.WordTrace]
  refine ⟨295293730985752533673883741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196862487323835022449255827 295293730985752533673883741)
  ·
    refine ⟨110735149119657200127706403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295293730985752533673883741 110735149119657200127706403)
    ·
      refine ⟨166102723679485800191559605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110735149119657200127706403 166102723679485800191559605)
      ·
        refine ⟨15572130344951793767958713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166102723679485800191559605 15572130344951793767958713)
        ·
          refine ⟨11679097758713845325969035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15572130344951793767958713 11679097758713845325969035)
          ·
            refine ⟨17518646638070767988953553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11679097758713845325969035 17518646638070767988953553)
            ·
              refine ⟨13138984978553075991715165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17518646638070767988953553 13138984978553075991715165)
              ·
                refine ⟨4927119366957403496893187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13138984978553075991715165 4927119366957403496893187)
                ·
                  refine ⟨7390679050436105245339781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927119366957403496893187 7390679050436105245339781)
                  ·
                    refine ⟨1385752321956769733501209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7390679050436105245339781 1385752321956769733501209)
                    ·
                      rfl

theorem cell23_8096229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_8096229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096229 prefixEnd_8096229 := by exact prefixLift 8096229
  have htrace : WordTrace (prefixWord ++ tailWord_8096229) baseStart_8096229 baseEnd_8096229 := by
    simpa [prefixWord, tailWord_8096229, baseEnd_8096229] using wordTrace_append hprefix tailTrace_8096229
  have hstable : (prefixWord ++ tailWord_8096229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096229).length < 2 ^ (prefixWord ++ tailWord_8096229).sum := by decide
  have hdescent : baseEnd_8096229 < baseStart_8096229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096242 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 6]
def baseStart_8096242 : Nat := 118140960795 + 8096242 * 2 ^ 59
def prefixEnd_8096242 : Nat := 4983230072969 + 3 ^ 40 * 8096242 * 2
def baseEnd_8096242 : Nat := 461918182346535294404563

theorem tailTrace_8096242 : CollatzResearch.WordTrace tailWord_8096242 prefixEnd_8096242 461918182346535294404563 := by
  unfold tailWord_8096242
  simp only [CollatzResearch.WordTrace]
  refine ⟨73823551283676359223526745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196862803423136957929404653 73823551283676359223526745)
  ·
    refine ⟨55367663462757269417645059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73823551283676359223526745 55367663462757269417645059)
    ·
      refine ⟨83051495194135904126467589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55367663462757269417645059 83051495194135904126467589)
      ·
        refine ⟨15572155348900482023712673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83051495194135904126467589 15572155348900482023712673)
        ·
          refine ⟨11679116511675361517784505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15572155348900482023712673 11679116511675361517784505)
          ·
            refine ⟨8759337383756521138338379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11679116511675361517784505 8759337383756521138338379)
            ·
              refine ⟨13139006075634781707507569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759337383756521138338379 13139006075634781707507569)
              ·
                refine ⟨9854254556726086280630677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13139006075634781707507569 9854254556726086280630677)
                ·
                  refine ⟨461918182346535294404563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9854254556726086280630677 461918182346535294404563)
                  ·
                    rfl

theorem cell23_8096242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_8096242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096242 prefixEnd_8096242 := by exact prefixLift 8096242
  have htrace : WordTrace (prefixWord ++ tailWord_8096242) baseStart_8096242 baseEnd_8096242 := by
    simpa [prefixWord, tailWord_8096242, baseEnd_8096242] using wordTrace_append hprefix tailTrace_8096242
  have hstable : (prefixWord ++ tailWord_8096242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096242).length < 2 ^ (prefixWord ++ tailWord_8096242).sum := by decide
  have hdescent : baseEnd_8096242 < baseStart_8096242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096275 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 4]
def baseStart_8096275 : Nat := 118140960795 + 8096275 * 2 ^ 59
def prefixEnd_8096275 : Nat := 4983230072969 + 3 ^ 40 * 8096275 * 2
def baseEnd_8096275 : Nat := 4157280585980416020528415

theorem tailTrace_8096275 : CollatzResearch.WordTrace tailWord_8096275 prefixEnd_8096275 4157280585980416020528415 := by
  unfold tailWord_8096275
  simp only [CollatzResearch.WordTrace]
  refine ⟨295295408743585883530058279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196863605829057255686705519 295295408743585883530058279)
  ·
    refine ⟨442943113115378825295087419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295295408743585883530058279 442943113115378825295087419)
    ·
      refine ⟨664414669673068237942631129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442943113115378825295087419 664414669673068237942631129)
      ·
        refine ⟨498311002254801178456973347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664414669673068237942631129 498311002254801178456973347)
        ·
          refine ⟨747466503382201767685460021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498311002254801178456973347 747466503382201767685460021)
          ·
            refine ⟨70074984692081415720511877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 747466503382201767685460021 70074984692081415720511877)
            ·
              refine ⟨13139059629765265447595977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70074984692081415720511877 13139059629765265447595977)
              ·
                refine ⟨9854294722323949085696983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13139059629765265447595977 9854294722323949085696983)
                ·
                  refine ⟨14781442083485923628545475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9854294722323949085696983 14781442083485923628545475)
                  ·
                    refine ⟨22172163125228885442818213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14781442083485923628545475 22172163125228885442818213)
                    ·
                      refine ⟨4157280585980416020528415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22172163125228885442818213 4157280585980416020528415)
                      ·
                        rfl

theorem cell23_8096275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 4].length) (baseStart_8096275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096275 prefixEnd_8096275 := by exact prefixLift 8096275
  have htrace : WordTrace (prefixWord ++ tailWord_8096275) baseStart_8096275 baseEnd_8096275 := by
    simpa [prefixWord, tailWord_8096275, baseEnd_8096275] using wordTrace_append hprefix tailTrace_8096275
  have hstable : (prefixWord ++ tailWord_8096275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096275).length < 2 ^ (prefixWord ++ tailWord_8096275).sum := by decide
  have hdescent : baseEnd_8096275 < baseStart_8096275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096281 : List Nat := [1, 2, 1, 2, 1, 1, 2, 13]
def baseStart_8096281 : Nat := 118140960795 + 8096281 * 2 ^ 59
def prefixEnd_8096281 : Nat := 4983230072969 + 3 ^ 40 * 8096281 * 2
def baseEnd_8096281 : Nat := 153973469143123814705681

theorem tailTrace_8096281 : CollatzResearch.WordTrace tailWord_8096281 prefixEnd_8096281 153973469143123814705681 := by
  unfold tailWord_8096281
  simp only [CollatzResearch.WordTrace]
  refine ⟨295295627581564146554776697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196863751721042764369851131 295295627581564146554776697)
  ·
    refine ⟨221471720686173109916082523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295295627581564146554776697 221471720686173109916082523)
    ·
      refine ⟨332207581029259664874123785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221471720686173109916082523 332207581029259664874123785)
      ·
        refine ⟨249155685771944748655592839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332207581029259664874123785 249155685771944748655592839)
        ·
          refine ⟨373733528657917122983389259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249155685771944748655592839 373733528657917122983389259)
          ·
            refine ⟨560600292986875684475083889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373733528657917122983389259 560600292986875684475083889)
            ·
              refine ⟨420450219740156763356312917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560600292986875684475083889 420450219740156763356312917)
              ·
                refine ⟨153973469143123814705681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 420450219740156763356312917 153973469143123814705681)
                ·
                  rfl

theorem cell23_8096281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 13].length) (baseStart_8096281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096281 prefixEnd_8096281 := by exact prefixLift 8096281
  have htrace : WordTrace (prefixWord ++ tailWord_8096281) baseStart_8096281 baseEnd_8096281 := by
    simpa [prefixWord, tailWord_8096281, baseEnd_8096281] using wordTrace_append hprefix tailTrace_8096281
  have hstable : (prefixWord ++ tailWord_8096281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096281).length < 2 ^ (prefixWord ++ tailWord_8096281).sum := by decide
  have hdescent : baseEnd_8096281 < baseStart_8096281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096285 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_8096285 : Nat := 118140960795 + 8096285 * 2 ^ 59
def prefixEnd_8096285 : Nat := 4983230072969 + 3 ^ 40 * 8096285 * 2
def baseEnd_8096285 : Nat := 1385761906928986993801123

theorem tailTrace_8096285 : CollatzResearch.WordTrace tailWord_8096285 prefixEnd_8096285 1385761906928986993801123 := by
  unfold tailWord_8096285
  simp only [CollatzResearch.WordTrace]
  refine ⟨295295773473549655237922309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196863848982366436825281539 295295773473549655237922309)
  ·
    refine ⟨55367957526290560357110433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295295773473549655237922309 55367957526290560357110433)
    ·
      refine ⟨41525968144717920267832825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55367957526290560357110433 41525968144717920267832825)
      ·
        refine ⟨31144476108538440200874619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41525968144717920267832825 31144476108538440200874619)
        ·
          refine ⟨46716714162807660301311929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31144476108538440200874619 46716714162807660301311929)
          ·
            refine ⟨35037535622105745225983947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46716714162807660301311929 35037535622105745225983947)
            ·
              refine ⟨52556303433158617838975921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35037535622105745225983947 52556303433158617838975921)
              ·
                refine ⟨39417227574868963379231941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52556303433158617838975921 39417227574868963379231941)
                ·
                  refine ⟨7390730170287930633605989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39417227574868963379231941 7390730170287930633605989)
                  ·
                    refine ⟨1385761906928986993801123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7390730170287930633605989 1385761906928986993801123)
                    ·
                      rfl

theorem cell23_8096285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_8096285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096285 prefixEnd_8096285 := by exact prefixLift 8096285
  have htrace : WordTrace (prefixWord ++ tailWord_8096285) baseStart_8096285 baseEnd_8096285 := by
    simpa [prefixWord, tailWord_8096285, baseEnd_8096285] using wordTrace_append hprefix tailTrace_8096285
  have hstable : (prefixWord ++ tailWord_8096285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096285).length < 2 ^ (prefixWord ++ tailWord_8096285).sum := by decide
  have hdescent : baseEnd_8096285 < baseStart_8096285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096298 : List Nat := [3, 1, 4, 1, 1, 2, 11]
def baseStart_8096298 : Nat := 118140960795 + 8096298 * 2 ^ 59
def prefixEnd_8096298 : Nat := 4983230072969 + 3 ^ 40 * 8096298 * 2
def baseEnd_8096298 : Nat := 51324597481919375685689

theorem tailTrace_8096298 : CollatzResearch.WordTrace tailWord_8096298 prefixEnd_8096298 51324597481919375685689 := by
  unfold tailWord_8096298
  simp only [CollatzResearch.WordTrace]
  refine ⟨73824061905625639614536387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196864165081668372305430365 73824061905625639614536387)
  ·
    refine ⟨110736092858438459421804581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73824061905625639614536387 110736092858438459421804581)
    ·
      refine ⟨20763017410957211141588359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110736092858438459421804581 20763017410957211141588359)
      ·
        refine ⟨31144526116435816712382539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20763017410957211141588359 31144526116435816712382539)
        ·
          refine ⟨46716789174653725068573809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31144526116435816712382539 46716789174653725068573809)
          ·
            refine ⟨35037591880990293801430357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46716789174653725068573809 35037591880990293801430357)
            ·
              refine ⟨51324597481919375685689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35037591880990293801430357 51324597481919375685689)
              ·
                rfl

theorem cell23_8096298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 11].length) (baseStart_8096298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096298 prefixEnd_8096298 := by exact prefixLift 8096298
  have htrace : WordTrace (prefixWord ++ tailWord_8096298) baseStart_8096298 baseEnd_8096298 := by
    simpa [prefixWord, tailWord_8096298, baseEnd_8096298] using wordTrace_append hprefix tailTrace_8096298
  have hstable : (prefixWord ++ tailWord_8096298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096298).length < 2 ^ (prefixWord ++ tailWord_8096298).sum := by decide
  have hdescent : baseEnd_8096298 < baseStart_8096298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096326 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_8096326 : Nat := 118140960795 + 8096326 * 2 ^ 59
def prefixEnd_8096326 : Nat := 4983230072969 + 3 ^ 40 * 8096326 * 2
def baseEnd_8096326 : Nat := 4157306773493795320990681

theorem tailTrace_8096326 : CollatzResearch.WordTrace tailWord_8096326 prefixEnd_8096326 4157306773493795320990681 := by
  unfold tailWord_8096326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9228039652075034976255151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196864845910934079493443221 9228039652075034976255151)
  ·
    refine ⟨13842059478112552464382727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9228039652075034976255151 13842059478112552464382727)
    ·
      refine ⟨20763089217168828696574091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13842059478112552464382727 20763089217168828696574091)
      ·
        refine ⟨31144633825753243044861137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20763089217168828696574091 31144633825753243044861137)
        ·
          refine ⟨23358475369314932283645853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31144633825753243044861137 23358475369314932283645853)
          ·
            refine ⟨8759428263493099606367195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23358475369314932283645853 8759428263493099606367195)
            ·
              refine ⟨13139142395239649409550793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759428263493099606367195 13139142395239649409550793)
              ·
                refine ⟨9854356796429737057163095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13139142395239649409550793 9854356796429737057163095)
                ·
                  refine ⟨14781535194644605585744643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9854356796429737057163095 14781535194644605585744643)
                  ·
                    refine ⟨22172302791966908378616965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14781535194644605585744643 22172302791966908378616965)
                    ·
                      refine ⟨4157306773493795320990681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22172302791966908378616965 4157306773493795320990681)
                      ·
                        rfl

theorem cell23_8096326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_8096326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096326 prefixEnd_8096326 := by exact prefixLift 8096326
  have htrace : WordTrace (prefixWord ++ tailWord_8096326) baseStart_8096326 baseEnd_8096326 := by
    simpa [prefixWord, tailWord_8096326, baseEnd_8096326] using wordTrace_append hprefix tailTrace_8096326
  have hstable : (prefixWord ++ tailWord_8096326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096326).length < 2 ^ (prefixWord ++ tailWord_8096326).sum := by decide
  have hdescent : baseEnd_8096326 < baseStart_8096326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096352 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 1, 3, 2]
def baseStart_8096352 : Nat := 118140960795 + 8096352 * 2 ^ 59
def prefixEnd_8096352 : Nat := 4983230072969 + 3 ^ 40 * 8096352 * 2
def baseEnd_8096352 : Nat := 4157320123990812219265561

theorem tailTrace_8096352 : CollatzResearch.WordTrace tailWord_8096352 prefixEnd_8096352 4157320123990812219265561 := by
  unfold tailWord_8096352
  simp only [CollatzResearch.WordTrace]
  refine ⟨147649108582153462840305655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196865478109537950453740873 147649108582153462840305655)
  ·
    refine ⟨221473662873230194260458483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147649108582153462840305655 221473662873230194260458483)
    ·
      refine ⟨332210494309845291390687725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221473662873230194260458483 332210494309845291390687725)
      ·
        refine ⟨124578935366191984271507897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332210494309845291390687725 124578935366191984271507897)
        ·
          refine ⟨93434201524643988203630923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124578935366191984271507897 93434201524643988203630923)
          ·
            refine ⟨140151302286965982305446385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93434201524643988203630923 140151302286965982305446385)
            ·
              refine ⟨105113476715224486729084789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140151302286965982305446385 105113476715224486729084789)
              ·
                refine ⟨9854388442052295630851699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105113476715224486729084789 9854388442052295630851699)
                ·
                  refine ⟨14781582663078443446277549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9854388442052295630851699 14781582663078443446277549)
                  ·
                    refine ⟨5543093498654416292354081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14781582663078443446277549 5543093498654416292354081)
                    ·
                      refine ⟨4157320123990812219265561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543093498654416292354081 4157320123990812219265561)
                      ·
                        rfl

theorem cell23_8096352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_8096352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096352 prefixEnd_8096352 := by exact prefixLift 8096352
  have htrace : WordTrace (prefixWord ++ tailWord_8096352) baseStart_8096352 baseEnd_8096352 := by
    simpa [prefixWord, tailWord_8096352, baseEnd_8096352] using wordTrace_append hprefix tailTrace_8096352
  have hstable : (prefixWord ++ tailWord_8096352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096352).length < 2 ^ (prefixWord ++ tailWord_8096352).sum := by decide
  have hdescent : baseEnd_8096352 < baseStart_8096352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096360 : List Nat := [2, 1, 4, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_8096360 : Nat := 118140960795 + 8096360 * 2 ^ 59
def prefixEnd_8096360 : Nat := 4983230072969 + 3 ^ 40 * 8096360 * 2
def baseEnd_8096360 : Nat := 4157324231836048187965525

theorem tailTrace_8096360 : CollatzResearch.WordTrace tailWord_8096360 prefixEnd_8096360 4157324231836048187965525 := by
  unfold tailWord_8096360
  simp only [CollatzResearch.WordTrace]
  refine ⟨147649254474138971523451267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196865672632185295364601689 147649254474138971523451267)
  ·
    refine ⟨221473881711208457285176901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147649254474138971523451267 221473881711208457285176901)
    ·
      refine ⟨41526352820851585740970669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221473881711208457285176901 41526352820851585740970669)
      ·
        refine ⟨15572382307819344652864001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41526352820851585740970669 15572382307819344652864001)
        ·
          refine ⟨11679286730864508489648001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15572382307819344652864001 11679286730864508489648001)
          ·
            refine ⟨8759465048148381367236001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11679286730864508489648001 8759465048148381367236001)
            ·
              refine ⟨6569598786111286025427001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8759465048148381367236001 6569598786111286025427001)
              ·
                refine ⟨4927199089583464519070251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6569598786111286025427001 4927199089583464519070251)
                ·
                  refine ⟨7390798634375196778605377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927199089583464519070251 7390798634375196778605377)
                  ·
                    refine ⟨5543098975781397583954033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7390798634375196778605377 5543098975781397583954033)
                    ·
                      refine ⟨4157324231836048187965525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543098975781397583954033 4157324231836048187965525)
                      ·
                        rfl

theorem cell23_8096360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_8096360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096360 prefixEnd_8096360 := by exact prefixLift 8096360
  have htrace : WordTrace (prefixWord ++ tailWord_8096360) baseStart_8096360 baseEnd_8096360 := by
    simpa [prefixWord, tailWord_8096360, baseEnd_8096360] using wordTrace_append hprefix tailTrace_8096360
  have hstable : (prefixWord ++ tailWord_8096360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096360).length < 2 ^ (prefixWord ++ tailWord_8096360).sum := by decide
  have hdescent : baseEnd_8096360 < baseStart_8096360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096365 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_8096365 : Nat := 118140960795 + 8096365 * 2 ^ 59
def prefixEnd_8096365 : Nat := 4983230072969 + 3 ^ 40 * 8096365 * 2
def baseEnd_8096365 : Nat := 4157326799239320668403001

theorem tailTrace_8096365 : CollatzResearch.WordTrace tailWord_8096365 prefixEnd_8096365 4157326799239320668403001 := by
  unfold tailWord_8096365
  simp only [CollatzResearch.WordTrace]
  refine ⟨295298691313259828900834549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196865794208839885933889699 295298691313259828900834549)
  ·
    refine ⟨27684252310618108959453239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295298691313259828900834549 27684252310618108959453239)
    ·
      refine ⟨41526378465927163439179859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27684252310618108959453239 41526378465927163439179859)
      ·
        refine ⟨62289567698890745158769789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41526378465927163439179859 62289567698890745158769789)
        ·
          refine ⟨23358587887084029434538671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62289567698890745158769789 23358587887084029434538671)
          ·
            refine ⟨35037881830626044151808007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23358587887084029434538671 35037881830626044151808007)
            ·
              refine ⟨52556822745939066227712011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35037881830626044151808007 52556822745939066227712011)
              ·
                refine ⟨78835234118908599341568017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52556822745939066227712011 78835234118908599341568017)
                ·
                  refine ⟨59126425589181449506176013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78835234118908599341568017 59126425589181449506176013)
                  ·
                    refine ⟨22172409595943043564816005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59126425589181449506176013 22172409595943043564816005)
                    ·
                      refine ⟨4157326799239320668403001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22172409595943043564816005 4157326799239320668403001)
                      ·
                        rfl

theorem cell23_8096365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_8096365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096365 prefixEnd_8096365 := by exact prefixLift 8096365
  have htrace : WordTrace (prefixWord ++ tailWord_8096365) baseStart_8096365 baseEnd_8096365 := by
    simpa [prefixWord, tailWord_8096365, baseEnd_8096365] using wordTrace_append hprefix tailTrace_8096365
  have hstable : (prefixWord ++ tailWord_8096365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096365).length < 2 ^ (prefixWord ++ tailWord_8096365).sum := by decide
  have hdescent : baseEnd_8096365 < baseStart_8096365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096385 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_8096385 : Nat := 118140960795 + 8096385 * 2 ^ 59
def prefixEnd_8096385 : Nat := 4983230072969 + 3 ^ 40 * 8096385 * 2
def baseEnd_8096385 : Nat := 4157337068852410590152909

theorem tailTrace_8096385 : CollatzResearch.WordTrace tailWord_8096385 prefixEnd_8096385 4157337068852410590152909 := by
  unfold tailWord_8096385
  simp only [CollatzResearch.WordTrace]
  refine ⟨295299420773187372316562609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196866280515458248211041739 295299420773187372316562609)
  ·
    refine ⟨221474565579890529237421957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295299420773187372316562609 221474565579890529237421957)
    ·
      refine ⟨41526481046229474232016617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221474565579890529237421957 41526481046229474232016617)
      ·
        refine ⟨31144860784672105674012463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41526481046229474232016617 31144860784672105674012463)
        ·
          refine ⟨46717291177008158511018695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31144860784672105674012463 46717291177008158511018695)
          ·
            refine ⟨70075936765512237766528043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46717291177008158511018695 70075936765512237766528043)
            ·
              refine ⟨105113905148268356649792065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70075936765512237766528043 105113905148268356649792065)
              ·
                refine ⟨78835428861201267487344049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105113905148268356649792065 78835428861201267487344049)
                ·
                  refine ⟨59126571645900950615508037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78835428861201267487344049 59126571645900950615508037)
                  ·
                    refine ⟨11086232183606428240407757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59126571645900950615508037 11086232183606428240407757)
                    ·
                      refine ⟨4157337068852410590152909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11086232183606428240407757 4157337068852410590152909)
                      ·
                        rfl

theorem cell23_8096385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_8096385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096385 prefixEnd_8096385 := by exact prefixLift 8096385
  have htrace : WordTrace (prefixWord ++ tailWord_8096385) baseStart_8096385 baseEnd_8096385 := by
    simpa [prefixWord, tailWord_8096385, baseEnd_8096385] using wordTrace_append hprefix tailTrace_8096385
  have hstable : (prefixWord ++ tailWord_8096385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096385).length < 2 ^ (prefixWord ++ tailWord_8096385).sum := by decide
  have hdescent : baseEnd_8096385 < baseStart_8096385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096433 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 1, 4, 2]
def baseStart_8096433 : Nat := 118140960795 + 8096433 * 2 ^ 59
def prefixEnd_8096433 : Nat := 4983230072969 + 3 ^ 40 * 8096433 * 2
def baseEnd_8096433 : Nat := 4157361715923826402352689

theorem tailTrace_8096433 : CollatzResearch.WordTrace tailWord_8096433 prefixEnd_8096433 4157361715923826402352689 := by
  unfold tailWord_8096433
  simp only [CollatzResearch.WordTrace]
  refine ⟨295301171477013476514309953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196867447651342317676206635 295301171477013476514309953)
  ·
    refine ⟨221475878607760107385732465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295301171477013476514309953 221475878607760107385732465)
    ·
      refine ⟨166106908955820080539299349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221475878607760107385732465 166106908955820080539299349)
      ·
        refine ⟨7786261357304066275279657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166106908955820080539299349 7786261357304066275279657)
        ·
          refine ⟨5839696017978049706459743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7786261357304066275279657 5839696017978049706459743)
          ·
            refine ⟨8759544026967074559689615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5839696017978049706459743 8759544026967074559689615)
            ·
              refine ⟨13139316040450611839534423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759544026967074559689615 13139316040450611839534423)
              ·
                refine ⟨19708974060675917759301635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13139316040450611839534423 19708974060675917759301635)
                ·
                  refine ⟨29563461091013876638952453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19708974060675917759301635 29563461091013876638952453)
                  ·
                    refine ⟨5543148954565101869803585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29563461091013876638952453 5543148954565101869803585)
                    ·
                      refine ⟨4157361715923826402352689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5543148954565101869803585 4157361715923826402352689)
                      ·
                        rfl

theorem cell23_8096433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_8096433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096433 prefixEnd_8096433 := by exact prefixLift 8096433
  have htrace : WordTrace (prefixWord ++ tailWord_8096433) baseStart_8096433 baseEnd_8096433 := by
    simpa [prefixWord, tailWord_8096433, baseEnd_8096433] using wordTrace_append hprefix tailTrace_8096433
  have hstable : (prefixWord ++ tailWord_8096433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096433).length < 2 ^ (prefixWord ++ tailWord_8096433).sum := by decide
  have hdescent : baseEnd_8096433 < baseStart_8096433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096469 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_8096469 : Nat := 118140960795 + 8096469 * 2 ^ 59
def prefixEnd_8096469 : Nat := 4983230072969 + 3 ^ 40 * 8096469 * 2
def baseEnd_8096469 : Nat := 1385793400409129420500841

theorem tailTrace_8096469 : CollatzResearch.WordTrace tailWord_8096469 prefixEnd_8096469 1385793400409129420500841 := by
  unfold tailWord_8096469
  simp only [CollatzResearch.WordTrace]
  refine ⟨295302484504883054662620461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196868323003255369775080307 295302484504883054662620461)
  ·
    refine ⟨110738431689331145498482673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295302484504883054662620461 110738431689331145498482673)
    ·
      refine ⟨83053823766998359123862005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110738431689331145498482673 83053823766998359123862005)
      ·
        refine ⟨7786295978156096167862063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83053823766998359123862005 7786295978156096167862063)
        ·
          refine ⟨11679443967234144251793095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7786295978156096167862063 11679443967234144251793095)
          ·
            refine ⟨17519165950851216377689643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11679443967234144251793095 17519165950851216377689643)
            ·
              refine ⟨26278748926276824566534465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17519165950851216377689643 26278748926276824566534465)
              ·
                refine ⟨19709061694707618424900849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26278748926276824566534465 19709061694707618424900849)
                ·
                  refine ⟨14781796271030713818675637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19709061694707618424900849 14781796271030713818675637)
                  ·
                    refine ⟨1385793400409129420500841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14781796271030713818675637 1385793400409129420500841)
                    ·
                      rfl

theorem cell23_8096469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_8096469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096469 prefixEnd_8096469 := by exact prefixLift 8096469
  have htrace : WordTrace (prefixWord ++ tailWord_8096469) baseStart_8096469 baseEnd_8096469 := by
    simpa [prefixWord, tailWord_8096469, baseEnd_8096469] using wordTrace_append hprefix tailTrace_8096469
  have hstable : (prefixWord ++ tailWord_8096469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096469).length < 2 ^ (prefixWord ++ tailWord_8096469).sum := by decide
  have hdescent : baseEnd_8096469 < baseStart_8096469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096472 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_8096472 : Nat := 118140960795 + 8096472 * 2 ^ 59
def prefixEnd_8096472 : Nat := 4983230072969 + 3 ^ 40 * 8096472 * 2
def baseEnd_8096472 : Nat := 4157381741669351749765009

theorem tailTrace_8096472 : CollatzResearch.WordTrace tailWord_8096472 prefixEnd_8096472 4157381741669351749765009 := by
  unfold tailWord_8096472
  simp only [CollatzResearch.WordTrace]
  refine ⟨147651296961936093087489835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196868395949248124116653113 147651296961936093087489835)
  ·
    refine ⟨221476945442904139631234753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147651296961936093087489835 221476945442904139631234753)
    ·
      refine ⟨166107709082178104723426065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221476945442904139631234753 166107709082178104723426065)
      ·
        refine ⟨124580781811633578542569549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166107709082178104723426065 124580781811633578542569549)
        ·
          refine ⟨46717793179362591953463581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124580781811633578542569549 46717793179362591953463581)
          ·
            refine ⟨17519172442260971982548843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46717793179362591953463581 17519172442260971982548843)
            ·
              refine ⟨26278758663391457973823265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17519172442260971982548843 26278758663391457973823265)
              ·
                refine ⟨19709068997543593480367449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26278758663391457973823265 19709068997543593480367449)
                ·
                  refine ⟨14781801748157695110275587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19709068997543593480367449 14781801748157695110275587)
                  ·
                    refine ⟨22172702622236542665413381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14781801748157695110275587 22172702622236542665413381)
                    ·
                      refine ⟨4157381741669351749765009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22172702622236542665413381 4157381741669351749765009)
                      ·
                        rfl

theorem cell23_8096472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_8096472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096472 prefixEnd_8096472 := by exact prefixLift 8096472
  have htrace : WordTrace (prefixWord ++ tailWord_8096472) baseStart_8096472 baseEnd_8096472 := by
    simpa [prefixWord, tailWord_8096472, baseEnd_8096472] using wordTrace_append hprefix tailTrace_8096472
  have hstable : (prefixWord ++ tailWord_8096472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096472).length < 2 ^ (prefixWord ++ tailWord_8096472).sum := by decide
  have hdescent : baseEnd_8096472 < baseStart_8096472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096505 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 3]
def baseStart_8096505 : Nat := 118140960795 + 8096505 * 2 ^ 59
def prefixEnd_8096505 : Nat := 4983230072969 + 3 ^ 40 * 8096505 * 2
def baseEnd_8096505 : Nat := 4157398686530950120652357

theorem tailTrace_8096505 : CollatzResearch.WordTrace tailWord_8096505 prefixEnd_8096505 4157398686530950120652357 := by
  unfold tailWord_8096505
  simp only [CollatzResearch.WordTrace]
  refine ⟨295303797532752632810930969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196869198355168421873953979 295303797532752632810930969)
  ·
    refine ⟨221477848149564474608198227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295303797532752632810930969 221477848149564474608198227)
    ·
      refine ⟨332216772224346711912297341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221477848149564474608198227 332216772224346711912297341)
      ·
        refine ⟨124581289584130016967111503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332216772224346711912297341 124581289584130016967111503)
        ·
          refine ⟨186871934376195025450667255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124581289584130016967111503 186871934376195025450667255)
          ·
            refine ⟨280307901564292538176000883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186871934376195025450667255 280307901564292538176000883)
            ·
              refine ⟨420461852346438807264001325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280307901564292538176000883 420461852346438807264001325)
              ·
                refine ⟨157673194629914552724000497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420461852346438807264001325 157673194629914552724000497)
                ·
                  refine ⟨118254895972435914543000373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157673194629914552724000497 118254895972435914543000373)
                  ·
                    refine ⟨11086396497415866988406285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118254895972435914543000373 11086396497415866988406285)
                    ·
                      refine ⟨4157398686530950120652357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11086396497415866988406285 4157398686530950120652357)
                      ·
                        rfl

theorem cell23_8096505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_8096505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096505 prefixEnd_8096505 := by exact prefixLift 8096505
  have htrace : WordTrace (prefixWord ++ tailWord_8096505) baseStart_8096505 baseEnd_8096505 := by
    simpa [prefixWord, tailWord_8096505, baseEnd_8096505] using wordTrace_append hprefix tailTrace_8096505
  have hstable : (prefixWord ++ tailWord_8096505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096505).length < 2 ^ (prefixWord ++ tailWord_8096505).sum := by decide
  have hdescent : baseEnd_8096505 < baseStart_8096505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8096555 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 1, 6]
def baseStart_8096555 : Nat := 118140960795 + 8096555 * 2 ^ 59
def prefixEnd_8096555 : Nat := 4983230072969 + 3 ^ 40 * 8096555 * 2
def baseEnd_8096555 : Nat := 1385808120187891641675709

theorem tailTrace_8096555 : CollatzResearch.WordTrace tailWord_8096555 prefixEnd_8096555 1385808120187891641675709 := by
  unfold tailWord_8096555
  simp only [CollatzResearch.WordTrace]
  refine ⟨295305621182571491350251119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196870414121714327566834079 295305621182571491350251119)
  ·
    refine ⟨442958431773857237025376679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295305621182571491350251119 442958431773857237025376679)
    ·
      refine ⟨664437647660785855538065019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442958431773857237025376679 664437647660785855538065019)
      ·
        refine ⟨996656471491178783307097529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664437647660785855538065019 996656471491178783307097529)
        ·
          refine ⟨747492353618384087480323147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996656471491178783307097529 747492353618384087480323147)
          ·
            refine ⟨1121238530427576131220484721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747492353618384087480323147 1121238530427576131220484721)
            ·
              refine ⟨840928897820682098415363541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121238530427576131220484721 840928897820682098415363541)
              ·
                refine ⟨19709271042672236681610083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 840928897820682098415363541 19709271042672236681610083)
                ·
                  refine ⟨29563906564008355022415125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19709271042672236681610083 29563906564008355022415125)
                  ·
                    refine ⟨1385808120187891641675709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29563906564008355022415125 1385808120187891641675709)
                    ·
                      rfl

theorem cell23_8096555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 6].length) (baseStart_8096555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8096555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8096555 prefixEnd_8096555 := by exact prefixLift 8096555
  have htrace : WordTrace (prefixWord ++ tailWord_8096555) baseStart_8096555 baseEnd_8096555 := by
    simpa [prefixWord, tailWord_8096555, baseEnd_8096555] using wordTrace_append hprefix tailTrace_8096555
  have hstable : (prefixWord ++ tailWord_8096555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8096555).length < 2 ^ (prefixWord ++ tailWord_8096555).sum := by decide
  have hdescent : baseEnd_8096555 < baseStart_8096555 := by decide
  rcases family_descends (prefixWord ++ tailWord_8096555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
