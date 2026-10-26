import V185TrunkScan23Chunk1023

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6062695 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_6062695 : Nat := 118140960795 + 6062695 * 2 ^ 59
def prefixEnd_6062695 : Nat := 4983230072969 + 3 ^ 40 * 6062695 * 2
def baseEnd_6062695 : Nat := 3113076596610262411630679

theorem tailTrace_6062695 : CollatzResearch.WordTrace tailWord_6062695 prefixEnd_6062695 3113076596610262411630679 := by
  unfold tailWord_6062695
  simp only [CollatzResearch.WordTrace]
  refine ⟨221124652770898915716645539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147416435180599277144430359 221124652770898915716645539)
  ·
    refine ⟨331686979156348373574968309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221124652770898915716645539 331686979156348373574968309)
    ·
      refine ⟨31095654295907660022653279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 331686979156348373574968309 31095654295907660022653279)
      ·
        refine ⟨46643481443861490033979919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31095654295907660022653279 46643481443861490033979919)
        ·
          refine ⟨69965222165792235050969879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46643481443861490033979919 69965222165792235050969879)
          ·
            refine ⟨104947833248688352576454819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69965222165792235050969879 104947833248688352576454819)
            ·
              refine ⟨157421749873032528864682229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104947833248688352576454819 157421749873032528864682229)
              ·
                refine ⟨14758289050596799581063959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157421749873032528864682229 14758289050596799581063959)
                ·
                  refine ⟨22137433575895199371595939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14758289050596799581063959 22137433575895199371595939)
                  ·
                    refine ⟨33206150363842799057393909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22137433575895199371595939 33206150363842799057393909)
                    ·
                      refine ⟨3113076596610262411630679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33206150363842799057393909 3113076596610262411630679)
                      ·
                        rfl

theorem cell23_6062695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_6062695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062695 prefixEnd_6062695 := by exact prefixLift 6062695
  have htrace : WordTrace (prefixWord ++ tailWord_6062695) baseStart_6062695 baseEnd_6062695 := by
    simpa [prefixWord, tailWord_6062695, baseEnd_6062695] using wordTrace_append hprefix tailTrace_6062695
  have hstable : (prefixWord ++ tailWord_6062695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062695).length < 2 ^ (prefixWord ++ tailWord_6062695).sum := by decide
  have hdescent : baseEnd_6062695 < baseStart_6062695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062795 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 4]
def baseStart_6062795 : Nat := 118140960795 + 6062795 * 2 ^ 59
def prefixEnd_6062795 : Nat := 4983230072969 + 3 ^ 40 * 6062795 * 2
def baseEnd_6062795 : Nat := 3113127944675712020380219

theorem tailTrace_6062795 : CollatzResearch.WordTrace tailWord_6062795 prefixEnd_6062795 3113127944675712020380219 := by
  unfold tailWord_6062795
  simp only [CollatzResearch.WordTrace]
  refine ⟨221128300070536632795285839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147418866713691088530190559 221128300070536632795285839)
  ·
    refine ⟨331692450105804949192928759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221128300070536632795285839 331692450105804949192928759)
    ·
      refine ⟨497538675158707423789393139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331692450105804949192928759 497538675158707423789393139)
      ·
        refine ⟨746308012738061135684089709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497538675158707423789393139 746308012738061135684089709)
        ·
          refine ⟨279865504776772925881533641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 746308012738061135684089709 279865504776772925881533641)
          ·
            refine ⟨209899128582579694411150231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279865504776772925881533641 209899128582579694411150231)
            ·
              refine ⟨314848692873869541616725347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209899128582579694411150231 314848692873869541616725347)
              ·
                refine ⟨472273039310804312425088021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314848692873869541616725347 472273039310804312425088021)
                ·
                  refine ⟨22137798717693952144926001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 472273039310804312425088021 22137798717693952144926001)
                  ·
                    refine ⟨16603349038270464108694501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22137798717693952144926001 16603349038270464108694501)
                    ·
                      refine ⟨3113127944675712020380219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16603349038270464108694501 3113127944675712020380219)
                      ·
                        rfl

theorem cell23_6062795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 4].length) (baseStart_6062795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062795 prefixEnd_6062795 := by exact prefixLift 6062795
  have htrace : WordTrace (prefixWord ++ tailWord_6062795) baseStart_6062795 baseEnd_6062795 := by
    simpa [prefixWord, tailWord_6062795, baseEnd_6062795] using wordTrace_append hprefix tailTrace_6062795
  have hstable : (prefixWord ++ tailWord_6062795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062795).length < 2 ^ (prefixWord ++ tailWord_6062795).sum := by decide
  have hdescent : baseEnd_6062795 < baseStart_6062795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062832 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 3]
def baseStart_6062832 : Nat := 118140960795 + 6062832 * 2 ^ 59
def prefixEnd_6062832 : Nat := 4983230072969 + 3 ^ 40 * 6062832 * 2
def baseEnd_6062832 : Nat := 3113146943459928375617549

theorem tailTrace_6062832 : CollatzResearch.WordTrace tailWord_6062832 prefixEnd_6062832 3113146943459928375617549 := by
  unfold tailWord_6062832
  simp only [CollatzResearch.WordTrace]
  refine ⟨110564824785701294057191375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147419766380935058742921833 110564824785701294057191375)
  ·
    refine ⟨165847237178551941085787063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110564824785701294057191375 165847237178551941085787063)
    ·
      refine ⟨248770855767827911628680595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165847237178551941085787063 248770855767827911628680595)
      ·
        refine ⟨373156283651741867443020893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248770855767827911628680595 373156283651741867443020893)
        ·
          refine ⟨139933606369403200291132835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373156283651741867443020893 139933606369403200291132835)
          ·
            refine ⟨209900409554104800436699253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139933606369403200291132835 209900409554104800436699253)
            ·
              refine ⟨19678163395697325040940555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209900409554104800436699253 19678163395697325040940555)
              ·
                refine ⟨29517245093545987561410833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19678163395697325040940555 29517245093545987561410833)
                ·
                  refine ⟨22137933820159490671058125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29517245093545987561410833 22137933820159490671058125)
                  ·
                    refine ⟨8301725182559809001646797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22137933820159490671058125 8301725182559809001646797)
                    ·
                      refine ⟨3113146943459928375617549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8301725182559809001646797 3113146943459928375617549)
                      ·
                        rfl

theorem cell23_6062832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_6062832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062832 prefixEnd_6062832 := by exact prefixLift 6062832
  have htrace : WordTrace (prefixWord ++ tailWord_6062832) baseStart_6062832 baseEnd_6062832 := by
    simpa [prefixWord, tailWord_6062832, baseEnd_6062832] using wordTrace_append hprefix tailTrace_6062832
  have hstable : (prefixWord ++ tailWord_6062832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062832).length < 2 ^ (prefixWord ++ tailWord_6062832).sum := by decide
  have hdescent : baseEnd_6062832 < baseStart_6062832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062835 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 1, 7]
def baseStart_6062835 : Nat := 118140960795 + 6062835 * 2 ^ 59
def prefixEnd_6062835 : Nat := 4983230072969 + 3 ^ 40 * 6062835 * 2
def baseEnd_6062835 : Nat := 1037716161300630621293345

theorem tailTrace_6062835 : CollatzResearch.WordTrace tailWord_6062835 prefixEnd_6062835 1037716161300630621293345 := by
  unfold tailWord_6062835
  simp only [CollatzResearch.WordTrace]
  refine ⟨221129758990391719626741959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147419839326927813084494639 221129758990391719626741959)
  ·
    refine ⟨331694638485587579440112939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221129758990391719626741959 331694638485587579440112939)
    ·
      refine ⟨497541957728381369160169409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331694638485587579440112939 497541957728381369160169409)
      ·
        refine ⟨373156468296286026870127057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497541957728381369160169409 373156468296286026870127057)
        ·
          refine ⟨279867351222214520152595293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373156468296286026870127057 279867351222214520152595293)
          ·
            refine ⟨104950256708330445057223235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279867351222214520152595293 104950256708330445057223235)
            ·
              refine ⟨157425385062495667585834853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104950256708330445057223235 157425385062495667585834853)
              ·
                refine ⟨29517259699217937672344035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157425385062495667585834853 29517259699217937672344035)
                ·
                  refine ⟨44275889548826906508516053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29517259699217937672344035 44275889548826906508516053)
                  ·
                    refine ⟨1037716161300630621293345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44275889548826906508516053 1037716161300630621293345)
                    ·
                      rfl

theorem cell23_6062835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 7].length) (baseStart_6062835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062835 prefixEnd_6062835 := by exact prefixLift 6062835
  have htrace : WordTrace (prefixWord ++ tailWord_6062835) baseStart_6062835 baseEnd_6062835 := by
    simpa [prefixWord, tailWord_6062835, baseEnd_6062835] using wordTrace_append hprefix tailTrace_6062835
  have hstable : (prefixWord ++ tailWord_6062835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062835).length < 2 ^ (prefixWord ++ tailWord_6062835).sum := by decide
  have hdescent : baseEnd_6062835 < baseStart_6062835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062852 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_6062852 : Nat := 118140960795 + 6062852 * 2 ^ 59
def prefixEnd_6062852 : Nat := 4983230072969 + 3 ^ 40 * 6062852 * 2
def baseEnd_6062852 : Nat := 1037719071024339432455819

theorem tailTrace_6062852 : CollatzResearch.WordTrace tailWord_6062852 prefixEnd_6062852 1037719071024339432455819 := by
  unfold tailWord_6062852
  simp only [CollatzResearch.WordTrace]
  refine ⟨110565189515665065765055405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147420252687553421020073873 110565189515665065765055405)
  ·
    refine ⟨41461946068374399661895777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110565189515665065765055405 41461946068374399661895777)
    ·
      refine ⟨31096459551280799746421833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41461946068374399661895777 31096459551280799746421833)
      ·
        refine ⟨23322344663460599809816375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31096459551280799746421833 23322344663460599809816375)
        ·
          refine ⟨34983516995190899714724563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23322344663460599809816375 34983516995190899714724563)
          ·
            refine ⟨52475275492786349572086845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34983516995190899714724563 52475275492786349572086845)
            ·
              refine ⟨19678228309794881089532567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52475275492786349572086845 19678228309794881089532567)
              ·
                refine ⟨29517342464692321634298851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19678228309794881089532567 29517342464692321634298851)
                ·
                  refine ⟨44276013697038482451448277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29517342464692321634298851 44276013697038482451448277)
                  ·
                    refine ⟨1037719071024339432455819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44276013697038482451448277 1037719071024339432455819)
                    ·
                      rfl

theorem cell23_6062852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_6062852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062852 prefixEnd_6062852 := by exact prefixLift 6062852
  have htrace : WordTrace (prefixWord ++ tailWord_6062852) baseStart_6062852 baseEnd_6062852 := by
    simpa [prefixWord, tailWord_6062852, baseEnd_6062852] using wordTrace_append hprefix tailTrace_6062852
  have hstable : (prefixWord ++ tailWord_6062852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062852).length < 2 ^ (prefixWord ++ tailWord_6062852).sum := by decide
  have hdescent : baseEnd_6062852 < baseStart_6062852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062872 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6062872 : Nat := 118140960795 + 6062872 * 2 ^ 59
def prefixEnd_6062872 : Nat := 4983230072969 + 3 ^ 40 * 6062872 * 2
def baseEnd_6062872 : Nat := 3113167482686108219117365

theorem tailTrace_6062872 : CollatzResearch.WordTrace tailWord_6062872 prefixEnd_6062872 3113167482686108219117365 := by
  unfold tailWord_6062872
  simp only [CollatzResearch.WordTrace]
  refine ⟨110565554245628837472919435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147420738994171783297225913 110565554245628837472919435)
  ·
    refine ⟨165848331368443256209379153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110565554245628837472919435 165848331368443256209379153)
    ·
      refine ⟨124386248526332442157034365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165848331368443256209379153 124386248526332442157034365)
      ·
        refine ⟨46644843197374665808887887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124386248526332442157034365 46644843197374665808887887)
        ·
          refine ⟨69967264796061998713331831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46644843197374665808887887 69967264796061998713331831)
          ·
            refine ⟨104950897194092998069997747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69967264796061998713331831 104950897194092998069997747)
            ·
              refine ⟨157426345791139497104996621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104950897194092998069997747 157426345791139497104996621)
              ·
                refine ⟨59034879671677311414373733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157426345791139497104996621 59034879671677311414373733)
                ·
                  refine ⟨11069039938439495890195075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59034879671677311414373733 11069039938439495890195075)
                  ·
                    refine ⟨16603559907659243835292613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11069039938439495890195075 16603559907659243835292613)
                    ·
                      refine ⟨3113167482686108219117365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16603559907659243835292613 3113167482686108219117365)
                      ·
                        rfl

theorem cell23_6062872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6062872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062872 prefixEnd_6062872 := by exact prefixLift 6062872
  have htrace : WordTrace (prefixWord ++ tailWord_6062872) baseStart_6062872 baseEnd_6062872 := by
    simpa [prefixWord, tailWord_6062872, baseEnd_6062872] using wordTrace_append hprefix tailTrace_6062872
  have hstable : (prefixWord ++ tailWord_6062872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062872).length < 2 ^ (prefixWord ++ tailWord_6062872).sum := by decide
  have hdescent : baseEnd_6062872 < baseStart_6062872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062892 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_6062892 : Nat := 118140960795 + 6062892 * 2 ^ 59
def prefixEnd_6062892 : Nat := 4983230072969 + 3 ^ 40 * 6062892 * 2
def baseEnd_6062892 : Nat := 3113177752299198140867273

theorem tailTrace_6062892 : CollatzResearch.WordTrace tailWord_6062892 prefixEnd_6062892 3113177752299198140867273 := by
  unfold tailWord_6062892
  simp only [CollatzResearch.WordTrace]
  refine ⟨110565918975592609180783465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147421225300790145574377953 110565918975592609180783465)
  ·
    refine ⟨82924439231694456885587599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110565918975592609180783465 82924439231694456885587599)
    ·
      refine ⟨124386658847541685328381399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82924439231694456885587599 124386658847541685328381399)
      ·
        refine ⟨186579988271312527992572099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124386658847541685328381399 186579988271312527992572099)
        ·
          refine ⟨279869982406968791988858149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186579988271312527992572099 279869982406968791988858149)
          ·
            refine ⟨52475621701306648497910903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279869982406968791988858149 52475621701306648497910903)
            ·
              refine ⟨78713432551959972746866355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52475621701306648497910903 78713432551959972746866355)
              ·
                refine ⟨118070148827939959120299533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78713432551959972746866355 118070148827939959120299533)
                ·
                  refine ⟨44276305810477484670112325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118070148827939959120299533 44276305810477484670112325)
                  ·
                    refine ⟨8301807339464528375646061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44276305810477484670112325 8301807339464528375646061)
                    ·
                      refine ⟨3113177752299198140867273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8301807339464528375646061 3113177752299198140867273)
                      ·
                        rfl

theorem cell23_6062892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_6062892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062892 prefixEnd_6062892 := by exact prefixLift 6062892
  have htrace : WordTrace (prefixWord ++ tailWord_6062892) baseStart_6062892 baseEnd_6062892 := by
    simpa [prefixWord, tailWord_6062892, baseEnd_6062892] using wordTrace_append hprefix tailTrace_6062892
  have hstable : (prefixWord ++ tailWord_6062892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062892).length < 2 ^ (prefixWord ++ tailWord_6062892).sum := by decide
  have hdescent : baseEnd_6062892 < baseStart_6062892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062895 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 12]
def baseStart_6062895 : Nat := 118140960795 + 6062895 * 2 ^ 59
def prefixEnd_6062895 : Nat := 4983230072969 + 3 ^ 40 * 6062895 * 2
def baseEnd_6062895 : Nat := 345908810304573514347751

theorem tailTrace_6062895 : CollatzResearch.WordTrace tailWord_6062895 prefixEnd_6062895 345908810304573514347751 := by
  unfold tailWord_6062895
  simp only [CollatzResearch.WordTrace]
  refine ⟨221131947370174349873926139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147421298246782899915950759 221131947370174349873926139)
  ·
    refine ⟨331697921055261524810889209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221131947370174349873926139 331697921055261524810889209)
    ·
      refine ⟨248773440791446143608166907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331697921055261524810889209 248773440791446143608166907)
      ·
        refine ⟨373160161187169215412250361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248773440791446143608166907 373160161187169215412250361)
        ·
          refine ⟨279870120890376911559187771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373160161187169215412250361 279870120890376911559187771)
          ·
            refine ⟨419805181335565367338781657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279870120890376911559187771 419805181335565367338781657)
            ·
              refine ⟨314853886001674025504086243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419805181335565367338781657 314853886001674025504086243)
              ·
                refine ⟨472280829002511038256129365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314853886001674025504086243 472280829002511038256129365)
                ·
                  refine ⟨345908810304573514347751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 472280829002511038256129365 345908810304573514347751)
                  ·
                    rfl

theorem cell23_6062895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 12].length) (baseStart_6062895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062895 prefixEnd_6062895 := by exact prefixLift 6062895
  have htrace : WordTrace (prefixWord ++ tailWord_6062895) baseStart_6062895 baseEnd_6062895 := by
    simpa [prefixWord, tailWord_6062895, baseEnd_6062895] using wordTrace_append hprefix tailTrace_6062895
  have hstable : (prefixWord ++ tailWord_6062895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062895).length < 2 ^ (prefixWord ++ tailWord_6062895).sum := by decide
  have hdescent : baseEnd_6062895 < baseStart_6062895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062899 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 3, 4]
def baseStart_6062899 : Nat := 118140960795 + 6062899 * 2 ^ 59
def prefixEnd_6062899 : Nat := 4983230072969 + 3 ^ 40 * 6062899 * 2
def baseEnd_6062899 : Nat := 1037727115554593204493247

theorem tailTrace_6062899 : CollatzResearch.WordTrace tailWord_6062899 prefixEnd_6062899 1037727115554593204493247 := by
  unfold tailWord_6062899
  simp only [CollatzResearch.WordTrace]
  refine ⟨221132093262159858557071751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147421395508106572371381167 221132093262159858557071751)
  ·
    refine ⟨331698139893239787835607627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221132093262159858557071751 331698139893239787835607627)
    ·
      refine ⟨497547209839859681753411441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331698139893239787835607627 497547209839859681753411441)
      ·
        refine ⟨373160407379894761315058581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497547209839859681753411441 373160407379894761315058581)
        ·
          refine ⟨17491894095932566936643371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 373160407379894761315058581 17491894095932566936643371)
          ·
            refine ⟨26237841143898850404965057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17491894095932566936643371 26237841143898850404965057)
            ·
              refine ⟨19678380857924137803723793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26237841143898850404965057 19678380857924137803723793)
              ·
                refine ⟨14758785643443103352792845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19678380857924137803723793 14758785643443103352792845)
                ·
                  refine ⟨5534544616291163757297317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14758785643443103352792845 5534544616291163757297317)
                  ·
                    refine ⟨1037727115554593204493247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5534544616291163757297317 1037727115554593204493247)
                    ·
                      rfl

theorem cell23_6062899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 4].length) (baseStart_6062899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062899 prefixEnd_6062899 := by exact prefixLift 6062899
  have htrace : WordTrace (prefixWord ++ tailWord_6062899) baseStart_6062899 baseEnd_6062899 := by
    simpa [prefixWord, tailWord_6062899, baseEnd_6062899] using wordTrace_append hprefix tailTrace_6062899
  have hstable : (prefixWord ++ tailWord_6062899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062899).length < 2 ^ (prefixWord ++ tailWord_6062899).sum := by decide
  have hdescent : baseEnd_6062899 < baseStart_6062899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062933 : List Nat := [1, 3, 2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_6062933 : Nat := 118140960795 + 6062933 * 2 ^ 59
def prefixEnd_6062933 : Nat := 4983230072969 + 3 ^ 40 * 6062933 * 2
def baseEnd_6062933 : Nat := 1037732935002010826818195

theorem tailTrace_6062933 : CollatzResearch.WordTrace tailWord_6062933 prefixEnd_6062933 1037732935002010826818195 := by
  unfold tailWord_6062933
  simp only [CollatzResearch.WordTrace]
  refine ⟨221133333344036682363809453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147422222229357788242539635 221133333344036682363809453)
  ·
    refine ⟨82925000004013755886428545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221133333344036682363809453 82925000004013755886428545)
    ·
      refine ⟨62193750003010316914821409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82925000004013755886428545 62193750003010316914821409)
      ·
        refine ⟨46645312502257737686116057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62193750003010316914821409 46645312502257737686116057)
        ·
          refine ⟨34983984376693303264587043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46645312502257737686116057 34983984376693303264587043)
          ·
            refine ⟨52475976565039954896880565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34983984376693303264587043 52475976565039954896880565)
            ·
              refine ⟨4919622802972495771582553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52475976565039954896880565 4919622802972495771582553)
              ·
                refine ⟨3689717102229371828686915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4919622802972495771582553 3689717102229371828686915)
                ·
                  refine ⟨5534575653344057743030373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689717102229371828686915 5534575653344057743030373)
                  ·
                    refine ⟨1037732935002010826818195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5534575653344057743030373 1037732935002010826818195)
                    ·
                      rfl

theorem cell23_6062933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_6062933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062933 prefixEnd_6062933 := by exact prefixLift 6062933
  have htrace : WordTrace (prefixWord ++ tailWord_6062933) baseStart_6062933 baseEnd_6062933 := by
    simpa [prefixWord, tailWord_6062933, baseEnd_6062933] using wordTrace_append hprefix tailTrace_6062933
  have hstable : (prefixWord ++ tailWord_6062933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062933).length < 2 ^ (prefixWord ++ tailWord_6062933).sum := by decide
  have hdescent : baseEnd_6062933 < baseStart_6062933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062946 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 6]
def baseStart_6062946 : Nat := 118140960795 + 6062946 * 2 ^ 59
def prefixEnd_6062946 : Nat := 4983230072969 + 3 ^ 40 * 6062946 * 2
def baseEnd_6062946 : Nat := 345911720028282325510225

theorem tailTrace_6062946 : CollatzResearch.WordTrace tailWord_6062946 prefixEnd_6062946 345911720028282325510225 := by
  unfold tailWord_6062946
  simp only [CollatzResearch.WordTrace]
  refine ⟨55283451873247396396008173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147422538328659723722688461 55283451873247396396008173)
  ·
    refine ⟨20731294452467773648503065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55283451873247396396008173 20731294452467773648503065)
    ·
      refine ⟨15548470839350830236377299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20731294452467773648503065 15548470839350830236377299)
      ·
        refine ⟨23322706259026245354565949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15548470839350830236377299 23322706259026245354565949)
        ·
          refine ⟨8746014847134842007962231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23322706259026245354565949 8746014847134842007962231)
          ·
            refine ⟨13119022270702263011943347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8746014847134842007962231 13119022270702263011943347)
            ·
              refine ⟨19678533406053394517915021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13119022270702263011943347 19678533406053394517915021)
              ·
                refine ⟨7379450027270022944218133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19678533406053394517915021 7379450027270022944218133)
                ·
                  refine ⟨345911720028282325510225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7379450027270022944218133 345911720028282325510225)
                  ·
                    rfl

theorem cell23_6062946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_6062946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062946 prefixEnd_6062946 := by exact prefixLift 6062946
  have htrace : WordTrace (prefixWord ++ tailWord_6062946) baseStart_6062946 baseEnd_6062946 := by
    simpa [prefixWord, tailWord_6062946, baseEnd_6062946] using wordTrace_append hprefix tailTrace_6062946
  have hstable : (prefixWord ++ tailWord_6062946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062946).length < 2 ^ (prefixWord ++ tailWord_6062946).sum := by decide
  have hdescent : baseEnd_6062946 < baseStart_6062946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062949 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 3, 5, 2]
def baseStart_6062949 : Nat := 118140960795 + 6062949 * 2 ^ 59
def prefixEnd_6062949 : Nat := 4983230072969 + 3 ^ 40 * 6062949 * 2
def baseEnd_6062949 : Nat := 3113207020696504417854511

theorem tailTrace_6062949 : CollatzResearch.WordTrace tailWord_6062949 prefixEnd_6062949 3113207020696504417854511 := by
  unfold tailWord_6062949
  simp only [CollatzResearch.WordTrace]
  refine ⟨221133916911978717096391901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147422611274652478064261267 221133916911978717096391901)
  ·
    refine ⟨82925218841992018911146963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221133916911978717096391901 82925218841992018911146963)
    ·
      refine ⟨124387828262988028366720445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82925218841992018911146963 124387828262988028366720445)
      ·
        refine ⟨46645435598620510637520167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124387828262988028366720445 46645435598620510637520167)
        ·
          refine ⟨69968153397930765956280251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46645435598620510637520167 69968153397930765956280251)
          ·
            refine ⟨104952230096896148934420377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69968153397930765956280251 104952230096896148934420377)
            ·
              refine ⟨78714172572672111700815283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104952230096896148934420377 78714172572672111700815283)
              ·
                refine ⟨118071258859008167551222925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78714172572672111700815283 118071258859008167551222925)
                ·
                  refine ⟨44276722072128062831708597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118071258859008167551222925 44276722072128062831708597)
                  ·
                    refine ⟨4150942694262005890472681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44276722072128062831708597 4150942694262005890472681)
                    ·
                      refine ⟨3113207020696504417854511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4150942694262005890472681 3113207020696504417854511)
                      ·
                        rfl

theorem cell23_6062949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_6062949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062949 prefixEnd_6062949 := by exact prefixLift 6062949
  have htrace : WordTrace (prefixWord ++ tailWord_6062949) baseStart_6062949 baseEnd_6062949 := by
    simpa [prefixWord, tailWord_6062949, baseEnd_6062949] using wordTrace_append hprefix tailTrace_6062949
  have hstable : (prefixWord ++ tailWord_6062949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062949).length < 2 ^ (prefixWord ++ tailWord_6062949).sum := by decide
  have hdescent : baseEnd_6062949 < baseStart_6062949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062999 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_6062999 : Nat := 118140960795 + 6062999 * 2 ^ 59
def prefixEnd_6062999 : Nat := 4983230072969 + 3 ^ 40 * 6062999 * 2
def baseEnd_6062999 : Nat := 3113232694729229222229281

theorem tailTrace_6062999 : CollatzResearch.WordTrace tailWord_6062999 prefixEnd_6062999 3113232694729229222229281 := by
  unfold tailWord_6062999
  simp only [CollatzResearch.WordTrace]
  refine ⟨221135740561797575635712051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147423827041198383757141367 221135740561797575635712051)
  ·
    refine ⟨331703610842696363453568077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221135740561797575635712051 331703610842696363453568077)
    ·
      refine ⟨124388854066011136295088029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331703610842696363453568077 124388854066011136295088029)
      ·
        refine ⟨46645820274754176110658011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124388854066011136295088029 46645820274754176110658011)
        ·
          refine ⟨69968730412131264165987017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46645820274754176110658011 69968730412131264165987017)
          ·
            refine ⟨52476547809098448124490263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69968730412131264165987017 52476547809098448124490263)
            ·
              refine ⟨78714821713647672186735395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52476547809098448124490263 78714821713647672186735395)
              ·
                refine ⟨118072232570471508280103093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78714821713647672186735395 118072232570471508280103093)
                ·
                  refine ⟨11069271803481703901259665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118072232570471508280103093 11069271803481703901259665)
                  ·
                    refine ⟨8301953852611277925944749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11069271803481703901259665 8301953852611277925944749)
                    ·
                      refine ⟨3113232694729229222229281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8301953852611277925944749 3113232694729229222229281)
                      ·
                        rfl

theorem cell23_6062999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_6062999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062999 prefixEnd_6062999 := by exact prefixLift 6062999
  have htrace : WordTrace (prefixWord ++ tailWord_6062999) baseStart_6062999 baseEnd_6062999 := by
    simpa [prefixWord, tailWord_6062999, baseEnd_6062999] using wordTrace_append hprefix tailTrace_6062999
  have hstable : (prefixWord ++ tailWord_6062999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062999).length < 2 ^ (prefixWord ++ tailWord_6062999).sum := by decide
  have hdescent : baseEnd_6062999 < baseStart_6062999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063033 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 1, 2, 3]
def baseStart_6063033 : Nat := 118140960795 + 6063033 * 2 ^ 59
def prefixEnd_6063033 : Nat := 4983230072969 + 3 ^ 40 * 6063033 * 2
def baseEnd_6063033 : Nat := 3113250153071482089204125

theorem tailTrace_6063033 : CollatzResearch.WordTrace tailWord_6063033 prefixEnd_6063033 3113250153071482089204125 := by
  unfold tailWord_6063033
  simp only [CollatzResearch.WordTrace]
  refine ⟨221136980643674399442449753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147424653762449599628299835 221136980643674399442449753)
  ·
    refine ⟨165852735482755799581837315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221136980643674399442449753 165852735482755799581837315)
    ·
      refine ⟨248779103224133699372755973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165852735482755799581837315 248779103224133699372755973)
      ·
        refine ⟨46646081854525068632391745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248779103224133699372755973 46646081854525068632391745)
        ·
          refine ⟨34984561390893801474293809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46646081854525068632391745 34984561390893801474293809)
          ·
            refine ⟨26238421043170351105720357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34984561390893801474293809 26238421043170351105720357)
            ·
              refine ⟨4919703945594440832322567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26238421043170351105720357 4919703945594440832322567)
              ·
                refine ⟨7379555918391661248483851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919703945594440832322567 7379555918391661248483851)
                ·
                  refine ⟨11069333877587491872725777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7379555918391661248483851 11069333877587491872725777)
                  ·
                    refine ⟨8302000408190618904544333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11069333877587491872725777 8302000408190618904544333)
                    ·
                      refine ⟨3113250153071482089204125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8302000408190618904544333 3113250153071482089204125)
                      ·
                        rfl

theorem cell23_6063033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_6063033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063033 prefixEnd_6063033 := by exact prefixLift 6063033
  have htrace : WordTrace (prefixWord ++ tailWord_6063033) baseStart_6063033 baseEnd_6063033 := by
    simpa [prefixWord, tailWord_6063033, baseEnd_6063033] using wordTrace_append hprefix tailTrace_6063033
  have hstable : (prefixWord ++ tailWord_6063033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063033).length < 2 ^ (prefixWord ++ tailWord_6063033).sum := by decide
  have hdescent : baseEnd_6063033 < baseStart_6063033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063089 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_6063089 : Nat := 118140960795 + 6063089 * 2 ^ 59
def prefixEnd_6063089 : Nat := 4983230072969 + 3 ^ 40 * 6063089 * 2
def baseEnd_6063089 : Nat := 3113278907988133870103867

theorem tailTrace_6063089 : CollatzResearch.WordTrace tailWord_6063089 prefixEnd_6063089 3113278907988133870103867 := by
  unfold tailWord_6063089
  simp only [CollatzResearch.WordTrace]
  refine ⟨221139023131471521006488321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147426015420981014004325547 221139023131471521006488321)
  ·
    refine ⟨165854267348603640754866241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221139023131471521006488321 165854267348603640754866241)
    ·
      refine ⟨124390700511452730566149681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165854267348603640754866241 124390700511452730566149681)
      ·
        refine ⟨93293025383589547924612261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124390700511452730566149681 93293025383589547924612261)
        ·
          refine ⟨17492442259423040235864799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93293025383589547924612261 17492442259423040235864799)
          ·
            refine ⟨26238663389134560353797199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17492442259423040235864799 26238663389134560353797199)
            ·
              refine ⟨39357995083701840530695799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26238663389134560353797199 39357995083701840530695799)
              ·
                refine ⟨59036992625552760796043699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39357995083701840530695799 59036992625552760796043699)
                ·
                  refine ⟨88555488938329141194065549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59036992625552760796043699 88555488938329141194065549)
                  ·
                    refine ⟨33208308351873427947774581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88555488938329141194065549 33208308351873427947774581)
                    ·
                      refine ⟨3113278907988133870103867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33208308351873427947774581 3113278907988133870103867)
                      ·
                        rfl

theorem cell23_6063089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_6063089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063089 prefixEnd_6063089 := by exact prefixLift 6063089
  have htrace : WordTrace (prefixWord ++ tailWord_6063089) baseStart_6063089 baseEnd_6063089 := by
    simpa [prefixWord, tailWord_6063089, baseEnd_6063089] using wordTrace_append hprefix tailTrace_6063089
  have hstable : (prefixWord ++ tailWord_6063089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063089).length < 2 ^ (prefixWord ++ tailWord_6063089).sum := by decide
  have hdescent : baseEnd_6063089 < baseStart_6063089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063159 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_6063159 : Nat := 118140960795 + 6063159 * 2 ^ 59
def prefixEnd_6063159 : Nat := 4983230072969 + 3 ^ 40 * 6063159 * 2
def baseEnd_6063159 : Nat := 3113314851633948596228545

theorem tailTrace_6063159 : CollatzResearch.WordTrace tailWord_6063159 prefixEnd_6063159 3113314851633948596228545 := by
  unfold tailWord_6063159
  simp only [CollatzResearch.WordTrace]
  refine ⟨221141576241217922961536531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147427717494145281974357687 221141576241217922961536531)
  ·
    refine ⟨331712364361826884442304797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221141576241217922961536531 331712364361826884442304797)
    ·
      refine ⟨124392136635685081665864299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331712364361826884442304797 124392136635685081665864299)
      ·
        refine ⟨186588204953527622498796449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124392136635685081665864299 186588204953527622498796449)
        ·
          refine ⟨139941153715145716874097337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186588204953527622498796449 139941153715145716874097337)
          ·
            refine ⟨104955865286359287655573003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139941153715145716874097337 104955865286359287655573003)
            ·
              refine ⟨157433797929538931483359505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104955865286359287655573003 157433797929538931483359505)
              ·
                refine ⟨118075348447154198612519629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157433797929538931483359505 118075348447154198612519629)
                ·
                  refine ⟨44278255667682824479694861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118075348447154198612519629 44278255667682824479694861)
                  ·
                    refine ⟨16604345875381059179885573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44278255667682824479694861 16604345875381059179885573)
                    ·
                      refine ⟨3113314851633948596228545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16604345875381059179885573 3113314851633948596228545)
                      ·
                        rfl

theorem cell23_6063159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_6063159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063159 prefixEnd_6063159 := by exact prefixLift 6063159
  have htrace : WordTrace (prefixWord ++ tailWord_6063159) baseStart_6063159 baseEnd_6063159 := by
    simpa [prefixWord, tailWord_6063159, baseEnd_6063159] using wordTrace_append hprefix tailTrace_6063159
  have hstable : (prefixWord ++ tailWord_6063159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063159).length < 2 ^ (prefixWord ++ tailWord_6063159).sum := by decide
  have hdescent : baseEnd_6063159 < baseStart_6063159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063160 : List Nat := [2, 1, 2, 1, 5, 3, 2, 2, 5]
def baseStart_6063160 : Nat := 118140960795 + 6063160 * 2 ^ 59
def prefixEnd_6063160 : Nat := 4983230072969 + 3 ^ 40 * 6063160 * 2
def baseEnd_6063160 : Nat := 345923929457178121368449

theorem tailTrace_6063160 : CollatzResearch.WordTrace tailWord_6063160 prefixEnd_6063160 345923929457178121368449 := by
  unfold tailWord_6063160
  simp only [CollatzResearch.WordTrace]
  refine ⟨110570806357107150066161467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147427741809476200088215289 110570806357107150066161467)
  ·
    refine ⟨165856209535660725099242201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110570806357107150066161467 165856209535660725099242201)
    ·
      refine ⟨124392157151745543824431651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165856209535660725099242201 124392157151745543824431651)
      ·
        refine ⟨186588235727618315736647477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124392157151745543824431651 186588235727618315736647477)
        ·
          refine ⟨17492647099464217100310701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186588235727618315736647477 17492647099464217100310701)
          ·
            refine ⟨6559742662299081412616513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17492647099464217100310701 6559742662299081412616513)
            ·
              refine ⟨4919806996724311059462385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6559742662299081412616513 4919806996724311059462385)
              ·
                refine ⟨3689855247543233294596789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4919806996724311059462385 3689855247543233294596789)
                ·
                  refine ⟨345923929457178121368449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3689855247543233294596789 345923929457178121368449)
                  ·
                    rfl

theorem cell23_6063160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 5].length) (baseStart_6063160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063160 prefixEnd_6063160 := by exact prefixLift 6063160
  have htrace : WordTrace (prefixWord ++ tailWord_6063160) baseStart_6063160 baseEnd_6063160 := by
    simpa [prefixWord, tailWord_6063160, baseEnd_6063160] using wordTrace_append hprefix tailTrace_6063160
  have hstable : (prefixWord ++ tailWord_6063160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063160).length < 2 ^ (prefixWord ++ tailWord_6063160).sum := by decide
  have hdescent : baseEnd_6063160 < baseStart_6063160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063190 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6063190 : Nat := 118140960795 + 6063190 * 2 ^ 59
def prefixEnd_6063190 : Nat := 4983230072969 + 3 ^ 40 * 6063190 * 2
def baseEnd_6063190 : Nat := 1037776923178079324980301

theorem tailTrace_6063190 : CollatzResearch.WordTrace tailWord_6063190 prefixEnd_6063190 1037776923178079324980301 := by
  unfold tailWord_6063190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13821419181506600953494689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147428471269403743503943349 13821419181506600953494689)
  ·
    refine ⟨10366064386129950715121017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13821419181506600953494689 10366064386129950715121017)
    ·
      refine ⟨7774548289597463036340763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10366064386129950715121017 7774548289597463036340763)
      ·
        refine ⟨11661822434396194554511145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7774548289597463036340763 11661822434396194554511145)
        ·
          refine ⟨8746366825797145915883359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11661822434396194554511145 8746366825797145915883359)
          ·
            refine ⟨13119550238695718873825039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8746366825797145915883359 13119550238695718873825039)
            ·
              refine ⟨19679325358043578310737559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13119550238695718873825039 19679325358043578310737559)
              ·
                refine ⟨29518988037065367466106339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19679325358043578310737559 29518988037065367466106339)
                ·
                  refine ⟨44278482055598051199159509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29518988037065367466106339 44278482055598051199159509)
                  ·
                    refine ⟨1037776923178079324980301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44278482055598051199159509 1037776923178079324980301)
                    ·
                      rfl

theorem cell23_6063190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6063190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063190 prefixEnd_6063190 := by exact prefixLift 6063190
  have htrace : WordTrace (prefixWord ++ tailWord_6063190) baseStart_6063190 baseEnd_6063190 := by
    simpa [prefixWord, tailWord_6063190, baseEnd_6063190] using wordTrace_append hprefix tailTrace_6063190
  have hstable : (prefixWord ++ tailWord_6063190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063190).length < 2 ^ (prefixWord ++ tailWord_6063190).sum := by decide
  have hdescent : baseEnd_6063190 < baseStart_6063190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063199 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 8]
def baseStart_6063199 : Nat := 118140960795 + 6063199 * 2 ^ 59
def prefixEnd_6063199 : Nat := 4983230072969 + 3 ^ 40 * 6063199 * 2
def baseEnd_6063199 : Nat := 345926154540014271080929

theorem tailTrace_6063199 : CollatzResearch.WordTrace tailWord_6063199 prefixEnd_6063199 345926154540014271080929 := by
  unfold tailWord_6063199
  simp only [CollatzResearch.WordTrace]
  refine ⟨221143035161073009792992651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147428690107382006528661767 221143035161073009792992651)
  ·
    refine ⟨331714552741609514689488977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221143035161073009792992651 331714552741609514689488977)
    ·
      refine ⟨248785914556207136017116733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331714552741609514689488977 248785914556207136017116733)
      ·
        refine ⟨93294717958577676006418775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248785914556207136017116733 93294717958577676006418775)
        ·
          refine ⟨139942076937866514009628163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93294717958577676006418775 139942076937866514009628163)
          ·
            refine ⟨209913115406799771014442245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139942076937866514009628163 209913115406799771014442245)
            ·
              refine ⟨39358709138774957065207921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209913115406799771014442245 39358709138774957065207921)
              ·
                refine ⟨29519031854081217798905941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39358709138774957065207921 29519031854081217798905941)
                ·
                  refine ⟨345926154540014271080929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29519031854081217798905941 345926154540014271080929)
                  ·
                    rfl

theorem cell23_6063199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 8].length) (baseStart_6063199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063199 prefixEnd_6063199 := by exact prefixLift 6063199
  have htrace : WordTrace (prefixWord ++ tailWord_6063199) baseStart_6063199 baseEnd_6063199 := by
    simpa [prefixWord, tailWord_6063199, baseEnd_6063199] using wordTrace_append hprefix tailTrace_6063199
  have hstable : (prefixWord ++ tailWord_6063199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063199).length < 2 ^ (prefixWord ++ tailWord_6063199).sum := by decide
  have hdescent : baseEnd_6063199 < baseStart_6063199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063297 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6063297 : Nat := 118140960795 + 6063297 * 2 ^ 59
def prefixEnd_6063297 : Nat := 4983230072969 + 3 ^ 40 * 6063297 * 2
def baseEnd_6063297 : Nat := 1037795237321423018767637

theorem tailTrace_6063297 : CollatzResearch.WordTrace tailWord_6063297 prefixEnd_6063297 1037795237321423018767637 := by
  unfold tailWord_6063297
  simp only [CollatzResearch.WordTrace]
  refine ⟨221146609514717972530060145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147431073009811981686706763 221146609514717972530060145)
  ·
    refine ⟨165859957136038479397545109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221146609514717972530060145 165859957136038479397545109)
    ·
      refine ⟨7774685490751803721759927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 165859957136038479397545109 7774685490751803721759927)
      ·
        refine ⟨11662028236127705582639891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7774685490751803721759927 11662028236127705582639891)
        ·
          refine ⟨17493042354191558373959837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11662028236127705582639891 17493042354191558373959837)
          ·
            refine ⟨6559890882821834390234939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17493042354191558373959837 6559890882821834390234939)
            ·
              refine ⟨9839836324232751585352409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6559890882821834390234939 9839836324232751585352409)
              ·
                refine ⟨7379877243174563689014307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9839836324232751585352409 7379877243174563689014307)
                ·
                  refine ⟨11069815864761845533521461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7379877243174563689014307 11069815864761845533521461)
                  ·
                    refine ⟨1037795237321423018767637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11069815864761845533521461 1037795237321423018767637)
                    ·
                      rfl

theorem cell23_6063297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6063297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063297 prefixEnd_6063297 := by exact prefixLift 6063297
  have htrace : WordTrace (prefixWord ++ tailWord_6063297) baseStart_6063297 baseEnd_6063297 := by
    simpa [prefixWord, tailWord_6063297, baseEnd_6063297] using wordTrace_append hprefix tailTrace_6063297
  have hstable : (prefixWord ++ tailWord_6063297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063297).length < 2 ^ (prefixWord ++ tailWord_6063297).sum := by decide
  have hdescent : baseEnd_6063297 < baseStart_6063297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063300 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_6063300 : Nat := 118140960795 + 6063300 * 2 ^ 59
def prefixEnd_6063300 : Nat := 4983230072969 + 3 ^ 40 * 6063300 * 2
def baseEnd_6063300 : Nat := 3113387252406232544565397

theorem tailTrace_6063300 : CollatzResearch.WordTrace tailWord_6063300 prefixEnd_6063300 3113387252406232544565397 := by
  unfold tailWord_6063300
  simp only [CollatzResearch.WordTrace]
  refine ⟨110573359466853552021209677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147431145955804736028279569 110573359466853552021209677)
  ·
    refine ⟨41465009800070082007953629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110573359466853552021209677 41465009800070082007953629)
    ·
      refine ⟨15549378675026280752982611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41465009800070082007953629 15549378675026280752982611)
      ·
        refine ⟨23324068012539421129473917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15549378675026280752982611 23324068012539421129473917)
        ·
          refine ⟨8746525504702282923552719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23324068012539421129473917 8746525504702282923552719)
          ·
            refine ⟨13119788257053424385329079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8746525504702282923552719 13119788257053424385329079)
            ·
              refine ⟨19679682385580136577993619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13119788257053424385329079 19679682385580136577993619)
              ·
                refine ⟨29519523578370204866990429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19679682385580136577993619 29519523578370204866990429)
                ·
                  refine ⟨11069821341888826825121411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29519523578370204866990429 11069821341888826825121411)
                  ·
                    refine ⟨16604732012833240237682117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11069821341888826825121411 16604732012833240237682117)
                    ·
                      refine ⟨3113387252406232544565397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16604732012833240237682117 3113387252406232544565397)
                      ·
                        rfl

theorem cell23_6063300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_6063300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063300 prefixEnd_6063300 := by exact prefixLift 6063300
  have htrace : WordTrace (prefixWord ++ tailWord_6063300) baseStart_6063300 baseEnd_6063300 := by
    simpa [prefixWord, tailWord_6063300, baseEnd_6063300] using wordTrace_append hprefix tailTrace_6063300
  have hstable : (prefixWord ++ tailWord_6063300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063300).length < 2 ^ (prefixWord ++ tailWord_6063300).sum := by decide
  have hdescent : baseEnd_6063300 < baseStart_6063300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063306 : List Nat := [3, 1, 2, 1, 3, 2, 2, 9]
def baseStart_6063306 : Nat := 118140960795 + 6063306 * 2 ^ 59
def prefixEnd_6063306 : Nat := 4983230072969 + 3 ^ 40 * 6063306 * 2
def baseEnd_6063306 : Nat := 115310753084820723003347

theorem tailTrace_6063306 : CollatzResearch.WordTrace tailWord_6063306 prefixEnd_6063306 115310753084820723003347 := by
  unfold tailWord_6063306
  simp only [CollatzResearch.WordTrace]
  refine ⟨55286734442921341766784443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147431291847790244711425181 55286734442921341766784443)
  ·
    refine ⟨82930101664382012650176665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55286734442921341766784443 82930101664382012650176665)
    ·
      refine ⟨62197576248286509487632499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82930101664382012650176665 62197576248286509487632499)
      ·
        refine ⟨93296364372429764231448749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62197576248286509487632499 93296364372429764231448749)
        ·
          refine ⟨34986136639661161586793281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93296364372429764231448749 34986136639661161586793281)
          ·
            refine ⟨26239602479745871190094961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34986136639661161586793281 26239602479745871190094961)
            ·
              refine ⟨19679701859809403392571221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26239602479745871190094961 19679701859809403392571221)
              ·
                refine ⟨115310753084820723003347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19679701859809403392571221 115310753084820723003347)
                ·
                  rfl

theorem cell23_6063306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 9].length) (baseStart_6063306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063306 prefixEnd_6063306 := by exact prefixLift 6063306
  have htrace : WordTrace (prefixWord ++ tailWord_6063306) baseStart_6063306 baseEnd_6063306 := by
    simpa [prefixWord, tailWord_6063306, baseEnd_6063306] using wordTrace_append hprefix tailTrace_6063306
  have hstable : (prefixWord ++ tailWord_6063306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063306).length < 2 ^ (prefixWord ++ tailWord_6063306).sum := by decide
  have hdescent : baseEnd_6063306 < baseStart_6063306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063317 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_6063317 : Nat := 118140960795 + 6063317 * 2 ^ 59
def prefixEnd_6063317 : Nat := 4983230072969 + 3 ^ 40 * 6063317 * 2
def baseEnd_6063317 : Nat := 3113395981577358978052819

theorem tailTrace_6063317 : CollatzResearch.WordTrace tailWord_6063317 prefixEnd_6063317 3113395981577358978052819 := by
  unfold tailWord_6063317
  simp only [CollatzResearch.WordTrace]
  refine ⟨221147338974645515945788205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147431559316430343963858803 221147338974645515945788205)
  ·
    refine ⟨82930252115492068479670577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221147338974645515945788205 82930252115492068479670577)
    ·
      refine ⟨62197689086619051359752933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82930252115492068479670577 62197689086619051359752933)
      ·
        refine ⟨11662066703741072129953675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62197689086619051359752933 11662066703741072129953675)
        ·
          refine ⟨17493100055611608194930513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11662066703741072129953675 17493100055611608194930513)
          ·
            refine ⟨13119825041708706146197885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17493100055611608194930513 13119825041708706146197885)
            ·
              refine ⟨4919934390640764804824207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13119825041708706146197885 4919934390640764804824207)
              ·
                refine ⟨7379901585961147207236311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919934390640764804824207 7379901585961147207236311)
                ·
                  refine ⟨11069852378941720810854467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7379901585961147207236311 11069852378941720810854467)
                  ·
                    refine ⟨16604778568412581216281701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11069852378941720810854467 16604778568412581216281701)
                    ·
                      refine ⟨3113395981577358978052819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16604778568412581216281701 3113395981577358978052819)
                      ·
                        rfl

theorem cell23_6063317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_6063317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063317 prefixEnd_6063317 := by exact prefixLift 6063317
  have htrace : WordTrace (prefixWord ++ tailWord_6063317) baseStart_6063317 baseEnd_6063317 := by
    simpa [prefixWord, tailWord_6063317, baseEnd_6063317] using wordTrace_append hprefix tailTrace_6063317
  have hstable : (prefixWord ++ tailWord_6063317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063317).length < 2 ^ (prefixWord ++ tailWord_6063317).sum := by decide
  have hdescent : baseEnd_6063317 < baseStart_6063317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063320 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 1, 1, 5]
def baseStart_6063320 : Nat := 118140960795 + 6063320 * 2 ^ 59
def prefixEnd_6063320 : Nat := 4983230072969 + 3 ^ 40 * 6063320 * 2
def baseEnd_6063320 : Nat := 3113397522019322466315305

theorem tailTrace_6063320 : CollatzResearch.WordTrace tailWord_6063320 prefixEnd_6063320 3113397522019322466315305 := by
  unfold tailWord_6063320
  simp only [CollatzResearch.WordTrace]
  refine ⟨110573724196817323729073707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147431632262423098305431609 110573724196817323729073707)
  ·
    refine ⟨165860586295225985593610561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110573724196817323729073707 165860586295225985593610561)
    ·
      refine ⟨124395439721419489195207921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165860586295225985593610561 124395439721419489195207921)
      ·
        refine ⟨93296579791064616896405941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124395439721419489195207921 93296579791064616896405941)
        ·
          refine ⟨8746554355412307834038057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93296579791064616896405941 8746554355412307834038057)
          ·
            refine ⟨6559915766559230875528543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8746554355412307834038057 6559915766559230875528543)
            ·
              refine ⟨9839873649838846313292815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6559915766559230875528543 9839873649838846313292815)
              ·
                refine ⟨14759810474758269469939223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9839873649838846313292815 14759810474758269469939223)
                ·
                  refine ⟨22139715712137404204908835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14759810474758269469939223 22139715712137404204908835)
                  ·
                    refine ⟨33209573568206106307363253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22139715712137404204908835 33209573568206106307363253)
                    ·
                      refine ⟨3113397522019322466315305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33209573568206106307363253 3113397522019322466315305)
                      ·
                        rfl

theorem cell23_6063320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_6063320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063320 prefixEnd_6063320 := by exact prefixLift 6063320
  have htrace : WordTrace (prefixWord ++ tailWord_6063320) baseStart_6063320 baseEnd_6063320 := by
    simpa [prefixWord, tailWord_6063320, baseEnd_6063320] using wordTrace_append hprefix tailTrace_6063320
  have hstable : (prefixWord ++ tailWord_6063320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063320).length < 2 ^ (prefixWord ++ tailWord_6063320).sum := by decide
  have hdescent : baseEnd_6063320 < baseStart_6063320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063336 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 1, 9]
def baseStart_6063336 : Nat := 118140960795 + 6063336 * 2 ^ 59
def prefixEnd_6063336 : Nat := 4983230072969 + 3 ^ 40 * 6063336 * 2
def baseEnd_6063336 : Nat := 1037801912569931467905077

theorem tailTrace_6063336 : CollatzResearch.WordTrace tailWord_6063336 prefixEnd_6063336 1037801912569931467905077 := by
  unfold tailWord_6063336
  simp only [CollatzResearch.WordTrace]
  refine ⟨110574015980788341095364931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147432021307717788127153241 110574015980788341095364931)
  ·
    refine ⟨165861023971182511643047397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110574015980788341095364931 165861023971182511643047397)
    ·
      refine ⟨31098941994596720933071387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165861023971182511643047397 31098941994596720933071387)
      ·
        refine ⟨46648412991895081399607081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31098941994596720933071387 46648412991895081399607081)
        ·
          refine ⟨34986309743921311049705311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46648412991895081399607081 34986309743921311049705311)
          ·
            refine ⟨52479464615881966574557967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34986309743921311049705311 52479464615881966574557967)
            ·
              refine ⟨78719196923822949861836951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52479464615881966574557967 78719196923822949861836951)
              ·
                refine ⟨118078795385734424792755427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78719196923822949861836951 118078795385734424792755427)
                ·
                  refine ⟨177118193078601637189133141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118078795385734424792755427 177118193078601637189133141)
                  ·
                    refine ⟨1037801912569931467905077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 177118193078601637189133141 1037801912569931467905077)
                    ·
                      rfl

theorem cell23_6063336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_6063336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063336 prefixEnd_6063336 := by exact prefixLift 6063336
  have htrace : WordTrace (prefixWord ++ tailWord_6063336) baseStart_6063336 baseEnd_6063336 := by
    simpa [prefixWord, tailWord_6063336, baseEnd_6063336] using wordTrace_append hprefix tailTrace_6063336
  have hstable : (prefixWord ++ tailWord_6063336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063336).length < 2 ^ (prefixWord ++ tailWord_6063336).sum := by decide
  have hdescent : baseEnd_6063336 < baseStart_6063336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063350 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_6063350 : Nat := 118140960795 + 6063350 * 2 ^ 59
def prefixEnd_6063350 : Nat := 4983230072969 + 3 ^ 40 * 6063350 * 2
def baseEnd_6063350 : Nat := 3113412926438957348940167

theorem tailTrace_6063350 : CollatzResearch.WordTrace tailWord_6063350 prefixEnd_6063350 3113412926438957348940167 := by
  unfold tailWord_6063350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13821783911470372661358719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147432361722350641721159669 13821783911470372661358719)
  ·
    refine ⟨20732675867205558992038079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13821783911470372661358719 20732675867205558992038079)
    ·
      refine ⟨31099013800808338488057119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20732675867205558992038079 31099013800808338488057119)
      ·
        refine ⟨46648520701212507732085679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31099013800808338488057119 46648520701212507732085679)
        ·
          refine ⟨69972781051818761598128519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46648520701212507732085679 69972781051818761598128519)
          ·
            refine ⟨104959171577728142397192779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69972781051818761598128519 104959171577728142397192779)
            ·
              refine ⟨157438757366592213595789169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104959171577728142397192779 157438757366592213595789169)
              ·
                refine ⟨118079068024944160196841877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157438757366592213595789169 118079068024944160196841877)
                ·
                  refine ⟨5534956313669257509226963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118079068024944160196841877 5534956313669257509226963)
                  ·
                    refine ⟨8302434470503886263840445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5534956313669257509226963 8302434470503886263840445)
                    ·
                      refine ⟨3113412926438957348940167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8302434470503886263840445 3113412926438957348940167)
                      ·
                        rfl

theorem cell23_6063350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_6063350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063350 prefixEnd_6063350 := by exact prefixLift 6063350
  have htrace : WordTrace (prefixWord ++ tailWord_6063350) baseStart_6063350 baseEnd_6063350 := by
    simpa [prefixWord, tailWord_6063350, baseEnd_6063350] using wordTrace_append hprefix tailTrace_6063350
  have hstable : (prefixWord ++ tailWord_6063350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063350).length < 2 ^ (prefixWord ++ tailWord_6063350).sum := by decide
  have hdescent : baseEnd_6063350 < baseStart_6063350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063360 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 1, 3, 2]
def baseStart_6063360 : Nat := 118140960795 + 6063360 * 2 ^ 59
def prefixEnd_6063360 : Nat := 4983230072969 + 3 ^ 40 * 6063360 * 2
def baseEnd_6063360 : Nat := 3113418061245502309815121

theorem tailTrace_6063360 : CollatzResearch.WordTrace tailWord_6063360 prefixEnd_6063360 3113418061245502309815121 := by
  unfold tailWord_6063360
  simp only [CollatzResearch.WordTrace]
  refine ⟨110574453656744867144801767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147432604875659822859735689 110574453656744867144801767)
  ·
    refine ⟨165861680485117300717202651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110574453656744867144801767 165861680485117300717202651)
    ·
      refine ⟨248792520727675951075803977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165861680485117300717202651 248792520727675951075803977)
      ·
        refine ⟨186594390545756963306852983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248792520727675951075803977 186594390545756963306852983)
        ·
          refine ⟨279891585818635444960279475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186594390545756963306852983 279891585818635444960279475)
          ·
            refine ⟨419837378727953167440419213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279891585818635444960279475 419837378727953167440419213)
            ·
              refine ⟨157439017022982437790157205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419837378727953167440419213 157439017022982437790157205)
              ·
                refine ⟨7379953922952301771413619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157439017022982437790157205 7379953922952301771413619)
                ·
                  refine ⟨11069930884428452657120429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7379953922952301771413619 11069930884428452657120429)
                  ·
                    refine ⟨4151224081660669746420161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11069930884428452657120429 4151224081660669746420161)
                    ·
                      refine ⟨3113418061245502309815121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4151224081660669746420161 3113418061245502309815121)
                      ·
                        rfl

theorem cell23_6063360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_6063360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063360 prefixEnd_6063360 := by exact prefixLift 6063360
  have htrace : WordTrace (prefixWord ++ tailWord_6063360) baseStart_6063360 baseEnd_6063360 := by
    simpa [prefixWord, tailWord_6063360, baseEnd_6063360] using wordTrace_append hprefix tailTrace_6063360
  have hstable : (prefixWord ++ tailWord_6063360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063360).length < 2 ^ (prefixWord ++ tailWord_6063360).sum := by decide
  have hdescent : baseEnd_6063360 < baseStart_6063360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063376 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_6063376 : Nat := 118140960795 + 6063376 * 2 ^ 59
def prefixEnd_6063376 : Nat := 4983230072969 + 3 ^ 40 * 6063376 * 2
def baseEnd_6063376 : Nat := 3113426276935974247215047

theorem tailTrace_6063376 : CollatzResearch.WordTrace tailWord_6063376 prefixEnd_6063376 3113426276935974247215047 := by
  unfold tailWord_6063376
  simp only [CollatzResearch.WordTrace]
  refine ⟨110574745440715884511092991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147432993920954512681457321 110574745440715884511092991)
  ·
    refine ⟨165862118161073826766639487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110574745440715884511092991 165862118161073826766639487)
    ·
      refine ⟨248793177241610740149959231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165862118161073826766639487 248793177241610740149959231)
      ·
        refine ⟨373189765862416110224938847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248793177241610740149959231 373189765862416110224938847)
        ·
          refine ⟨559784648793624165337408271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373189765862416110224938847 559784648793624165337408271)
          ·
            refine ⟨839676973190436248006112407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559784648793624165337408271 839676973190436248006112407)
            ·
              refine ⟨1259515459785654372009168611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839676973190436248006112407 1259515459785654372009168611)
              ·
                refine ⟨1889273189678481558013752917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259515459785654372009168611 1889273189678481558013752917)
                ·
                  refine ⟨22139920191544705757973667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1889273189678481558013752917 22139920191544705757973667)
                  ·
                    refine ⟨33209880287317058636960501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22139920191544705757973667 33209880287317058636960501)
                    ·
                      refine ⟨3113426276935974247215047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33209880287317058636960501 3113426276935974247215047)
                      ·
                        rfl

theorem cell23_6063376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_6063376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063376 prefixEnd_6063376 := by exact prefixLift 6063376
  have htrace : WordTrace (prefixWord ++ tailWord_6063376) baseStart_6063376 baseEnd_6063376 := by
    simpa [prefixWord, tailWord_6063376, baseEnd_6063376] using wordTrace_append hprefix tailTrace_6063376
  have hstable : (prefixWord ++ tailWord_6063376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063376).length < 2 ^ (prefixWord ++ tailWord_6063376).sum := by decide
  have hdescent : baseEnd_6063376 < baseStart_6063376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063413 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 7]
def baseStart_6063413 : Nat := 118140960795 + 6063413 * 2 ^ 59
def prefixEnd_6063413 : Nat := 4983230072969 + 3 ^ 40 * 6063413 * 2
def baseEnd_6063413 : Nat := 345938363968910066939153

theorem tailTrace_6063413 : CollatzResearch.WordTrace tailWord_6063413 prefixEnd_6063413 345938363968910066939153 := by
  unfold tailWord_6063413
  simp only [CollatzResearch.WordTrace]
  refine ⟨221150840382297724341282893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147433893588198482894188595 221150840382297724341282893)
  ·
    refine ⟨82931565143361646627981085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221150840382297724341282893 82931565143361646627981085)
    ·
      refine ⟨31099336928760617485492907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82931565143361646627981085 31099336928760617485492907)
      ·
        refine ⟨46649005393140926228239361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31099336928760617485492907 46649005393140926228239361)
        ·
          refine ⟨34986754044855694671179521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46649005393140926228239361 34986754044855694671179521)
          ·
            refine ⟨26240065533641771003384641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34986754044855694671179521 26240065533641771003384641)
            ·
              refine ⟨19680049150231328252538481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26240065533641771003384641 19680049150231328252538481)
              ·
                refine ⟨14760036862673496189403861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19680049150231328252538481 14760036862673496189403861)
                ·
                  refine ⟨345938363968910066939153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14760036862673496189403861 345938363968910066939153)
                  ·
                    rfl

theorem cell23_6063413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_6063413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063413 prefixEnd_6063413 := by exact prefixLift 6063413
  have htrace : WordTrace (prefixWord ++ tailWord_6063413) baseStart_6063413 baseEnd_6063413 := by
    simpa [prefixWord, tailWord_6063413, baseEnd_6063413] using wordTrace_append hprefix tailTrace_6063413
  have hstable : (prefixWord ++ tailWord_6063413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063413).length < 2 ^ (prefixWord ++ tailWord_6063413).sum := by decide
  have hdescent : baseEnd_6063413 < baseStart_6063413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063443 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 2, 5]
def baseStart_6063443 : Nat := 118140960795 + 6063443 * 2 ^ 59
def prefixEnd_6063443 : Nat := 4983230072969 + 3 ^ 40 * 6063443 * 2
def baseEnd_6063443 : Nat := 1037820226713275161692413

theorem tailTrace_6063443 : CollatzResearch.WordTrace tailWord_6063443 prefixEnd_6063443 1037820226713275161692413 := by
  unfold tailWord_6063443
  simp only [CollatzResearch.WordTrace]
  refine ⟨221151934572189039464874983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147434623048126026309916655 221151934572189039464874983)
  ·
    refine ⟨331727901858283559197312475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221151934572189039464874983 331727901858283559197312475)
    ·
      refine ⟨497591852787425338795968713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331727901858283559197312475 497591852787425338795968713)
      ·
        refine ⟨373193889590569004096976535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497591852787425338795968713 373193889590569004096976535)
        ·
          refine ⟨559790834385853506145464803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373193889590569004096976535 559790834385853506145464803)
          ·
            refine ⟨839686251578780259218197205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559790834385853506145464803 839686251578780259218197205)
            ·
              refine ⟨19680146521377662325426497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 839686251578780259218197205 19680146521377662325426497)
              ·
                refine ⟨14760109891033246744069873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19680146521377662325426497 14760109891033246744069873)
                ·
                  refine ⟨11070082418274935058052405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14760109891033246744069873 11070082418274935058052405)
                  ·
                    refine ⟨1037820226713275161692413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11070082418274935058052405 1037820226713275161692413)
                    ·
                      rfl

theorem cell23_6063443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 5].length) (baseStart_6063443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063443 prefixEnd_6063443 := by exact prefixLift 6063443
  have htrace : WordTrace (prefixWord ++ tailWord_6063443) baseStart_6063443 baseEnd_6063443 := by
    simpa [prefixWord, tailWord_6063443, baseEnd_6063443] using wordTrace_append hprefix tailTrace_6063443
  have hstable : (prefixWord ++ tailWord_6063443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063443).length < 2 ^ (prefixWord ++ tailWord_6063443).sum := by decide
  have hdescent : baseEnd_6063443 < baseStart_6063443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063447 : List Nat := [1, 1, 3, 2, 3, 3, 3, 2, 5]
def baseStart_6063447 : Nat := 118140960795 + 6063447 * 2 ^ 59
def prefixEnd_6063447 : Nat := 4983230072969 + 3 ^ 40 * 6063447 * 2
def baseEnd_6063447 : Nat := 345940303784715941047469

theorem tailTrace_6063447 : CollatzResearch.WordTrace tailWord_6063447 prefixEnd_6063447 345940303784715941047469 := by
  unfold tailWord_6063447
  simp only [CollatzResearch.WordTrace]
  refine ⟨221152080464174548148020595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147434720309449698765347063 221152080464174548148020595)
  ·
    refine ⟨331728120696261822222030893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221152080464174548148020595 331728120696261822222030893)
    ·
      refine ⟨124398045261098183333261585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331728120696261822222030893 124398045261098183333261585)
      ·
        refine ⟨93298533945823637499946189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124398045261098183333261585 93298533945823637499946189)
        ·
          refine ⟨34986950229683864062479821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93298533945823637499946189 34986950229683864062479821)
          ·
            refine ⟨13120106336131449023429933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34986950229683864062479821 13120106336131449023429933)
            ·
              refine ⟨4920039876049293383786225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13120106336131449023429933 4920039876049293383786225)
              ·
                refine ⟨3690029907036970037839669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920039876049293383786225 3690029907036970037839669)
                ·
                  refine ⟨345940303784715941047469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3690029907036970037839669 345940303784715941047469)
                  ·
                    rfl

theorem cell23_6063447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 5].length) (baseStart_6063447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063447 prefixEnd_6063447 := by exact prefixLift 6063447
  have htrace : WordTrace (prefixWord ++ tailWord_6063447) baseStart_6063447 baseEnd_6063447 := by
    simpa [prefixWord, tailWord_6063447, baseEnd_6063447] using wordTrace_append hprefix tailTrace_6063447
  have hstable : (prefixWord ++ tailWord_6063447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063447).length < 2 ^ (prefixWord ++ tailWord_6063447).sum := by decide
  have hdescent : baseEnd_6063447 < baseStart_6063447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063477 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_6063477 : Nat := 118140960795 + 6063477 * 2 ^ 59
def prefixEnd_6063477 : Nat := 4983230072969 + 3 ^ 40 * 6063477 * 2
def baseEnd_6063477 : Nat := 1037826046160692784017361

theorem tailTrace_6063477 : CollatzResearch.WordTrace tailWord_6063477 prefixEnd_6063477 1037826046160692784017361 := by
  unfold tailWord_6063477
  simp only [CollatzResearch.WordTrace]
  refine ⟨221153174654065863271612685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147435449769377242181075123 221153174654065863271612685)
  ·
    refine ⟨82932440495274698726854757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221153174654065863271612685 82932440495274698726854757)
    ·
      refine ⟨15549832592864006011285267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82932440495274698726854757 15549832592864006011285267)
      ·
        refine ⟨23324748889296009016927901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15549832592864006011285267 23324748889296009016927901)
        ·
          refine ⟨8746780833486003381347963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23324748889296009016927901 8746780833486003381347963)
          ·
            refine ⟨13120171250229005072021945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8746780833486003381347963 13120171250229005072021945)
            ·
              refine ⟨9840128437671753804016459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13120171250229005072021945 9840128437671753804016459)
              ·
                refine ⟨14760192656507630706024689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9840128437671753804016459 14760192656507630706024689)
                ·
                  refine ⟨11070144492380723029518517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14760192656507630706024689 11070144492380723029518517)
                  ·
                    refine ⟨1037826046160692784017361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11070144492380723029518517 1037826046160692784017361)
                    ·
                      rfl

theorem cell23_6063477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_6063477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063477 prefixEnd_6063477 := by exact prefixLift 6063477
  have htrace : WordTrace (prefixWord ++ tailWord_6063477) baseStart_6063477 baseEnd_6063477 := by
    simpa [prefixWord, tailWord_6063477, baseEnd_6063477] using wordTrace_append hprefix tailTrace_6063477
  have hstable : (prefixWord ++ tailWord_6063477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063477).length < 2 ^ (prefixWord ++ tailWord_6063477).sum := by decide
  have hdescent : baseEnd_6063477 < baseStart_6063477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063500 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_6063500 : Nat := 118140960795 + 6063500 * 2 ^ 59
def prefixEnd_6063500 : Nat := 4983230072969 + 3 ^ 40 * 6063500 * 2
def baseEnd_6063500 : Nat := 3113489948537131762064477

theorem tailTrace_6063500 : CollatzResearch.WordTrace tailWord_6063500 prefixEnd_6063500 3113489948537131762064477 := by
  unfold tailWord_6063500
  simp only [CollatzResearch.WordTrace]
  refine ⟨110577006766491269099849977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147436009021988358799799969 110577006766491269099849977)
  ·
    refine ⟨82932755074868451824887483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110577006766491269099849977 82932755074868451824887483)
    ·
      refine ⟨124399132612302677737331225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82932755074868451824887483 124399132612302677737331225)
      ·
        refine ⟨93299349459227008302998419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124399132612302677737331225 93299349459227008302998419)
        ·
          refine ⟨139949024188840512454497629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93299349459227008302998419 139949024188840512454497629)
          ·
            refine ⟨52480884070815192170436611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139949024188840512454497629 52480884070815192170436611)
            ·
              refine ⟨78721326106222788255654917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52480884070815192170436611 78721326106222788255654917)
              ·
                refine ⟨14760248644916772797935297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78721326106222788255654917 14760248644916772797935297)
                ·
                  refine ⟨11070186483687579598451473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14760248644916772797935297 11070186483687579598451473)
                  ·
                    refine ⟨8302639862765684698838605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11070186483687579598451473 8302639862765684698838605)
                    ·
                      refine ⟨3113489948537131762064477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8302639862765684698838605 3113489948537131762064477)
                      ·
                        rfl

theorem cell23_6063500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_6063500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063500 prefixEnd_6063500 := by exact prefixLift 6063500
  have htrace : WordTrace (prefixWord ++ tailWord_6063500) baseStart_6063500 baseEnd_6063500 := by
    simpa [prefixWord, tailWord_6063500, baseEnd_6063500] using wordTrace_append hprefix tailTrace_6063500
  have hstable : (prefixWord ++ tailWord_6063500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063500).length < 2 ^ (prefixWord ++ tailWord_6063500).sum := by decide
  have hdescent : baseEnd_6063500 < baseStart_6063500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063563 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 3, 6]
def baseStart_6063563 : Nat := 118140960795 + 6063563 * 2 ^ 59
def prefixEnd_6063563 : Nat := 4983230072969 + 3 ^ 40 * 6063563 * 2
def baseEnd_6063563 : Nat := 1037840765939455005192229

theorem tailTrace_6063563 : CollatzResearch.WordTrace tailWord_6063563 prefixEnd_6063563 1037840765939455005192229 := by
  unfold tailWord_6063563
  simp only [CollatzResearch.WordTrace]
  refine ⟨221156311331754299959243343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147437540887836199972828895 221156311331754299959243343)
  ·
    refine ⟨331734466997631449938865015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221156311331754299959243343 331734466997631449938865015)
    ·
      refine ⟨497601700496447174908297523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331734466997631449938865015 497601700496447174908297523)
      ·
        refine ⟨746402550744670762362446285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497601700496447174908297523 746402550744670762362446285)
        ·
          refine ⟨279900956529251535885917357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 746402550744670762362446285 279900956529251535885917357)
          ·
            refine ⟨104962858698469325957219009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279900956529251535885917357 104962858698469325957219009)
            ·
              refine ⟨78722144023851994467914257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104962858698469325957219009 78722144023851994467914257)
              ·
                refine ⟨59041608017888995850935693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78722144023851994467914257 59041608017888995850935693)
                ·
                  refine ⟨22140603006708373444100885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59041608017888995850935693 22140603006708373444100885)
                  ·
                    refine ⟨1037840765939455005192229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22140603006708373444100885 1037840765939455005192229)
                    ·
                      rfl

theorem cell23_6063563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 6].length) (baseStart_6063563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063563 prefixEnd_6063563 := by exact prefixLift 6063563
  have htrace : WordTrace (prefixWord ++ tailWord_6063563) baseStart_6063563 baseEnd_6063563 := by
    simpa [prefixWord, tailWord_6063563, baseEnd_6063563] using wordTrace_append hprefix tailTrace_6063563
  have hstable : (prefixWord ++ tailWord_6063563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063563).length < 2 ^ (prefixWord ++ tailWord_6063563).sum := by decide
  have hdescent : baseEnd_6063563 < baseStart_6063563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063564 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 3, 1, 3]
def baseStart_6063564 : Nat := 118140960795 + 6063564 * 2 ^ 59
def prefixEnd_6063564 : Nat := 4983230072969 + 3 ^ 40 * 6063564 * 2
def baseEnd_6063564 : Nat := 3113522811299019511664183

theorem tailTrace_6063564 : CollatzResearch.WordTrace tailWord_6063564 prefixEnd_6063564 3113522811299019511664183 := by
  unfold tailWord_6063564
  simp only [CollatzResearch.WordTrace]
  refine ⟨110578173902375338565014873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147437565203167118086686497 110578173902375338565014873)
  ·
    refine ⟨82933630426781503923761155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110578173902375338565014873 82933630426781503923761155)
    ·
      refine ⟨124400445640172255885641733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82933630426781503923761155 124400445640172255885641733)
      ·
        refine ⟨23325083557532297978557825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124400445640172255885641733 23325083557532297978557825)
        ·
          refine ⟨17493812668149223483918369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23325083557532297978557825 17493812668149223483918369)
          ·
            refine ⟨13120359501111917612938777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17493812668149223483918369 13120359501111917612938777)
            ·
              refine ⟨9840269625833938209704083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13120359501111917612938777 9840269625833938209704083)
              ·
                refine ⟨14760404438750907314556125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9840269625833938209704083 14760404438750907314556125)
                ·
                  refine ⟨5535151664531590242958547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14760404438750907314556125 5535151664531590242958547)
                  ·
                    refine ⟨8302727496797385364437821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5535151664531590242958547 8302727496797385364437821)
                    ·
                      refine ⟨3113522811299019511664183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8302727496797385364437821 3113522811299019511664183)
                      ·
                        rfl

theorem cell23_6063564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_6063564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063564 prefixEnd_6063564 := by exact prefixLift 6063564
  have htrace : WordTrace (prefixWord ++ tailWord_6063564) baseStart_6063564 baseEnd_6063564 := by
    simpa [prefixWord, tailWord_6063564, baseEnd_6063564] using wordTrace_append hprefix tailTrace_6063564
  have hstable : (prefixWord ++ tailWord_6063564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063564).length < 2 ^ (prefixWord ++ tailWord_6063564).sum := by decide
  have hdescent : baseEnd_6063564 < baseStart_6063564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063574 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_6063574 : Nat := 118140960795 + 6063574 * 2 ^ 59
def prefixEnd_6063574 : Nat := 4983230072969 + 3 ^ 40 * 6063574 * 2
def baseEnd_6063574 : Nat := 3113527946105564472539137

theorem tailTrace_6063574 : CollatzResearch.WordTrace tailWord_6063574 prefixEnd_6063574 3113527946105564472539137 := by
  unfold tailWord_6063574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13822294533419653052368361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147437808356476299225262517 13822294533419653052368361)
  ·
    refine ⟨10366720900064739789276271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13822294533419653052368361 10366720900064739789276271)
    ·
      refine ⟨15550081350097109683914407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10366720900064739789276271 15550081350097109683914407)
      ·
        refine ⟨23325122025145664525871611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15550081350097109683914407 23325122025145664525871611)
        ·
          refine ⟨34987683037718496788807417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23325122025145664525871611 34987683037718496788807417)
          ·
            refine ⟨26240762278288872591605563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34987683037718496788807417 26240762278288872591605563)
            ·
              refine ⟨39361143417433308887408345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26240762278288872591605563 39361143417433308887408345)
              ·
                refine ⟨29520857563074981665556259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39361143417433308887408345 29520857563074981665556259)
                ·
                  refine ⟨44281286344612472498334389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29520857563074981665556259 44281286344612472498334389)
                  ·
                    refine ⟨4151370594807419296718849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44281286344612472498334389 4151370594807419296718849)
                    ·
                      refine ⟨3113527946105564472539137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4151370594807419296718849 3113527946105564472539137)
                      ·
                        rfl

theorem cell23_6063574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_6063574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063574 prefixEnd_6063574 := by exact prefixLift 6063574
  have htrace : WordTrace (prefixWord ++ tailWord_6063574) baseStart_6063574 baseEnd_6063574 := by
    simpa [prefixWord, tailWord_6063574, baseEnd_6063574] using wordTrace_append hprefix tailTrace_6063574
  have hstable : (prefixWord ++ tailWord_6063574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063574).length < 2 ^ (prefixWord ++ tailWord_6063574).sum := by decide
  have hdescent : baseEnd_6063574 < baseStart_6063574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063587 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 4]
def baseStart_6063587 : Nat := 118140960795 + 6063587 * 2 ^ 59
def prefixEnd_6063587 : Nat := 4983230072969 + 3 ^ 40 * 6063587 * 2
def baseEnd_6063587 : Nat := 3113534621354072921676577

theorem tailTrace_6063587 : CollatzResearch.WordTrace tailWord_6063587 prefixEnd_6063587 3113534621354072921676577 := by
  unfold tailWord_6063587
  simp only [CollatzResearch.WordTrace]
  refine ⟨221157186683667352058117015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147438124455778234705411343 221157186683667352058117015)
  ·
    refine ⟨331735780025501028087175523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221157186683667352058117015 331735780025501028087175523)
    ·
      refine ⟨497603670038251542130763285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331735780025501028087175523 497603670038251542130763285)
      ·
        refine ⟨23325172033043041037379529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 497603670038251542130763285 23325172033043041037379529)
        ·
          refine ⟨17493879024782280778034647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23325172033043041037379529 17493879024782280778034647)
          ·
            refine ⟨26240818537173421167051971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17493879024782280778034647 26240818537173421167051971)
            ·
              refine ⟨39361227805760131750577957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26240818537173421167051971 39361227805760131750577957)
              ·
                refine ⟨7380230213580024703233367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39361227805760131750577957 7380230213580024703233367)
                ·
                  refine ⟨11070345320370037054850051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7380230213580024703233367 11070345320370037054850051)
                  ·
                    refine ⟨16605517980555055582275077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11070345320370037054850051 16605517980555055582275077)
                    ·
                      refine ⟨3113534621354072921676577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16605517980555055582275077 3113534621354072921676577)
                      ·
                        rfl

theorem cell23_6063587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_6063587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063587 prefixEnd_6063587 := by exact prefixLift 6063587
  have htrace : WordTrace (prefixWord ++ tailWord_6063587) baseStart_6063587 baseEnd_6063587 := by
    simpa [prefixWord, tailWord_6063587, baseEnd_6063587] using wordTrace_append hprefix tailTrace_6063587
  have hstable : (prefixWord ++ tailWord_6063587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063587).length < 2 ^ (prefixWord ++ tailWord_6063587).sum := by decide
  have hdescent : baseEnd_6063587 < baseStart_6063587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063650 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_6063650 : Nat := 118140960795 + 6063650 * 2 ^ 59
def prefixEnd_6063650 : Nat := 4983230072969 + 3 ^ 40 * 6063650 * 2
def baseEnd_6063650 : Nat := 3113566970635306175188787

theorem tailTrace_6063650 : CollatzResearch.WordTrace tailWord_6063650 prefixEnd_6063650 3113566970635306175188787 := by
  unfold tailWord_6063650
  simp only [CollatzResearch.WordTrace]
  refine ⟨55289871120609778454415101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147439656321626075878440269 55289871120609778454415101)
  ·
    refine ⟨20733701670228666920405663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55289871120609778454415101 20733701670228666920405663)
    ·
      refine ⟨31100552505343000380608495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20733701670228666920405663 31100552505343000380608495)
      ·
        refine ⟨46650828758014500570912743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31100552505343000380608495 46650828758014500570912743)
        ·
          refine ⟨69976243137021750856369115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46650828758014500570912743 69976243137021750856369115)
          ·
            refine ⟨104964364705532626284553673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69976243137021750856369115 104964364705532626284553673)
            ·
              refine ⟨78723273529149469713415255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104964364705532626284553673 78723273529149469713415255)
              ·
                refine ⟨118084910293724204570122883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78723273529149469713415255 118084910293724204570122883)
                ·
                  refine ⟨177127365440586306855184325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118084910293724204570122883 177127365440586306855184325)
                  ·
                    refine ⟨33211381020109932535347061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177127365440586306855184325 33211381020109932535347061)
                    ·
                      refine ⟨3113566970635306175188787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33211381020109932535347061 3113566970635306175188787)
                      ·
                        rfl

theorem cell23_6063650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_6063650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063650 prefixEnd_6063650 := by exact prefixLift 6063650
  have htrace : WordTrace (prefixWord ++ tailWord_6063650) baseStart_6063650 baseEnd_6063650 := by
    simpa [prefixWord, tailWord_6063650, baseEnd_6063650] using wordTrace_append hprefix tailTrace_6063650
  have hstable : (prefixWord ++ tailWord_6063650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063650).length < 2 ^ (prefixWord ++ tailWord_6063650).sum := by decide
  have hdescent : baseEnd_6063650 < baseStart_6063650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063687 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 2, 6]
def baseStart_6063687 : Nat := 118140960795 + 6063687 * 2 ^ 59
def prefixEnd_6063687 : Nat := 4983230072969 + 3 ^ 40 * 6063687 * 2
def baseEnd_6063687 : Nat := 1037861989806507510142039

theorem tailTrace_6063687 : CollatzResearch.WordTrace tailWord_6063687 prefixEnd_6063687 1037861989806507510142039 := by
  unfold tailWord_6063687
  simp only [CollatzResearch.WordTrace]
  refine ⟨221160833983305069136757315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147440555988870046091171543 221160833983305069136757315)
  ·
    refine ⟨331741250974957603705135973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221160833983305069136757315 331741250974957603705135973)
    ·
      refine ⟨62201484557804550694712995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331741250974957603705135973 62201484557804550694712995)
      ·
        refine ⟨93302226836706826042069493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62201484557804550694712995 93302226836706826042069493)
        ·
          refine ⟨8747083765941264941444015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93302226836706826042069493 8747083765941264941444015)
          ·
            refine ⟨13120625648911897412166023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8747083765941264941444015 13120625648911897412166023)
            ·
              refine ⟨19680938473367846118249035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13120625648911897412166023 19680938473367846118249035)
              ·
                refine ⟨29521407710051769177373553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19680938473367846118249035 29521407710051769177373553)
                ·
                  refine ⟨22141055782538826883030165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29521407710051769177373553 22141055782538826883030165)
                  ·
                    refine ⟨1037861989806507510142039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22141055782538826883030165 1037861989806507510142039)
                    ·
                      rfl

theorem cell23_6063687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_6063687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063687 prefixEnd_6063687 := by exact prefixLift 6063687
  have htrace : WordTrace (prefixWord ++ tailWord_6063687) baseStart_6063687 baseEnd_6063687 := by
    simpa [prefixWord, tailWord_6063687, baseEnd_6063687] using wordTrace_append hprefix tailTrace_6063687
  have hstable : (prefixWord ++ tailWord_6063687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063687).length < 2 ^ (prefixWord ++ tailWord_6063687).sum := by decide
  have hdescent : baseEnd_6063687 < baseStart_6063687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063694 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_6063694 : Nat := 118140960795 + 6063694 * 2 ^ 59
def prefixEnd_6063694 : Nat := 4983230072969 + 3 ^ 40 * 6063694 * 2
def baseEnd_6063694 : Nat := 3113589563784104003038585

theorem tailTrace_6063694 : CollatzResearch.WordTrace tailWord_6063694 prefixEnd_6063694 3113589563784104003038585 := by
  unfold tailWord_6063694
  simp only [CollatzResearch.WordTrace]
  refine ⟨27645136161784963666532767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147440726196186472888174757 27645136161784963666532767)
  ·
    refine ⟨41467704242677445499799151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27645136161784963666532767 41467704242677445499799151)
    ·
      refine ⟨62201556364016168249698727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41467704242677445499799151 62201556364016168249698727)
      ·
        refine ⟨93302334546024252374548091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62201556364016168249698727 93302334546024252374548091)
        ·
          refine ⟨139953501819036378561822137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93302334546024252374548091 139953501819036378561822137)
          ·
            refine ⟨104965126364277283921366603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139953501819036378561822137 104965126364277283921366603)
            ·
              refine ⟨157447689546415925882049905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104965126364277283921366603 157447689546415925882049905)
              ·
                refine ⟨118085767159811944411537429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157447689546415925882049905 118085767159811944411537429)
                ·
                  refine ⟨5535270335616184894290817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118085767159811944411537429 5535270335616184894290817)
                  ·
                    refine ⟨4151452751712138670718113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5535270335616184894290817 4151452751712138670718113)
                    ·
                      refine ⟨3113589563784104003038585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4151452751712138670718113 3113589563784104003038585)
                      ·
                        rfl

theorem cell23_6063694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_6063694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063694 prefixEnd_6063694 := by exact prefixLift 6063694
  have htrace : WordTrace (prefixWord ++ tailWord_6063694) baseStart_6063694 baseEnd_6063694 := by
    simpa [prefixWord, tailWord_6063694, baseEnd_6063694] using wordTrace_append hprefix tailTrace_6063694
  have hstable : (prefixWord ++ tailWord_6063694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063694).length < 2 ^ (prefixWord ++ tailWord_6063694).sum := by decide
  have hdescent : baseEnd_6063694 < baseStart_6063694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063728 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 2, 2, 2]
def baseStart_6063728 : Nat := 118140960795 + 6063728 * 2 ^ 59
def prefixEnd_6063728 : Nat := 4983230072969 + 3 ^ 40 * 6063728 * 2
def baseEnd_6063728 : Nat := 3113607022126356870013429

theorem tailTrace_6063728 : CollatzResearch.WordTrace tailWord_6063728 prefixEnd_6063728 3113607022126356870013429 := by
  unfold tailWord_6063728
  simp only [CollatzResearch.WordTrace]
  refine ⟨110581164688078266569499919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147441552917437688759333225 110581164688078266569499919)
  ·
    refine ⟨165871747032117399854249879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110581164688078266569499919 165871747032117399854249879)
    ·
      refine ⟨248807620548176099781374819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165871747032117399854249879 248807620548176099781374819)
      ·
        refine ⟨373211430822264149672062229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248807620548176099781374819 373211430822264149672062229)
        ·
          refine ⟨17494285819793632015877917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 373211430822264149672062229 17494285819793632015877917)
          ·
            refine ⟨6560357182422612005954219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17494285819793632015877917 6560357182422612005954219)
            ·
              refine ⟨9840535773633918008931329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6560357182422612005954219 9840535773633918008931329)
              ·
                refine ⟨7380401830225438506698497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9840535773633918008931329 7380401830225438506698497)
                ·
                  refine ⟨5535301372669078880023873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7380401830225438506698497 5535301372669078880023873)
                  ·
                    refine ⟨4151476029501809160017905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5535301372669078880023873 4151476029501809160017905)
                    ·
                      refine ⟨3113607022126356870013429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4151476029501809160017905 3113607022126356870013429)
                      ·
                        rfl

theorem cell23_6063728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 2, 2].length) (baseStart_6063728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063728 prefixEnd_6063728 := by exact prefixLift 6063728
  have htrace : WordTrace (prefixWord ++ tailWord_6063728) baseStart_6063728 baseEnd_6063728 := by
    simpa [prefixWord, tailWord_6063728, baseEnd_6063728] using wordTrace_append hprefix tailTrace_6063728
  have hstable : (prefixWord ++ tailWord_6063728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063728).length < 2 ^ (prefixWord ++ tailWord_6063728).sum := by decide
  have hdescent : baseEnd_6063728 < baseStart_6063728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063734 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_6063734 : Nat := 118140960795 + 6063734 * 2 ^ 59
def prefixEnd_6063734 : Nat := 4983230072969 + 3 ^ 40 * 6063734 * 2
def baseEnd_6063734 : Nat := 345956678112253760726489

theorem tailTrace_6063734 : CollatzResearch.WordTrace tailWord_6063734 prefixEnd_6063734 345956678112253760726489 := by
  unfold tailWord_6063734
  simp only [CollatzResearch.WordTrace]
  refine ⟨13822659263383424760232391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147441698809423197442478837 13822659263383424760232391)
  ·
    refine ⟨20733988895075137140348587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13822659263383424760232391 20733988895075137140348587)
    ·
      refine ⟨31100983342612705710522881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20733988895075137140348587 31100983342612705710522881)
      ·
        refine ⟨23325737506959529282892161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31100983342612705710522881 23325737506959529282892161)
        ·
          refine ⟨17494303130219646962169121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23325737506959529282892161 17494303130219646962169121)
          ·
            refine ⟨13120727347664735221626841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17494303130219646962169121 13120727347664735221626841)
            ·
              refine ⟨9840545510748551416220131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13120727347664735221626841 9840545510748551416220131)
              ·
                refine ⟨14760818266122827124330197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9840545510748551416220131 14760818266122827124330197)
                ·
                  refine ⟨345956678112253760726489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14760818266122827124330197 345956678112253760726489)
                  ·
                    rfl

theorem cell23_6063734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_6063734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063734 prefixEnd_6063734 := by exact prefixLift 6063734
  have htrace : WordTrace (prefixWord ++ tailWord_6063734) baseStart_6063734 baseEnd_6063734 := by
    simpa [prefixWord, tailWord_6063734, baseEnd_6063734] using wordTrace_append hprefix tailTrace_6063734
  have hstable : (prefixWord ++ tailWord_6063734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063734).length < 2 ^ (prefixWord ++ tailWord_6063734).sum := by decide
  have hdescent : baseEnd_6063734 < baseStart_6063734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063740 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_6063740 : Nat := 118140960795 + 6063740 * 2 ^ 59
def prefixEnd_6063740 : Nat := 4983230072969 + 3 ^ 40 * 6063740 * 2
def baseEnd_6063740 : Nat := 3113613183894210823063373

theorem tailTrace_6063740 : CollatzResearch.WordTrace tailWord_6063740 prefixEnd_6063740 3113613183894210823063373 := by
  unfold tailWord_6063740
  simp only [CollatzResearch.WordTrace]
  refine ⟨110581383526056529594218337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147441844701408706125624449 110581383526056529594218337)
  ·
    refine ⟨82936037644542397195663753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110581383526056529594218337 82936037644542397195663753)
    ·
      refine ⟨62202028233406797896747815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82936037644542397195663753 62202028233406797896747815)
      ·
        refine ⟨93303042350110196845121723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62202028233406797896747815 93303042350110196845121723)
        ·
          refine ⟨139954563525165295267682585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93303042350110196845121723 139954563525165295267682585)
          ·
            refine ⟨104965922643873971450761939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139954563525165295267682585 104965922643873971450761939)
            ·
              refine ⟨157448883965810957176142909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104965922643873971450761939 157448883965810957176142909)
              ·
                refine ⟨59043331487179108941053591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157448883965810957176142909 59043331487179108941053591)
                ·
                  refine ⟨88564997230768663411580387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59043331487179108941053591 88564997230768663411580387)
                  ·
                    refine ⟨132847495846152995117370581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88564997230768663411580387 132847495846152995117370581)
                    ·
                      refine ⟨3113613183894210823063373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132847495846152995117370581 3113613183894210823063373)
                      ·
                        rfl

theorem cell23_6063740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_6063740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063740 prefixEnd_6063740 := by exact prefixLift 6063740
  have htrace : WordTrace (prefixWord ++ tailWord_6063740) baseStart_6063740 baseEnd_6063740 := by
    simpa [prefixWord, tailWord_6063740, baseEnd_6063740] using wordTrace_append hprefix tailTrace_6063740
  have hstable : (prefixWord ++ tailWord_6063740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063740).length < 2 ^ (prefixWord ++ tailWord_6063740).sum := by decide
  have hdescent : baseEnd_6063740 < baseStart_6063740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063767 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_6063767 : Nat := 118140960795 + 6063767 * 2 ^ 59
def prefixEnd_6063767 : Nat := 4983230072969 + 3 ^ 40 * 6063767 * 2
def baseEnd_6063767 : Nat := 3113627047871882217425749

theorem tailTrace_6063767 : CollatzResearch.WordTrace tailWord_6063767 prefixEnd_6063767 3113627047871882217425749 := by
  unfold tailWord_6063767
  simp only [CollatzResearch.WordTrace]
  refine ⟨221163751823015242799669555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147442501215343495199779703 221163751823015242799669555)
  ·
    refine ⟨331745627734522864199504333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221163751823015242799669555 331745627734522864199504333)
    ·
      refine ⟨124404610400446074074814125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331745627734522864199504333 124404610400446074074814125)
      ·
        refine ⟨46651728900167277778055297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124404610400446074074814125 46651728900167277778055297)
        ·
          refine ⟨34988796675125458333541473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46651728900167277778055297 34988796675125458333541473)
          ·
            refine ⟨26241597506344093750156105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34988796675125458333541473 26241597506344093750156105)
            ·
              refine ⟨19681198129758070312617079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26241597506344093750156105 19681198129758070312617079)
              ·
                refine ⟨29521797194637105468925619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19681198129758070312617079 29521797194637105468925619)
                ·
                  refine ⟨44282695791955658203388429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29521797194637105468925619 44282695791955658203388429)
                  ·
                    refine ⟨16606010921983371826270661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44282695791955658203388429 16606010921983371826270661)
                    ·
                      refine ⟨3113627047871882217425749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16606010921983371826270661 3113627047871882217425749)
                      ·
                        rfl

theorem cell23_6063767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_6063767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063767 prefixEnd_6063767 := by exact prefixLift 6063767
  have htrace : WordTrace (prefixWord ++ tailWord_6063767) baseStart_6063767 baseEnd_6063767 := by
    simpa [prefixWord, tailWord_6063767, baseEnd_6063767] using wordTrace_append hprefix tailTrace_6063767
  have hstable : (prefixWord ++ tailWord_6063767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063767).length < 2 ^ (prefixWord ++ tailWord_6063767).sum := by decide
  have hdescent : baseEnd_6063767 < baseStart_6063767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063794 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_6063794 : Nat := 118140960795 + 6063794 * 2 ^ 59
def prefixEnd_6063794 : Nat := 4983230072969 + 3 ^ 40 * 6063794 * 2
def baseEnd_6063794 : Nat := 1037880303949851203929375

theorem tailTrace_6063794 : CollatzResearch.WordTrace tailWord_6063794 prefixEnd_6063794 1037880303949851203929375 := by
  unfold tailWord_6063794
  simp only [CollatzResearch.WordTrace]
  refine ⟨55291184148479356602725609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147443157729278284273934957 55291184148479356602725609)
  ·
    refine ⟨41468388111359517452044207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55291184148479356602725609 41468388111359517452044207)
    ·
      refine ⟨62202582167039276178066311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41468388111359517452044207 62202582167039276178066311)
      ·
        refine ⟨93303873250558914267099467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62202582167039276178066311 93303873250558914267099467)
        ·
          refine ⟨139955809875838371400649201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93303873250558914267099467 139955809875838371400649201)
          ·
            refine ⟨104966857406878778550486901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139955809875838371400649201 104966857406878778550486901)
            ·
              refine ⟨9840642881894885489108147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104966857406878778550486901 9840642881894885489108147)
              ·
                refine ⟨14760964322842328233662221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9840642881894885489108147 14760964322842328233662221)
                ·
                  refine ⟨5535361621065873087623333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14760964322842328233662221 5535361621065873087623333)
                  ·
                    refine ⟨1037880303949851203929375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535361621065873087623333 1037880303949851203929375)
                    ·
                      rfl

theorem cell23_6063794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_6063794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063794 prefixEnd_6063794 := by exact prefixLift 6063794
  have htrace : WordTrace (prefixWord ++ tailWord_6063794) baseStart_6063794 baseEnd_6063794 := by
    simpa [prefixWord, tailWord_6063794, baseEnd_6063794] using wordTrace_append hprefix tailTrace_6063794
  have hstable : (prefixWord ++ tailWord_6063794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063794).length < 2 ^ (prefixWord ++ tailWord_6063794).sum := by decide
  have hdescent : baseEnd_6063794 < baseStart_6063794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063807 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 6]
def baseStart_6063807 : Nat := 118140960795 + 6063807 * 2 ^ 59
def prefixEnd_6063807 : Nat := 4983230072969 + 3 ^ 40 * 6063807 * 2
def baseEnd_6063807 : Nat := 345960843010895784547285

theorem tailTrace_6063807 : CollatzResearch.WordTrace tailWord_6063807 prefixEnd_6063807 345960843010895784547285 := by
  unfold tailWord_6063807
  simp only [CollatzResearch.WordTrace]
  refine ⟨221165210742870329631125675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147443473828580219754083783 221165210742870329631125675)
  ·
    refine ⟨331747816114305494446688513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221165210742870329631125675 331747816114305494446688513)
    ·
      refine ⟨248810862085729120835016385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331747816114305494446688513 248810862085729120835016385)
      ·
        refine ⟨186608146564296840626262289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248810862085729120835016385 186608146564296840626262289)
        ·
          refine ⟨139956109923222630469696717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186608146564296840626262289 139956109923222630469696717)
          ·
            refine ⟨52483541221208486426136269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139956109923222630469696717 52483541221208486426136269)
            ·
              refine ⟨19681327957953182409801101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52483541221208486426136269 19681327957953182409801101)
              ·
                refine ⟨7380497984232443403675413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19681327957953182409801101 7380497984232443403675413)
                ·
                  refine ⟨345960843010895784547285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7380497984232443403675413 345960843010895784547285)
                  ·
                    rfl

theorem cell23_6063807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 6].length) (baseStart_6063807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063807 prefixEnd_6063807 := by exact prefixLift 6063807
  have htrace : WordTrace (prefixWord ++ tailWord_6063807) baseStart_6063807 baseEnd_6063807 := by
    simpa [prefixWord, tailWord_6063807, baseEnd_6063807] using wordTrace_append hprefix tailTrace_6063807
  have hstable : (prefixWord ++ tailWord_6063807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063807).length < 2 ^ (prefixWord ++ tailWord_6063807).sum := by decide
  have hdescent : baseEnd_6063807 < baseStart_6063807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063887 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_6063887 : Nat := 118140960795 + 6063887 * 2 ^ 59
def prefixEnd_6063887 : Nat := 4983230072969 + 3 ^ 40 * 6063887 * 2
def baseEnd_6063887 : Nat := 3113688665550421747925197

theorem tailTrace_6063887 : CollatzResearch.WordTrace tailWord_6063887 prefixEnd_6063887 3113688665550421747925197 := by
  unfold tailWord_6063887
  simp only [CollatzResearch.WordTrace]
  refine ⟨221168128582580503294037915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147445419055053668862691943 221168128582580503294037915)
  ·
    refine ⟨331752192873870754941056873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221168128582580503294037915 331752192873870754941056873)
    ·
      refine ⟨248814144655403066205792655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331752192873870754941056873 248814144655403066205792655)
      ·
        refine ⟨373221216983104599308688983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248814144655403066205792655 373221216983104599308688983)
        ·
          refine ⟨559831825474656898963033475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373221216983104599308688983 559831825474656898963033475)
          ·
            refine ⟨839747738211985348444550213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559831825474656898963033475 839747738211985348444550213)
            ·
              refine ⟨157452700914747252833353165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 839747738211985348444550213 157452700914747252833353165)
              ·
                refine ⟨59044762843030219812507437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157452700914747252833353165 59044762843030219812507437)
                ·
                  refine ⟨22141786066136332429690289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59044762843030219812507437 22141786066136332429690289)
                  ·
                    refine ⟨16606339549602249322267717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22141786066136332429690289 16606339549602249322267717)
                    ·
                      refine ⟨3113688665550421747925197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16606339549602249322267717 3113688665550421747925197)
                      ·
                        rfl

theorem cell23_6063887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_6063887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063887 prefixEnd_6063887 := by exact prefixLift 6063887
  have htrace : WordTrace (prefixWord ++ tailWord_6063887) baseStart_6063887 baseEnd_6063887 := by
    simpa [prefixWord, tailWord_6063887, baseEnd_6063887] using wordTrace_append hprefix tailTrace_6063887
  have hstable : (prefixWord ++ tailWord_6063887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063887).length < 2 ^ (prefixWord ++ tailWord_6063887).sum := by decide
  have hdescent : baseEnd_6063887 < baseStart_6063887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063892 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 6]
def baseStart_6063892 : Nat := 118140960795 + 6063892 * 2 ^ 59
def prefixEnd_6063892 : Nat := 4983230072969 + 3 ^ 40 * 6063892 * 2
def baseEnd_6063892 : Nat := 345965692550410469818075

theorem tailTrace_6063892 : CollatzResearch.WordTrace tailWord_6063892 prefixEnd_6063892 345965692550410469818075 := by
  unfold tailWord_6063892
  simp only [CollatzResearch.WordTrace]
  refine ⟨110584155473781194573984965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147445540631708259431979953 110584155473781194573984965)
  ·
    refine ⟨20734529151333973982622181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110584155473781194573984965 20734529151333973982622181)
    ·
      refine ⟨3887724215875120121741659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20734529151333973982622181 3887724215875120121741659)
      ·
        refine ⟨5831586323812680182612489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3887724215875120121741659 5831586323812680182612489)
        ·
          refine ⟨4373689742859510136959367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5831586323812680182612489 4373689742859510136959367)
          ·
            refine ⟨6560534614289265205439051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4373689742859510136959367 6560534614289265205439051)
            ·
              refine ⟨9840801921433897808158577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6560534614289265205439051 9840801921433897808158577)
              ·
                refine ⟨7380601441075423356118933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9840801921433897808158577 7380601441075423356118933)
                ·
                  refine ⟨345965692550410469818075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7380601441075423356118933 345965692550410469818075)
                  ·
                    rfl

theorem cell23_6063892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_6063892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063892 prefixEnd_6063892 := by exact prefixLift 6063892
  have htrace : WordTrace (prefixWord ++ tailWord_6063892) baseStart_6063892 baseEnd_6063892 := by
    simpa [prefixWord, tailWord_6063892, baseEnd_6063892] using wordTrace_append hprefix tailTrace_6063892
  have hstable : (prefixWord ++ tailWord_6063892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063892).length < 2 ^ (prefixWord ++ tailWord_6063892).sum := by decide
  have hdescent : baseEnd_6063892 < baseStart_6063892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063902 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6063902 : Nat := 118140960795 + 6063902 * 2 ^ 59
def prefixEnd_6063902 : Nat := 4983230072969 + 3 ^ 40 * 6063902 * 2
def baseEnd_6063902 : Nat := 3113696367760239189237629

theorem tailTrace_6063902 : CollatzResearch.WordTrace tailWord_6063902 prefixEnd_6063902 3113696367760239189237629 := by
  unfold tailWord_6063902
  simp only [CollatzResearch.WordTrace]
  refine ⟨27646084459690770106979245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147445783785017440570555973 27646084459690770106979245)
  ·
    refine ⟨10367281672384038790117217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27646084459690770106979245 10367281672384038790117217)
    ·
      refine ⟨7775461254288029092587913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10367281672384038790117217 7775461254288029092587913)
      ·
        refine ⟨5831595940716021819440935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7775461254288029092587913 5831595940716021819440935)
        ·
          refine ⟨8747393911074032729161403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5831595940716021819440935 8747393911074032729161403)
          ·
            refine ⟨13121090866611049093742105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8747393911074032729161403 13121090866611049093742105)
            ·
              refine ⟨9840818149958286820306579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13121090866611049093742105 9840818149958286820306579)
              ·
                refine ⟨14761227224937430230459869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9840818149958286820306579 14761227224937430230459869)
                ·
                  refine ⟨5535460209351536336422451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14761227224937430230459869 5535460209351536336422451)
                  ·
                    refine ⟨8303190314027304504633677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5535460209351536336422451 8303190314027304504633677)
                    ·
                      refine ⟨3113696367760239189237629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8303190314027304504633677 3113696367760239189237629)
                      ·
                        rfl

theorem cell23_6063902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6063902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063902 prefixEnd_6063902 := by exact prefixLift 6063902
  have htrace : WordTrace (prefixWord ++ tailWord_6063902) baseStart_6063902 baseEnd_6063902 := by
    simpa [prefixWord, tailWord_6063902, baseEnd_6063902] using wordTrace_append hprefix tailTrace_6063902
  have hstable : (prefixWord ++ tailWord_6063902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063902).length < 2 ^ (prefixWord ++ tailWord_6063902).sum := by decide
  have hdescent : baseEnd_6063902 < baseStart_6063902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063908 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_6063908 : Nat := 118140960795 + 6063908 * 2 ^ 59
def prefixEnd_6063908 : Nat := 4983230072969 + 3 ^ 40 * 6063908 * 2
def baseEnd_6063908 : Nat := 3113699448644166165762601

theorem tailTrace_6063908 : CollatzResearch.WordTrace tailWord_6063908 prefixEnd_6063908 3113699448644166165762601 := by
  unfold tailWord_6063908
  simp only [CollatzResearch.WordTrace]
  refine ⟨110584447257752211940276189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147445929677002949253701585 110584447257752211940276189)
  ·
    refine ⟨41469167721657079477603571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110584447257752211940276189 41469167721657079477603571)
    ·
      refine ⟨62203751582485619216405357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41469167721657079477603571 62203751582485619216405357)
      ·
        refine ⟨23326406843432107206152009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62203751582485619216405357 23326406843432107206152009)
        ·
          refine ⟨17494805132574080404614007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23326406843432107206152009 17494805132574080404614007)
          ·
            refine ⟨26242207698861120606921011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17494805132574080404614007 26242207698861120606921011)
            ·
              refine ⟨39363311548291680910381517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26242207698861120606921011 39363311548291680910381517)
              ·
                refine ⟨14761241830609380341393069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39363311548291680910381517 14761241830609380341393069)
                ·
                  refine ⟨5535465686478517628022401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14761241830609380341393069 5535465686478517628022401)
                  ·
                    refine ⟨4151599264858888221016801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5535465686478517628022401 4151599264858888221016801)
                    ·
                      refine ⟨3113699448644166165762601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4151599264858888221016801 3113699448644166165762601)
                      ·
                        rfl

theorem cell23_6063908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_6063908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063908 prefixEnd_6063908 := by exact prefixLift 6063908
  have htrace : WordTrace (prefixWord ++ tailWord_6063908) baseStart_6063908 baseEnd_6063908 := by
    simpa [prefixWord, tailWord_6063908, baseEnd_6063908] using wordTrace_append hprefix tailTrace_6063908
  have hstable : (prefixWord ++ tailWord_6063908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063908).length < 2 ^ (prefixWord ++ tailWord_6063908).sum := by decide
  have hdescent : baseEnd_6063908 < baseStart_6063908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063918 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_6063918 : Nat := 118140960795 + 6063918 * 2 ^ 59
def prefixEnd_6063918 : Nat := 4983230072969 + 3 ^ 40 * 6063918 * 2
def baseEnd_6063918 : Nat := 1037901527816903708879185

theorem tailTrace_6063918 : CollatzResearch.WordTrace tailWord_6063918 prefixEnd_6063918 1037901527816903708879185 := by
  unfold tailWord_6063918
  simp only [CollatzResearch.WordTrace]
  refine ⟨27646157405683524448552051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147446172830312130392277605 27646157405683524448552051)
  ·
    refine ⟨41469236108525286672828077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27646157405683524448552051 41469236108525286672828077)
    ·
      refine ⟨15550963540696982502310529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41469236108525286672828077 15550963540696982502310529)
      ·
        refine ⟨11663222655522736876732897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15550963540696982502310529 11663222655522736876732897)
        ·
          refine ⟨8747416991642052657549673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11663222655522736876732897 8747416991642052657549673)
          ·
            refine ⟨6560562743731539493162255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8747416991642052657549673 6560562743731539493162255)
            ·
              refine ⟨9840844115597309239743383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6560562743731539493162255 9840844115597309239743383)
              ·
                refine ⟨14761266173395963859615075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9840844115597309239743383 14761266173395963859615075)
                ·
                  refine ⟨22141899260093945789422613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14761266173395963859615075 22141899260093945789422613)
                  ·
                    refine ⟨1037901527816903708879185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22141899260093945789422613 1037901527816903708879185)
                    ·
                      rfl

theorem cell23_6063918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_6063918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063918 prefixEnd_6063918 := by exact prefixLift 6063918
  have htrace : WordTrace (prefixWord ++ tailWord_6063918) baseStart_6063918 baseEnd_6063918 := by
    simpa [prefixWord, tailWord_6063918, baseEnd_6063918] using wordTrace_append hprefix tailTrace_6063918
  have hstable : (prefixWord ++ tailWord_6063918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063918).length < 2 ^ (prefixWord ++ tailWord_6063918).sum := by decide
  have hdescent : baseEnd_6063918 < baseStart_6063918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063921 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 4]
def baseStart_6063921 : Nat := 118140960795 + 6063921 * 2 ^ 59
def prefixEnd_6063921 : Nat := 4983230072969 + 3 ^ 40 * 6063921 * 2
def baseEnd_6063921 : Nat := 3113706123892674614900041

theorem tailTrace_6063921 : CollatzResearch.WordTrace tailWord_6063921 prefixEnd_6063921 3113706123892674614900041 := by
  unfold tailWord_6063921
  simp only [CollatzResearch.WordTrace]
  refine ⟨221169368664457327100775617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147446245776304884733850411 221169368664457327100775617)
  ·
    refine ⟨165877026498342995325581713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221169368664457327100775617 165877026498342995325581713)
    ·
      refine ⟨124407769873757246494186285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165877026498342995325581713 124407769873757246494186285)
      ·
        refine ⟨46652913702658967435319857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124407769873757246494186285 46652913702658967435319857)
        ·
          refine ⟨34989685276994225576489893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46652913702658967435319857 34989685276994225576489893)
          ·
            refine ⟨6560565989436417295591855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34989685276994225576489893 6560565989436417295591855)
            ·
              refine ⟨9840848984154625943387783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6560565989436417295591855 9840848984154625943387783)
              ·
                refine ⟨14761273476231938915081675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9840848984154625943387783 14761273476231938915081675)
                ·
                  refine ⟨22141910214347908372622513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14761273476231938915081675 22141910214347908372622513)
                  ·
                    refine ⟨16606432660760931279466885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22141910214347908372622513 16606432660760931279466885)
                    ·
                      refine ⟨3113706123892674614900041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16606432660760931279466885 3113706123892674614900041)
                      ·
                        rfl

theorem cell23_6063921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_6063921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063921 prefixEnd_6063921 := by exact prefixLift 6063921
  have htrace : WordTrace (prefixWord ++ tailWord_6063921) baseStart_6063921 baseEnd_6063921 := by
    simpa [prefixWord, tailWord_6063921, baseEnd_6063921] using wordTrace_append hprefix tailTrace_6063921
  have hstable : (prefixWord ++ tailWord_6063921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063921).length < 2 ^ (prefixWord ++ tailWord_6063921).sum := by decide
  have hdescent : baseEnd_6063921 < baseStart_6063921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063977 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_6063977 : Nat := 118140960795 + 6063977 * 2 ^ 59
def prefixEnd_6063977 : Nat := 4983230072969 + 3 ^ 40 * 6063977 * 2
def baseEnd_6063977 : Nat := 3113734878809326395799783

theorem tailTrace_6063977 : CollatzResearch.WordTrace tailWord_6063977 prefixEnd_6063977 3113734878809326395799783 := by
  unfold tailWord_6063977
  simp only [CollatzResearch.WordTrace]
  refine ⟨221171411152254448664814185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147447607434836299109876123 221171411152254448664814185)
  ·
    refine ⟨165878558364190836498610639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221171411152254448664814185 165878558364190836498610639)
    ·
      refine ⟨248817837546286254747915959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165878558364190836498610639 248817837546286254747915959)
      ·
        refine ⟨373226756319429382121873939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248817837546286254747915959 373226756319429382121873939)
        ·
          refine ⟨559840134479144073182810909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373226756319429382121873939 559840134479144073182810909)
          ·
            refine ⟨209940050429679027443554091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559840134479144073182810909 209940050429679027443554091)
            ·
              refine ⟨314910075644518541165331137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209940050429679027443554091 314910075644518541165331137)
              ·
                refine ⟨236182556733388905873998353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314910075644518541165331137 236182556733388905873998353)
                ·
                  refine ⟨177136917550041679405498765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236182556733388905873998353 177136917550041679405498765)
                  ·
                    refine ⟨66426344081265629777062037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177136917550041679405498765 66426344081265629777062037)
                    ·
                      refine ⟨3113734878809326395799783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66426344081265629777062037 3113734878809326395799783)
                      ·
                        rfl

theorem cell23_6063977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_6063977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063977 prefixEnd_6063977 := by exact prefixLift 6063977
  have htrace : WordTrace (prefixWord ++ tailWord_6063977) baseStart_6063977 baseEnd_6063977 := by
    simpa [prefixWord, tailWord_6063977, baseEnd_6063977] using wordTrace_append hprefix tailTrace_6063977
  have hstable : (prefixWord ++ tailWord_6063977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063977).length < 2 ^ (prefixWord ++ tailWord_6063977).sum := by decide
  have hdescent : baseEnd_6063977 < baseStart_6063977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6063987 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 9]
def baseStart_6063987 : Nat := 118140960795 + 6063987 * 2 ^ 59
def prefixEnd_6063987 : Nat := 4983230072969 + 3 ^ 40 * 6063987 * 2
def baseEnd_6063987 : Nat := 345971112623985706297193

theorem tailTrace_6063987 : CollatzResearch.WordTrace tailWord_6063987 prefixEnd_6063987 345971112623985706297193 := by
  unfold tailWord_6063987
  simp only [CollatzResearch.WordTrace]
  refine ⟨221171775882218220372678215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147447850588145480248452143 221171775882218220372678215)
  ·
    refine ⟨331757663823327330559017323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221171775882218220372678215 331757663823327330559017323)
    ·
      refine ⟨497636495734990995838525985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331757663823327330559017323 497636495734990995838525985)
      ·
        refine ⟨373227371801243246878894489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497636495734990995838525985 373227371801243246878894489)
        ·
          refine ⟨279920528850932435159170867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373227371801243246878894489 279920528850932435159170867)
          ·
            refine ⟨419880793276398652738756301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279920528850932435159170867 419880793276398652738756301)
            ·
              refine ⟨157455297478649494777033613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419880793276398652738756301 157455297478649494777033613)
              ·
                refine ⟨59045736554493560541387605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157455297478649494777033613 59045736554493560541387605)
                ·
                  refine ⟨345971112623985706297193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59045736554493560541387605 345971112623985706297193)
                  ·
                    rfl

theorem cell23_6063987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 9].length) (baseStart_6063987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6063987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6063987 prefixEnd_6063987 := by exact prefixLift 6063987
  have htrace : WordTrace (prefixWord ++ tailWord_6063987) baseStart_6063987 baseEnd_6063987 := by
    simpa [prefixWord, tailWord_6063987, baseEnd_6063987] using wordTrace_append hprefix tailTrace_6063987
  have hstable : (prefixWord ++ tailWord_6063987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6063987).length < 2 ^ (prefixWord ++ tailWord_6063987).sum := by decide
  have hdescent : baseEnd_6063987 < baseStart_6063987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6063987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064021 : List Nat := [1, 3, 2, 1, 1, 3, 3, 4, 5]
def baseStart_6064021 : Nat := 118140960795 + 6064021 * 2 ^ 59
def prefixEnd_6064021 : Nat := 4983230072969 + 3 ^ 40 * 6064021 * 2
def baseEnd_6064021 : Nat := 345973052439791580405509

theorem tailTrace_6064021 : CollatzResearch.WordTrace tailWord_6064021 prefixEnd_6064021 345973052439791580405509 := by
  unfold tailWord_6064021
  simp only [CollatzResearch.WordTrace]
  refine ⟨221173015964095044179415917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147448677309396696119610611 221173015964095044179415917)
  ·
    refine ⟨82939880986535641567280969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221173015964095044179415917 82939880986535641567280969)
    ·
      refine ⟨62204910739901731175460727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82939880986535641567280969 62204910739901731175460727)
      ·
        refine ⟨93307366109852596763191091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62204910739901731175460727 93307366109852596763191091)
        ·
          refine ⟨139961049164778895144786637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93307366109852596763191091 139961049164778895144786637)
          ·
            refine ⟨52485393436792085679294989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139961049164778895144786637 52485393436792085679294989)
            ·
              refine ⟨19682022538797032129735621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52485393436792085679294989 19682022538797032129735621)
              ·
                refine ⟨3690379226024443524325429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19682022538797032129735621 3690379226024443524325429)
                ·
                  refine ⟨345973052439791580405509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3690379226024443524325429 345973052439791580405509)
                  ·
                    rfl

theorem cell23_6064021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_6064021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064021 prefixEnd_6064021 := by exact prefixLift 6064021
  have htrace : WordTrace (prefixWord ++ tailWord_6064021) baseStart_6064021 baseEnd_6064021 := by
    simpa [prefixWord, tailWord_6064021, baseEnd_6064021] using wordTrace_append hprefix tailTrace_6064021
  have hstable : (prefixWord ++ tailWord_6064021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064021).length < 2 ^ (prefixWord ++ tailWord_6064021).sum := by decide
  have hdescent : baseEnd_6064021 < baseStart_6064021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064074 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_6064074 : Nat := 118140960795 + 6064074 * 2 ^ 59
def prefixEnd_6064074 : Nat := 4983230072969 + 3 ^ 40 * 6064074 * 2
def baseEnd_6064074 : Nat := 3113784686432812516286837

theorem tailTrace_6064074 : CollatzResearch.WordTrace tailWord_6064074 prefixEnd_6064074 3113784686432812516286837 := by
  unfold tailWord_6064074
  simp only [CollatzResearch.WordTrace]
  refine ⟨55293737258225758557773819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147449966021935356154063517 55293737258225758557773819)
  ·
    refine ⟨82940605887338637836660729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55293737258225758557773819 82940605887338637836660729)
    ·
      refine ⟨62205454415503978377495547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82940605887338637836660729 62205454415503978377495547)
      ·
        refine ⟨93308181623255967566243321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62205454415503978377495547 93308181623255967566243321)
        ·
          refine ⟨69981136217441975674682491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93308181623255967566243321 69981136217441975674682491)
          ·
            refine ⟨104971704326162963512023737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69981136217441975674682491 104971704326162963512023737)
            ·
              refine ⟨78728778244622222634017803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104971704326162963512023737 78728778244622222634017803)
              ·
                refine ⟨118093167366933333951026705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78728778244622222634017803 118093167366933333951026705)
                ·
                  refine ⟨88569875525200000463270029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118093167366933333951026705 88569875525200000463270029)
                  ·
                    refine ⟨33213703321950000173726261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88569875525200000463270029 33213703321950000173726261)
                    ·
                      refine ⟨3113784686432812516286837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33213703321950000173726261 3113784686432812516286837)
                      ·
                        rfl

theorem cell23_6064074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_6064074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064074 prefixEnd_6064074 := by exact prefixLift 6064074
  have htrace : WordTrace (prefixWord ++ tailWord_6064074) baseStart_6064074 baseEnd_6064074 := by
    simpa [prefixWord, tailWord_6064074, baseEnd_6064074] using wordTrace_append hprefix tailTrace_6064074
  have hstable : (prefixWord ++ tailWord_6064074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064074).length < 2 ^ (prefixWord ++ tailWord_6064074).sum := by decide
  have hdescent : baseEnd_6064074 < baseStart_6064074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064132 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_6064132 : Nat := 118140960795 + 6064132 * 2 ^ 59
def prefixEnd_6064132 : Nat := 4983230072969 + 3 ^ 40 * 6064132 * 2
def baseEnd_6064132 : Nat := 1037938156103591096453857

theorem tailTrace_6064132 : CollatzResearch.WordTrace tailWord_6064132 prefixEnd_6064132 1037938156103591096453857 := by
  unfold tailWord_6064132
  simp only [CollatzResearch.WordTrace]
  refine ⟨110588532233346455068353325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147451376311128606757804433 110588532233346455068353325)
  ·
    refine ⟨41470699587504920650632497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110588532233346455068353325 41470699587504920650632497)
    ·
      refine ⟨31103024690628690487974373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41470699587504920650632497 31103024690628690487974373)
      ·
        refine ⟨5831817129492879466495195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31103024690628690487974373 5831817129492879466495195)
        ·
          refine ⟨8747725694239319199742793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5831817129492879466495195 8747725694239319199742793)
          ·
            refine ⟨6560794270679489399807095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8747725694239319199742793 6560794270679489399807095)
            ·
              refine ⟨9841191406019234099710643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6560794270679489399807095 9841191406019234099710643)
              ·
                refine ⟨14761787109028851149565965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9841191406019234099710643 14761787109028851149565965)
                ·
                  refine ⟨5535670165885819181087237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14761787109028851149565965 5535670165885819181087237)
                  ·
                    refine ⟨1037938156103591096453857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535670165885819181087237 1037938156103591096453857)
                    ·
                      rfl

theorem cell23_6064132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_6064132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064132 prefixEnd_6064132 := by exact prefixLift 6064132
  have htrace : WordTrace (prefixWord ++ tailWord_6064132) baseStart_6064132 baseEnd_6064132 := by
    simpa [prefixWord, tailWord_6064132, baseEnd_6064132] using wordTrace_append hprefix tailTrace_6064132
  have hstable : (prefixWord ++ tailWord_6064132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064132).length < 2 ^ (prefixWord ++ tailWord_6064132).sum := by decide
  have hdescent : baseEnd_6064132 < baseStart_6064132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064165 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 2, 3, 2]
def baseStart_6064165 : Nat := 118140960795 + 6064165 * 2 ^ 59
def prefixEnd_6064165 : Nat := 4983230072969 + 3 ^ 40 * 6064165 * 2
def baseEnd_6064165 : Nat := 3113831413172371660248919

theorem tailTrace_6064165 : CollatzResearch.WordTrace tailWord_6064165 prefixEnd_6064165 3113831413172371660248919 := by
  unfold tailWord_6064165
  simp only [CollatzResearch.WordTrace]
  refine ⟨221178268075573356772657949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147452178717048904515105299 221178268075573356772657949)
  ·
    refine ⟨82941850528340008789746731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221178268075573356772657949 82941850528340008789746731)
    ·
      refine ⟨124412775792510013184620097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82941850528340008789746731 124412775792510013184620097)
      ·
        refine ⟨93309581844382509888465073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124412775792510013184620097 93309581844382509888465073)
        ·
          refine ⟨69982186383286882416348805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93309581844382509888465073 69982186383286882416348805)
          ·
            refine ⟨13121659946866290453065401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69982186383286882416348805 13121659946866290453065401)
            ·
              refine ⟨9841244960149717839799051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13121659946866290453065401 9841244960149717839799051)
              ·
                refine ⟨14761867440224576759698577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9841244960149717839799051 14761867440224576759698577)
                ·
                  refine ⟨11071400580168432569773933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14761867440224576759698577 11071400580168432569773933)
                  ·
                    refine ⟨4151775217563162213665225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11071400580168432569773933 4151775217563162213665225)
                    ·
                      refine ⟨3113831413172371660248919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4151775217563162213665225 3113831413172371660248919)
                      ·
                        rfl

theorem cell23_6064165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_6064165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064165 prefixEnd_6064165 := by exact prefixLift 6064165
  have htrace : WordTrace (prefixWord ++ tailWord_6064165) baseStart_6064165 baseEnd_6064165 := by
    simpa [prefixWord, tailWord_6064165, baseEnd_6064165] using wordTrace_append hprefix tailTrace_6064165
  have hstable : (prefixWord ++ tailWord_6064165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064165).length < 2 ^ (prefixWord ++ tailWord_6064165).sum := by decide
  have hdescent : baseEnd_6064165 < baseStart_6064165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064171 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 4, 4]
def baseStart_6064171 : Nat := 118140960795 + 6064171 * 2 ^ 59
def prefixEnd_6064171 : Nat := 4983230072969 + 3 ^ 40 * 6064171 * 2
def baseEnd_6064171 : Nat := 1037944831352099545591297

theorem tailTrace_6064171 : CollatzResearch.WordTrace tailWord_6064171 prefixEnd_6064171 1037944831352099545591297 := by
  unfold tailWord_6064171
  simp only [CollatzResearch.WordTrace]
  refine ⟨221178486913551619797376367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147452324609034413198250911 221178486913551619797376367)
  ·
    refine ⟨331767730370327429696064551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221178486913551619797376367 331767730370327429696064551)
    ·
      refine ⟨497651595555491144544096827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331767730370327429696064551 497651595555491144544096827)
      ·
        refine ⟨746477393333236716816145241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497651595555491144544096827 746477393333236716816145241)
        ·
          refine ⟨559858044999927537612108931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746477393333236716816145241 559858044999927537612108931)
          ·
            refine ⟨839787067499891306418163397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559858044999927537612108931 839787067499891306418163397)
            ·
              refine ⟨157460075156229619953405637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 839787067499891306418163397 157460075156229619953405637)
              ·
                refine ⟨29523764091793053741263557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157460075156229619953405637 29523764091793053741263557)
                ·
                  refine ⟨5535705767211197576486917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29523764091793053741263557 5535705767211197576486917)
                  ·
                    refine ⟨1037944831352099545591297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535705767211197576486917 1037944831352099545591297)
                    ·
                      rfl

theorem cell23_6064171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 4].length) (baseStart_6064171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064171 prefixEnd_6064171 := by exact prefixLift 6064171
  have htrace : WordTrace (prefixWord ++ tailWord_6064171) baseStart_6064171 baseEnd_6064171 := by
    simpa [prefixWord, tailWord_6064171, baseEnd_6064171] using wordTrace_append hprefix tailTrace_6064171
  have hstable : (prefixWord ++ tailWord_6064171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064171).length < 2 ^ (prefixWord ++ tailWord_6064171).sum := by decide
  have hdescent : baseEnd_6064171 < baseStart_6064171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064184 : List Nat := [2, 1, 2, 1, 17]
def baseStart_6064184 : Nat := 118140960795 + 6064184 * 2 ^ 59
def prefixEnd_6064184 : Nat := 4983230072969 + 3 ^ 40 * 6064184 * 2
def baseEnd_6064184 : Nat := 4271387063518253890139

theorem tailTrace_6064184 : CollatzResearch.WordTrace tailWord_6064184 prefixEnd_6064184 4271387063518253890139 := by
  unfold tailWord_6064184
  simp only [CollatzResearch.WordTrace]
  refine ⟨110589480531252261508799803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147452640708336348678399737 110589480531252261508799803)
  ·
    refine ⟨165884220796878392263199705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110589480531252261508799803 165884220796878392263199705)
    ·
      refine ⟨124413165597658794197399779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165884220796878392263199705 124413165597658794197399779)
      ·
        refine ⟨186619748396488191296099669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124413165597658794197399779 186619748396488191296099669)
        ·
          refine ⟨4271387063518253890139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 186619748396488191296099669 4271387063518253890139)
          ·
            rfl

theorem cell23_6064184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 17].length) (baseStart_6064184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064184 prefixEnd_6064184 := by exact prefixLift 6064184
  have htrace : WordTrace (prefixWord ++ tailWord_6064184) baseStart_6064184 baseEnd_6064184 := by
    simpa [prefixWord, tailWord_6064184, baseEnd_6064184] using wordTrace_append hprefix tailTrace_6064184
  have hstable : (prefixWord ++ tailWord_6064184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064184).length < 2 ^ (prefixWord ++ tailWord_6064184).sum := by decide
  have hdescent : baseEnd_6064184 < baseStart_6064184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064205 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_6064205 : Nat := 118140960795 + 6064205 * 2 ^ 59
def prefixEnd_6064205 : Nat := 4983230072969 + 3 ^ 40 * 6064205 * 2
def baseEnd_6064205 : Nat := 1037950650799517167916245

theorem tailTrace_6064205 : CollatzResearch.WordTrace tailWord_6064205 prefixEnd_6064205 1037950650799517167916245 := by
  unfold tailWord_6064205
  simp only [CollatzResearch.WordTrace]
  refine ⟨221179726995428443604114069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147453151330285629069409379 221179726995428443604114069)
  ·
    refine ⟨10367799702910708293942847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221179726995428443604114069 10367799702910708293942847)
    ·
      refine ⟨15551699554366062440914271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10367799702910708293942847 15551699554366062440914271)
      ·
        refine ⟨23327549331549093661371407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15551699554366062440914271 23327549331549093661371407)
        ·
          refine ⟨34991323997323640492057111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23327549331549093661371407 34991323997323640492057111)
          ·
            refine ⟨52486985995985460738085667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34991323997323640492057111 52486985995985460738085667)
            ·
              refine ⟨78730478993978191107128501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52486985995985460738085667 78730478993978191107128501)
              ·
                refine ⟨7380982405685455416293297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78730478993978191107128501 7380982405685455416293297)
                ·
                  refine ⟨5535736804264091562219973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7380982405685455416293297 5535736804264091562219973)
                  ·
                    refine ⟨1037950650799517167916245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535736804264091562219973 1037950650799517167916245)
                    ·
                      rfl

theorem cell23_6064205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_6064205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064205 prefixEnd_6064205 := by exact prefixLift 6064205
  have htrace : WordTrace (prefixWord ++ tailWord_6064205) baseStart_6064205 baseEnd_6064205 := by
    simpa [prefixWord, tailWord_6064205, baseEnd_6064205] using wordTrace_append hprefix tailTrace_6064205
  have hstable : (prefixWord ++ tailWord_6064205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064205).length < 2 ^ (prefixWord ++ tailWord_6064205).sum := by decide
  have hdescent : baseEnd_6064205 < baseStart_6064205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064228 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_6064228 : Nat := 118140960795 + 6064228 * 2 ^ 59
def prefixEnd_6064228 : Nat := 4983230072969 + 3 ^ 40 * 6064228 * 2
def baseEnd_6064228 : Nat := 3113863762453604913761129

theorem tailTrace_6064228 : CollatzResearch.WordTrace tailWord_6064228 prefixEnd_6064228 3113863762453604913761129 := by
  unfold tailWord_6064228
  simp only [CollatzResearch.WordTrace]
  refine ⟨110590282937172559266100669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147453710582896745688134225 110590282937172559266100669)
  ·
    refine ⟨41471356101439709724787751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110590282937172559266100669 41471356101439709724787751)
    ·
      refine ⟨62207034152159564587181627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41471356101439709724787751 62207034152159564587181627)
      ·
        refine ⟨93310551228239346880772441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62207034152159564587181627 93310551228239346880772441)
        ·
          refine ⟨69982913421179510160579331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93310551228239346880772441 69982913421179510160579331)
          ·
            refine ⟨104974370131769265240868997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69982913421179510160579331 104974370131769265240868997)
            ·
              refine ⟨19682694399706737232662937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104974370131769265240868997 19682694399706737232662937)
              ·
                refine ⟨14762020799780052924497203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19682694399706737232662937 14762020799780052924497203)
                ·
                  refine ⟨22143031199670079386745805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14762020799780052924497203 22143031199670079386745805)
                  ·
                    refine ⟨8303636699876279770029677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22143031199670079386745805 8303636699876279770029677)
                    ·
                      refine ⟨3113863762453604913761129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8303636699876279770029677 3113863762453604913761129)
                      ·
                        rfl

theorem cell23_6064228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_6064228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064228 prefixEnd_6064228 := by exact prefixLift 6064228
  have htrace : WordTrace (prefixWord ++ tailWord_6064228) baseStart_6064228 baseEnd_6064228 := by
    simpa [prefixWord, tailWord_6064228, baseEnd_6064228] using wordTrace_append hprefix tailTrace_6064228
  have hstable : (prefixWord ++ tailWord_6064228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064228).length < 2 ^ (prefixWord ++ tailWord_6064228).sum := by decide
  have hdescent : baseEnd_6064228 < baseStart_6064228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064229 : List Nat := [1, 3, 1, 3, 2, 3, 2, 3, 1, 2, 2]
def baseStart_6064229 : Nat := 118140960795 + 6064229 * 2 ^ 59
def prefixEnd_6064229 : Nat := 4983230072969 + 3 ^ 40 * 6064229 * 2
def baseEnd_6064229 : Nat := 3113864275934259409848625

theorem tailTrace_6064229 : CollatzResearch.WordTrace tailWord_6064229 prefixEnd_6064229 3113864275934259409848625 := by
  unfold tailWord_6064229
  simp only [CollatzResearch.WordTrace]
  refine ⟨221180602347341495702987741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147453734898227663801991827 221180602347341495702987741)
  ·
    refine ⟨82942725880253060888620403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221180602347341495702987741 82942725880253060888620403)
    ·
      refine ⟨124414088820379591332930605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82942725880253060888620403 124414088820379591332930605)
      ·
        refine ⟨46655283307642346749848977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124414088820379591332930605 46655283307642346749848977)
        ·
          refine ⟨34991462480731760062386733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46655283307642346749848977 34991462480731760062386733)
          ·
            refine ⟨13121798430274410023395025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34991462480731760062386733 13121798430274410023395025)
            ·
              refine ⟨9841348822705807517546269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13121798430274410023395025 9841348822705807517546269)
              ·
                refine ⟨3690505808514677819079851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9841348822705807517546269 3690505808514677819079851)
                ·
                  refine ⟨5535758712772016728619777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690505808514677819079851 5535758712772016728619777)
                  ·
                    refine ⟨4151819034579012546464833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5535758712772016728619777 4151819034579012546464833)
                    ·
                      refine ⟨3113864275934259409848625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4151819034579012546464833 3113864275934259409848625)
                      ·
                        rfl

theorem cell23_6064229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_6064229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064229 prefixEnd_6064229 := by exact prefixLift 6064229
  have htrace : WordTrace (prefixWord ++ tailWord_6064229) baseStart_6064229 baseEnd_6064229 := by
    simpa [prefixWord, tailWord_6064229, baseEnd_6064229] using wordTrace_append hprefix tailTrace_6064229
  have hstable : (prefixWord ++ tailWord_6064229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064229).length < 2 ^ (prefixWord ++ tailWord_6064229).sum := by decide
  have hdescent : baseEnd_6064229 < baseStart_6064229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064281 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_6064281 : Nat := 118140960795 + 6064281 * 2 ^ 59
def prefixEnd_6064281 : Nat := 4983230072969 + 3 ^ 40 * 6064281 * 2
def baseEnd_6064281 : Nat := 3113890976928293206398385

theorem tailTrace_6064281 : CollatzResearch.WordTrace tailWord_6064281 prefixEnd_6064281 3113890976928293206398385 := by
  unfold tailWord_6064281
  simp only [CollatzResearch.WordTrace]
  refine ⟨221182498943153108583880697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147454999295435405722587131 221182498943153108583880697)
  ·
    refine ⟨165886874207364831437910523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221182498943153108583880697 165886874207364831437910523)
    ·
      refine ⟨248830311311047247156865785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165886874207364831437910523 248830311311047247156865785)
      ·
        refine ⟨186622733483285435367649339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248830311311047247156865785 186622733483285435367649339)
        ·
          refine ⟨279934100224928153051474009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186622733483285435367649339 279934100224928153051474009)
          ·
            refine ⟨209950575168696114788605507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279934100224928153051474009 209950575168696114788605507)
            ·
              refine ⟨314925862753044172182908261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209950575168696114788605507 314925862753044172182908261)
              ·
                refine ⟨59048599266195782284295299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314925862753044172182908261 59048599266195782284295299)
                ·
                  refine ⟨88572898899293673426442949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59048599266195782284295299 88572898899293673426442949)
                  ·
                    refine ⟨16607418543617563767458053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88572898899293673426442949 16607418543617563767458053)
                    ·
                      refine ⟨3113890976928293206398385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16607418543617563767458053 3113890976928293206398385)
                      ·
                        rfl

theorem cell23_6064281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_6064281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064281 prefixEnd_6064281 := by exact prefixLift 6064281
  have htrace : WordTrace (prefixWord ++ tailWord_6064281) baseStart_6064281 baseEnd_6064281 := by
    simpa [prefixWord, tailWord_6064281, baseEnd_6064281] using wordTrace_append hprefix tailTrace_6064281
  have hstable : (prefixWord ++ tailWord_6064281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064281).length < 2 ^ (prefixWord ++ tailWord_6064281).sum := by decide
  have hdescent : baseEnd_6064281 < baseStart_6064281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064288 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_6064288 : Nat := 118140960795 + 6064288 * 2 ^ 59
def prefixEnd_6064288 : Nat := 4983230072969 + 3 ^ 40 * 6064288 * 2
def baseEnd_6064288 : Nat := 3113894571292874679010853

theorem tailTrace_6064288 : CollatzResearch.WordTrace tailWord_6064288 prefixEnd_6064288 3113894571292874679010853 := by
  unfold tailWord_6064288
  simp only [CollatzResearch.WordTrace]
  refine ⟨110591377127063874389692759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147455169502751832519590345 110591377127063874389692759)
  ·
    refine ⟨165887065690595811584539139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110591377127063874389692759 165887065690595811584539139)
    ·
      refine ⟨248830598535893717376808709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165887065690595811584539139 248830598535893717376808709)
      ·
        refine ⟨46655737225480072008151633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248830598535893717376808709 46655737225480072008151633)
        ·
          refine ⟨34991802919110054006113725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46655737225480072008151633 34991802919110054006113725)
          ·
            refine ⟨13121926094666270252292647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34991802919110054006113725 13121926094666270252292647)
            ·
              refine ⟨19682889141999405378438971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13121926094666270252292647 19682889141999405378438971)
              ·
                refine ⟨29524333712999108067658457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19682889141999405378438971 29524333712999108067658457)
                ·
                  refine ⟨22143250284749331050743843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29524333712999108067658457 22143250284749331050743843)
                  ·
                    refine ⟨33214875427123996576115765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22143250284749331050743843 33214875427123996576115765)
                    ·
                      refine ⟨3113894571292874679010853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33214875427123996576115765 3113894571292874679010853)
                      ·
                        rfl

theorem cell23_6064288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_6064288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064288 prefixEnd_6064288 := by exact prefixLift 6064288
  have htrace : WordTrace (prefixWord ++ tailWord_6064288) baseStart_6064288 baseEnd_6064288 := by
    simpa [prefixWord, tailWord_6064288, baseEnd_6064288] using wordTrace_append hprefix tailTrace_6064288
  have hstable : (prefixWord ++ tailWord_6064288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064288).length < 2 ^ (prefixWord ++ tailWord_6064288).sum := by decide
  have hdescent : baseEnd_6064288 < baseStart_6064288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064322 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6064322 : Nat := 118140960795 + 6064322 * 2 ^ 59
def prefixEnd_6064322 : Nat := 4983230072969 + 3 ^ 40 * 6064322 * 2
def baseEnd_6064322 : Nat := 3113912029635127545985697

theorem tailTrace_6064322 : CollatzResearch.WordTrace tailWord_6064322 prefixEnd_6064322 3113912029635127545985697 := by
  unfold tailWord_6064322
  simp only [CollatzResearch.WordTrace]
  refine ⟨55295998584001143146530805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147455996224003048390748813 55295998584001143146530805)
  ·
    refine ⟨5183999867250107169987263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55295998584001143146530805 5183999867250107169987263)
    ·
      refine ⟨7775999800875160754980895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5183999867250107169987263 7775999800875160754980895)
      ·
        refine ⟨11663999701312741132471343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7775999800875160754980895 11663999701312741132471343)
        ·
          refine ⟨17495999551969111698707015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11663999701312741132471343 17495999551969111698707015)
          ·
            refine ⟨26243999327953667548060523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17495999551969111698707015 26243999327953667548060523)
            ·
              refine ⟨39365998991930501322090785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26243999327953667548060523 39365998991930501322090785)
              ·
                refine ⟨29524499243947875991568089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39365998991930501322090785 29524499243947875991568089)
                ·
                  refine ⟨22143374432960906993676067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29524499243947875991568089 22143374432960906993676067)
                  ·
                    refine ⟨33215061649441360490514101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22143374432960906993676067 33215061649441360490514101)
                    ·
                      refine ⟨3113912029635127545985697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33215061649441360490514101 3113912029635127545985697)
                      ·
                        rfl

theorem cell23_6064322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6064322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064322 prefixEnd_6064322 := by exact prefixLift 6064322
  have htrace : WordTrace (prefixWord ++ tailWord_6064322) baseStart_6064322 baseEnd_6064322 := by
    simpa [prefixWord, tailWord_6064322, baseEnd_6064322] using wordTrace_append hprefix tailTrace_6064322
  have hstable : (prefixWord ++ tailWord_6064322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064322).length < 2 ^ (prefixWord ++ tailWord_6064322).sum := by decide
  have hdescent : baseEnd_6064322 < baseStart_6064322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064331 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 7]
def baseStart_6064331 : Nat := 118140960795 + 6064331 * 2 ^ 59
def prefixEnd_6064331 : Nat := 4983230072969 + 3 ^ 40 * 6064331 * 2
def baseEnd_6064331 : Nat := 3113916650961018010773155

theorem tailTrace_6064331 : CollatzResearch.WordTrace tailWord_6064331 prefixEnd_6064331 3113916650961018010773155 := by
  unfold tailWord_6064331
  simp only [CollatzResearch.WordTrace]
  refine ⟨221184322592971967123200847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147456215061981311415467231 221184322592971967123200847)
  ·
    refine ⟨331776483889457950684801271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221184322592971967123200847 331776483889457950684801271)
    ·
      refine ⟨497664725834186926027201907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331776483889457950684801271 497664725834186926027201907)
      ·
        refine ⟨746497088751280389040802861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497664725834186926027201907 746497088751280389040802861)
        ·
          refine ⟨279936408281730145890301073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 746497088751280389040802861 279936408281730145890301073)
          ·
            refine ⟨209952306211297609417725805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279936408281730145890301073 209952306211297609417725805)
            ·
              refine ⟨78732114829236603531647177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209952306211297609417725805 78732114829236603531647177)
              ·
                refine ⟨59049086121927452648735383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78732114829236603531647177 59049086121927452648735383)
                ·
                  refine ⟨88573629182891178973103075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59049086121927452648735383 88573629182891178973103075)
                  ·
                    refine ⟨132860443774336768459654613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88573629182891178973103075 132860443774336768459654613)
                    ·
                      refine ⟨3113916650961018010773155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132860443774336768459654613 3113916650961018010773155)
                      ·
                        rfl

theorem cell23_6064331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_6064331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064331 prefixEnd_6064331 := by exact prefixLift 6064331
  have htrace : WordTrace (prefixWord ++ tailWord_6064331) baseStart_6064331 baseEnd_6064331 := by
    simpa [prefixWord, tailWord_6064331, baseEnd_6064331] using wordTrace_append hprefix tailTrace_6064331
  have hstable : (prefixWord ++ tailWord_6064331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064331).length < 2 ^ (prefixWord ++ tailWord_6064331).sum := by decide
  have hdescent : baseEnd_6064331 < baseStart_6064331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064359 : List Nat := [1, 1, 5, 3, 1, 3, 2, 2, 5]
def baseStart_6064359 : Nat := 118140960795 + 6064359 * 2 ^ 59
def prefixEnd_6064359 : Nat := 4983230072969 + 3 ^ 40 * 6064359 * 2
def baseEnd_6064359 : Nat := 345992336491038211247003

theorem tailTrace_6064359 : CollatzResearch.WordTrace tailWord_6064359 prefixEnd_6064359 345992336491038211247003 := by
  unfold tailWord_6064359
  simp only [CollatzResearch.WordTrace]
  refine ⟨221185343836870527905220131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147456895891247018603480087 221185343836870527905220131)
  ·
    refine ⟨331778015755305791857830197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221185343836870527905220131 331778015755305791857830197)
    ·
      refine ⟨31104188977059917986671581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 331778015755305791857830197 31104188977059917986671581)
      ·
        refine ⟨11664070866397469245001843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31104188977059917986671581 11664070866397469245001843)
        ·
          refine ⟨17496106299596203867502765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11664070866397469245001843 17496106299596203867502765)
          ·
            refine ⟨6561039862348576450313537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17496106299596203867502765 6561039862348576450313537)
            ·
              refine ⟨4920779896761432337735153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6561039862348576450313537 4920779896761432337735153)
              ·
                refine ⟨3690584922571074253301365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920779896761432337735153 3690584922571074253301365)
                ·
                  refine ⟨345992336491038211247003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3690584922571074253301365 345992336491038211247003)
                  ·
                    rfl

theorem cell23_6064359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 5].length) (baseStart_6064359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064359 prefixEnd_6064359 := by exact prefixLift 6064359
  have htrace : WordTrace (prefixWord ++ tailWord_6064359) baseStart_6064359 baseEnd_6064359 := by
    simpa [prefixWord, tailWord_6064359, baseEnd_6064359] using wordTrace_append hprefix tailTrace_6064359
  have hstable : (prefixWord ++ tailWord_6064359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064359).length < 2 ^ (prefixWord ++ tailWord_6064359).sum := by decide
  have hdescent : baseEnd_6064359 < baseStart_6064359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064368 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 7, 4]
def baseStart_6064368 : Nat := 118140960795 + 6064368 * 2 ^ 59
def prefixEnd_6064368 : Nat := 4983230072969 + 3 ^ 40 * 6064368 * 2
def baseEnd_6064368 : Nat := 1037978549915078122003495

theorem tailTrace_6064368 : CollatzResearch.WordTrace tailWord_6064368 prefixEnd_6064368 1037978549915078122003495 := by
  unfold tailWord_6064368
  simp only [CollatzResearch.WordTrace]
  refine ⟨110592836046918961221148879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147457114729225281628198505 110592836046918961221148879)
  ·
    refine ⟨165889254070378441831723319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110592836046918961221148879 165889254070378441831723319)
    ·
      refine ⟨248833881105567662747584979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165889254070378441831723319 248833881105567662747584979)
      ·
        refine ⟨373250821658351494121377469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248833881105567662747584979 373250821658351494121377469)
        ·
          refine ⟨139969058121881810295516551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373250821658351494121377469 139969058121881810295516551)
          ·
            refine ⟨209953587182822715443274827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139969058121881810295516551 209953587182822715443274827)
            ·
              refine ⟨314930380774234073164912241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209953587182822715443274827 314930380774234073164912241)
              ·
                refine ⟨236197785580675554873684181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314930380774234073164912241 236197785580675554873684181)
                ·
                  refine ⟨5535885599547083317351973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 236197785580675554873684181 5535885599547083317351973)
                  ·
                    refine ⟨1037978549915078122003495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535885599547083317351973 1037978549915078122003495)
                    ·
                      rfl

theorem cell23_6064368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 4].length) (baseStart_6064368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064368 prefixEnd_6064368 := by exact prefixLift 6064368
  have htrace : WordTrace (prefixWord ++ tailWord_6064368) baseStart_6064368 baseEnd_6064368 := by
    simpa [prefixWord, tailWord_6064368, baseEnd_6064368] using wordTrace_append hprefix tailTrace_6064368
  have hstable : (prefixWord ++ tailWord_6064368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064368).length < 2 ^ (prefixWord ++ tailWord_6064368).sum := by decide
  have hdescent : baseEnd_6064368 < baseStart_6064368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064385 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 3, 4]
def baseStart_6064385 : Nat := 118140960795 + 6064385 * 2 ^ 59
def prefixEnd_6064385 : Nat := 4983230072969 + 3 ^ 40 * 6064385 * 2
def baseEnd_6064385 : Nat := 1037981459638786933165969

theorem tailTrace_6064385 : CollatzResearch.WordTrace tailWord_6064385 prefixEnd_6064385 1037981459638786933165969 := by
  unfold tailWord_6064385
  simp only [CollatzResearch.WordTrace]
  refine ⟨221186292134776334345666609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147457528089850889563777739 221186292134776334345666609)
  ·
    refine ⟨165889719101082250759249957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221186292134776334345666609 165889719101082250759249957)
    ·
      refine ⟨31104322331452922017359367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165889719101082250759249957 31104322331452922017359367)
      ·
        refine ⟨46656483497179383026039051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31104322331452922017359367 46656483497179383026039051)
        ·
          refine ⟨69984725245769074539058577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46656483497179383026039051 69984725245769074539058577)
          ·
            refine ⟨52488543934326805904293933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69984725245769074539058577 52488543934326805904293933)
            ·
              refine ⟨19683203975372552214110225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52488543934326805904293933 19683203975372552214110225)
              ·
                refine ⟨14762402981529414160582669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19683203975372552214110225 14762402981529414160582669)
                ·
                  refine ⟨5535901118073530310218501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14762402981529414160582669 5535901118073530310218501)
                  ·
                    refine ⟨1037981459638786933165969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5535901118073530310218501 1037981459638786933165969)
                    ·
                      rfl

theorem cell23_6064385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_6064385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064385 prefixEnd_6064385 := by exact prefixLift 6064385
  have htrace : WordTrace (prefixWord ++ tailWord_6064385) baseStart_6064385 baseEnd_6064385 := by
    simpa [prefixWord, tailWord_6064385, baseEnd_6064385] using wordTrace_append hprefix tailTrace_6064385
  have hstable : (prefixWord ++ tailWord_6064385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064385).length < 2 ^ (prefixWord ++ tailWord_6064385).sum := by decide
  have hdescent : baseEnd_6064385 < baseStart_6064385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064392 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_6064392 : Nat := 118140960795 + 6064392 * 2 ^ 59
def prefixEnd_6064392 : Nat := 4983230072969 + 3 ^ 40 * 6064392 * 2
def baseEnd_6064392 : Nat := 3113947973280942272110375

theorem tailTrace_6064392 : CollatzResearch.WordTrace tailWord_6064392 prefixEnd_6064392 3113947973280942272110375 := by
  unfold tailWord_6064392
  simp only [CollatzResearch.WordTrace]
  refine ⟨110593273722875487270585715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147457698297167316360780953 110593273722875487270585715)
  ·
    refine ⟨165889910584313230905878573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110593273722875487270585715 165889910584313230905878573)
    ·
      refine ⟨62208716469117461589704465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165889910584313230905878573 62208716469117461589704465)
      ·
        refine ⟨46656537351838096192278349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62208716469117461589704465 46656537351838096192278349)
        ·
          refine ⟨17496201506939286072104381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46656537351838096192278349 17496201506939286072104381)
          ·
            refine ⟨6561075565102232277039143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17496201506939286072104381 6561075565102232277039143)
            ·
              refine ⟨9841613347653348415558715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6561075565102232277039143 9841613347653348415558715)
              ·
                refine ⟨14762420021480022623338073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9841613347653348415558715 14762420021480022623338073)
                ·
                  refine ⟨11071815016110016967503555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14762420021480022623338073 11071815016110016967503555)
                  ·
                    refine ⟨16607722524165025451255333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11071815016110016967503555 16607722524165025451255333)
                    ·
                      refine ⟨3113947973280942272110375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16607722524165025451255333 3113947973280942272110375)
                      ·
                        rfl

theorem cell23_6064392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_6064392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064392 prefixEnd_6064392 := by exact prefixLift 6064392
  have htrace : WordTrace (prefixWord ++ tailWord_6064392) baseStart_6064392 baseEnd_6064392 := by
    simpa [prefixWord, tailWord_6064392, baseEnd_6064392] using wordTrace_append hprefix tailTrace_6064392
  have hstable : (prefixWord ++ tailWord_6064392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064392).length < 2 ^ (prefixWord ++ tailWord_6064392).sum := by decide
  have hdescent : baseEnd_6064392 < baseStart_6064392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064398 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_6064398 : Nat := 118140960795 + 6064398 * 2 ^ 59
def prefixEnd_6064398 : Nat := 4983230072969 + 3 ^ 40 * 6064398 * 2
def baseEnd_6064398 : Nat := 345994561573874360959483

theorem tailTrace_6064398 : CollatzResearch.WordTrace tailWord_6064398 prefixEnd_6064398 345994561573874360959483 := by
  unfold tailWord_6064398
  simp only [CollatzResearch.WordTrace]
  refine ⟨27648345785466154695736231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147457844189152825043926565 27648345785466154695736231)
  ·
    refine ⟨41472518678199232043604347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27648345785466154695736231 41472518678199232043604347)
    ·
      refine ⟨62208778017298848065406521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41472518678199232043604347 62208778017298848065406521)
      ·
        refine ⟨46656583512974136049054891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62208778017298848065406521 46656583512974136049054891)
        ·
          refine ⟨69984875269461204073582337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46656583512974136049054891 69984875269461204073582337)
          ·
            refine ⟨52488656452095903055186753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69984875269461204073582337 52488656452095903055186753)
            ·
              refine ⟨39366492339071927291390065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52488656452095903055186753 39366492339071927291390065)
              ·
                refine ⟨29524869254303945468542549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39366492339071927291390065 29524869254303945468542549)
                ·
                  refine ⟨345994561573874360959483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29524869254303945468542549 345994561573874360959483)
                  ·
                    rfl

theorem cell23_6064398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_6064398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064398 prefixEnd_6064398 := by exact prefixLift 6064398
  have htrace : WordTrace (prefixWord ++ tailWord_6064398) baseStart_6064398 baseEnd_6064398 := by
    simpa [prefixWord, tailWord_6064398, baseEnd_6064398] using wordTrace_append hprefix tailTrace_6064398
  have hstable : (prefixWord ++ tailWord_6064398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064398).length < 2 ^ (prefixWord ++ tailWord_6064398).sum := by decide
  have hdescent : baseEnd_6064398 < baseStart_6064398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064415 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 6]
def baseStart_6064415 : Nat := 118140960795 + 6064415 * 2 ^ 59
def prefixEnd_6064415 : Nat := 4983230072969 + 3 ^ 40 * 6064415 * 2
def baseEnd_6064415 : Nat := 345995531481777298013641

theorem tailTrace_6064415 : CollatzResearch.WordTrace tailWord_6064415 prefixEnd_6064415 345995531481777298013641 := by
  unfold tailWord_6064415
  simp only [CollatzResearch.WordTrace]
  refine ⟨221187386324667649469258699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147458257549778432979505799 221187386324667649469258699)
  ·
    refine ⟨331781079487001474203888049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221187386324667649469258699 331781079487001474203888049)
    ·
      refine ⟨248835809615251105652916037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331781079487001474203888049 248835809615251105652916037)
      ·
        refine ⟨46656714302859582309921757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248835809615251105652916037 46656714302859582309921757)
        ·
          refine ⟨17496267863572343366220659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46656714302859582309921757 17496267863572343366220659)
          ·
            refine ⟨26244401795358515049330989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17496267863572343366220659 26244401795358515049330989)
            ·
              refine ⟨9841650673259443143499121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26244401795358515049330989 9841650673259443143499121)
              ·
                refine ⟨7381238004944582357624341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9841650673259443143499121 7381238004944582357624341)
                ·
                  refine ⟨345995531481777298013641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7381238004944582357624341 345995531481777298013641)
                  ·
                    rfl

theorem cell23_6064415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 6].length) (baseStart_6064415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064415 prefixEnd_6064415 := by exact prefixLift 6064415
  have htrace : WordTrace (prefixWord ++ tailWord_6064415) baseStart_6064415 baseEnd_6064415 := by
    simpa [prefixWord, tailWord_6064415, baseEnd_6064415] using wordTrace_append hprefix tailTrace_6064415
  have hstable : (prefixWord ++ tailWord_6064415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064415).length < 2 ^ (prefixWord ++ tailWord_6064415).sum := by decide
  have hdescent : baseEnd_6064415 < baseStart_6064415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064428 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_6064428 : Nat := 118140960795 + 6064428 * 2 ^ 59
def prefixEnd_6064428 : Nat := 4983230072969 + 3 ^ 40 * 6064428 * 2
def baseEnd_6064428 : Nat := 1037988819528168043753403

theorem tailTrace_6064428 : CollatzResearch.WordTrace tailWord_6064428 prefixEnd_6064428 1037988819528168043753403 := by
  unfold tailWord_6064428
  simp only [CollatzResearch.WordTrace]
  refine ⟨110593930236810276344740969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147458573649080368459654625 110593930236810276344740969)
  ·
    refine ⟨82945447677607707258555727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110593930236810276344740969 82945447677607707258555727)
    ·
      refine ⟨124418171516411560887833591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82945447677607707258555727 124418171516411560887833591)
      ·
        refine ⟨186627257274617341331750387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124418171516411560887833591 186627257274617341331750387)
        ·
          refine ⟨279940885911926011997625581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186627257274617341331750387 279940885911926011997625581)
          ·
            refine ⟨104977832216972254499109593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279940885911926011997625581 104977832216972254499109593)
            ·
              refine ⟨78733374162729190874332195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104977832216972254499109593 78733374162729190874332195)
              ·
                refine ⟨118100061244093786311498293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78733374162729190874332195 118100061244093786311498293)
                ·
                  refine ⟨11071880741633792466702965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118100061244093786311498293 11071880741633792466702965)
                  ·
                    refine ⟨1037988819528168043753403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11071880741633792466702965 1037988819528168043753403)
                    ·
                      rfl

theorem cell23_6064428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_6064428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064428 prefixEnd_6064428 := by exact prefixLift 6064428
  have htrace : WordTrace (prefixWord ++ tailWord_6064428) baseStart_6064428 baseEnd_6064428 := by
    simpa [prefixWord, tailWord_6064428, baseEnd_6064428] using wordTrace_append hprefix tailTrace_6064428
  have hstable : (prefixWord ++ tailWord_6064428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064428).length < 2 ^ (prefixWord ++ tailWord_6064428).sum := by decide
  have hdescent : baseEnd_6064428 < baseStart_6064428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064435 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 3, 5, 2]
def baseStart_6064435 : Nat := 118140960795 + 6064435 * 2 ^ 59
def prefixEnd_6064435 : Nat := 4983230072969 + 3 ^ 40 * 6064435 * 2
def baseEnd_6064435 : Nat := 3113970052949085603872677

theorem tailTrace_6064435 : CollatzResearch.WordTrace tailWord_6064435 prefixEnd_6064435 3113970052949085603872677 := by
  unfold tailWord_6064435
  simp only [CollatzResearch.WordTrace]
  refine ⟨221188115784595192884986759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147458743856396795256657839 221188115784595192884986759)
  ·
    refine ⟨331782173676892789327480139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221188115784595192884986759 331782173676892789327480139)
    ·
      refine ⟨497673260515339183991220209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331782173676892789327480139 497673260515339183991220209)
      ·
        refine ⟨373254945386504387993415157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497673260515339183991220209 373254945386504387993415157)
        ·
          refine ⟨34992651129984786374382671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 373254945386504387993415157 34992651129984786374382671)
          ·
            refine ⟨52488976694977179561574007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34992651129984786374382671 52488976694977179561574007)
            ·
              refine ⟨78733465042465769342361011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52488976694977179561574007 78733465042465769342361011)
              ·
                refine ⟨118100197563698654013541517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78733465042465769342361011 118100197563698654013541517)
                ·
                  refine ⟨44287574086386995255078069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118100197563698654013541517 44287574086386995255078069)
                  ·
                    refine ⟨4151960070598780805163569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44287574086386995255078069 4151960070598780805163569)
                    ·
                      refine ⟨3113970052949085603872677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4151960070598780805163569 3113970052949085603872677)
                      ·
                        rfl

theorem cell23_6064435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 5, 2].length) (baseStart_6064435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064435 prefixEnd_6064435 := by exact prefixLift 6064435
  have htrace : WordTrace (prefixWord ++ tailWord_6064435) baseStart_6064435 baseEnd_6064435 := by
    simpa [prefixWord, tailWord_6064435, baseEnd_6064435] using wordTrace_append hprefix tailTrace_6064435
  have hstable : (prefixWord ++ tailWord_6064435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064435).length < 2 ^ (prefixWord ++ tailWord_6064435).sum := by decide
  have hdescent : baseEnd_6064435 < baseStart_6064435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064442 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3]
def baseStart_6064442 : Nat := 118140960795 + 6064442 * 2 ^ 59
def prefixEnd_6064442 : Nat := 4983230072969 + 3 ^ 40 * 6064442 * 2
def baseEnd_6064442 : Nat := 3113973647313667076485145

theorem tailTrace_6064442 : CollatzResearch.WordTrace tailWord_6064442 prefixEnd_6064442 3113973647313667076485145 := by
  unfold tailWord_6064442
  simp only [CollatzResearch.WordTrace]
  refine ⟨55297092773892458270122895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147458914063713222053661053 55297092773892458270122895)
  ·
    refine ⟨82945639160838687405184343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55297092773892458270122895 82945639160838687405184343)
    ·
      refine ⟨124418458741258031107776515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82945639160838687405184343 124418458741258031107776515)
      ·
        refine ⟨186627688111887046661664773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124418458741258031107776515 186627688111887046661664773)
        ·
          refine ⟨34992691520978821249062145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186627688111887046661664773 34992691520978821249062145)
          ·
            refine ⟨26244518640734115936796609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34992691520978821249062145 26244518640734115936796609)
            ·
              refine ⟨19683388980550586952597457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26244518640734115936796609 19683388980550586952597457)
              ·
                refine ⟨14762541735412940214448093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19683388980550586952597457 14762541735412940214448093)
                ·
                  refine ⟨5535953150779852580418035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14762541735412940214448093 5535953150779852580418035)
                  ·
                    refine ⟨8303929726169778870627053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5535953150779852580418035 8303929726169778870627053)
                    ·
                      refine ⟨3113973647313667076485145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8303929726169778870627053 3113973647313667076485145)
                      ·
                        rfl

theorem cell23_6064442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_6064442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064442 prefixEnd_6064442 := by exact prefixLift 6064442
  have htrace : WordTrace (prefixWord ++ tailWord_6064442) baseStart_6064442 baseEnd_6064442 := by
    simpa [prefixWord, tailWord_6064442, baseEnd_6064442] using wordTrace_append hprefix tailTrace_6064442
  have hstable : (prefixWord ++ tailWord_6064442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064442).length < 2 ^ (prefixWord ++ tailWord_6064442).sum := by decide
  have hdescent : baseEnd_6064442 < baseStart_6064442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064469 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_6064469 : Nat := 118140960795 + 6064469 * 2 ^ 59
def prefixEnd_6064469 : Nat := 4983230072969 + 3 ^ 40 * 6064469 * 2
def baseEnd_6064469 : Nat := 3113987511291338470847521

theorem tailTrace_6064469 : CollatzResearch.WordTrace tailWord_6064469 prefixEnd_6064469 3113987511291338470847521 := by
  unfold tailWord_6064469
  simp only [CollatzResearch.WordTrace]
  refine ⟨221189355866472016691724461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147459570577648011127816307 221189355866472016691724461)
  ·
    refine ⟨82946008449927006259396673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221189355866472016691724461 82946008449927006259396673)
    ·
      refine ⟨62209506337445254694547505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82946008449927006259396673 62209506337445254694547505)
      ·
        refine ⟨46657129753083941020910629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62209506337445254694547505 46657129753083941020910629)
        ·
          refine ⟨8748211828703238941420743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46657129753083941020910629 8748211828703238941420743)
          ·
            refine ⟨13122317743054858412131115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8748211828703238941420743 13122317743054858412131115)
            ·
              refine ⟨19683476614582287618196673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13122317743054858412131115 19683476614582287618196673)
              ·
                refine ⟨14762607460936715713647505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19683476614582287618196673 14762607460936715713647505)
                ·
                  refine ⟨11071955595702536785235629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14762607460936715713647505 11071955595702536785235629)
                  ·
                    refine ⟨4151983348388451294463361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11071955595702536785235629 4151983348388451294463361)
                    ·
                      refine ⟨3113987511291338470847521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4151983348388451294463361 3113987511291338470847521)
                      ·
                        rfl

theorem cell23_6064469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_6064469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064469 prefixEnd_6064469 := by exact prefixLift 6064469
  have htrace : WordTrace (prefixWord ++ tailWord_6064469) baseStart_6064469 baseEnd_6064469 := by
    simpa [prefixWord, tailWord_6064469, baseEnd_6064469] using wordTrace_append hprefix tailTrace_6064469
  have hstable : (prefixWord ++ tailWord_6064469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064469).length < 2 ^ (prefixWord ++ tailWord_6064469).sum := by decide
  have hdescent : baseEnd_6064469 < baseStart_6064469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064485 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_6064485 : Nat := 118140960795 + 6064485 * 2 ^ 59
def prefixEnd_6064485 : Nat := 4983230072969 + 3 ^ 40 * 6064485 * 2
def baseEnd_6064485 : Nat := 3113995726981810408247447

theorem tailTrace_6064485 : CollatzResearch.WordTrace tailWord_6064485 prefixEnd_6064485 3113995726981810408247447 := by
  unfold tailWord_6064485
  simp only [CollatzResearch.WordTrace]
  refine ⟨221189939434414051424306909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147459959622942700949537939 221189939434414051424306909)
  ·
    refine ⟨82946227287905269284115091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221189939434414051424306909 82946227287905269284115091)
    ·
      refine ⟨124419340931857903926172637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82946227287905269284115091 124419340931857903926172637)
      ·
        refine ⟨46657252849446713972314739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124419340931857903926172637 46657252849446713972314739)
        ·
          refine ⟨69985879274170070958472109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46657252849446713972314739 69985879274170070958472109)
          ·
            refine ⟨26244704727813776609427041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69985879274170070958472109 26244704727813776609427041)
            ·
              refine ⟨19683528545860332457070281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26244704727813776609427041 19683528545860332457070281)
              ·
                refine ⟨14762646409395249342802711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19683528545860332457070281 14762646409395249342802711)
                ·
                  refine ⟨22143969614092874014204067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14762646409395249342802711 22143969614092874014204067)
                  ·
                    refine ⟨33215954421139311021306101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22143969614092874014204067 33215954421139311021306101)
                    ·
                      refine ⟨3113995726981810408247447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33215954421139311021306101 3113995726981810408247447)
                      ·
                        rfl

theorem cell23_6064485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_6064485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064485 prefixEnd_6064485 := by exact prefixLift 6064485
  have htrace : WordTrace (prefixWord ++ tailWord_6064485) baseStart_6064485 baseEnd_6064485 := by
    simpa [prefixWord, tailWord_6064485, baseEnd_6064485] using wordTrace_append hprefix tailTrace_6064485
  have hstable : (prefixWord ++ tailWord_6064485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064485).length < 2 ^ (prefixWord ++ tailWord_6064485).sum := by decide
  have hdescent : baseEnd_6064485 < baseStart_6064485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064516 : List Nat := [2, 3, 2, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_6064516 : Nat := 118140960795 + 6064516 * 2 ^ 59
def prefixEnd_6064516 : Nat := 4983230072969 + 3 ^ 40 * 6064516 * 2
def baseEnd_6064516 : Nat := 3114011644882099786959805

theorem tailTrace_6064516 : CollatzResearch.WordTrace tailWord_6064516 prefixEnd_6064516 3114011644882099786959805 := by
  unfold tailWord_6064516
  simp only [CollatzResearch.WordTrace]
  refine ⟨110595535048650871859342701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147460713398201162479123601 110595535048650871859342701)
  ·
    refine ⟨41473325643244076947253513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110595535048650871859342701 41473325643244076947253513)
    ·
      refine ⟨31104994232433057710440135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41473325643244076947253513 31104994232433057710440135)
      ·
        refine ⟨46657491348649586565660203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31104994232433057710440135 46657491348649586565660203)
        ·
          refine ⟨69986237022974379848490305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46657491348649586565660203 69986237022974379848490305)
          ·
            refine ⟨52489677767230784886367729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69986237022974379848490305 52489677767230784886367729)
            ·
              refine ⟨39367258325423088664775797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52489677767230784886367729 39367258325423088664775797)
              ·
                refine ⟨3690680468008414562322731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39367258325423088664775797 3690680468008414562322731)
                ·
                  refine ⟨5536020702012621843484097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690680468008414562322731 5536020702012621843484097)
                  ·
                    refine ⟨4152015526509466382613073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5536020702012621843484097 4152015526509466382613073)
                    ·
                      refine ⟨3114011644882099786959805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4152015526509466382613073 3114011644882099786959805)
                      ·
                        rfl

theorem cell23_6064516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_6064516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064516 prefixEnd_6064516 := by exact prefixLift 6064516
  have htrace : WordTrace (prefixWord ++ tailWord_6064516) baseStart_6064516 baseEnd_6064516 := by
    simpa [prefixWord, tailWord_6064516, baseEnd_6064516] using wordTrace_append hprefix tailTrace_6064516
  have hstable : (prefixWord ++ tailWord_6064516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064516).length < 2 ^ (prefixWord ++ tailWord_6064516).sum := by decide
  have hdescent : baseEnd_6064516 < baseStart_6064516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064519 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_6064519 : Nat := 118140960795 + 6064519 * 2 ^ 59
def prefixEnd_6064519 : Nat := 4983230072969 + 3 ^ 40 * 6064519 * 2
def baseEnd_6064519 : Nat := 3114013185324063275222291

theorem tailTrace_6064519 : CollatzResearch.WordTrace tailWord_6064519 prefixEnd_6064519 3114013185324063275222291 := by
  unfold tailWord_6064519
  simp only [CollatzResearch.WordTrace]
  refine ⟨221191179516290875231044611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147460786344193916820696407 221191179516290875231044611)
  ·
    refine ⟨331786769274436312846566917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221191179516290875231044611 331786769274436312846566917)
    ·
      refine ⟨62210019238956808658731297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331786769274436312846566917 62210019238956808658731297)
      ·
        refine ⟨46657514429217606494048473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62210019238956808658731297 46657514429217606494048473)
        ·
          refine ⟨34993135821913204870536355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46657514429217606494048473 34993135821913204870536355)
          ·
            refine ⟨52489703732869807305804533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34993135821913204870536355 52489703732869807305804533)
            ·
              refine ⟨4920909724956544434919175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52489703732869807305804533 4920909724956544434919175)
              ·
                refine ⟨7381364587434816652378763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920909724956544434919175 7381364587434816652378763)
                ·
                  refine ⟨11072046881152224978568145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7381364587434816652378763 11072046881152224978568145)
                  ·
                    refine ⟨8304035160864168733926109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11072046881152224978568145 8304035160864168733926109)
                    ·
                      refine ⟨3114013185324063275222291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8304035160864168733926109 3114013185324063275222291)
                      ·
                        rfl

theorem cell23_6064519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_6064519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064519 prefixEnd_6064519 := by exact prefixLift 6064519
  have htrace : WordTrace (prefixWord ++ tailWord_6064519) baseStart_6064519 baseEnd_6064519 := by
    simpa [prefixWord, tailWord_6064519, baseEnd_6064519] using wordTrace_append hprefix tailTrace_6064519
  have hstable : (prefixWord ++ tailWord_6064519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064519).length < 2 ^ (prefixWord ++ tailWord_6064519).sum := by decide
  have hdescent : baseEnd_6064519 < baseStart_6064519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064522 : List Nat := [3, 1, 2, 5, 2, 10]
def baseStart_6064522 : Nat := 118140960795 + 6064522 * 2 ^ 59
def prefixEnd_6064522 : Nat := 4983230072969 + 3 ^ 40 * 6064522 * 2
def baseEnd_6064522 : Nat := 12814875414675007257139

theorem tailTrace_6064522 : CollatzResearch.WordTrace tailWord_6064522 prefixEnd_6064522 12814875414675007257139 := by
  unfold tailWord_6064522
  simp only [CollatzResearch.WordTrace]
  refine ⟨55297822233820001685850955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147460859290186671162269213 55297822233820001685850955)
  ·
    refine ⟨82946733350730002528776433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55297822233820001685850955 82946733350730002528776433)
    ·
      refine ⟨62210050013047501896582325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82946733350730002528776433 62210050013047501896582325)
      ·
        refine ⟨5832192188723203302804593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62210050013047501896582325 5832192188723203302804593)
        ·
          refine ⟨4374144141542402477103445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5832192188723203302804593 4374144141542402477103445)
          ·
            refine ⟨12814875414675007257139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4374144141542402477103445 12814875414675007257139)
            ·
              rfl

theorem cell23_6064522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 10].length) (baseStart_6064522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064522 prefixEnd_6064522 := by exact prefixLift 6064522
  have htrace : WordTrace (prefixWord ++ tailWord_6064522) baseStart_6064522 baseEnd_6064522 := by
    simpa [prefixWord, tailWord_6064522, baseEnd_6064522] using wordTrace_append hprefix tailTrace_6064522
  have hstable : (prefixWord ++ tailWord_6064522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064522).length < 2 ^ (prefixWord ++ tailWord_6064522).sum := by decide
  have hdescent : baseEnd_6064522 < baseStart_6064522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064585 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_6064585 : Nat := 118140960795 + 6064585 * 2 ^ 59
def prefixEnd_6064585 : Nat := 4983230072969 + 3 ^ 40 * 6064585 * 2
def baseEnd_6064585 : Nat := 3114047075047260016996987

theorem tailTrace_6064585 : CollatzResearch.WordTrace tailWord_6064585 prefixEnd_6064585 3114047075047260016996987 := by
  unfold tailWord_6064585
  simp only [CollatzResearch.WordTrace]
  refine ⟨221193586734051768502947209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147462391156034512335298139 221193586734051768502947209)
  ·
    refine ⟨165895190050538826377210407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221193586734051768502947209 165895190050538826377210407)
    ·
      refine ⟨248842785075808239565815611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165895190050538826377210407 248842785075808239565815611)
      ·
        refine ⟨373264177613712359348723417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248842785075808239565815611 373264177613712359348723417)
        ·
          refine ⟨279948133210284269511542563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373264177613712359348723417 279948133210284269511542563)
          ·
            refine ⟨419922199815426404267313845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279948133210284269511542563 419922199815426404267313845)
            ·
              refine ⟨39367706232696225400060673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 419922199815426404267313845 39367706232696225400060673)
              ·
                refine ⟨29525779674522169050045505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39367706232696225400060673 29525779674522169050045505)
                ·
                  refine ⟨22144334755891626787534129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29525779674522169050045505 22144334755891626787534129)
                  ·
                    refine ⟨16608251066918720090650597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22144334755891626787534129 16608251066918720090650597)
                    ·
                      refine ⟨3114047075047260016996987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16608251066918720090650597 3114047075047260016996987)
                      ·
                        rfl

theorem cell23_6064585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_6064585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064585 prefixEnd_6064585 := by exact prefixLift 6064585
  have htrace : WordTrace (prefixWord ++ tailWord_6064585) baseStart_6064585 baseEnd_6064585 := by
    simpa [prefixWord, tailWord_6064585, baseEnd_6064585] using wordTrace_append hprefix tailTrace_6064585
  have hstable : (prefixWord ++ tailWord_6064585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064585).length < 2 ^ (prefixWord ++ tailWord_6064585).sum := by decide
  have hdescent : baseEnd_6064585 < baseStart_6064585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064610 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6064610 : Nat := 118140960795 + 6064610 * 2 ^ 59
def prefixEnd_6064610 : Nat := 4983230072969 + 3 ^ 40 * 6064610 * 2
def baseEnd_6064610 : Nat := 3114059912063622419184373

theorem tailTrace_6064610 : CollatzResearch.WordTrace tailWord_6064610 prefixEnd_6064610 3114059912063622419184373 := by
  unfold tailWord_6064610
  simp only [CollatzResearch.WordTrace]
  refine ⟨55298624639740299443151821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147462999039307465181738189 55298624639740299443151821)
  ·
    refine ⟨20736984239902612291181933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55298624639740299443151821 20736984239902612291181933)
    ·
      refine ⟨7776369089963479609193225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20736984239902612291181933 7776369089963479609193225)
      ·
        refine ⟨5832276817472609706894919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7776369089963479609193225 5832276817472609706894919)
        ·
          refine ⟨8748415226208914560342379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832276817472609706894919 8748415226208914560342379)
          ·
            refine ⟨13122622839313371840513569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8748415226208914560342379 13122622839313371840513569)
            ·
              refine ⟨9841967129485028880385177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13122622839313371840513569 9841967129485028880385177)
              ·
                refine ⟨7381475347113771660288883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9841967129485028880385177 7381475347113771660288883)
                ·
                  refine ⟨11072213020670657490433325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7381475347113771660288883 11072213020670657490433325)
                  ·
                    refine ⟨4152079882751496558912497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11072213020670657490433325 4152079882751496558912497)
                    ·
                      refine ⟨3114059912063622419184373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4152079882751496558912497 3114059912063622419184373)
                      ·
                        rfl

theorem cell23_6064610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6064610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064610 prefixEnd_6064610 := by exact prefixLift 6064610
  have htrace : WordTrace (prefixWord ++ tailWord_6064610) baseStart_6064610 baseEnd_6064610 := by
    simpa [prefixWord, tailWord_6064610, baseEnd_6064610] using wordTrace_append hprefix tailTrace_6064610
  have hstable : (prefixWord ++ tailWord_6064610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064610).length < 2 ^ (prefixWord ++ tailWord_6064610).sum := by decide
  have hdescent : baseEnd_6064610 < baseStart_6064610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064625 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 1, 7]
def baseStart_6064625 : Nat := 118140960795 + 6064625 * 2 ^ 59
def prefixEnd_6064625 : Nat := 4983230072969 + 3 ^ 40 * 6064625 * 2
def baseEnd_6064625 : Nat := 1038022538091146620165601

theorem tailTrace_6064625 : CollatzResearch.WordTrace tailWord_6064625 prefixEnd_6064625 1038022538091146620165601 := by
  unfold tailWord_6064625
  simp only [CollatzResearch.WordTrace]
  refine ⟨221195045653906855334403329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147463363769271236889602219 221195045653906855334403329)
  ·
    refine ⟨165896284240430141500802497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221195045653906855334403329 165896284240430141500802497)
    ·
      refine ⟨124422213180322606125601873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165896284240430141500802497 124422213180322606125601873)
      ·
        refine ⟨93316659885241954594201405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124422213180322606125601873 93316659885241954594201405)
        ·
          refine ⟨34993747456965732972825527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93316659885241954594201405 34993747456965732972825527)
          ·
            refine ⟨52490621185448599459238291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34993747456965732972825527 52490621185448599459238291)
            ·
              refine ⟨78735931778172899188857437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52490621185448599459238291 78735931778172899188857437)
              ·
                refine ⟨29525974416814837195821539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78735931778172899188857437 29525974416814837195821539)
                ·
                  refine ⟨44288961625222255793732309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29525974416814837195821539 44288961625222255793732309)
                  ·
                    refine ⟨1038022538091146620165601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44288961625222255793732309 1038022538091146620165601)
                    ·
                      rfl

theorem cell23_6064625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_6064625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064625 prefixEnd_6064625 := by exact prefixLift 6064625
  have htrace : WordTrace (prefixWord ++ tailWord_6064625) baseStart_6064625 baseEnd_6064625 := by
    simpa [prefixWord, tailWord_6064625, baseEnd_6064625] using wordTrace_append hprefix tailTrace_6064625
  have hstable : (prefixWord ++ tailWord_6064625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064625).length < 2 ^ (prefixWord ++ tailWord_6064625).sum := by decide
  have hdescent : baseEnd_6064625 < baseStart_6064625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064652 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_6064652 : Nat := 118140960795 + 6064652 * 2 ^ 59
def prefixEnd_6064652 : Nat := 4983230072969 + 3 ^ 40 * 6064652 * 2
def baseEnd_6064652 : Nat := 3114081478251111254859179

theorem tailTrace_6064652 : CollatzResearch.WordTrace tailWord_6064652 prefixEnd_6064652 3114081478251111254859179 := by
  unfold tailWord_6064652
  simp only [CollatzResearch.WordTrace]
  refine ⟨110598015212404519472818105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147464020283206025963757473 110598015212404519472818105)
  ·
    refine ⟨82948511409303389604613579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110598015212404519472818105 82948511409303389604613579)
    ·
      refine ⟨124422767113955084406920369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82948511409303389604613579 124422767113955084406920369)
      ·
        refine ⟨93317075335466313305190277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124422767113955084406920369 93317075335466313305190277)
        ·
          refine ⟨17496951625399933744723177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93317075335466313305190277 17496951625399933744723177)
          ·
            refine ⟨13122713719049950308542383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17496951625399933744723177 13122713719049950308542383)
            ·
              refine ⟨19684070578574925462813575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13122713719049950308542383 19684070578574925462813575)
              ·
                refine ⟨29526105867862388194220363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19684070578574925462813575 29526105867862388194220363)
                ·
                  refine ⟨44289158801793582291330545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29526105867862388194220363 44289158801793582291330545)
                  ·
                    refine ⟨33216869101345186718497909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44289158801793582291330545 33216869101345186718497909)
                    ·
                      refine ⟨3114081478251111254859179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33216869101345186718497909 3114081478251111254859179)
                      ·
                        rfl

theorem cell23_6064652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_6064652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064652 prefixEnd_6064652 := by exact prefixLift 6064652
  have htrace : WordTrace (prefixWord ++ tailWord_6064652) baseStart_6064652 baseEnd_6064652 := by
    simpa [prefixWord, tailWord_6064652, baseEnd_6064652] using wordTrace_append hprefix tailTrace_6064652
  have hstable : (prefixWord ++ tailWord_6064652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064652).length < 2 ^ (prefixWord ++ tailWord_6064652).sum := by decide
  have hdescent : baseEnd_6064652 < baseStart_6064652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064676 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_6064676 : Nat := 118140960795 + 6064676 * 2 ^ 59
def prefixEnd_6064676 : Nat := 4983230072969 + 3 ^ 40 * 6064676 * 2
def baseEnd_6064676 : Nat := 1038031267262273053653023

theorem tailTrace_6064676 : CollatzResearch.WordTrace tailWord_6064676 prefixEnd_6064676 1038031267262273053653023 := by
  unfold tailWord_6064676
  simp only [CollatzResearch.WordTrace]
  refine ⟨110598452888361045522254941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147464603851148060696339921 110598452888361045522254941)
  ·
    refine ⟨41474419833135392070845603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110598452888361045522254941 41474419833135392070845603)
    ·
      refine ⟨62211629749703088106268405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41474419833135392070845603 62211629749703088106268405)
      ·
        refine ⟨5832340289034664509962663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62211629749703088106268405 5832340289034664509962663)
        ·
          refine ⟨8748510433551996764943995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832340289034664509962663 8748510433551996764943995)
          ·
            refine ⟨13122765650327995147415993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8748510433551996764943995 13122765650327995147415993)
            ·
              refine ⟨9842074237745996360561995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13122765650327995147415993 9842074237745996360561995)
              ·
                refine ⟨14763111356618994540842993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9842074237745996360561995 14763111356618994540842993)
                ·
                  refine ⟨11072333517464245905632245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14763111356618994540842993 11072333517464245905632245)
                  ·
                    refine ⟨1038031267262273053653023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11072333517464245905632245 1038031267262273053653023)
                    ·
                      rfl

theorem cell23_6064676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_6064676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064676 prefixEnd_6064676 := by exact prefixLift 6064676
  have htrace : WordTrace (prefixWord ++ tailWord_6064676) baseStart_6064676 baseEnd_6064676 := by
    simpa [prefixWord, tailWord_6064676, baseEnd_6064676] using wordTrace_append hprefix tailTrace_6064676
  have hstable : (prefixWord ++ tailWord_6064676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064676).length < 2 ^ (prefixWord ++ tailWord_6064676).sum := by decide
  have hdescent : baseEnd_6064676 < baseStart_6064676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064739 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 1, 5, 2]
def baseStart_6064739 : Nat := 118140960795 + 6064739 * 2 ^ 59
def prefixEnd_6064739 : Nat := 4983230072969 + 3 ^ 40 * 6064739 * 2
def baseEnd_6064739 : Nat := 3114126151068052414471279

theorem tailTrace_6064739 : CollatzResearch.WordTrace tailWord_6064739 prefixEnd_6064739 3114126151068052414471279 := by
  unfold tailWord_6064739
  simp only [CollatzResearch.WordTrace]
  refine ⟨221199203575493852804053271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147466135716995901869368847 221199203575493852804053271)
  ·
    refine ⟨331798805363240779206079907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221199203575493852804053271 331798805363240779206079907)
    ·
      refine ⟨497698208044861168809119861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331798805363240779206079907 497698208044861168809119861)
      ·
        refine ⟨46659207004205734575854987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 497698208044861168809119861 46659207004205734575854987)
        ·
          refine ⟨69988810506308601863782481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46659207004205734575854987 69988810506308601863782481)
          ·
            refine ⟨52491607879731451397836861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69988810506308601863782481 52491607879731451397836861)
            ·
              refine ⟨19684352954899294274188823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52491607879731451397836861 19684352954899294274188823)
              ·
                refine ⟨29526529432348941411283235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19684352954899294274188823 29526529432348941411283235)
                ·
                  refine ⟨44289794148523412116924853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29526529432348941411283235 44289794148523412116924853)
                  ·
                    refine ⟨4152168201424069885961705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44289794148523412116924853 4152168201424069885961705)
                    ·
                      refine ⟨3114126151068052414471279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4152168201424069885961705 3114126151068052414471279)
                      ·
                        rfl

theorem cell23_6064739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_6064739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064739 prefixEnd_6064739 := by exact prefixLift 6064739
  have htrace : WordTrace (prefixWord ++ tailWord_6064739) baseStart_6064739 baseEnd_6064739 := by
    simpa [prefixWord, tailWord_6064739, baseEnd_6064739] using wordTrace_append hprefix tailTrace_6064739
  have hstable : (prefixWord ++ tailWord_6064739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064739).length < 2 ^ (prefixWord ++ tailWord_6064739).sum := by decide
  have hdescent : baseEnd_6064739 < baseStart_6064739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064786 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_6064786 : Nat := 118140960795 + 6064786 * 2 ^ 59
def prefixEnd_6064786 : Nat := 4983230072969 + 3 ^ 40 * 6064786 * 2
def baseEnd_6064786 : Nat := 3114150284658813730583563

theorem tailTrace_6064786 : CollatzResearch.WordTrace tailWord_6064786 prefixEnd_6064786 3114150284658813730583563 := by
  unfold tailWord_6064786
  simp only [CollatzResearch.WordTrace]
  refine ⟨55300229451580894957753553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147467278537549053220676141 55300229451580894957753553)
  ·
    refine ⟨41475172088685671218315165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55300229451580894957753553 41475172088685671218315165)
    ·
      refine ⟨15553189533257126706868187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41475172088685671218315165 15553189533257126706868187)
      ·
        refine ⟨23329784299885690060302281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15553189533257126706868187 23329784299885690060302281)
        ·
          refine ⟨17497338224914267545226711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23329784299885690060302281 17497338224914267545226711)
          ·
            refine ⟨26246007337371401317840067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17497338224914267545226711 26246007337371401317840067)
            ·
              refine ⟨39369011006057101976760101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26246007337371401317840067 39369011006057101976760101)
              ·
                refine ⟨7381689563635706620642519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39369011006057101976760101 7381689563635706620642519)
                ·
                  refine ⟨11072534345453559930963779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7381689563635706620642519 11072534345453559930963779)
                  ·
                    refine ⟨16608801518180339896445669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11072534345453559930963779 16608801518180339896445669)
                    ·
                      refine ⟨3114150284658813730583563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16608801518180339896445669 3114150284658813730583563)
                      ·
                        rfl

theorem cell23_6064786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_6064786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064786 prefixEnd_6064786 := by exact prefixLift 6064786
  have htrace : WordTrace (prefixWord ++ tailWord_6064786) baseStart_6064786 baseEnd_6064786 := by
    simpa [prefixWord, tailWord_6064786, baseEnd_6064786] using wordTrace_append hprefix tailTrace_6064786
  have hstable : (prefixWord ++ tailWord_6064786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064786).length < 2 ^ (prefixWord ++ tailWord_6064786).sum := by decide
  have hdescent : baseEnd_6064786 < baseStart_6064786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064792 : List Nat := [2, 1, 2, 4, 1, 1, 3, 9]
def baseStart_6064792 : Nat := 118140960795 + 6064792 * 2 ^ 59
def prefixEnd_6064792 : Nat := 4983230072969 + 3 ^ 40 * 6064792 * 2
def baseEnd_6064792 : Nat := 115339013538620026189205

theorem tailTrace_6064792 : CollatzResearch.WordTrace tailWord_6064792 prefixEnd_6064792 115339013538620026189205 := by
  unfold tailWord_6064792
  simp only [CollatzResearch.WordTrace]
  refine ⟨110600568322150921427866315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147467424429534561903821753 110600568322150921427866315)
  ·
    refine ⟨165900852483226382141799473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110600568322150921427866315 165900852483226382141799473)
    ·
      refine ⟨124425639362419786606349605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165900852483226382141799473 124425639362419786606349605)
      ·
        refine ⟨23329807380453709988690551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124425639362419786606349605 23329807380453709988690551)
        ·
          refine ⟨34994711070680564983035827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23329807380453709988690551 34994711070680564983035827)
          ·
            refine ⟨52492066606020847474553741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34994711070680564983035827 52492066606020847474553741)
            ·
              refine ⟨19684524977257817802957653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52492066606020847474553741 19684524977257817802957653)
              ·
                refine ⟨115339013538620026189205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19684524977257817802957653 115339013538620026189205)
                ·
                  rfl

theorem cell23_6064792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 9].length) (baseStart_6064792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064792 prefixEnd_6064792 := by exact prefixLift 6064792
  have htrace : WordTrace (prefixWord ++ tailWord_6064792) baseStart_6064792 baseEnd_6064792 := by
    simpa [prefixWord, tailWord_6064792, baseEnd_6064792] using wordTrace_append hprefix tailTrace_6064792
  have hstable : (prefixWord ++ tailWord_6064792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064792).length < 2 ^ (prefixWord ++ tailWord_6064792).sum := by decide
  have hdescent : baseEnd_6064792 < baseStart_6064792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064803 : List Nat := [1, 1, 1, 4, 1, 1, 2, 7, 1, 2, 2]
def baseStart_6064803 : Nat := 118140960795 + 6064803 * 2 ^ 59
def prefixEnd_6064803 : Nat := 4983230072969 + 3 ^ 40 * 6064803 * 2
def baseEnd_6064803 : Nat := 3114159013829940164070985

theorem tailTrace_6064803 : CollatzResearch.WordTrace tailWord_6064803 prefixEnd_6064803 3114159013829940164070985 := by
  unfold tailWord_6064803
  simp only [CollatzResearch.WordTrace]
  refine ⟨221201537847261991734383063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147467691898174661156255375 221201537847261991734383063)
  ·
    refine ⟨331802306770892987601574595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221201537847261991734383063 331802306770892987601574595)
    ·
      refine ⟨497703460156339481402361893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331802306770892987601574595 497703460156339481402361893)
      ·
        refine ⟨93319398779313652762942855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 497703460156339481402361893 93319398779313652762942855)
        ·
          refine ⟨139979098168970479144414283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93319398779313652762942855 139979098168970479144414283)
          ·
            refine ⟨209968647253455718716621425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139979098168970479144414283 209968647253455718716621425)
            ·
              refine ⟨157476485440091789037466069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209968647253455718716621425 157476485440091789037466069)
              ·
                refine ⟨3690855127502151305565611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 157476485440091789037466069 3690855127502151305565611)
                ·
                  refine ⟨5536282691253226958348417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690855127502151305565611 5536282691253226958348417)
                  ·
                    refine ⟨4152212018439920218761313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5536282691253226958348417 4152212018439920218761313)
                    ·
                      refine ⟨3114159013829940164070985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4152212018439920218761313 3114159013829940164070985)
                      ·
                        rfl

theorem cell23_6064803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_6064803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064803 prefixEnd_6064803 := by exact prefixLift 6064803
  have htrace : WordTrace (prefixWord ++ tailWord_6064803) baseStart_6064803 baseEnd_6064803 := by
    simpa [prefixWord, tailWord_6064803, baseEnd_6064803] using wordTrace_append hprefix tailTrace_6064803
  have hstable : (prefixWord ++ tailWord_6064803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064803).length < 2 ^ (prefixWord ++ tailWord_6064803).sum := by decide
  have hdescent : baseEnd_6064803 < baseStart_6064803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064853 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6064853 : Nat := 118140960795 + 6064853 * 2 ^ 59
def prefixEnd_6064853 : Nat := 4983230072969 + 3 ^ 40 * 6064853 * 2
def baseEnd_6064853 : Nat := 3114184687862664968445755

theorem tailTrace_6064853 : CollatzResearch.WordTrace tailWord_6064853 prefixEnd_6064853 3114184687862664968445755 := by
  unfold tailWord_6064853
  simp only [CollatzResearch.WordTrace]
  refine ⟨221203361497080850273703213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147468907664720566849135475 221203361497080850273703213)
  ·
    refine ⟨82951260561405318852638705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221203361497080850273703213 82951260561405318852638705)
    ·
      refine ⟨62213445421053989139479029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82951260561405318852638705 62213445421053989139479029)
      ·
        refine ⟨5832510508223811481826159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62213445421053989139479029 5832510508223811481826159)
        ·
          refine ⟨8748765762335717222739239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832510508223811481826159 8748765762335717222739239)
          ·
            refine ⟨13123148643503575834108859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8748765762335717222739239 13123148643503575834108859)
            ·
              refine ⟨19684722965255363751163289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13123148643503575834108859 19684722965255363751163289)
              ·
                refine ⟨14763542223941522813372467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19684722965255363751163289 14763542223941522813372467)
                ·
                  refine ⟨22145313335912284220058701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14763542223941522813372467 22145313335912284220058701)
                  ·
                    refine ⟨8304492500967106582522013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22145313335912284220058701 8304492500967106582522013)
                    ·
                      refine ⟨3114184687862664968445755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8304492500967106582522013 3114184687862664968445755)
                      ·
                        rfl

theorem cell23_6064853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6064853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064853 prefixEnd_6064853 := by exact prefixLift 6064853
  have htrace : WordTrace (prefixWord ++ tailWord_6064853) baseStart_6064853 baseEnd_6064853 := by
    simpa [prefixWord, tailWord_6064853, baseEnd_6064853] using wordTrace_append hprefix tailTrace_6064853
  have hstable : (prefixWord ++ tailWord_6064853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064853).length < 2 ^ (prefixWord ++ tailWord_6064853).sum := by decide
  have hdescent : baseEnd_6064853 < baseStart_6064853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064879 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 3]
def baseStart_6064879 : Nat := 118140960795 + 6064879 * 2 ^ 59
def prefixEnd_6064879 : Nat := 4983230072969 + 3 ^ 40 * 6064879 * 2
def baseEnd_6064879 : Nat := 3114198038359681866720635

theorem tailTrace_6064879 : CollatzResearch.WordTrace tailWord_6064879 prefixEnd_6064879 3114198038359681866720635 := by
  unfold tailWord_6064879
  simp only [CollatzResearch.WordTrace]
  refine ⟨221204309794986656714149691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147469539863324437809433127 221204309794986656714149691)
  ·
    refine ⟨331806464692479985071224537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221204309794986656714149691 331806464692479985071224537)
    ·
      refine ⟨248854848519359988803418403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331806464692479985071224537 248854848519359988803418403)
      ·
        refine ⟨373282272779039983205127605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248854848519359988803418403 373282272779039983205127605)
        ·
          refine ⟨34995213073034998425480713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 373282272779039983205127605 34995213073034998425480713)
          ·
            refine ⟨26246409804776248819110535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34995213073034998425480713 26246409804776248819110535)
            ·
              refine ⟨39369614707164373228665803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26246409804776248819110535 39369614707164373228665803)
              ·
                refine ⟨59054422060746559842998705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39369614707164373228665803 59054422060746559842998705)
                ·
                  refine ⟨44290816545559919882249029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59054422060746559842998705 44290816545559919882249029)
                  ·
                    refine ⟨8304528102292484977921693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44290816545559919882249029 8304528102292484977921693)
                    ·
                      refine ⟨3114198038359681866720635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8304528102292484977921693 3114198038359681866720635)
                      ·
                        rfl

theorem cell23_6064879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_6064879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064879 prefixEnd_6064879 := by exact prefixLift 6064879
  have htrace : WordTrace (prefixWord ++ tailWord_6064879) baseStart_6064879 baseEnd_6064879 := by
    simpa [prefixWord, tailWord_6064879, baseEnd_6064879] using wordTrace_append hprefix tailTrace_6064879
  have hstable : (prefixWord ++ tailWord_6064879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064879).length < 2 ^ (prefixWord ++ tailWord_6064879).sum := by decide
  have hdescent : baseEnd_6064879 < baseStart_6064879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064893 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_6064893 : Nat := 118140960795 + 6064893 * 2 ^ 59
def prefixEnd_6064893 : Nat := 4983230072969 + 3 ^ 40 * 6064893 * 2
def baseEnd_6064893 : Nat := 3114205227088844811945571

theorem tailTrace_6064893 : CollatzResearch.WordTrace tailWord_6064893 prefixEnd_6064893 3114205227088844811945571 := by
  unfold tailWord_6064893
  simp only [CollatzResearch.WordTrace]
  refine ⟨221204820416935937105159333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147469880277957291403439555 221204820416935937105159333)
  ·
    refine ⟨41475903828175488207217375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221204820416935937105159333 41475903828175488207217375)
    ·
      refine ⟨62213855742263232310826063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41475903828175488207217375 62213855742263232310826063)
      ·
        refine ⟨93320783613394848466239095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62213855742263232310826063 93320783613394848466239095)
        ·
          refine ⟨139981175420092272699358643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93320783613394848466239095 139981175420092272699358643)
          ·
            refine ⟨209971763130138409049037965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139981175420092272699358643 209971763130138409049037965)
            ·
              refine ⟨78739411173801903393389237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209971763130138409049037965 78739411173801903393389237)
              ·
                refine ⟨7381819797543928443130241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78739411173801903393389237 7381819797543928443130241)
                ·
                  refine ⟨5536364848157946332347681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7381819797543928443130241 5536364848157946332347681)
                  ·
                    refine ⟨4152273636118459749260761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5536364848157946332347681 4152273636118459749260761)
                    ·
                      refine ⟨3114205227088844811945571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4152273636118459749260761 3114205227088844811945571)
                      ·
                        rfl

theorem cell23_6064893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_6064893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064893 prefixEnd_6064893 := by exact prefixLift 6064893
  have htrace : WordTrace (prefixWord ++ tailWord_6064893) baseStart_6064893 baseEnd_6064893 := by
    simpa [prefixWord, tailWord_6064893, baseEnd_6064893] using wordTrace_append hprefix tailTrace_6064893
  have hstable : (prefixWord ++ tailWord_6064893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064893).length < 2 ^ (prefixWord ++ tailWord_6064893).sum := by decide
  have hdescent : baseEnd_6064893 < baseStart_6064893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064914 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_6064914 : Nat := 118140960795 + 6064914 * 2 ^ 59
def prefixEnd_6064914 : Nat := 4983230072969 + 3 ^ 40 * 6064914 * 2
def baseEnd_6064914 : Nat := 3114216010182589229782975

theorem tailTrace_6064914 : CollatzResearch.WordTrace tailWord_6064914 prefixEnd_6064914 3114216010182589229782975 := by
  unfold tailWord_6064914
  simp only [CollatzResearch.WordTrace]
  refine ⟨55301396587464964422918449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147470390899906571794449197 55301396587464964422918449)
  ·
    refine ⟨41476047440598723317188837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55301396587464964422918449 41476047440598723317188837)
    ·
      refine ⟨7776758895112260621972907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41476047440598723317188837 7776758895112260621972907)
      ·
        refine ⟨11665138342668390932959361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7776758895112260621972907 11665138342668390932959361)
        ·
          refine ⟨8748853757001293199719521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11665138342668390932959361 8748853757001293199719521)
          ·
            refine ⟨6561640317750969899789641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8748853757001293199719521 6561640317750969899789641)
            ·
              refine ⟨4921230238313227424842231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6561640317750969899789641 4921230238313227424842231)
              ·
                refine ⟨7381845357469841137263347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921230238313227424842231 7381845357469841137263347)
                ·
                  refine ⟨11072768036204761705895021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7381845357469841137263347 11072768036204761705895021)
                  ·
                    refine ⟨4152288013576785639710633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11072768036204761705895021 4152288013576785639710633)
                    ·
                      refine ⟨3114216010182589229782975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4152288013576785639710633 3114216010182589229782975)
                      ·
                        rfl

theorem cell23_6064914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_6064914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064914 prefixEnd_6064914 := by exact prefixLift 6064914
  have htrace : WordTrace (prefixWord ++ tailWord_6064914) baseStart_6064914 baseEnd_6064914 := by
    simpa [prefixWord, tailWord_6064914, baseEnd_6064914] using wordTrace_append hprefix tailTrace_6064914
  have hstable : (prefixWord ++ tailWord_6064914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064914).length < 2 ^ (prefixWord ++ tailWord_6064914).sum := by decide
  have hdescent : baseEnd_6064914 < baseStart_6064914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064929 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 4, 5]
def baseStart_6064929 : Nat := 118140960795 + 6064929 * 2 ^ 59
def prefixEnd_6064929 : Nat := 4983230072969 + 3 ^ 40 * 6064929 * 2
def baseEnd_6064929 : Nat := 1038074570797468890365135

theorem tailTrace_6064929 : CollatzResearch.WordTrace tailWord_6064929 prefixEnd_6064929 1038074570797468890365135 := by
  unfold tailWord_6064929
  simp only [CollatzResearch.WordTrace]
  refine ⟨221206133444805515253469841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147470755629870343502313227 221206133444805515253469841)
  ·
    refine ⟨165904600083604136440102381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221206133444805515253469841 165904600083604136440102381)
    ·
      refine ⟨62214225031351551165038393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165904600083604136440102381 62214225031351551165038393)
      ·
        refine ⟨46660668773513663373778795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62214225031351551165038393 46660668773513663373778795)
        ·
          refine ⟨69991003160270495060668193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46660668773513663373778795 69991003160270495060668193)
          ·
            refine ⟨52493252370202871295501145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69991003160270495060668193 52493252370202871295501145)
            ·
              refine ⟨39369939277652153471625859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52493252370202871295501145 39369939277652153471625859)
              ·
                refine ⟨59054908916478230207438789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39369939277652153471625859 59054908916478230207438789)
                ·
                  refine ⟨11072795421839668163894773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59054908916478230207438789 11072795421839668163894773)
                  ·
                    refine ⟨1038074570797468890365135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11072795421839668163894773 1038074570797468890365135)
                    ·
                      rfl

theorem cell23_6064929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_6064929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064929 prefixEnd_6064929 := by exact prefixLift 6064929
  have htrace : WordTrace (prefixWord ++ tailWord_6064929) baseStart_6064929 baseEnd_6064929 := by
    simpa [prefixWord, tailWord_6064929, baseEnd_6064929] using wordTrace_append hprefix tailTrace_6064929
  have hstable : (prefixWord ++ tailWord_6064929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064929).length < 2 ^ (prefixWord ++ tailWord_6064929).sum := by decide
  have hdescent : baseEnd_6064929 < baseStart_6064929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6064986 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_6064986 : Nat := 118140960795 + 6064986 * 2 ^ 59
def prefixEnd_6064986 : Nat := 4983230072969 + 3 ^ 40 * 6064986 * 2
def baseEnd_6064986 : Nat := 3114252980789712948082643

theorem tailTrace_6064986 : CollatzResearch.WordTrace tailWord_6064986 prefixEnd_6064986 3114252980789712948082643 := by
  unfold tailWord_6064986
  simp only [CollatzResearch.WordTrace]
  refine ⟨55302053101399753497073703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147472141603732675992196541 55302053101399753497073703)
  ·
    refine ⟨82953079652099630245610555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55302053101399753497073703 82953079652099630245610555)
    ·
      refine ⟨124429619478149445368415833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82953079652099630245610555 124429619478149445368415833)
      ·
        refine ⟨93322214608612084026311875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124429619478149445368415833 93322214608612084026311875)
        ·
          refine ⟨139983321912918126039467813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93322214608612084026311875 139983321912918126039467813)
          ·
            refine ⟨26246872858672148632400215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139983321912918126039467813 26246872858672148632400215)
            ·
              refine ⟨39370309288008222948600323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26246872858672148632400215 39370309288008222948600323)
              ·
                refine ⟨59055463932012334422900485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39370309288008222948600323 59055463932012334422900485)
                ·
                  refine ⟨11072899487252312704293841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59055463932012334422900485 11072899487252312704293841)
                  ·
                    refine ⟨8304674615439234528220381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11072899487252312704293841 8304674615439234528220381)
                    ·
                      refine ⟨3114252980789712948082643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8304674615439234528220381 3114252980789712948082643)
                      ·
                        rfl

theorem cell23_6064986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_6064986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6064986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6064986 prefixEnd_6064986 := by exact prefixLift 6064986
  have htrace : WordTrace (prefixWord ++ tailWord_6064986) baseStart_6064986 baseEnd_6064986 := by
    simpa [prefixWord, tailWord_6064986, baseEnd_6064986] using wordTrace_append hprefix tailTrace_6064986
  have hstable : (prefixWord ++ tailWord_6064986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6064986).length < 2 ^ (prefixWord ++ tailWord_6064986).sum := by decide
  have hdescent : baseEnd_6064986 < baseStart_6064986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6064986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065036 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_6065036 : Nat := 118140960795 + 6065036 * 2 ^ 59
def prefixEnd_6065036 : Nat := 4983230072969 + 3 ^ 40 * 6065036 * 2
def baseEnd_6065036 : Nat := 1038092884940812584152471

theorem tailTrace_6065036 : CollatzResearch.WordTrace tailWord_6065036 prefixEnd_6065036 1038092884940812584152471 := by
  unfold tailWord_6065036
  simp only [CollatzResearch.WordTrace]
  refine ⟨110605018027708936263807481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147473357370278581685076641 110605018027708936263807481)
  ·
    refine ⟨82953763520781702197855611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110605018027708936263807481 82953763520781702197855611)
    ·
      refine ⟨124430645281172553296783417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82953763520781702197855611 124430645281172553296783417)
      ·
        refine ⟨93322983960879414972587563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124430645281172553296783417 93322983960879414972587563)
        ·
          refine ⟨139984475941319122458881345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93322983960879414972587563 139984475941319122458881345)
          ·
            refine ⟨104988356955989341844161009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139984475941319122458881345 104988356955989341844161009)
            ·
              refine ⟨78741267716992006383120757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104988356955989341844161009 78741267716992006383120757)
              ·
                refine ⟨7381993848468000598417571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78741267716992006383120757 7381993848468000598417571)
                ·
                  refine ⟨11072990772702000897626357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7381993848468000598417571 11072990772702000897626357)
                  ·
                    refine ⟨1038092884940812584152471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11072990772702000897626357 1038092884940812584152471)
                    ·
                      rfl

theorem cell23_6065036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_6065036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065036 prefixEnd_6065036 := by exact prefixLift 6065036
  have htrace : WordTrace (prefixWord ++ tailWord_6065036) baseStart_6065036 baseEnd_6065036 := by
    simpa [prefixWord, tailWord_6065036, baseEnd_6065036] using wordTrace_append hprefix tailTrace_6065036
  have hstable : (prefixWord ++ tailWord_6065036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065036).length < 2 ^ (prefixWord ++ tailWord_6065036).sum := by decide
  have hdescent : baseEnd_6065036 < baseStart_6065036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065049 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 5, 6]
def baseStart_6065049 : Nat := 118140960795 + 6065049 * 2 ^ 59
def prefixEnd_6065049 : Nat := 4983230072969 + 3 ^ 40 * 6065049 * 2
def baseEnd_6065049 : Nat := 1038095110023648733864951

theorem tailTrace_6065049 : CollatzResearch.WordTrace tailWord_6065049 prefixEnd_6065049 1038095110023648733864951 := by
  unfold tailWord_6065049
  simp only [CollatzResearch.WordTrace]
  refine ⟨221210510204370775747838201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147473673469580517165225467 221210510204370775747838201)
  ·
    refine ⟨165907882653278081810878651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221210510204370775747838201 165907882653278081810878651)
    ·
      refine ⟨248861823979917122716317977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165907882653278081810878651 248861823979917122716317977)
      ·
        refine ⟨186646367984937842037238483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248861823979917122716317977 186646367984937842037238483)
        ·
          refine ⟨279969551977406763055857725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186646367984937842037238483 279969551977406763055857725)
          ·
            refine ⟨104988581991527536145946647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279969551977406763055857725 104988581991527536145946647)
            ·
              refine ⟨157482872987291304218919971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104988581991527536145946647 157482872987291304218919971)
              ·
                refine ⟨236224309480936956328379957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157482872987291304218919971 236224309480936956328379957)
                ·
                  refine ⟨22146029013837839655785621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236224309480936956328379957 22146029013837839655785621)
                  ·
                    refine ⟨1038095110023648733864951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22146029013837839655785621 1038095110023648733864951)
                    ·
                      rfl

theorem cell23_6065049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_6065049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065049 prefixEnd_6065049 := by exact prefixLift 6065049
  have htrace : WordTrace (prefixWord ++ tailWord_6065049) baseStart_6065049 baseEnd_6065049 := by
    simpa [prefixWord, tailWord_6065049, baseEnd_6065049] using wordTrace_append hprefix tailTrace_6065049
  have hstable : (prefixWord ++ tailWord_6065049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065049).length < 2 ^ (prefixWord ++ tailWord_6065049).sum := by decide
  have hdescent : baseEnd_6065049 < baseStart_6065049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065056 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_6065056 : Nat := 118140960795 + 6065056 * 2 ^ 59
def prefixEnd_6065056 : Nat := 4983230072969 + 3 ^ 40 * 6065056 * 2
def baseEnd_6065056 : Nat := 3114288924435527674207321

theorem tailTrace_6065056 : CollatzResearch.WordTrace tailWord_6065056 prefixEnd_6065056 3114288924435527674207321 := by
  unfold tailWord_6065056
  simp only [CollatzResearch.WordTrace]
  refine ⟨110605382757672707971671511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147473843676896943962228681 110605382757672707971671511)
  ·
    refine ⟨165908074136509061957507267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110605382757672707971671511 165908074136509061957507267)
    ·
      refine ⟨248862111204763592936260901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165908074136509061957507267 248862111204763592936260901)
      ·
        refine ⟨46661645850893173675548919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248862111204763592936260901 46661645850893173675548919)
        ·
          refine ⟨69992468776339760513323379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46661645850893173675548919 69992468776339760513323379)
          ·
            refine ⟨104988703164509640769985069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69992468776339760513323379 104988703164509640769985069)
            ·
              refine ⟨39370763686691115288744401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104988703164509640769985069 39370763686691115288744401)
              ·
                refine ⟨29528072765018336466558301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39370763686691115288744401 29528072765018336466558301)
                ·
                  refine ⟨11073027286881876174959363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29528072765018336466558301 11073027286881876174959363)
                  ·
                    refine ⟨16609540930322814262439045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11073027286881876174959363 16609540930322814262439045)
                    ·
                      refine ⟨3114288924435527674207321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16609540930322814262439045 3114288924435527674207321)
                      ·
                        rfl

theorem cell23_6065056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_6065056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065056 prefixEnd_6065056 := by exact prefixLift 6065056
  have htrace : WordTrace (prefixWord ++ tailWord_6065056) baseStart_6065056 baseEnd_6065056 := by
    simpa [prefixWord, tailWord_6065056, baseEnd_6065056] using wordTrace_append hprefix tailTrace_6065056
  have hstable : (prefixWord ++ tailWord_6065056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065056).length < 2 ^ (prefixWord ++ tailWord_6065056).sum := by decide
  have hdescent : baseEnd_6065056 < baseStart_6065056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065079 : List Nat := [1, 1, 3, 1, 3, 1, 2, 11]
def baseStart_6065079 : Nat := 118140960795 + 6065079 * 2 ^ 59
def prefixEnd_6065079 : Nat := 4983230072969 + 3 ^ 40 * 6065079 * 2
def baseEnd_6065079 : Nat := 115344471647799299415545

theorem tailTrace_6065079 : CollatzResearch.WordTrace tailWord_6065079 prefixEnd_6065079 115344471647799299415545 := by
  unfold tailWord_6065079
  simp only [CollatzResearch.WordTrace]
  refine ⟨221211604394262090871430291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147474402929508060580953527 221211604394262090871430291)
  ·
    refine ⟨331817406591393136307145437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221211604394262090871430291 331817406591393136307145437)
    ·
      refine ⟨124431527471772426115179539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331817406591393136307145437 124431527471772426115179539)
      ·
        refine ⟨186647291207658639172769309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124431527471772426115179539 186647291207658639172769309)
        ·
          refine ⟨69992734202871989689788491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186647291207658639172769309 69992734202871989689788491)
          ·
            refine ⟨104989101304307984534682737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69992734202871989689788491 104989101304307984534682737)
            ·
              refine ⟨78741825978230988401012053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104989101304307984534682737 78741825978230988401012053)
              ·
                refine ⟨115344471647799299415545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 78741825978230988401012053 115344471647799299415545)
                ·
                  rfl

theorem cell23_6065079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 11].length) (baseStart_6065079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065079 prefixEnd_6065079 := by exact prefixLift 6065079
  have htrace : WordTrace (prefixWord ++ tailWord_6065079) baseStart_6065079 baseEnd_6065079 := by
    simpa [prefixWord, tailWord_6065079, baseEnd_6065079] using wordTrace_append hprefix tailTrace_6065079
  have hstable : (prefixWord ++ tailWord_6065079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065079).length < 2 ^ (prefixWord ++ tailWord_6065079).sum := by decide
  have hdescent : baseEnd_6065079 < baseStart_6065079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065096 : List Nat := [2, 1, 3, 1, 5, 1, 10]
def baseStart_6065096 : Nat := 118140960795 + 6065096 * 2 ^ 59
def prefixEnd_6065096 : Nat := 4983230072969 + 3 ^ 40 * 6065096 * 2
def baseEnd_6065096 : Nat := 38448264983477870588977

theorem tailTrace_6065096 : CollatzResearch.WordTrace tailWord_6065096 prefixEnd_6065096 38448264983477870588977 := by
  unfold tailWord_6065096
  simp only [CollatzResearch.WordTrace]
  refine ⟨110606112217600251387399571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147474816290133668516532761 110606112217600251387399571)
  ·
    refine ⟨165909168326400377081099357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110606112217600251387399571 165909168326400377081099357)
    ·
      refine ⟨62215938122400141405412259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165909168326400377081099357 62215938122400141405412259)
      ·
        refine ⟨93323907183600212108118389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62215938122400141405412259 93323907183600212108118389)
        ·
          refine ⟨8749116298462519885136099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93323907183600212108118389 8749116298462519885136099)
          ·
            refine ⟨13123674447693779827704149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8749116298462519885136099 13123674447693779827704149)
            ·
              refine ⟨38448264983477870588977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13123674447693779827704149 38448264983477870588977)
              ·
                rfl

theorem cell23_6065096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 10].length) (baseStart_6065096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065096 prefixEnd_6065096 := by exact prefixLift 6065096
  have htrace : WordTrace (prefixWord ++ tailWord_6065096) baseStart_6065096 baseEnd_6065096 := by
    simpa [prefixWord, tailWord_6065096, baseEnd_6065096] using wordTrace_append hprefix tailTrace_6065096
  have hstable : (prefixWord ++ tailWord_6065096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065096).length < 2 ^ (prefixWord ++ tailWord_6065096).sum := by decide
  have hdescent : baseEnd_6065096 < baseStart_6065096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065101 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6065101 : Nat := 118140960795 + 6065101 * 2 ^ 59
def prefixEnd_6065101 : Nat := 4983230072969 + 3 ^ 40 * 6065101 * 2
def baseEnd_6065101 : Nat := 3114312031064979998144615

theorem tailTrace_6065101 : CollatzResearch.WordTrace tailWord_6065101 prefixEnd_6065101 3114312031064979998144615 := by
  unfold tailWord_6065101
  simp only [CollatzResearch.WordTrace]
  refine ⟨221212406800182388628731157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147474937866788259085820771 221212406800182388628731157)
  ·
    refine ⟨10369331568758549466971773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221212406800182388628731157 10369331568758549466971773)
    ·
      refine ⟨3888499338284456050114415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10369331568758549466971773 3888499338284456050114415)
      ·
        refine ⟨5832749007426684075171623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3888499338284456050114415 5832749007426684075171623)
        ·
          refine ⟨8749123511140026112757435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832749007426684075171623 8749123511140026112757435)
          ·
            refine ⟨13123685266710039169136153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8749123511140026112757435 13123685266710039169136153)
            ·
              refine ⟨9842763950032529376852115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13123685266710039169136153 9842763950032529376852115)
              ·
                refine ⟨14764145925048794065278173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9842763950032529376852115 14764145925048794065278173)
                ·
                  refine ⟨5536554721893297774479315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14764145925048794065278173 5536554721893297774479315)
                  ·
                    refine ⟨8304832082839946661718973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5536554721893297774479315 8304832082839946661718973)
                    ·
                      refine ⟨3114312031064979998144615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8304832082839946661718973 3114312031064979998144615)
                      ·
                        rfl

theorem cell23_6065101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6065101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065101 prefixEnd_6065101 := by exact prefixLift 6065101
  have htrace : WordTrace (prefixWord ++ tailWord_6065101) baseStart_6065101 baseEnd_6065101 := by
    simpa [prefixWord, tailWord_6065101, baseEnd_6065101] using wordTrace_append hprefix tailTrace_6065101
  have hstable : (prefixWord ++ tailWord_6065101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065101).length < 2 ^ (prefixWord ++ tailWord_6065101).sum := by decide
  have hdescent : baseEnd_6065101 < baseStart_6065101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065110 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6065110 : Nat := 118140960795 + 6065110 * 2 ^ 59
def prefixEnd_6065110 : Nat := 4983230072969 + 3 ^ 40 * 6065110 * 2
def baseEnd_6065110 : Nat := 3114316652390870462932073

theorem tailTrace_6065110 : CollatzResearch.WordTrace tailWord_6065110 prefixEnd_6065110 3114316652390870462932073 := by
  unfold tailWord_6065110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13825795941071861447863049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147475156704766522110539189 13825795941071861447863049)
  ·
    refine ⟨10369346955803896085897287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13825795941071861447863049 10369346955803896085897287)
    ·
      refine ⟨15554020433705844128845931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10369346955803896085897287 15554020433705844128845931)
      ·
        refine ⟨23331030650558766193268897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15554020433705844128845931 23331030650558766193268897)
        ·
          refine ⟨17498272987919074644951673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23331030650558766193268897 17498272987919074644951673)
          ·
            refine ⟨13123704740939305983713755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17498272987919074644951673 13123704740939305983713755)
            ·
              refine ⟨19685557111408958975570633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13123704740939305983713755 19685557111408958975570633)
              ·
                refine ⟨14764167833556719231677975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19685557111408958975570633 14764167833556719231677975)
                ·
                  refine ⟨22146251750335078847516963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14764167833556719231677975 22146251750335078847516963)
                  ·
                    refine ⟨33219377625502618271275445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22146251750335078847516963 33219377625502618271275445)
                    ·
                      refine ⟨3114316652390870462932073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33219377625502618271275445 3114316652390870462932073)
                      ·
                        rfl

theorem cell23_6065110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6065110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065110 prefixEnd_6065110 := by exact prefixLift 6065110
  have htrace : WordTrace (prefixWord ++ tailWord_6065110) baseStart_6065110 baseEnd_6065110 := by
    simpa [prefixWord, tailWord_6065110, baseEnd_6065110] using wordTrace_append hprefix tailTrace_6065110
  have hstable : (prefixWord ++ tailWord_6065110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065110).length < 2 ^ (prefixWord ++ tailWord_6065110).sum := by decide
  have hdescent : baseEnd_6065110 < baseStart_6065110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065117 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_6065117 : Nat := 118140960795 + 6065117 * 2 ^ 59
def prefixEnd_6065117 : Nat := 4983230072969 + 3 ^ 40 * 6065117 * 2
def baseEnd_6065117 : Nat := 1038106748918483978514847

theorem tailTrace_6065117 : CollatzResearch.WordTrace tailWord_6065117 prefixEnd_6065117 1038106748918483978514847 := by
  unfold tailWord_6065117
  simp only [CollatzResearch.WordTrace]
  refine ⟨221212990368124423361313605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147475326912082948907542403 221212990368124423361313605)
  ·
    refine ⟨41477435694023329380246301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221212990368124423361313605 41477435694023329380246301)
    ·
      refine ⟨15554038385258748517592363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41477435694023329380246301 15554038385258748517592363)
      ·
        refine ⟨23331057577888122776388545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15554038385258748517592363 23331057577888122776388545)
        ·
          refine ⟨17498293183416092082291409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23331057577888122776388545 17498293183416092082291409)
          ·
            refine ⟨13123719887562069061718557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17498293183416092082291409 13123719887562069061718557)
            ·
              refine ⟨4921394957835775898144459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13123719887562069061718557 4921394957835775898144459)
              ·
                refine ⟨7382092436753663847216689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921394957835775898144459 7382092436753663847216689)
                ·
                  refine ⟨5536569327565247885412517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7382092436753663847216689 5536569327565247885412517)
                  ·
                    refine ⟨1038106748918483978514847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5536569327565247885412517 1038106748918483978514847)
                    ·
                      rfl

theorem cell23_6065117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_6065117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065117 prefixEnd_6065117 := by exact prefixLift 6065117
  have htrace : WordTrace (prefixWord ++ tailWord_6065117) baseStart_6065117 baseEnd_6065117 := by
    simpa [prefixWord, tailWord_6065117, baseEnd_6065117] using wordTrace_append hprefix tailTrace_6065117
  have hstable : (prefixWord ++ tailWord_6065117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065117).length < 2 ^ (prefixWord ++ tailWord_6065117).sum := by decide
  have hdescent : baseEnd_6065117 < baseStart_6065117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065203 : List Nat := [1, 1, 1, 2, 4, 1, 1, 7, 5]
def baseStart_6065203 : Nat := 118140960795 + 6065203 * 2 ^ 59
def prefixEnd_6065203 : Nat := 4983230072969 + 3 ^ 40 * 6065203 * 2
def baseEnd_6065203 : Nat := 346040489565748733229905

theorem tailTrace_6065203 : CollatzResearch.WordTrace tailWord_6065203 prefixEnd_6065203 346040489565748733229905 := by
  unfold tailWord_6065203
  simp only [CollatzResearch.WordTrace]
  refine ⟨221216127045812860048944263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147477418030541906699296175 221216127045812860048944263)
  ·
    refine ⟨331824190568719290073416395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221216127045812860048944263 331824190568719290073416395)
    ·
      refine ⟨497736285853078935110124593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331824190568719290073416395 497736285853078935110124593)
      ·
        refine ⟨373302214389809201332593445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497736285853078935110124593 373302214389809201332593445)
        ·
          refine ⟨69994165198089225249861271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 373302214389809201332593445 69994165198089225249861271)
          ·
            refine ⟨104991247797133837874791907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69994165198089225249861271 104991247797133837874791907)
            ·
              refine ⟨157486871695700756812187861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104991247797133837874791907 157486871695700756812187861)
              ·
                refine ⟨3691098555367986487785653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 157486871695700756812187861 3691098555367986487785653)
                ·
                  refine ⟨346040489565748733229905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3691098555367986487785653 346040489565748733229905)
                  ·
                    rfl

theorem cell23_6065203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 5].length) (baseStart_6065203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065203 prefixEnd_6065203 := by exact prefixLift 6065203
  have htrace : WordTrace (prefixWord ++ tailWord_6065203) baseStart_6065203 baseEnd_6065203 := by
    simpa [prefixWord, tailWord_6065203, baseEnd_6065203] using wordTrace_append hprefix tailTrace_6065203
  have hstable : (prefixWord ++ tailWord_6065203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065203).length < 2 ^ (prefixWord ++ tailWord_6065203).sum := by decide
  have hdescent : baseEnd_6065203 < baseStart_6065203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065214 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_6065214 : Nat := 118140960795 + 6065214 * 2 ^ 59
def prefixEnd_6065214 : Nat := 4983230072969 + 3 ^ 40 * 6065214 * 2
def baseEnd_6065214 : Nat := 3114370054378938056031595

theorem tailTrace_6065214 : CollatzResearch.WordTrace tailWord_6065214 prefixEnd_6065214 3114370054378938056031595 := by
  unfold tailWord_6065214
  simp only [CollatzResearch.WordTrace]
  refine ⟨27652066031096626115949337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147477685499182005951729797 27652066031096626115949337)
  ·
    refine ⟨20739049523322469586962003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27652066031096626115949337 20739049523322469586962003)
    ·
      refine ⟨31108574284983704380443005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20739049523322469586962003 31108574284983704380443005)
      ·
        refine ⟨11665715356868889142666127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31108574284983704380443005 11665715356868889142666127)
        ·
          refine ⟨17498573035303333713999191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11665715356868889142666127 17498573035303333713999191)
          ·
            refine ⟨26247859552955000570998787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17498573035303333713999191 26247859552955000570998787)
            ·
              refine ⟨39371789329432500856498181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26247859552955000570998787 39371789329432500856498181)
              ·
                refine ⟨7382210499268593910593409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39371789329432500856498181 7382210499268593910593409)
                ·
                  refine ⟨5536657874451445432945057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7382210499268593910593409 5536657874451445432945057)
                  ·
                    refine ⟨4152493405838584074708793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5536657874451445432945057 4152493405838584074708793)
                    ·
                      refine ⟨3114370054378938056031595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4152493405838584074708793 3114370054378938056031595)
                      ·
                        rfl

theorem cell23_6065214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_6065214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065214 prefixEnd_6065214 := by exact prefixLift 6065214
  have htrace : WordTrace (prefixWord ++ tailWord_6065214) baseStart_6065214 baseEnd_6065214 := by
    simpa [prefixWord, tailWord_6065214, baseEnd_6065214] using wordTrace_append hprefix tailTrace_6065214
  have hstable : (prefixWord ++ tailWord_6065214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065214).length < 2 ^ (prefixWord ++ tailWord_6065214).sum := by decide
  have hdescent : baseEnd_6065214 < baseStart_6065214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065250 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_6065250 : Nat := 118140960795 + 6065250 * 2 ^ 59
def prefixEnd_6065250 : Nat := 4983230072969 + 3 ^ 40 * 6065250 * 2
def baseEnd_6065250 : Nat := 1038129513227499971727143

theorem tailTrace_6065250 : CollatzResearch.WordTrace tailWord_6065250 prefixEnd_6065250 1038129513227499971727143 := by
  unfold tailWord_6065250
  simp only [CollatzResearch.WordTrace]
  refine ⟨55304460319160646768976301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147478560851095058050603469 55304460319160646768976301)
  ·
    refine ⟨20739172619685242538366113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55304460319160646768976301 20739172619685242538366113)
    ·
      refine ⟨15554379464763931903774585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20739172619685242538366113 15554379464763931903774585)
      ·
        refine ⟨11665784598572948927830939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15554379464763931903774585 11665784598572948927830939)
        ·
          refine ⟨17498676897859423391746409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11665784598572948927830939 17498676897859423391746409)
          ·
            refine ⟨13124007673394567543809807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17498676897859423391746409 13124007673394567543809807)
            ·
              refine ⟨19686011510091851315714711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13124007673394567543809807 19686011510091851315714711)
              ·
                refine ⟨29529017265137776973572067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19686011510091851315714711 29529017265137776973572067)
                ·
                  refine ⟨44293525897706665460358101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29529017265137776973572067 44293525897706665460358101)
                  ·
                    refine ⟨1038129513227499971727143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44293525897706665460358101 1038129513227499971727143)
                    ·
                      rfl

theorem cell23_6065250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_6065250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065250 prefixEnd_6065250 := by exact prefixLift 6065250
  have htrace : WordTrace (prefixWord ++ tailWord_6065250) baseStart_6065250 baseEnd_6065250 := by
    simpa [prefixWord, tailWord_6065250, baseEnd_6065250] using wordTrace_append hprefix tailTrace_6065250
  have hstable : (prefixWord ++ tailWord_6065250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065250).length < 2 ^ (prefixWord ++ tailWord_6065250).sum := by decide
  have hdescent : baseEnd_6065250 < baseStart_6065250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065253 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_6065253 : Nat := 118140960795 + 6065253 * 2 ^ 59
def prefixEnd_6065253 : Nat := 4983230072969 + 3 ^ 40 * 6065253 * 2
def baseEnd_6065253 : Nat := 3114390080124463403443915

theorem tailTrace_6065253 : CollatzResearch.WordTrace tailWord_6065253 prefixEnd_6065253 3114390080124463403443915 := by
  unfold tailWord_6065253
  simp only [CollatzResearch.WordTrace]
  refine ⟨221217950695631718588264413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147478633797087812392176275 221217950695631718588264413)
  ·
    refine ⟨82956731510861894470599155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221217950695631718588264413 82956731510861894470599155)
    ·
      refine ⟨124435097266292841705898733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82956731510861894470599155 124435097266292841705898733)
      ·
        refine ⟨46663161474859815639712025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124435097266292841705898733 46663161474859815639712025)
        ·
          refine ⟨34997371106144861729784019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46663161474859815639712025 34997371106144861729784019)
          ·
            refine ⟨52496056659217292594676029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34997371106144861729784019 52496056659217292594676029)
            ·
              refine ⟨19686021247206484723003511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52496056659217292594676029 19686021247206484723003511)
              ·
                refine ⟨29529031870809727084505267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19686021247206484723003511 29529031870809727084505267)
                ·
                  refine ⟨44293547806214590626757901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29529031870809727084505267 44293547806214590626757901)
                  ·
                    refine ⟨16610080427330471485034213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44293547806214590626757901 16610080427330471485034213)
                    ·
                      refine ⟨3114390080124463403443915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16610080427330471485034213 3114390080124463403443915)
                      ·
                        rfl

theorem cell23_6065253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_6065253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065253 prefixEnd_6065253 := by exact prefixLift 6065253
  have htrace : WordTrace (prefixWord ++ tailWord_6065253) baseStart_6065253 baseEnd_6065253 := by
    simpa [prefixWord, tailWord_6065253, baseEnd_6065253] using wordTrace_append hprefix tailTrace_6065253
  have hstable : (prefixWord ++ tailWord_6065253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065253).length < 2 ^ (prefixWord ++ tailWord_6065253).sum := by decide
  have hdescent : baseEnd_6065253 < baseStart_6065253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065263 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 5, 4]
def baseStart_6065263 : Nat := 118140960795 + 6065263 * 2 ^ 59
def prefixEnd_6065263 : Nat := 4983230072969 + 3 ^ 40 * 6065263 * 2
def baseEnd_6065263 : Nat := 1038131738310336121439623

theorem tailTrace_6065263 : CollatzResearch.WordTrace tailWord_6065263 prefixEnd_6065263 1038131738310336121439623 := by
  unfold tailWord_6065263
  simp only [CollatzResearch.WordTrace]
  refine ⟨221218315425595490296128443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147478876950396993530752295 221218315425595490296128443)
  ·
    refine ⟨331827473138393235444192665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221218315425595490296128443 331827473138393235444192665)
    ·
      refine ⟨248870604853794926583144499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331827473138393235444192665 248870604853794926583144499)
      ·
        refine ⟨373305907280692389874716749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248870604853794926583144499 373305907280692389874716749)
        ·
          refine ⟨139989715230259646203018781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373305907280692389874716749 139989715230259646203018781)
          ·
            refine ⟨52496143211347367326132043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139989715230259646203018781 52496143211347367326132043)
            ·
              refine ⟨78744214817021050989198065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52496143211347367326132043 78744214817021050989198065)
              ·
                refine ⟨59058161112765788241898549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78744214817021050989198065 59058161112765788241898549)
                ·
                  refine ⟨5536702604321792647677989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59058161112765788241898549 5536702604321792647677989)
                  ·
                    refine ⟨1038131738310336121439623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5536702604321792647677989 1038131738310336121439623)
                    ·
                      rfl

theorem cell23_6065263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 4].length) (baseStart_6065263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065263 prefixEnd_6065263 := by exact prefixLift 6065263
  have htrace : WordTrace (prefixWord ++ tailWord_6065263) baseStart_6065263 baseEnd_6065263 := by
    simpa [prefixWord, tailWord_6065263, baseEnd_6065263] using wordTrace_append hprefix tailTrace_6065263
  have hstable : (prefixWord ++ tailWord_6065263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065263).length < 2 ^ (prefixWord ++ tailWord_6065263).sum := by decide
  have hdescent : baseEnd_6065263 < baseStart_6065263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065270 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_6065270 : Nat := 118140960795 + 6065270 * 2 ^ 59
def prefixEnd_6065270 : Nat := 4983230072969 + 3 ^ 40 * 6065270 * 2
def baseEnd_6065270 : Nat := 3114398809295589836931337

theorem tailTrace_6065270 : CollatzResearch.WordTrace tailWord_6065270 prefixEnd_6065270 3114398809295589836931337 := by
  unfold tailWord_6065270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13826160671035633155727079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147479047157713420327755509 13826160671035633155727079)
  ·
    refine ⟨20739241006553449733590619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13826160671035633155727079 20739241006553449733590619)
    ·
      refine ⟨31108861509830174600385929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20739241006553449733590619 31108861509830174600385929)
      ·
        refine ⟨23331646132372630950289447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31108861509830174600385929 23331646132372630950289447)
        ·
          refine ⟨34997469198558946425434171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23331646132372630950289447 34997469198558946425434171)
          ·
            refine ⟨52496203797838419638151257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34997469198558946425434171 52496203797838419638151257)
            ·
              refine ⟨39372152848378814728613443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52496203797838419638151257 39372152848378814728613443)
              ·
                refine ⟨59058229272568222092920165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39372152848378814728613443 59058229272568222092920165)
                ·
                  refine ⟨11073417988606541642422531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59058229272568222092920165 11073417988606541642422531)
                  ·
                    refine ⟨16610126982909812463633797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11073417988606541642422531 16610126982909812463633797)
                    ·
                      refine ⟨3114398809295589836931337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16610126982909812463633797 3114398809295589836931337)
                      ·
                        rfl

theorem cell23_6065270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_6065270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065270 prefixEnd_6065270 := by exact prefixLift 6065270
  have htrace : WordTrace (prefixWord ++ tailWord_6065270) baseStart_6065270 baseEnd_6065270 := by
    simpa [prefixWord, tailWord_6065270, baseEnd_6065270] using wordTrace_append hprefix tailTrace_6065270
  have hstable : (prefixWord ++ tailWord_6065270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065270).length < 2 ^ (prefixWord ++ tailWord_6065270).sum := by decide
  have hdescent : baseEnd_6065270 < baseStart_6065270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065310 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_6065310 : Nat := 118140960795 + 6065310 * 2 ^ 59
def prefixEnd_6065310 : Nat := 4983230072969 + 3 ^ 40 * 6065310 * 2
def baseEnd_6065310 : Nat := 346046594280196631159017

theorem tailTrace_6065310 : CollatzResearch.WordTrace tailWord_6065310 prefixEnd_6065310 346046594280196631159017 := by
  unfold tailWord_6065310
  simp only [CollatzResearch.WordTrace]
  refine ⟨27652503707053152165386173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147480019770950144882059589 27652503707053152165386173)
  ·
    refine ⟨10369688890144932062019815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27652503707053152165386173 10369688890144932062019815)
    ·
      refine ⟨15554533335217398093029723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10369688890144932062019815 15554533335217398093029723)
      ·
        refine ⟨23331800002826097139544585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15554533335217398093029723 23331800002826097139544585)
        ·
          refine ⟨17498850002119572854658439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23331800002826097139544585 17498850002119572854658439)
          ·
            refine ⟨26248275003179359281987659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17498850002119572854658439 26248275003179359281987659)
            ·
              refine ⟨39372412504769038922981489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26248275003179359281987659 39372412504769038922981489)
              ·
                refine ⟨29529309378576779192236117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39372412504769038922981489 29529309378576779192236117)
                ·
                  refine ⟨346046594280196631159017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29529309378576779192236117 346046594280196631159017)
                  ·
                    rfl

theorem cell23_6065310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_6065310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065310 prefixEnd_6065310 := by exact prefixLift 6065310
  have htrace : WordTrace (prefixWord ++ tailWord_6065310) baseStart_6065310 baseEnd_6065310 := by
    simpa [prefixWord, tailWord_6065310, baseEnd_6065310] using wordTrace_append hprefix tailTrace_6065310
  have hstable : (prefixWord ++ tailWord_6065310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065310).length < 2 ^ (prefixWord ++ tailWord_6065310).sum := by decide
  have hdescent : baseEnd_6065310 < baseStart_6065310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065337 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 3]
def baseStart_6065337 : Nat := 118140960795 + 6065337 * 2 ^ 59
def prefixEnd_6065337 : Nat := 4983230072969 + 3 ^ 40 * 6065337 * 2
def baseEnd_6065337 : Nat := 3114433212499441074793529

theorem tailTrace_6065337 : CollatzResearch.WordTrace tailWord_6065337 prefixEnd_6065337 3114433212499441074793529 := by
  unfold tailWord_6065337
  simp only [CollatzResearch.WordTrace]
  refine ⟨221221014427327400934322265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147480676284884933956214843 221221014427327400934322265)
  ·
    refine ⟨165915760820495550700741699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221221014427327400934322265 165915760820495550700741699)
    ·
      refine ⟨248873641230743326051112549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165915760820495550700741699 248873641230743326051112549)
      ·
        refine ⟨46663807730764373634583603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248873641230743326051112549 46663807730764373634583603)
        ·
          refine ⟨69995711596146560451875405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46663807730764373634583603 69995711596146560451875405)
          ·
            refine ⟨26248391848554960169453277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69995711596146560451875405 26248391848554960169453277)
            ·
              refine ⟨9843146943208110063544979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26248391848554960169453277 9843146943208110063544979)
              ·
                refine ⟨14764720414812165095317469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9843146943208110063544979 14764720414812165095317469)
                ·
                  refine ⟨5536770155554561910744051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14764720414812165095317469 5536770155554561910744051)
                  ·
                    refine ⟨8305155233331842866116077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5536770155554561910744051 8305155233331842866116077)
                    ·
                      refine ⟨3114433212499441074793529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8305155233331842866116077 3114433212499441074793529)
                      ·
                        rfl

theorem cell23_6065337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_6065337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065337 prefixEnd_6065337 := by exact prefixLift 6065337
  have htrace : WordTrace (prefixWord ++ tailWord_6065337) baseStart_6065337 baseEnd_6065337 := by
    simpa [prefixWord, tailWord_6065337, baseEnd_6065337] using wordTrace_append hprefix tailTrace_6065337
  have hstable : (prefixWord ++ tailWord_6065337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065337).length < 2 ^ (prefixWord ++ tailWord_6065337).sum := by decide
  have hdescent : baseEnd_6065337 < baseStart_6065337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065344 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 6]
def baseStart_6065344 : Nat := 118140960795 + 6065344 * 2 ^ 59
def prefixEnd_6065344 : Nat := 4983230072969 + 3 ^ 40 * 6065344 * 2
def baseEnd_6065344 : Nat := 346048534096002505267333

theorem tailTrace_6065344 : CollatzResearch.WordTrace tailWord_6065344 prefixEnd_6065344 346048534096002505267333 := by
  unfold tailWord_6065344
  simp only [CollatzResearch.WordTrace]
  refine ⟨110610634869151020564913543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147480846492201360753218057 110610634869151020564913543)
  ·
    refine ⟨165915952303726530847370315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110610634869151020564913543 165915952303726530847370315)
    ·
      refine ⟨248873928455589796271055473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165915952303726530847370315 248873928455589796271055473)
      ·
        refine ⟨186655446341692347203291605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248873928455589796271055473 186655446341692347203291605)
        ·
          refine ⟨4374737023633414387577147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 186655446341692347203291605 4374737023633414387577147)
          ·
            refine ⟨6562105535450121581365721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4374737023633414387577147 6562105535450121581365721)
            ·
              refine ⟨4921579151587591186024291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6562105535450121581365721 4921579151587591186024291)
              ·
                refine ⟨7382368727381386779036437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921579151587591186024291 7382368727381386779036437)
                ·
                  refine ⟨346048534096002505267333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7382368727381386779036437 346048534096002505267333)
                  ·
                    rfl

theorem cell23_6065344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 6].length) (baseStart_6065344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065344 prefixEnd_6065344 := by exact prefixLift 6065344
  have htrace : WordTrace (prefixWord ++ tailWord_6065344) baseStart_6065344 baseEnd_6065344 := by
    simpa [prefixWord, tailWord_6065344, baseEnd_6065344] using wordTrace_append hprefix tailTrace_6065344
  have hstable : (prefixWord ++ tailWord_6065344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065344).length < 2 ^ (prefixWord ++ tailWord_6065344).sum := by decide
  have hdescent : baseEnd_6065344 < baseStart_6065344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065363 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 3]
def baseStart_6065363 : Nat := 118140960795 + 6065363 * 2 ^ 59
def prefixEnd_6065363 : Nat := 4983230072969 + 3 ^ 40 * 6065363 * 2
def baseEnd_6065363 : Nat := 3114446562996457973068409

theorem tailTrace_6065363 : CollatzResearch.WordTrace tailWord_6065363 prefixEnd_6065363 3114446562996457973068409 := by
  unfold tailWord_6065363
  simp only [CollatzResearch.WordTrace]
  refine ⟨221221962725233207374768743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147481308483488804916512495 221221962725233207374768743)
  ·
    refine ⟨331832944087849811062153115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221221962725233207374768743 331832944087849811062153115)
    ·
      refine ⟨497749416131774716593229673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331832944087849811062153115 497749416131774716593229673)
      ·
        refine ⟨373312062098831037444922255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497749416131774716593229673 373312062098831037444922255)
        ·
          refine ⟨559968093148246556167383383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373312062098831037444922255 559968093148246556167383383)
          ·
            refine ⟨839952139722369834251075075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559968093148246556167383383 839952139722369834251075075)
            ·
              refine ⟨1259928209583554751376612613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839952139722369834251075075 1259928209583554751376612613)
              ·
                refine ⟨236236539296916515883114865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1259928209583554751376612613 236236539296916515883114865)
                ·
                  refine ⟨177177404472687386912336149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236236539296916515883114865 177177404472687386912336149)
                  ·
                    refine ⟨8305190834657221261515757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 177177404472687386912336149 8305190834657221261515757)
                    ·
                      refine ⟨3114446562996457973068409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8305190834657221261515757 3114446562996457973068409)
                      ·
                        rfl

theorem cell23_6065363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_6065363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065363 prefixEnd_6065363 := by exact prefixLift 6065363
  have htrace : WordTrace (prefixWord ++ tailWord_6065363) baseStart_6065363 baseEnd_6065363 := by
    simpa [prefixWord, tailWord_6065363, baseEnd_6065363] using wordTrace_append hprefix tailTrace_6065363
  have hstable : (prefixWord ++ tailWord_6065363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065363).length < 2 ^ (prefixWord ++ tailWord_6065363).sum := by decide
  have hdescent : baseEnd_6065363 < baseStart_6065363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065380 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_6065380 : Nat := 118140960795 + 6065380 * 2 ^ 59
def prefixEnd_6065380 : Nat := 4983230072969 + 3 ^ 40 * 6065380 * 2
def baseEnd_6065380 : Nat := 3114455292167584406555831

theorem tailTrace_6065380 : CollatzResearch.WordTrace tailWord_6065380 prefixEnd_6065380 3114455292167584406555831 := by
  unfold tailWord_6065380
  simp only [CollatzResearch.WordTrace]
  refine ⟨110611291383085809639068797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147481721844114412852091729 110611291383085809639068797)
  ·
    refine ⟨41479234268657178614650799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110611291383085809639068797 41479234268657178614650799)
    ·
      refine ⟨62218851402985767921976199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41479234268657178614650799 62218851402985767921976199)
      ·
        refine ⟨93328277104478651882964299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62218851402985767921976199 93328277104478651882964299)
        ·
          refine ⟨139992415656717977824446449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93328277104478651882964299 139992415656717977824446449)
          ·
            refine ⟨104994311742538483368334837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139992415656717977824446449 104994311742538483368334837)
            ·
              refine ⟨9843216725862982815781391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104994311742538483368334837 9843216725862982815781391)
              ·
                refine ⟨14764825088794474223672087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9843216725862982815781391 14764825088794474223672087)
                ·
                  refine ⟨22147237633191711335508131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14764825088794474223672087 22147237633191711335508131)
                  ·
                    refine ⟨33220856449787567003262197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22147237633191711335508131 33220856449787567003262197)
                    ·
                      refine ⟨3114455292167584406555831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33220856449787567003262197 3114455292167584406555831)
                      ·
                        rfl

theorem cell23_6065380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_6065380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065380 prefixEnd_6065380 := by exact prefixLift 6065380
  have htrace : WordTrace (prefixWord ++ tailWord_6065380) baseStart_6065380 baseEnd_6065380 := by
    simpa [prefixWord, tailWord_6065380, baseEnd_6065380] using wordTrace_append hprefix tailTrace_6065380
  have hstable : (prefixWord ++ tailWord_6065380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065380).length < 2 ^ (prefixWord ++ tailWord_6065380).sum := by decide
  have hdescent : baseEnd_6065380 < baseStart_6065380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065383 : List Nat := [1, 1, 5, 3, 13]
def baseStart_6065383 : Nat := 118140960795 + 6065383 * 2 ^ 59
def prefixEnd_6065383 : Nat := 4983230072969 + 3 ^ 40 * 6065383 * 2
def baseEnd_6065383 : Nat := 4272231594800477221973

theorem tailTrace_6065383 : CollatzResearch.WordTrace tailWord_6065383 prefixEnd_6065383 4272231594800477221973 := by
  unfold tailWord_6065383
  simp only [CollatzResearch.WordTrace]
  refine ⟨221222692185160750790496803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147481794790107167193664535 221222692185160750790496803)
  ·
    refine ⟨331834038277741126185745205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221222692185160750790496803 331834038277741126185745205)
    ·
      refine ⟨31109441088538230579913613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 331834038277741126185745205 31109441088538230579913613)
      ·
        refine ⟨11666040408201836467467605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31109441088538230579913613 11666040408201836467467605)
        ·
          refine ⟨4272231594800477221973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11666040408201836467467605 4272231594800477221973)
          ·
            rfl

theorem cell23_6065383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 13].length) (baseStart_6065383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065383 prefixEnd_6065383 := by exact prefixLift 6065383
  have htrace : WordTrace (prefixWord ++ tailWord_6065383) baseStart_6065383 baseEnd_6065383 := by
    simpa [prefixWord, tailWord_6065383, baseEnd_6065383] using wordTrace_append hprefix tailTrace_6065383
  have hstable : (prefixWord ++ tailWord_6065383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065383).length < 2 ^ (prefixWord ++ tailWord_6065383).sum := by decide
  have hdescent : baseEnd_6065383 < baseStart_6065383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065387 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 2, 4]
def baseStart_6065387 : Nat := 118140960795 + 6065387 * 2 ^ 59
def prefixEnd_6065387 : Nat := 4983230072969 + 3 ^ 40 * 6065387 * 2
def baseEnd_6065387 : Nat := 1038152962177388626389433

theorem tailTrace_6065387 : CollatzResearch.WordTrace tailWord_6065387 prefixEnd_6065387 1038152962177388626389433 := by
  unfold tailWord_6065387
  simp only [CollatzResearch.WordTrace]
  refine ⟨221222838077146259473642415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147481892051430839649094943 221222838077146259473642415)
  ·
    refine ⟨331834257115719389210463623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221222838077146259473642415 331834257115719389210463623)
    ·
      refine ⟨497751385673579083815695435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331834257115719389210463623 497751385673579083815695435)
      ·
        refine ⟨746627078510368625723543153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497751385673579083815695435 746627078510368625723543153)
        ·
          refine ⟨559970308882776469292657365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746627078510368625723543153 559970308882776469292657365)
          ·
            refine ⟨13124304114440073499046657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 559970308882776469292657365 13124304114440073499046657)
            ·
              refine ⟨9843228085830055124284993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13124304114440073499046657 9843228085830055124284993)
              ·
                refine ⟨7382421064372541343213745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9843228085830055124284993 7382421064372541343213745)
                ·
                  refine ⟨5536815798279406007410309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7382421064372541343213745 5536815798279406007410309)
                  ·
                    refine ⟨1038152962177388626389433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5536815798279406007410309 1038152962177388626389433)
                    ·
                      rfl

theorem cell23_6065387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 4].length) (baseStart_6065387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065387 prefixEnd_6065387 := by exact prefixLift 6065387
  have htrace : WordTrace (prefixWord ++ tailWord_6065387) baseStart_6065387 baseEnd_6065387 := by
    simpa [prefixWord, tailWord_6065387, baseEnd_6065387] using wordTrace_append hprefix tailTrace_6065387
  have hstable : (prefixWord ++ tailWord_6065387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065387).length < 2 ^ (prefixWord ++ tailWord_6065387).sum := by decide
  have hdescent : baseEnd_6065387 < baseStart_6065387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065413 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_6065413 : Nat := 118140960795 + 6065413 * 2 ^ 59
def prefixEnd_6065413 : Nat := 4983230072969 + 3 ^ 40 * 6065413 * 2
def baseEnd_6065413 : Nat := 1038157412343060925814393

theorem tailTrace_6065413 : CollatzResearch.WordTrace tailWord_6065413 prefixEnd_6065413 1038157412343060925814393 := by
  unfold tailWord_6065413
  simp only [CollatzResearch.WordTrace]
  refine ⟨221223786375052065914088893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147482524250034710609392595 221223786375052065914088893)
  ·
    refine ⟨82958919890644524717783335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221223786375052065914088893 82958919890644524717783335)
    ·
      refine ⟨124438379835966787076675003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82958919890644524717783335 124438379835966787076675003)
      ·
        refine ⟨186657569753950180615012505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124438379835966787076675003 186657569753950180615012505)
        ·
          refine ⟨139993177315462635461259379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186657569753950180615012505 139993177315462635461259379)
          ·
            refine ⟨209989765973193953191889069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139993177315462635461259379 209989765973193953191889069)
            ·
              refine ⟨78746162239947732446958401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209989765973193953191889069 78746162239947732446958401)
              ·
                refine ⟨59059621679960799335218801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78746162239947732446958401 59059621679960799335218801)
                ·
                  refine ⟨44294716259970599501414101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59059621679960799335218801 44294716259970599501414101)
                  ·
                    refine ⟨1038157412343060925814393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44294716259970599501414101 1038157412343060925814393)
                    ·
                      rfl

theorem cell23_6065413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_6065413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065413 prefixEnd_6065413 := by exact prefixLift 6065413
  have htrace : WordTrace (prefixWord ++ tailWord_6065413) baseStart_6065413 baseEnd_6065413 := by
    simpa [prefixWord, tailWord_6065413, baseEnd_6065413] using wordTrace_append hprefix tailTrace_6065413
  have hstable : (prefixWord ++ tailWord_6065413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065413).length < 2 ^ (prefixWord ++ tailWord_6065413).sum := by decide
  have hdescent : baseEnd_6065413 < baseStart_6065413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065438 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6065438 : Nat := 118140960795 + 6065438 * 2 ^ 59
def prefixEnd_6065438 : Nat := 4983230072969 + 3 ^ 40 * 6065438 * 2
def baseEnd_6065438 : Nat := 1038161691348515059876855

theorem tailTrace_6065438 : CollatzResearch.WordTrace tailWord_6065438 prefixEnd_6065438 1038161691348515059876855 := by
  unfold tailWord_6065438
  simp only [CollatzResearch.WordTrace]
  refine ⟨27653087274995186897968621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147483132133307663455832645 27653087274995186897968621)
  ·
    refine ⟨10369907728123195086738233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27653087274995186897968621 10369907728123195086738233)
    ·
      refine ⟨7777430796092396315053675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10369907728123195086738233 7777430796092396315053675)
      ·
        refine ⟨11666146194138594472580513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7777430796092396315053675 11666146194138594472580513)
        ·
          refine ⟨8749609645603945854435385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11666146194138594472580513 8749609645603945854435385)
          ·
            refine ⟨6562207234202959390826539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8749609645603945854435385 6562207234202959390826539)
            ·
              refine ⟨9843310851304439086239809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562207234202959390826539 9843310851304439086239809)
              ·
                refine ⟨7382483138478329314679857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9843310851304439086239809 7382483138478329314679857)
                ·
                  refine ⟨5536862353858746986009893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7382483138478329314679857 5536862353858746986009893)
                  ·
                    refine ⟨1038161691348515059876855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5536862353858746986009893 1038161691348515059876855)
                    ·
                      rfl

theorem cell23_6065438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6065438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065438 prefixEnd_6065438 := by exact prefixLift 6065438
  have htrace : WordTrace (prefixWord ++ tailWord_6065438) baseStart_6065438 baseEnd_6065438 := by
    simpa [prefixWord, tailWord_6065438, baseEnd_6065438] using wordTrace_append hprefix tailTrace_6065438
  have hstable : (prefixWord ++ tailWord_6065438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065438).length < 2 ^ (prefixWord ++ tailWord_6065438).sum := by decide
  have hdescent : baseEnd_6065438 < baseStart_6065438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065461 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_6065461 : Nat := 118140960795 + 6065461 * 2 ^ 59
def prefixEnd_6065461 : Nat := 4983230072969 + 3 ^ 40 * 6065461 * 2
def baseEnd_6065461 : Nat := 3114496884100598589642959

theorem tailTrace_6065461 : CollatzResearch.WordTrace tailWord_6065461 prefixEnd_6065461 3114496884100598589642959 := by
  unfold tailWord_6065461
  simp only [CollatzResearch.WordTrace]
  refine ⟨221225537078878170111836237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147483691385918780074557491 221225537078878170111836237)
  ·
    refine ⟨82959576404579313791938589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221225537078878170111836237 82959576404579313791938589)
    ·
      refine ⟨31109841151717242671976971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82959576404579313791938589 31109841151717242671976971)
      ·
        refine ⟨46664761727575864007965457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31109841151717242671976971 46664761727575864007965457)
        ·
          refine ⟨34998571295681898005974093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46664761727575864007965457 34998571295681898005974093)
          ·
            refine ⟨13124464235880711752240285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34998571295681898005974093 13124464235880711752240285)
            ·
              refine ⟨4921674088455266907090107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13124464235880711752240285 4921674088455266907090107)
              ·
                refine ⟨7382511132682900360635161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921674088455266907090107 7382511132682900360635161)
                ·
                  refine ⟨5536883349512175270476371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7382511132682900360635161 5536883349512175270476371)
                  ·
                    refine ⟨8305325024268262905714557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5536883349512175270476371 8305325024268262905714557)
                    ·
                      refine ⟨3114496884100598589642959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8305325024268262905714557 3114496884100598589642959)
                      ·
                        rfl

theorem cell23_6065461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_6065461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065461 prefixEnd_6065461 := by exact prefixLift 6065461
  have htrace : WordTrace (prefixWord ++ tailWord_6065461) baseStart_6065461 baseEnd_6065461 := by
    simpa [prefixWord, tailWord_6065461, baseEnd_6065461] using wordTrace_append hprefix tailTrace_6065461
  have hstable : (prefixWord ++ tailWord_6065461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065461).length < 2 ^ (prefixWord ++ tailWord_6065461).sum := by decide
  have hdescent : baseEnd_6065461 < baseStart_6065461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065484 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 4, 2, 2]
def baseStart_6065484 : Nat := 118140960795 + 6065484 * 2 ^ 59
def prefixEnd_6065484 : Nat := 4983230072969 + 3 ^ 40 * 6065484 * 2
def baseEnd_6065484 : Nat := 3114508694155651999655353

theorem tailTrace_6065484 : CollatzResearch.WordTrace tailWord_6065484 prefixEnd_6065484 3114508694155651999655353 := by
  unfold tailWord_6065484
  simp only [CollatzResearch.WordTrace]
  refine ⟨110613187978897422519961753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147484250638529896693282337 110613187978897422519961753)
  ·
    refine ⟨82959890984173066889971315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110613187978897422519961753 82959890984173066889971315)
    ·
      refine ⟨124439836476259600334956973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82959890984173066889971315 124439836476259600334956973)
      ·
        refine ⟨46664938678597350125608865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124439836476259600334956973 46664938678597350125608865)
        ·
          refine ⟨34998704008948012594206649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46664938678597350125608865 34998704008948012594206649)
          ·
            refine ⟨26249028006711009445654987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34998704008948012594206649 26249028006711009445654987)
            ·
              refine ⟨39373542010066514168482481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26249028006711009445654987 39373542010066514168482481)
              ·
                refine ⟨29530156507549885626361861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39373542010066514168482481 29530156507549885626361861)
                ·
                  refine ⟨5536904345165603554942849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29530156507549885626361861 5536904345165603554942849)
                  ·
                    refine ⟨4152678258874202666207137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5536904345165603554942849 4152678258874202666207137)
                    ·
                      refine ⟨3114508694155651999655353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4152678258874202666207137 3114508694155651999655353)
                      ·
                        rfl

theorem cell23_6065484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_6065484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065484 prefixEnd_6065484 := by exact prefixLift 6065484
  have htrace : WordTrace (prefixWord ++ tailWord_6065484) baseStart_6065484 baseEnd_6065484 := by
    simpa [prefixWord, tailWord_6065484, baseEnd_6065484] using wordTrace_append hprefix tailTrace_6065484
  have hstable : (prefixWord ++ tailWord_6065484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065484).length < 2 ^ (prefixWord ++ tailWord_6065484).sum := by decide
  have hdescent : baseEnd_6065484 < baseStart_6065484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065507 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 7]
def baseStart_6065507 : Nat := 118140960795 + 6065507 * 2 ^ 59
def prefixEnd_6065507 : Nat := 4983230072969 + 3 ^ 40 * 6065507 * 2
def baseEnd_6065507 : Nat := 346057833801189489963083

theorem tailTrace_6065507 : CollatzResearch.WordTrace tailWord_6065507 prefixEnd_6065507 346057833801189489963083 := by
  unfold tailWord_6065507
  simp only [CollatzResearch.WordTrace]
  refine ⟨221227214836711519968010775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147484809891141013312007183 221227214836711519968010775)
  ·
    refine ⟨331840822255067279952016163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221227214836711519968010775 331840822255067279952016163)
    ·
      refine ⟨497761233382600919928024245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331840822255067279952016163 497761233382600919928024245)
      ·
        refine ⟨46665115629618836243252273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 497761233382600919928024245 46665115629618836243252273)
        ·
          refine ⟨34998836722214127182439205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46665115629618836243252273 34998836722214127182439205)
          ·
            refine ⟨6562281885415148846707351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34998836722214127182439205 6562281885415148846707351)
            ·
              refine ⟨9843422828122723270061027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562281885415148846707351 9843422828122723270061027)
              ·
                refine ⟨14765134242184084905091541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9843422828122723270061027 14765134242184084905091541)
                ·
                  refine ⟨346057833801189489963083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14765134242184084905091541 346057833801189489963083)
                  ·
                    rfl

theorem cell23_6065507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 7].length) (baseStart_6065507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065507 prefixEnd_6065507 := by exact prefixLift 6065507
  have htrace : WordTrace (prefixWord ++ tailWord_6065507) baseStart_6065507 baseEnd_6065507 := by
    simpa [prefixWord, tailWord_6065507, baseEnd_6065507] using wordTrace_append hprefix tailTrace_6065507
  have hstable : (prefixWord ++ tailWord_6065507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065507).length < 2 ^ (prefixWord ++ tailWord_6065507).sum := by decide
  have hdescent : baseEnd_6065507 < baseStart_6065507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065520 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 4, 5]
def baseStart_6065520 : Nat := 118140960795 + 6065520 * 2 ^ 59
def prefixEnd_6065520 : Nat := 4983230072969 + 3 ^ 40 * 6065520 * 2
def baseEnd_6065520 : Nat := 1038175726486404619601729

theorem tailTrace_6065520 : CollatzResearch.WordTrace tailWord_6065520 prefixEnd_6065520 1038175726486404619601729 := by
  unfold tailWord_6065520
  simp only [CollatzResearch.WordTrace]
  refine ⟨110613844492832211594117007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147485125990442948792156009 110613844492832211594117007)
  ·
    refine ⟨165920766739248317391175511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110613844492832211594117007 165920766739248317391175511)
    ·
      refine ⟨248881150108872476086763267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165920766739248317391175511 248881150108872476086763267)
      ·
        refine ⟨373321725163308714130144901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248881150108872476086763267 373321725163308714130144901)
        ·
          refine ⟨69997823468120383899402169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 373321725163308714130144901 69997823468120383899402169)
          ·
            refine ⟨52498367601090287924551627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69997823468120383899402169 52498367601090287924551627)
            ·
              refine ⟨78747551401635431886827441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52498367601090287924551627 78747551401635431886827441)
              ·
                refine ⟨59060663551226573915120581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78747551401635431886827441 59060663551226573915120581)
                ·
                  refine ⟨11073874415854982609085109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59060663551226573915120581 11073874415854982609085109)
                  ·
                    refine ⟨1038175726486404619601729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11073874415854982609085109 1038175726486404619601729)
                    ·
                      rfl

theorem cell23_6065520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_6065520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065520 prefixEnd_6065520 := by exact prefixLift 6065520
  have htrace : WordTrace (prefixWord ++ tailWord_6065520) baseStart_6065520 baseEnd_6065520 := by
    simpa [prefixWord, tailWord_6065520, baseEnd_6065520] using wordTrace_append hprefix tailTrace_6065520
  have hstable : (prefixWord ++ tailWord_6065520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065520).length < 2 ^ (prefixWord ++ tailWord_6065520).sum := by decide
  have hdescent : baseEnd_6065520 < baseStart_6065520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065557 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_6065557 : Nat := 118140960795 + 6065557 * 2 ^ 59
def prefixEnd_6065557 : Nat := 4983230072969 + 3 ^ 40 * 6065557 * 2
def baseEnd_6065557 : Nat := 3114546178243430214042517

theorem tailTrace_6065557 : CollatzResearch.WordTrace tailWord_6065557 prefixEnd_6065557 3114546178243430214042517 := by
  unfold tailWord_6065557
  simp only [CollatzResearch.WordTrace]
  refine ⟨221229038486530378507330925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147486025657686919004887283 221229038486530378507330925)
  ·
    refine ⟨82960889432448891940249097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221229038486530378507330925 82960889432448891940249097)
    ·
      refine ⟨62220667074336668955186823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82960889432448891940249097 62220667074336668955186823)
      ·
        refine ⟨93331000611505003432780235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62220667074336668955186823 93331000611505003432780235)
        ·
          refine ⟨139996500917257505149170353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93331000611505003432780235 139996500917257505149170353)
          ·
            refine ⟨104997375687943128861877765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139996500917257505149170353 104997375687943128861877765)
            ·
              refine ⟨19687007941489336661602081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104997375687943128861877765 19687007941489336661602081)
              ·
                refine ⟨14765255956117002496201561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19687007941489336661602081 14765255956117002496201561)
                ·
                  refine ⟨11073941967087751872151171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14765255956117002496201561 11073941967087751872151171)
                  ·
                    refine ⟨16610912950631627808226757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11073941967087751872151171 16610912950631627808226757)
                    ·
                      refine ⟨3114546178243430214042517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16610912950631627808226757 3114546178243430214042517)
                      ·
                        rfl

theorem cell23_6065557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_6065557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065557 prefixEnd_6065557 := by exact prefixLift 6065557
  have htrace : WordTrace (prefixWord ++ tailWord_6065557) baseStart_6065557 baseEnd_6065557 := by
    simpa [prefixWord, tailWord_6065557, baseEnd_6065557] using wordTrace_append hprefix tailTrace_6065557
  have hstable : (prefixWord ++ tailWord_6065557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065557).length < 2 ^ (prefixWord ++ tailWord_6065557).sum := by decide
  have hdescent : baseEnd_6065557 < baseStart_6065557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065624 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 3, 1, 3]
def baseStart_6065624 : Nat := 118140960795 + 6065624 * 2 ^ 59
def prefixEnd_6065624 : Nat := 4983230072969 + 3 ^ 40 * 6065624 * 2
def baseEnd_6065624 : Nat := 3114580581447281451904709

theorem tailTrace_6065624 : CollatzResearch.WordTrace tailWord_6065624 prefixEnd_6065624 3114580581447281451904709 := by
  unfold tailWord_6065624
  simp only [CollatzResearch.WordTrace]
  refine ⟨110615741088643824475009963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147487654784858432633346617 110615741088643824475009963)
  ·
    refine ⟨165923611632965736712514945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110615741088643824475009963 165923611632965736712514945)
    ·
      refine ⟨124442708724724302534386209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165923611632965736712514945 124442708724724302534386209)
      ·
        refine ⟨93332031543543226900789657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124442708724724302534386209 93332031543543226900789657)
        ·
          refine ⟨69999023657657420175592243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93332031543543226900789657 69999023657657420175592243)
          ·
            refine ⟨104998535486486130263388365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69999023657657420175592243 104998535486486130263388365)
            ·
              refine ⟨39374450807432298848770637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104998535486486130263388365 39374450807432298848770637)
              ·
                refine ⟨14765419052787112068288989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39374450807432298848770637 14765419052787112068288989)
                ·
                  refine ⟨5537032144795167025608371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14765419052787112068288989 5537032144795167025608371)
                  ·
                    refine ⟨8305548217192750538412557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5537032144795167025608371 8305548217192750538412557)
                    ·
                      refine ⟨3114580581447281451904709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8305548217192750538412557 3114580581447281451904709)
                      ·
                        rfl

theorem cell23_6065624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_6065624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065624 prefixEnd_6065624 := by exact prefixLift 6065624
  have htrace : WordTrace (prefixWord ++ tailWord_6065624) baseStart_6065624 baseEnd_6065624 := by
    simpa [prefixWord, tailWord_6065624, baseEnd_6065624] using wordTrace_append hprefix tailTrace_6065624
  have hstable : (prefixWord ++ tailWord_6065624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065624).length < 2 ^ (prefixWord ++ tailWord_6065624).sum := by decide
  have hdescent : baseEnd_6065624 < baseStart_6065624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065647 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_6065647 : Nat := 118140960795 + 6065647 * 2 ^ 59
def prefixEnd_6065647 : Nat := 4983230072969 + 3 ^ 40 * 6065647 * 2
def baseEnd_6065647 : Nat := 3114592391502334861917103

theorem tailTrace_6065647 : CollatzResearch.WordTrace tailWord_6065647 prefixEnd_6065647 3114592391502334861917103 := by
  unfold tailWord_6065647
  simp only [CollatzResearch.WordTrace]
  refine ⟨221232321056204323878107195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147488214037469549252071463 221232321056204323878107195)
  ·
    refine ⟨331848481584306485817160793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221232321056204323878107195 331848481584306485817160793)
    ·
      refine ⟨248886361188229864362870595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331848481584306485817160793 248886361188229864362870595)
      ·
        refine ⟨373329541782344796544305893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248886361188229864362870595 373329541782344796544305893)
        ·
          refine ⟨69999289084189649352057355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 373329541782344796544305893 69999289084189649352057355)
          ·
            refine ⟨104998933626284474028086033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69999289084189649352057355 104998933626284474028086033)
            ·
              refine ⟨78749200219713355521064525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104998933626284474028086033 78749200219713355521064525)
              ·
                refine ⟨29530950082392508320399197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78749200219713355521064525 29530950082392508320399197)
                ·
                  refine ⟨11074106280897190620149699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29530950082392508320399197 11074106280897190620149699)
                  ·
                    refine ⟨16611159421345785930224549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11074106280897190620149699 16611159421345785930224549)
                    ·
                      refine ⟨3114592391502334861917103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16611159421345785930224549 3114592391502334861917103)
                      ·
                        rfl

theorem cell23_6065647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_6065647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065647 prefixEnd_6065647 := by exact prefixLift 6065647
  have htrace : WordTrace (prefixWord ++ tailWord_6065647) baseStart_6065647 baseEnd_6065647 := by
    simpa [prefixWord, tailWord_6065647, baseEnd_6065647] using wordTrace_append hprefix tailTrace_6065647
  have hstable : (prefixWord ++ tailWord_6065647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065647).length < 2 ^ (prefixWord ++ tailWord_6065647).sum := by decide
  have hdescent : baseEnd_6065647 < baseStart_6065647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065668 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6065668 : Nat := 118140960795 + 6065668 * 2 ^ 59
def prefixEnd_6065668 : Nat := 4983230072969 + 3 ^ 40 * 6065668 * 2
def baseEnd_6065668 : Nat := 3114603174596079279754507

theorem tailTrace_6065668 : CollatzResearch.WordTrace tailWord_6065668 prefixEnd_6065668 3114603174596079279754507 := by
  unfold tailWord_6065668
  simp only [CollatzResearch.WordTrace]
  refine ⟨110616543494564122232310829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147488724659418829643081105 110616543494564122232310829)
  ·
    refine ⟨41481203810461545837116561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110616543494564122232310829 41481203810461545837116561)
    ·
      refine ⟨31110902857846159377837421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41481203810461545837116561 31110902857846159377837421)
      ·
        refine ⟨11666588571692309766689033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31110902857846159377837421 11666588571692309766689033)
        ·
          refine ⟨8749941428769232325016775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11666588571692309766689033 8749941428769232325016775)
          ·
            refine ⟨13124912143153848487525163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8749941428769232325016775 13124912143153848487525163)
            ·
              refine ⟨19687368214730772731287745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13124912143153848487525163 19687368214730772731287745)
              ·
                refine ⟨14765526161048079548465809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19687368214730772731287745 14765526161048079548465809)
                ·
                  refine ⟨11074144620786059661349357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14765526161048079548465809 11074144620786059661349357)
                  ·
                    refine ⟨4152804232794772373006009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11074144620786059661349357 4152804232794772373006009)
                    ·
                      refine ⟨3114603174596079279754507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4152804232794772373006009 3114603174596079279754507)
                      ·
                        rfl

theorem cell23_6065668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6065668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065668 prefixEnd_6065668 := by exact prefixLift 6065668
  have htrace : WordTrace (prefixWord ++ tailWord_6065668) baseStart_6065668 baseEnd_6065668 := by
    simpa [prefixWord, tailWord_6065668, baseEnd_6065668] using wordTrace_append hprefix tailTrace_6065668
  have hstable : (prefixWord ++ tailWord_6065668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065668).length < 2 ^ (prefixWord ++ tailWord_6065668).sum := by decide
  have hdescent : baseEnd_6065668 < baseStart_6065668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065674 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_6065674 : Nat := 118140960795 + 6065674 * 2 ^ 59
def prefixEnd_6065674 : Nat := 4983230072969 + 3 ^ 40 * 6065674 * 2
def baseEnd_6065674 : Nat := 1038202085160002085426493

theorem tailTrace_6065674 : CollatzResearch.WordTrace tailWord_6065674 prefixEnd_6065674 1038202085160002085426493 := by
  unfold tailWord_6065674
  simp only [CollatzResearch.WordTrace]
  refine ⟨55308326456776626872335019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147488870551404338326226717 55308326456776626872335019)
  ·
    refine ⟨82962489685164940308502529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55308326456776626872335019 82962489685164940308502529)
    ·
      refine ⟨62221867263873705231376897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82962489685164940308502529 62221867263873705231376897)
      ·
        refine ⟨46666400447905278923532673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62221867263873705231376897 46666400447905278923532673)
        ·
          refine ⟨34999800335928959192649505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46666400447905278923532673 34999800335928959192649505)
          ·
            refine ⟨26249850251946719394487129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34999800335928959192649505 26249850251946719394487129)
            ·
              refine ⟨19687387688960039545865347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26249850251946719394487129 19687387688960039545865347)
              ·
                refine ⟨29531081533440059318798021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19687387688960039545865347 29531081533440059318798021)
                ·
                  refine ⟨5537077787520011122274629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29531081533440059318798021 5537077787520011122274629)
                  ·
                    refine ⟨1038202085160002085426493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5537077787520011122274629 1038202085160002085426493)
                    ·
                      rfl

theorem cell23_6065674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_6065674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065674 prefixEnd_6065674 := by exact prefixLift 6065674
  have htrace : WordTrace (prefixWord ++ tailWord_6065674) baseStart_6065674 baseEnd_6065674 := by
    simpa [prefixWord, tailWord_6065674, baseEnd_6065674] using wordTrace_append hprefix tailTrace_6065674
  have hstable : (prefixWord ++ tailWord_6065674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065674).length < 2 ^ (prefixWord ++ tailWord_6065674).sum := by decide
  have hdescent : baseEnd_6065674 < baseStart_6065674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065675 : List Nat := [1, 1, 1, 1, 8, 1, 3, 2, 1, 1, 3]
def baseStart_6065675 : Nat := 118140960795 + 6065675 * 2 ^ 59
def prefixEnd_6065675 : Nat := 4983230072969 + 3 ^ 40 * 6065675 * 2
def baseEnd_6065675 : Nat := 3114606768960660752366975

theorem tailTrace_6065675 : CollatzResearch.WordTrace tailWord_6065675 prefixEnd_6065675 3114606768960660752366975 := by
  unfold tailWord_6065675
  simp only [CollatzResearch.WordTrace]
  refine ⟨221233342300102884660126479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147488894866735256440084319 221233342300102884660126479)
  ·
    refine ⟨331850013450154326990189719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221233342300102884660126479 331850013450154326990189719)
    ·
      refine ⟨497775020175231490485284579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331850013450154326990189719 497775020175231490485284579)
      ·
        refine ⟨746662530262847235727926869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497775020175231490485284579 746662530262847235727926869)
        ·
          refine ⟨8749951526517741043686643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 746662530262847235727926869 8749951526517741043686643)
          ·
            refine ⟨13124927289776611565529965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8749951526517741043686643 13124927289776611565529965)
            ·
              refine ⟨4921847733666229337073737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13124927289776611565529965 4921847733666229337073737)
              ·
                refine ⟨3691385800249672002805303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4921847733666229337073737 3691385800249672002805303)
                ·
                  refine ⟨5537078700374508004207955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3691385800249672002805303 5537078700374508004207955)
                  ·
                    refine ⟨8305618050561762006311933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5537078700374508004207955 8305618050561762006311933)
                    ·
                      refine ⟨3114606768960660752366975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8305618050561762006311933 3114606768960660752366975)
                      ·
                        rfl

theorem cell23_6065675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 1, 1, 3].length) (baseStart_6065675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065675 prefixEnd_6065675 := by exact prefixLift 6065675
  have htrace : WordTrace (prefixWord ++ tailWord_6065675) baseStart_6065675 baseEnd_6065675 := by
    simpa [prefixWord, tailWord_6065675, baseEnd_6065675] using wordTrace_append hprefix tailTrace_6065675
  have hstable : (prefixWord ++ tailWord_6065675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065675).length < 2 ^ (prefixWord ++ tailWord_6065675).sum := by decide
  have hdescent : baseEnd_6065675 < baseStart_6065675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065718 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_6065718 : Nat := 118140960795 + 6065718 * 2 ^ 59
def prefixEnd_6065718 : Nat := 4983230072969 + 3 ^ 40 * 6065718 * 2
def baseEnd_6065718 : Nat := 3114628848628804084129277

theorem tailTrace_6065718 : CollatzResearch.WordTrace tailWord_6065718 prefixEnd_6065718 3114628848628804084129277 := by
  unfold tailWord_6065718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13827181914934193937746363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147489940425964735335961205 13827181914934193937746363)
  ·
    refine ⟨20740772872401290906619545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13827181914934193937746363 20740772872401290906619545)
    ·
      refine ⟨15555579654300968179964659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20740772872401290906619545 15555579654300968179964659)
      ·
        refine ⟨23333369481451452269946989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15555579654300968179964659 23333369481451452269946989)
        ·
          refine ⟨8750013555544294601230121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23333369481451452269946989 8750013555544294601230121)
          ·
            refine ⟨6562510166658220950922591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8750013555544294601230121 6562510166658220950922591)
            ·
              refine ⟨9843765249987331426383887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562510166658220950922591 9843765249987331426383887)
              ·
                refine ⟨14765647874980997139575831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9843765249987331426383887 14765647874980997139575831)
                ·
                  refine ⟨22148471812471495709363747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14765647874980997139575831 22148471812471495709363747)
                  ·
                    refine ⟨33222707718707243564045621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22148471812471495709363747 33222707718707243564045621)
                    ·
                      refine ⟨3114628848628804084129277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33222707718707243564045621 3114628848628804084129277)
                      ·
                        rfl

theorem cell23_6065718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_6065718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065718 prefixEnd_6065718 := by exact prefixLift 6065718
  have htrace : WordTrace (prefixWord ++ tailWord_6065718) baseStart_6065718 baseEnd_6065718 := by
    simpa [prefixWord, tailWord_6065718, baseEnd_6065718] using wordTrace_append hprefix tailTrace_6065718
  have hstable : (prefixWord ++ tailWord_6065718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065718).length < 2 ^ (prefixWord ++ tailWord_6065718).sum := by decide
  have hdescent : baseEnd_6065718 < baseStart_6065718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065804 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_6065804 : Nat := 118140960795 + 6065804 * 2 ^ 59
def prefixEnd_6065804 : Nat := 4983230072969 + 3 ^ 40 * 6065804 * 2
def baseEnd_6065804 : Nat := 3114673007965090747653881

theorem tailTrace_6065804 : CollatzResearch.WordTrace tailWord_6065804 prefixEnd_6065804 3114673007965090747653881 := by
  unfold tailWord_6065804
  simp only [CollatzResearch.WordTrace]
  refine ⟨110619023658317769845786233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147492031544423693127714977 110619023658317769845786233)
  ·
    refine ⟨82964267743738327384339675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110619023658317769845786233 82964267743738327384339675)
    ·
      refine ⟨124446401615607491076509513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82964267743738327384339675 124446401615607491076509513)
      ·
        refine ⟨93334801211705618307382135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124446401615607491076509513 93334801211705618307382135)
        ·
          refine ⟨140002201817558427461073203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93334801211705618307382135 140002201817558427461073203)
          ·
            refine ⟨210003302726337641191609805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140002201817558427461073203 210003302726337641191609805)
            ·
              refine ⟨78751238522376615446853677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210003302726337641191609805 78751238522376615446853677)
              ·
                refine ⟨29531714445891230792570129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78751238522376615446853677 29531714445891230792570129)
                ·
                  refine ⟨22148785834418423094427597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29531714445891230792570129 22148785834418423094427597)
                  ·
                    refine ⟨8305794687906908660410349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22148785834418423094427597 8305794687906908660410349)
                    ·
                      refine ⟨3114673007965090747653881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8305794687906908660410349 3114673007965090747653881)
                      ·
                        rfl

theorem cell23_6065804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_6065804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065804 prefixEnd_6065804 := by exact prefixLift 6065804
  have htrace : WordTrace (prefixWord ++ tailWord_6065804) baseStart_6065804 baseEnd_6065804 := by
    simpa [prefixWord, tailWord_6065804, baseEnd_6065804] using wordTrace_append hprefix tailTrace_6065804
  have hstable : (prefixWord ++ tailWord_6065804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065804).length < 2 ^ (prefixWord ++ tailWord_6065804).sum := by decide
  have hdescent : baseEnd_6065804 < baseStart_6065804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065817 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_6065817 : Nat := 118140960795 + 6065817 * 2 ^ 59
def prefixEnd_6065817 : Nat := 4983230072969 + 3 ^ 40 * 6065817 * 2
def baseEnd_6065817 : Nat := 3114679683213599196791321

theorem tailTrace_6065817 : CollatzResearch.WordTrace tailWord_6065817 prefixEnd_6065817 3114679683213599196791321 := by
  unfold tailWord_6065817
  simp only [CollatzResearch.WordTrace]
  refine ⟨221238521465588442911795705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147492347643725628607863803 221238521465588442911795705)
  ·
    refine ⟨165928891099191332183846779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221238521465588442911795705 165928891099191332183846779)
    ·
      refine ⟨248893336648786998275770169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165928891099191332183846779 248893336648786998275770169)
      ·
        refine ⟨186670002486590248706827627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248893336648786998275770169 186670002486590248706827627)
        ·
          refine ⟨280005003729885373060241441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186670002486590248706827627 280005003729885373060241441)
          ·
            refine ⟨210003752797414029795181081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280005003729885373060241441 210003752797414029795181081)
            ·
              refine ⟨157502814598060522346385811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210003752797414029795181081 157502814598060522346385811)
              ·
                refine ⟨236254221897090783519578717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157502814598060522346385811 236254221897090783519578717)
                ·
                  refine ⟨88595333211409043819842019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236254221897090783519578717 88595333211409043819842019)
                  ·
                    refine ⟨132892999817113565729763029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88595333211409043819842019 132892999817113565729763029)
                    ·
                      refine ⟨3114679683213599196791321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132892999817113565729763029 3114679683213599196791321)
                      ·
                        rfl

theorem cell23_6065817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_6065817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065817 prefixEnd_6065817 := by exact prefixLift 6065817
  have htrace : WordTrace (prefixWord ++ tailWord_6065817) baseStart_6065817 baseEnd_6065817 := by
    simpa [prefixWord, tailWord_6065817, baseEnd_6065817] using wordTrace_append hprefix tailTrace_6065817
  have hstable : (prefixWord ++ tailWord_6065817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065817).length < 2 ^ (prefixWord ++ tailWord_6065817).sum := by decide
  have hdescent : baseEnd_6065817 < baseStart_6065817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065824 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 1, 7]
def baseStart_6065824 : Nat := 118140960795 + 6065824 * 2 ^ 59
def prefixEnd_6065824 : Nat := 4983230072969 + 3 ^ 40 * 6065824 * 2
def baseEnd_6065824 : Nat := 1038227759192726889801263

theorem tailTrace_6065824 : CollatzResearch.WordTrace tailWord_6065824 prefixEnd_6065824 1038227759192726889801263 := by
  unfold tailWord_6065824
  simp only [CollatzResearch.WordTrace]
  refine ⟨110619388388281541553650263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147492517851042055404867017 110619388388281541553650263)
  ·
    refine ⟨165929082582422312330475395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110619388388281541553650263 165929082582422312330475395)
    ·
      refine ⟨248893623873633468495713093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165929082582422312330475395 248893623873633468495713093)
      ·
        refine ⟨46667554476306275342946205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248893623873633468495713093 46667554476306275342946205)
        ·
          refine ⟨17500332928614853253604827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46667554476306275342946205 17500332928614853253604827)
          ·
            refine ⟨26250499392922279880407241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17500332928614853253604827 26250499392922279880407241)
            ·
              refine ⟨19687874544691709910305431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26250499392922279880407241 19687874544691709910305431)
              ·
                refine ⟨29531811817037564865458147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19687874544691709910305431 29531811817037564865458147)
                ·
                  refine ⟨44297717725556347298187221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29531811817037564865458147 44297717725556347298187221)
                  ·
                    refine ⟨1038227759192726889801263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44297717725556347298187221 1038227759192726889801263)
                    ·
                      rfl

theorem cell23_6065824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_6065824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065824 prefixEnd_6065824 := by exact prefixLift 6065824
  have htrace : WordTrace (prefixWord ++ tailWord_6065824) baseStart_6065824 baseEnd_6065824 := by
    simpa [prefixWord, tailWord_6065824, baseEnd_6065824] using wordTrace_append hprefix tailTrace_6065824
  have hstable : (prefixWord ++ tailWord_6065824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065824).length < 2 ^ (prefixWord ++ tailWord_6065824).sum := by decide
  have hdescent : baseEnd_6065824 < baseStart_6065824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065828 : List Nat := [2, 3, 1, 2, 2, 4, 1, 3, 5]
def baseStart_6065828 : Nat := 118140960795 + 6065828 * 2 ^ 59
def prefixEnd_6065828 : Nat := 4983230072969 + 3 ^ 40 * 6065828 * 2
def baseEnd_6065828 : Nat := 346076147944533183750419

theorem tailTrace_6065828 : CollatzResearch.WordTrace tailWord_6065828 prefixEnd_6065828 346076147944533183750419 := by
  unfold tailWord_6065828
  simp only [CollatzResearch.WordTrace]
  refine ⟨110619461334274295895223069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147492615112365727860297425 110619461334274295895223069)
  ·
    refine ⟨41482298000352860960708651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110619461334274295895223069 41482298000352860960708651)
    ·
      refine ⟨62223447000529291441062977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41482298000352860960708651 62223447000529291441062977)
      ·
        refine ⟨46667585250396968580797233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62223447000529291441062977 46667585250396968580797233)
        ·
          refine ⟨35000688937797726435597925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46667585250396968580797233 35000688937797726435597925)
          ·
            refine ⟨6562629175837073706674611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35000688937797726435597925 6562629175837073706674611)
            ·
              refine ⟨9843943763755610560011917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562629175837073706674611 9843943763755610560011917)
              ·
                refine ⟨3691478911408353960004469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9843943763755610560011917 3691478911408353960004469)
                ·
                  refine ⟨346076147944533183750419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3691478911408353960004469 346076147944533183750419)
                  ·
                    rfl

theorem cell23_6065828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_6065828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065828 prefixEnd_6065828 := by exact prefixLift 6065828
  have htrace : WordTrace (prefixWord ++ tailWord_6065828) baseStart_6065828 baseEnd_6065828 := by
    simpa [prefixWord, tailWord_6065828, baseEnd_6065828] using wordTrace_append hprefix tailTrace_6065828
  have hstable : (prefixWord ++ tailWord_6065828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065828).length < 2 ^ (prefixWord ++ tailWord_6065828).sum := by decide
  have hdescent : baseEnd_6065828 < baseStart_6065828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065845 : List Nat := [1, 3, 3, 3, 2, 1, 3, 2, 5]
def baseStart_6065845 : Nat := 118140960795 + 6065845 * 2 ^ 59
def prefixEnd_6065845 : Nat := 4983230072969 + 3 ^ 40 * 6065845 * 2
def baseEnd_6065845 : Nat := 346077117852436120804577

theorem tailTrace_6065845 : CollatzResearch.WordTrace tailWord_6065845 prefixEnd_6065845 346077117852436120804577 := by
  unfold tailWord_6065845
  simp only [CollatzResearch.WordTrace]
  refine ⟨221239542709487003693814989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147493028472991335795876659 221239542709487003693814989)
  ·
    refine ⟨82964828516057626385180621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221239542709487003693814989 82964828516057626385180621)
    ·
      refine ⟨31111810693521609894442733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82964828516057626385180621 31111810693521609894442733)
      ·
        refine ⟨11666929010070603710416025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31111810693521609894442733 11666929010070603710416025)
        ·
          refine ⟨8750196757552952782812019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11666929010070603710416025 8750196757552952782812019)
          ·
            refine ⟨13125295136329429174218029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8750196757552952782812019 13125295136329429174218029)
            ·
              refine ⟨4921985676123535940331761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13125295136329429174218029 4921985676123535940331761)
              ·
                refine ⟨3691489257092651955248821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4921985676123535940331761 3691489257092651955248821)
                ·
                  refine ⟨346077117852436120804577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3691489257092651955248821 346077117852436120804577)
                  ·
                    rfl

theorem cell23_6065845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_6065845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065845 prefixEnd_6065845 := by exact prefixLift 6065845
  have htrace : WordTrace (prefixWord ++ tailWord_6065845) baseStart_6065845 baseEnd_6065845 := by
    simpa [prefixWord, tailWord_6065845, baseEnd_6065845] using wordTrace_append hprefix tailTrace_6065845
  have hstable : (prefixWord ++ tailWord_6065845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065845).length < 2 ^ (prefixWord ++ tailWord_6065845).sum := by decide
  have hdescent : baseEnd_6065845 < baseStart_6065845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065881 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 3]
def baseStart_6065881 : Nat := 118140960795 + 6065881 * 2 ^ 59
def prefixEnd_6065881 : Nat := 4983230072969 + 3 ^ 40 * 6065881 * 2
def baseEnd_6065881 : Nat := 3114712545975486946391027

theorem tailTrace_6065881 : CollatzResearch.WordTrace tailWord_6065881 prefixEnd_6065881 3114712545975486946391027 := by
  unfold tailWord_6065881
  simp only [CollatzResearch.WordTrace]
  refine ⟨221240855737356581842125497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147493903824904387894750331 221240855737356581842125497)
  ·
    refine ⟨165930641803017436381594123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221240855737356581842125497 165930641803017436381594123)
    ·
      refine ⟨248895962704526154572391185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165930641803017436381594123 248895962704526154572391185)
      ·
        refine ⟨186671972028394615929293389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248895962704526154572391185 186671972028394615929293389)
        ·
          refine ⟨70001989510647980973485021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186671972028394615929293389 70001989510647980973485021)
          ·
            refine ⟨26250746066492992865056883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70001989510647980973485021 26250746066492992865056883)
            ·
              refine ⟨39376119099739489297585325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26250746066492992865056883 39376119099739489297585325)
              ·
                refine ⟨14766044662402308486594497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39376119099739489297585325 14766044662402308486594497)
                ·
                  refine ⟨11074533496801731364945873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14766044662402308486594497 11074533496801731364945873)
                  ·
                    refine ⟨8305900122601298523709405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11074533496801731364945873 8305900122601298523709405)
                    ·
                      refine ⟨3114712545975486946391027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8305900122601298523709405 3114712545975486946391027)
                      ·
                        rfl

theorem cell23_6065881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_6065881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065881 prefixEnd_6065881 := by exact prefixLift 6065881
  have htrace : WordTrace (prefixWord ++ tailWord_6065881) baseStart_6065881 baseEnd_6065881 := by
    simpa [prefixWord, tailWord_6065881, baseEnd_6065881] using wordTrace_append hprefix tailTrace_6065881
  have hstable : (prefixWord ++ tailWord_6065881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065881).length < 2 ^ (prefixWord ++ tailWord_6065881).sum := by decide
  have hdescent : baseEnd_6065881 < baseStart_6065881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065901 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 6]
def baseStart_6065901 : Nat := 118140960795 + 6065901 * 2 ^ 59
def prefixEnd_6065901 : Nat := 4983230072969 + 3 ^ 40 * 6065901 * 2
def baseEnd_6065901 : Nat := 346080312843175207571215

theorem tailTrace_6065901 : CollatzResearch.WordTrace tailWord_6065901 prefixEnd_6065901 346080312843175207571215 := by
  unfold tailWord_6065901
  simp only [CollatzResearch.WordTrace]
  refine ⟨221241585197284125257853557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147494390131522750171902371 221241585197284125257853557)
  ·
    refine ⟨20741398612245386742923771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221241585197284125257853557 20741398612245386742923771)
    ·
      refine ⟨31112097918368080114385657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20741398612245386742923771 31112097918368080114385657)
      ·
        refine ⟨23334073438776060085789243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31112097918368080114385657 23334073438776060085789243)
        ·
          refine ⟨35001110158164090128683865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23334073438776060085789243 35001110158164090128683865)
          ·
            refine ⟨26250832618623067596512899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35001110158164090128683865 26250832618623067596512899)
            ·
              refine ⟨39376248927934601394769349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26250832618623067596512899 39376248927934601394769349)
              ·
                refine ⟨7383046673987737761519253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39376248927934601394769349 7383046673987737761519253)
                ·
                  refine ⟨346080312843175207571215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7383046673987737761519253 346080312843175207571215)
                  ·
                    rfl

theorem cell23_6065901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_6065901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065901 prefixEnd_6065901 := by exact prefixLift 6065901
  have htrace : WordTrace (prefixWord ++ tailWord_6065901) baseStart_6065901 baseEnd_6065901 := by
    simpa [prefixWord, tailWord_6065901, baseEnd_6065901] using wordTrace_append hprefix tailTrace_6065901
  have hstable : (prefixWord ++ tailWord_6065901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065901).length < 2 ^ (prefixWord ++ tailWord_6065901).sum := by decide
  have hdescent : baseEnd_6065901 < baseStart_6065901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065905 : List Nat := [1, 2, 2, 2, 2, 3, 4, 2, 1, 4]
def baseStart_6065905 : Nat := 118140960795 + 6065905 * 2 ^ 59
def prefixEnd_6065905 : Nat := 4983230072969 + 3 ^ 40 * 6065905 * 2
def baseEnd_6065905 : Nat := 1038241623170398284163639

theorem tailTrace_6065905 : CollatzResearch.WordTrace tailWord_6065905 prefixEnd_6065905 1038241623170398284163639 := by
  unfold tailWord_6065905
  simp only [CollatzResearch.WordTrace]
  refine ⟨221241731089269633940999169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147494487392846422627332779 221241731089269633940999169)
  ·
    refine ⟨165931298316952225455749377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221241731089269633940999169 165931298316952225455749377)
    ·
      refine ⟨124448473737714169091812033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165931298316952225455749377 124448473737714169091812033)
      ·
        refine ⟨93336355303285626818859025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124448473737714169091812033 93336355303285626818859025)
        ·
          refine ⟨70002266477464220114144269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93336355303285626818859025 70002266477464220114144269)
          ·
            refine ⟨26250849929049082542804101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70002266477464220114144269 26250849929049082542804101)
            ·
              refine ⟨4922034361696702976775769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26250849929049082542804101 4922034361696702976775769)
              ·
                refine ⟨3691525771272527232581827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4922034361696702976775769 3691525771272527232581827)
                ·
                  refine ⟨5537288656908790848872741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3691525771272527232581827 5537288656908790848872741)
                  ·
                    refine ⟨1038241623170398284163639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5537288656908790848872741 1038241623170398284163639)
                    ·
                      rfl

theorem cell23_6065905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_6065905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065905 prefixEnd_6065905 := by exact prefixLift 6065905
  have htrace : WordTrace (prefixWord ++ tailWord_6065905) baseStart_6065905 baseEnd_6065905 := by
    simpa [prefixWord, tailWord_6065905, baseEnd_6065905] using wordTrace_append hprefix tailTrace_6065905
  have hstable : (prefixWord ++ tailWord_6065905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065905).length < 2 ^ (prefixWord ++ tailWord_6065905).sum := by decide
  have hdescent : baseEnd_6065905 < baseStart_6065905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065926 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6065926 : Nat := 118140960795 + 6065926 * 2 ^ 59
def prefixEnd_6065926 : Nat := 4983230072969 + 3 ^ 40 * 6065926 * 2
def baseEnd_6065926 : Nat := 1038245217534979756776107

theorem tailTrace_6065926 : CollatzResearch.WordTrace tailWord_6065926 prefixEnd_6065926 1038245217534979756776107 := by
  unfold tailWord_6065926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6913828031943548578984801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147494998014795703018342421 6913828031943548578984801)
  ·
    refine ⟨5185371023957661434238601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6913828031943548578984801 5185371023957661434238601)
    ·
      refine ⟨3889028267968246075678951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5185371023957661434238601 3889028267968246075678951)
      ·
        refine ⟨5833542401952369113518427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889028267968246075678951 5833542401952369113518427)
        ·
          refine ⟨8750313602928553670277641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5833542401952369113518427 8750313602928553670277641)
          ·
            refine ⟨6562735202196415252708231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8750313602928553670277641 6562735202196415252708231)
            ·
              refine ⟨9844102803294622879062347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562735202196415252708231 9844102803294622879062347)
              ·
                refine ⟨14766154204941934318593521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9844102803294622879062347 14766154204941934318593521)
                ·
                  refine ⟨11074615653706450738945141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14766154204941934318593521 11074615653706450738945141)
                  ·
                    refine ⟨1038245217534979756776107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11074615653706450738945141 1038245217534979756776107)
                    ·
                      rfl

theorem cell23_6065926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6065926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065926 prefixEnd_6065926 := by exact prefixLift 6065926
  have htrace : WordTrace (prefixWord ++ tailWord_6065926) baseStart_6065926 baseEnd_6065926 := by
    simpa [prefixWord, tailWord_6065926, baseEnd_6065926] using wordTrace_append hprefix tailTrace_6065926
  have hstable : (prefixWord ++ tailWord_6065926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065926).length < 2 ^ (prefixWord ++ tailWord_6065926).sum := by decide
  have hdescent : baseEnd_6065926 < baseStart_6065926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065928 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_6065928 : Nat := 118140960795 + 6065928 * 2 ^ 59
def prefixEnd_6065928 : Nat := 4983230072969 + 3 ^ 40 * 6065928 * 2
def baseEnd_6065928 : Nat := 3114736679566248262503311

theorem tailTrace_6065928 : CollatzResearch.WordTrace tailWord_6065928 prefixEnd_6065928 3114736679566248262503311 := by
  unfold tailWord_6065928
  simp only [CollatzResearch.WordTrace]
  refine ⟨110621284984093154434543219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147495046645457539246057625 110621284984093154434543219)
  ·
    refine ⟨165931927476139731651814829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110621284984093154434543219 165931927476139731651814829)
    ·
      refine ⟨62224472803552399369430561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165931927476139731651814829 62224472803552399369430561)
      ·
        refine ⟨46668354602664299527072921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62224472803552399369430561 46668354602664299527072921)
        ·
          refine ⟨35001265951998224645304691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46668354602664299527072921 35001265951998224645304691)
          ·
            refine ⟨52501898927997336967957037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35001265951998224645304691 52501898927997336967957037)
            ·
              refine ⟨19688212097999001362983889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52501898927997336967957037 19688212097999001362983889)
              ·
                refine ⟨14766159073499251022237917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19688212097999001362983889 14766159073499251022237917)
                ·
                  refine ⟨5537309652562219133339219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14766159073499251022237917 5537309652562219133339219)
                  ·
                    refine ⟨8305964478843328700008829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5537309652562219133339219 8305964478843328700008829)
                    ·
                      refine ⟨3114736679566248262503311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8305964478843328700008829 3114736679566248262503311)
                      ·
                        rfl

theorem cell23_6065928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_6065928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065928 prefixEnd_6065928 := by exact prefixLift 6065928
  have htrace : WordTrace (prefixWord ++ tailWord_6065928) baseStart_6065928 baseEnd_6065928 := by
    simpa [prefixWord, tailWord_6065928, baseEnd_6065928] using wordTrace_append hprefix tailTrace_6065928
  have hstable : (prefixWord ++ tailWord_6065928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065928).length < 2 ^ (prefixWord ++ tailWord_6065928).sum := by decide
  have hdescent : baseEnd_6065928 < baseStart_6065928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065978 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_6065978 : Nat := 118140960795 + 6065978 * 2 ^ 59
def prefixEnd_6065978 : Nat := 4983230072969 + 3 ^ 40 * 6065978 * 2
def baseEnd_6065978 : Nat := 1038254117866324355626027

theorem tailTrace_6065978 : CollatzResearch.WordTrace tailWord_6065978 prefixEnd_6065978 1038254117866324355626027 := by
  unfold tailWord_6065978
  simp only [CollatzResearch.WordTrace]
  refine ⟨55311098404501291852101647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147496262412003444938937725 55311098404501291852101647)
  ·
    refine ⟨82966647606751937778152471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55311098404501291852101647 82966647606751937778152471)
    ·
      refine ⟨124449971410127906667228707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82966647606751937778152471 124449971410127906667228707)
      ·
        refine ⟨186674957115191860000843061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124449971410127906667228707 186674957115191860000843061)
        ·
          refine ⟨17500777229549236875079037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186674957115191860000843061 17500777229549236875079037)
          ·
            refine ⟨6562791461080963828154639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17500777229549236875079037 6562791461080963828154639)
            ·
              refine ⟨9844187191621445742231959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562791461080963828154639 9844187191621445742231959)
              ·
                refine ⟨14766280787432168613347939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9844187191621445742231959 14766280787432168613347939)
                ·
                  refine ⟨22149421181148252920021909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14766280787432168613347939 22149421181148252920021909)
                  ·
                    refine ⟨1038254117866324355626027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22149421181148252920021909 1038254117866324355626027)
                    ·
                      rfl

theorem cell23_6065978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_6065978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065978 prefixEnd_6065978 := by exact prefixLift 6065978
  have htrace : WordTrace (prefixWord ++ tailWord_6065978) baseStart_6065978 baseEnd_6065978 := by
    simpa [prefixWord, tailWord_6065978, baseEnd_6065978] using wordTrace_append hprefix tailTrace_6065978
  have hstable : (prefixWord ++ tailWord_6065978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065978).length < 2 ^ (prefixWord ++ tailWord_6065978).sum := by decide
  have hdescent : baseEnd_6065978 < baseStart_6065978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6065991 : List Nat := [1, 1, 4, 1, 2, 1, 6, 7]
def baseStart_6065991 : Nat := 118140960795 + 6065991 * 2 ^ 59
def prefixEnd_6065991 : Nat := 4983230072969 + 3 ^ 40 * 6065991 * 2
def baseEnd_6065991 : Nat := 115361815883240056148723

theorem tailTrace_6065991 : CollatzResearch.WordTrace tailWord_6065991 prefixEnd_6065991 115361815883240056148723 := by
  unfold tailWord_6065991
  simp only [CollatzResearch.WordTrace]
  refine ⟨221244867766958070628629827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147496578511305380419086551 221244867766958070628629827)
  ·
    refine ⟨331867301650437105942944741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221244867766958070628629827 331867301650437105942944741)
    ·
      refine ⟨62225119059456957364302139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331867301650437105942944741 62225119059456957364302139)
      ·
        refine ⟨93337678589185436046453209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62225119059456957364302139 93337678589185436046453209)
        ·
          refine ⟨70003258941889077034839907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93337678589185436046453209 70003258941889077034839907)
          ·
            refine ⟨105004888412833615552259861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70003258941889077034839907 105004888412833615552259861)
            ·
              refine ⟨4922104144351575729012181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105004888412833615552259861 4922104144351575729012181)
              ·
                refine ⟨115361815883240056148723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4922104144351575729012181 115361815883240056148723)
                ·
                  rfl

theorem cell23_6065991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 7].length) (baseStart_6065991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6065991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6065991 prefixEnd_6065991 := by exact prefixLift 6065991
  have htrace : WordTrace (prefixWord ++ tailWord_6065991) baseStart_6065991 baseEnd_6065991 := by
    simpa [prefixWord, tailWord_6065991, baseEnd_6065991] using wordTrace_append hprefix tailTrace_6065991
  have hstable : (prefixWord ++ tailWord_6065991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6065991).length < 2 ^ (prefixWord ++ tailWord_6065991).sum := by decide
  have hdescent : baseEnd_6065991 < baseStart_6065991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6065991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066019 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 3, 2, 2]
def baseStart_6066019 : Nat := 118140960795 + 6066019 * 2 ^ 59
def prefixEnd_6066019 : Nat := 4983230072969 + 3 ^ 40 * 6066019 * 2
def baseEnd_6066019 : Nat := 3114783406305807406465393

theorem tailTrace_6066019 : CollatzResearch.WordTrace tailWord_6066019 prefixEnd_6066019 3114783406305807406465393 := by
  unfold tailWord_6066019
  simp only [CollatzResearch.WordTrace]
  refine ⟨221245889010856631410649111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147497259340571087607099407 221245889010856631410649111)
  ·
    refine ⟨331868833516284947115973667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221245889010856631410649111 331868833516284947115973667)
    ·
      refine ⟨497803250274427420673960501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331868833516284947115973667 497803250274427420673960501)
      ·
        refine ⟨46669054713227570688183797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 497803250274427420673960501 46669054713227570688183797)
        ·
          refine ⟨4375223879365084752017231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46669054713227570688183797 4375223879365084752017231)
          ·
            refine ⟨6562835819047627128025847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375223879365084752017231 6562835819047627128025847)
            ·
              refine ⟨9844253728571440692038771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562835819047627128025847 9844253728571440692038771)
              ·
                refine ⟨14766380592857161038058157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9844253728571440692038771 14766380592857161038058157)
                ·
                  refine ⟨5537392722321435389271809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14766380592857161038058157 5537392722321435389271809)
                  ·
                    refine ⟨4153044541741076541953857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5537392722321435389271809 4153044541741076541953857)
                    ·
                      refine ⟨3114783406305807406465393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153044541741076541953857 3114783406305807406465393)
                      ·
                        rfl

theorem cell23_6066019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_6066019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066019 prefixEnd_6066019 := by exact prefixLift 6066019
  have htrace : WordTrace (prefixWord ++ tailWord_6066019) baseStart_6066019 baseEnd_6066019 := by
    simpa [prefixWord, tailWord_6066019, baseEnd_6066019] using wordTrace_append hprefix tailTrace_6066019
  have hstable : (prefixWord ++ tailWord_6066019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066019).length < 2 ^ (prefixWord ++ tailWord_6066019).sum := by decide
  have hdescent : baseEnd_6066019 < baseStart_6066019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066111 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 1, 7]
def baseStart_6066111 : Nat := 118140960795 + 6066111 * 2 ^ 59
def prefixEnd_6066111 : Nat := 4983230072969 + 3 ^ 40 * 6066111 * 2
def baseEnd_6066111 : Nat := 1038276882175340348838323

theorem tailTrace_6066111 : CollatzResearch.WordTrace tailWord_6066111 prefixEnd_6066111 1038276882175340348838323 := by
  unfold tailWord_6066111
  simp only [CollatzResearch.WordTrace]
  refine ⟨221249244526523331122998187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147499496351015554081998791 221249244526523331122998187)
  ·
    refine ⟨331873866789784996684497281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221249244526523331122998187 331873866789784996684497281)
    ·
      refine ⟨248905400092338747513372961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331873866789784996684497281 248905400092338747513372961)
      ·
        refine ⟨186679050069254060635029721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248905400092338747513372961 186679050069254060635029721)
        ·
          refine ⟨140009287551940545476272291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186679050069254060635029721 140009287551940545476272291)
          ·
            refine ⟨210013931327910818214408437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140009287551940545476272291 210013931327910818214408437)
            ·
              refine ⟨19688806061991639207600791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210013931327910818214408437 19688806061991639207600791)
              ·
                refine ⟨29533209092987458811401187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19688806061991639207600791 29533209092987458811401187)
                ·
                  refine ⟨44299813639481188217101781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29533209092987458811401187 44299813639481188217101781)
                  ·
                    refine ⟨1038276882175340348838323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44299813639481188217101781 1038276882175340348838323)
                    ·
                      rfl

theorem cell23_6066111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_6066111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066111 prefixEnd_6066111 := by exact prefixLift 6066111
  have htrace : WordTrace (prefixWord ++ tailWord_6066111) baseStart_6066111 baseEnd_6066111 := by
    simpa [prefixWord, tailWord_6066111, baseEnd_6066111] using wordTrace_append hprefix tailTrace_6066111
  have hstable : (prefixWord ++ tailWord_6066111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066111).length < 2 ^ (prefixWord ++ tailWord_6066111).sum := by decide
  have hdescent : baseEnd_6066111 < baseStart_6066111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066168 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_6066168 : Nat := 118140960795 + 6066168 * 2 ^ 59
def prefixEnd_6066168 : Nat := 4983230072969 + 3 ^ 40 * 6066168 * 2
def baseEnd_6066168 : Nat := 3114859914923327323502207

theorem tailTrace_6066168 : CollatzResearch.WordTrace tailWord_6066168 prefixEnd_6066168 3114859914923327323502207 := by
  unfold tailWord_6066168
  simp only [CollatzResearch.WordTrace]
  refine ⟨110625661743658414928911579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147500882324877886571882105 110625661743658414928911579)
  ·
    refine ⟨165938492615487622393367369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110625661743658414928911579 165938492615487622393367369)
    ·
      refine ⟨124453869461615716795025527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165938492615487622393367369 124453869461615716795025527)
      ·
        refine ⟨186680804192423575192538291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124453869461615716795025527 186680804192423575192538291)
        ·
          refine ⟨280021206288635362788807437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186680804192423575192538291 280021206288635362788807437)
          ·
            refine ⟨105007952358238261045802789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280021206288635362788807437 105007952358238261045802789)
            ·
              refine ⟨19688991067169673946088023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105007952358238261045802789 19688991067169673946088023)
              ·
                refine ⟨29533486600754510919132035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19688991067169673946088023 29533486600754510919132035)
                ·
                  refine ⟨44300229901131766378698053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29533486600754510919132035 44300229901131766378698053)
                  ·
                    refine ⟨8306293106462206196005885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44300229901131766378698053 8306293106462206196005885)
                    ·
                      refine ⟨3114859914923327323502207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8306293106462206196005885 3114859914923327323502207)
                      ·
                        rfl

theorem cell23_6066168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_6066168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066168 prefixEnd_6066168 := by exact prefixLift 6066168
  have htrace : WordTrace (prefixWord ++ tailWord_6066168) baseStart_6066168 baseEnd_6066168 := by
    simpa [prefixWord, tailWord_6066168, baseEnd_6066168] using wordTrace_append hprefix tailTrace_6066168
  have hstable : (prefixWord ++ tailWord_6066168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066168).length < 2 ^ (prefixWord ++ tailWord_6066168).sum := by decide
  have hdescent : baseEnd_6066168 < baseStart_6066168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066171 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 8]
def baseStart_6066171 : Nat := 118140960795 + 6066171 * 2 ^ 59
def prefixEnd_6066171 : Nat := 4983230072969 + 3 ^ 40 * 6066171 * 2
def baseEnd_6066171 : Nat := 346095717262810090196077

theorem tailTrace_6066171 : CollatzResearch.WordTrace tailWord_6066171 prefixEnd_6066171 346095717262810090196077 := by
  unfold tailWord_6066171
  simp only [CollatzResearch.WordTrace]
  refine ⟨221251432906305961370182367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147500955270870640913454911 221251432906305961370182367)
  ·
    refine ⟨331877149359458942055273551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221251432906305961370182367 331877149359458942055273551)
    ·
      refine ⟨497815724039188413082910327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331877149359458942055273551 497815724039188413082910327)
      ·
        refine ⟨746723586058782619624365491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497815724039188413082910327 746723586058782619624365491)
        ·
          refine ⟨1120085379088173929436548237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746723586058782619624365491 1120085379088173929436548237)
          ·
            refine ⟨420032017158065223538705589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1120085379088173929436548237 420032017158065223538705589)
            ·
              refine ⟨39378001608568614706753649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 420032017158065223538705589 39378001608568614706753649)
              ·
                refine ⟨29533501206426461030065237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39378001608568614706753649 29533501206426461030065237)
                ·
                  refine ⟨346095717262810090196077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29533501206426461030065237 346095717262810090196077)
                  ·
                    rfl

theorem cell23_6066171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 8].length) (baseStart_6066171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066171 prefixEnd_6066171 := by exact prefixLift 6066171
  have htrace : WordTrace (prefixWord ++ tailWord_6066171) baseStart_6066171 baseEnd_6066171 := by
    simpa [prefixWord, tailWord_6066171, baseEnd_6066171] using wordTrace_append hprefix tailTrace_6066171
  have hstable : (prefixWord ++ tailWord_6066171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066171).length < 2 ^ (prefixWord ++ tailWord_6066171).sum := by decide
  have hdescent : baseEnd_6066171 < baseStart_6066171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066188 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 6]
def baseStart_6066188 : Nat := 118140960795 + 6066188 * 2 ^ 59
def prefixEnd_6066188 : Nat := 4983230072969 + 3 ^ 40 * 6066188 * 2
def baseEnd_6066188 : Nat := 346096687170713027250235

theorem tailTrace_6066188 : CollatzResearch.WordTrace tailWord_6066188 prefixEnd_6066188 346096687170713027250235 := by
  unfold tailWord_6066188
  simp only [CollatzResearch.WordTrace]
  refine ⟨110626026473622186636775609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147501368631496248849034145 110626026473622186636775609)
  ·
    refine ⟨82969519855216639977581707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110626026473622186636775609 82969519855216639977581707)
    ·
      refine ⟨124454279782824959966372561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82969519855216639977581707 124454279782824959966372561)
      ·
        refine ⟨93340709837118719974779421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124454279782824959966372561 93340709837118719974779421)
        ·
          refine ⟨35002766188919519990542283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93340709837118719974779421 35002766188919519990542283)
          ·
            refine ⟨52504149283379279985813425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35002766188919519990542283 52504149283379279985813425)
            ·
              refine ⟨39378111962534459989360069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52504149283379279985813425 39378111962534459989360069)
              ·
                refine ⟨7383395992975211248005013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39378111962534459989360069 7383395992975211248005013)
                ·
                  refine ⟨346096687170713027250235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7383395992975211248005013 346096687170713027250235)
                  ·
                    rfl

theorem cell23_6066188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_6066188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066188 prefixEnd_6066188 := by exact prefixLift 6066188
  have htrace : WordTrace (prefixWord ++ tailWord_6066188) baseStart_6066188 baseEnd_6066188 := by
    simpa [prefixWord, tailWord_6066188, baseEnd_6066188] using wordTrace_append hprefix tailTrace_6066188
  have hstable : (prefixWord ++ tailWord_6066188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066188).length < 2 ^ (prefixWord ++ tailWord_6066188).sum := by decide
  have hdescent : baseEnd_6066188 < baseStart_6066188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066189 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6066189 : Nat := 118140960795 + 6066189 * 2 ^ 59
def prefixEnd_6066189 : Nat := 4983230072969 + 3 ^ 40 * 6066189 * 2
def baseEnd_6066189 : Nat := 3114870698017071741339611

theorem tailTrace_6066189 : CollatzResearch.WordTrace tailWord_6066189 prefixEnd_6066189 3114870698017071741339611 := by
  unfold tailWord_6066189
  simp only [CollatzResearch.WordTrace]
  refine ⟨221252089420240750444337621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147501392946827166962891747 221252089420240750444337621)
  ·
    refine ⟨5185595845786892588539163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 221252089420240750444337621 5185595845786892588539163)
    ·
      refine ⟨7778393768680338882808745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5185595845786892588539163 7778393768680338882808745)
      ·
        refine ⟨5833795326510254162106559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7778393768680338882808745 5833795326510254162106559)
        ·
          refine ⟨8750692989765381243159839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5833795326510254162106559 8750692989765381243159839)
          ·
            refine ⟨13126039484648071864739759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8750692989765381243159839 13126039484648071864739759)
            ·
              refine ⟨19689059226972107797109639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13126039484648071864739759 19689059226972107797109639)
              ·
                refine ⟨29533588840458161695664459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19689059226972107797109639 29533588840458161695664459)
                ·
                  refine ⟨44300383260687242543496689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29533588840458161695664459 44300383260687242543496689)
                  ·
                    refine ⟨33225287445515431907622517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44300383260687242543496689 33225287445515431907622517)
                    ·
                      refine ⟨3114870698017071741339611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33225287445515431907622517 3114870698017071741339611)
                      ·
                        rfl

theorem cell23_6066189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6066189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066189 prefixEnd_6066189 := by exact prefixLift 6066189
  have htrace : WordTrace (prefixWord ++ tailWord_6066189) baseStart_6066189 baseEnd_6066189 := by
    simpa [prefixWord, tailWord_6066189, baseEnd_6066189] using wordTrace_append hprefix tailTrace_6066189
  have hstable : (prefixWord ++ tailWord_6066189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066189).length < 2 ^ (prefixWord ++ tailWord_6066189).sum := by decide
  have hdescent : baseEnd_6066189 < baseStart_6066189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066201 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 2, 9]
def baseStart_6066201 : Nat := 118140960795 + 6066201 * 2 ^ 59
def prefixEnd_6066201 : Nat := 4983230072969 + 3 ^ 40 * 6066201 * 2
def baseEnd_6066201 : Nat := 1038292286594975231463185

theorem tailTrace_6066201 : CollatzResearch.WordTrace tailWord_6066201 prefixEnd_6066201 1038292286594975231463185 := by
  unfold tailWord_6066201
  simp only [CollatzResearch.WordTrace]
  refine ⟨221252527096197276493774457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147501684730798184329182971 221252527096197276493774457)
  ·
    refine ⟨165939395322147957370330843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221252527096197276493774457 165939395322147957370330843)
    ·
      refine ⟨248909092983221936055496265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165939395322147957370330843 248909092983221936055496265)
      ·
        refine ⟨186681819737416452041622199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248909092983221936055496265 186681819737416452041622199)
        ·
          refine ⟨280022729606124678062433299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186681819737416452041622199 280022729606124678062433299)
          ·
            refine ⟨420034094409187017093649949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280022729606124678062433299 420034094409187017093649949)
            ·
              refine ⟨157512785403445131410118731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420034094409187017093649949 157512785403445131410118731)
              ·
                refine ⟨236269178105167697115178097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157512785403445131410118731 236269178105167697115178097)
                ·
                  refine ⟨177201883578875772836383573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236269178105167697115178097 177201883578875772836383573)
                  ·
                    refine ⟨1038292286594975231463185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 177201883578875772836383573 1038292286594975231463185)
                    ·
                      rfl

theorem cell23_6066201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_6066201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066201 prefixEnd_6066201 := by exact prefixLift 6066201
  have htrace : WordTrace (prefixWord ++ tailWord_6066201) baseStart_6066201 baseEnd_6066201 := by
    simpa [prefixWord, tailWord_6066201, baseEnd_6066201] using wordTrace_append hprefix tailTrace_6066201
  have hstable : (prefixWord ++ tailWord_6066201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066201).length < 2 ^ (prefixWord ++ tailWord_6066201).sum := by decide
  have hdescent : baseEnd_6066201 < baseStart_6066201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066205 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 6]
def baseStart_6066205 : Nat := 118140960795 + 6066205 * 2 ^ 59
def prefixEnd_6066205 : Nat := 4983230072969 + 3 ^ 40 * 6066205 * 2
def baseEnd_6066205 : Nat := 346097657078615964304393

theorem tailTrace_6066205 : CollatzResearch.WordTrace tailWord_6066205 prefixEnd_6066205 346097657078615964304393 := by
  unfold tailWord_6066205
  simp only [CollatzResearch.WordTrace]
  refine ⟨221252672988182785176920069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147501781992121856784613379 221252672988182785176920069)
  ·
    refine ⟨41484876185284272220672513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221252672988182785176920069 41484876185284272220672513)
    ·
      refine ⟨31113657138963204165504385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41484876185284272220672513 31113657138963204165504385)
      ·
        refine ⟨23335242854222403124128289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31113657138963204165504385 23335242854222403124128289)
        ·
          refine ⟨17501432140666802343096217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23335242854222403124128289 17501432140666802343096217)
          ·
            refine ⟨13126074105500101757322163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17501432140666802343096217 13126074105500101757322163)
            ·
              refine ⟨19689111158250152635983245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13126074105500101757322163 19689111158250152635983245)
              ·
                refine ⟨7383416684343807238493717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19689111158250152635983245 7383416684343807238493717)
                ·
                  refine ⟨346097657078615964304393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7383416684343807238493717 346097657078615964304393)
                  ·
                    rfl

theorem cell23_6066205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_6066205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066205 prefixEnd_6066205 := by exact prefixLift 6066205
  have htrace : WordTrace (prefixWord ++ tailWord_6066205) baseStart_6066205 baseEnd_6066205 := by
    simpa [prefixWord, tailWord_6066205, baseEnd_6066205] using wordTrace_append hprefix tailTrace_6066205
  have hstable : (prefixWord ++ tailWord_6066205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066205).length < 2 ^ (prefixWord ++ tailWord_6066205).sum := by decide
  have hdescent : baseEnd_6066205 < baseStart_6066205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066265 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 2, 4]
def baseStart_6066265 : Nat := 118140960795 + 6066265 * 2 ^ 59
def prefixEnd_6066265 : Nat := 4983230072969 + 3 ^ 40 * 6066265 * 2
def baseEnd_6066265 : Nat := 1038303240848937814663087

theorem tailTrace_6066265 : CollatzResearch.WordTrace tailWord_6066265 prefixEnd_6066265 1038303240848937814663087 := by
  unfold tailWord_6066265
  simp only [CollatzResearch.WordTrace]
  refine ⟨221254861367965415424104249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147503240911976943616069499 221254861367965415424104249)
  ·
    refine ⟨165941146025974061568078187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221254861367965415424104249 165941146025974061568078187)
    ·
      refine ⟨248911719038961092352117281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165941146025974061568078187 248911719038961092352117281)
      ·
        refine ⟨186683789279220819264087961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248911719038961092352117281 186683789279220819264087961)
        ·
          refine ⟨140012841959415614448065971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186683789279220819264087961 140012841959415614448065971)
          ·
            refine ⟨210019262939123421672098957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140012841959415614448065971 210019262939123421672098957)
            ·
              refine ⟨78757223602171283127037109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210019262939123421672098957 78757223602171283127037109)
              ·
                refine ⟨7383489712703557793159729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78757223602171283127037109 7383489712703557793159729)
                ·
                  refine ⟨5537617284527668344869797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7383489712703557793159729 5537617284527668344869797)
                  ·
                    refine ⟨1038303240848937814663087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5537617284527668344869797 1038303240848937814663087)
                    ·
                      rfl

theorem cell23_6066265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 4].length) (baseStart_6066265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066265 prefixEnd_6066265 := by exact prefixLift 6066265
  have htrace : WordTrace (prefixWord ++ tailWord_6066265) baseStart_6066265 baseEnd_6066265 := by
    simpa [prefixWord, tailWord_6066265, baseEnd_6066265] using wordTrace_append hprefix tailTrace_6066265
  have hstable : (prefixWord ++ tailWord_6066265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066265).length < 2 ^ (prefixWord ++ tailWord_6066265).sum := by decide
  have hdescent : baseEnd_6066265 < baseStart_6066265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066272 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 5, 2, 2]
def baseStart_6066272 : Nat := 118140960795 + 6066272 * 2 ^ 59
def prefixEnd_6066272 : Nat := 4983230072969 + 3 ^ 40 * 6066272 * 2
def baseEnd_6066272 : Nat := 3114913316911394916601729

theorem tailTrace_6066272 : CollatzResearch.WordTrace tailWord_6066272 prefixEnd_6066272 3114913316911394916601729 := by
  unfold tailWord_6066272
  simp only [CollatzResearch.WordTrace]
  refine ⟨110627558339470027809804535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147503411119293370413072713 110627558339470027809804535)
  ·
    refine ⟨165941337509205041714706803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110627558339470027809804535 165941337509205041714706803)
    ·
      refine ⟨248912006263807562572060205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165941337509205041714706803 248912006263807562572060205)
      ·
        refine ⟨93342002348927835964522577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248912006263807562572060205 93342002348927835964522577)
        ·
          refine ⟨70006501761695876973391933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93342002348927835964522577 70006501761695876973391933)
          ·
            refine ⟨26252438160635953865021975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70006501761695876973391933 26252438160635953865021975)
            ·
              refine ⟨39378657240953930797532963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26252438160635953865021975 39378657240953930797532963)
              ·
                refine ⟨59067985861430896196299445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39378657240953930797532963 59067985861430896196299445)
                ·
                  refine ⟨5537623674509146518403073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59067985861430896196299445 5537623674509146518403073)
                  ·
                    refine ⟨4153217755881859888802305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5537623674509146518403073 4153217755881859888802305)
                    ·
                      refine ⟨3114913316911394916601729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153217755881859888802305 3114913316911394916601729)
                      ·
                        rfl

theorem cell23_6066272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_6066272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066272 prefixEnd_6066272 := by exact prefixLift 6066272
  have htrace : WordTrace (prefixWord ++ tailWord_6066272) baseStart_6066272 baseEnd_6066272 := by
    simpa [prefixWord, tailWord_6066272, baseEnd_6066272] using wordTrace_append hprefix tailTrace_6066272
  have hstable : (prefixWord ++ tailWord_6066272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066272).length < 2 ^ (prefixWord ++ tailWord_6066272).sum := by decide
  have hdescent : baseEnd_6066272 < baseStart_6066272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066275 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 3]
def baseStart_6066275 : Nat := 118140960795 + 6066275 * 2 ^ 59
def prefixEnd_6066275 : Nat := 4983230072969 + 3 ^ 40 * 6066275 * 2
def baseEnd_6066275 : Nat := 3114914857353358404864215

theorem tailTrace_6066275 : CollatzResearch.WordTrace tailWord_6066275 prefixEnd_6066275 3114914857353358404864215 := by
  unfold tailWord_6066275
  simp only [CollatzResearch.WordTrace]
  refine ⟨221255226097929187131968279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147503484065286124754645519 221255226097929187131968279)
  ·
    refine ⟨331882839146893780697952419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221255226097929187131968279 331882839146893780697952419)
    ·
      refine ⟨497824258720340671046928629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331882839146893780697952419 497824258720340671046928629)
      ·
        refine ⟨46671024255031937910649559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 497824258720340671046928629 46671024255031937910649559)
        ·
          refine ⟨70006536382547906865974339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46671024255031937910649559 70006536382547906865974339)
          ·
            refine ⟨105009804573821860298961509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70006536382547906865974339 105009804573821860298961509)
            ·
              refine ⟨19689338357591598806055283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105009804573821860298961509 19689338357591598806055283)
              ·
                refine ⟨29534007536387398209082925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19689338357591598806055283 29534007536387398209082925)
                ·
                  refine ⟨11075252826145274328406097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29534007536387398209082925 11075252826145274328406097)
                  ·
                    refine ⟨8306439619608955746304573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11075252826145274328406097 8306439619608955746304573)
                    ·
                      refine ⟨3114914857353358404864215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8306439619608955746304573 3114914857353358404864215)
                      ·
                        rfl

theorem cell23_6066275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_6066275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066275 prefixEnd_6066275 := by exact prefixLift 6066275
  have htrace : WordTrace (prefixWord ++ tailWord_6066275) baseStart_6066275 baseEnd_6066275 := by
    simpa [prefixWord, tailWord_6066275, baseEnd_6066275] using wordTrace_append hprefix tailTrace_6066275
  have hstable : (prefixWord ++ tailWord_6066275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066275).length < 2 ^ (prefixWord ++ tailWord_6066275).sum := by decide
  have hdescent : baseEnd_6066275 < baseStart_6066275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066285 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6066285 : Nat := 118140960795 + 6066285 * 2 ^ 59
def prefixEnd_6066285 : Nat := 4983230072969 + 3 ^ 40 * 6066285 * 2
def baseEnd_6066285 : Nat := 3114919992159903365739169

theorem tailTrace_6066285 : CollatzResearch.WordTrace tailWord_6066285 prefixEnd_6066285 3114919992159903365739169 := by
  unfold tailWord_6066285
  simp only [CollatzResearch.WordTrace]
  refine ⟨221255590827892958839832309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147503727218595305893221539 221255590827892958839832309)
  ·
    refine ⟨20742711640114964891234279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221255590827892958839832309 20742711640114964891234279)
    ·
      refine ⟨31114067460172447336851419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20742711640114964891234279 31114067460172447336851419)
      ·
        refine ⟨46671101190258671005277129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31114067460172447336851419 46671101190258671005277129)
        ·
          refine ⟨35003325892694003253957847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46671101190258671005277129 35003325892694003253957847)
          ·
            refine ⟨52504988839041004880936771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35003325892694003253957847 52504988839041004880936771)
            ·
              refine ⟨78757483258561507321405157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52504988839041004880936771 78757483258561507321405157)
              ·
                refine ⟨14767028110980282622763467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78757483258561507321405157 14767028110980282622763467)
                ·
                  refine ⟨22150542166470423934145201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14767028110980282622763467 22150542166470423934145201)
                  ·
                    refine ⟨16612906624852817950608901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22150542166470423934145201 16612906624852817950608901)
                    ·
                      refine ⟨3114919992159903365739169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16612906624852817950608901 3114919992159903365739169)
                      ·
                        rfl

theorem cell23_6066285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6066285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066285 prefixEnd_6066285 := by exact prefixLift 6066285
  have htrace : WordTrace (prefixWord ++ tailWord_6066285) baseStart_6066285 baseEnd_6066285 := by
    simpa [prefixWord, tailWord_6066285, baseEnd_6066285] using wordTrace_append hprefix tailTrace_6066285
  have hstable : (prefixWord ++ tailWord_6066285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066285).length < 2 ^ (prefixWord ++ tailWord_6066285).sum := by decide
  have hdescent : baseEnd_6066285 < baseStart_6066285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066335 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6066335 : Nat := 118140960795 + 6066335 * 2 ^ 59
def prefixEnd_6066335 : Nat := 4983230072969 + 3 ^ 40 * 6066335 * 2
def baseEnd_6066335 : Nat := 3114945666192628170113939

theorem tailTrace_6066335 : CollatzResearch.WordTrace tailWord_6066335 prefixEnd_6066335 3114945666192628170113939 := by
  unfold tailWord_6066335
  simp only [CollatzResearch.WordTrace]
  refine ⟨221257414477711817379152459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147504942985141211586101639 221257414477711817379152459)
  ·
    refine ⟨331886121716567726068728689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221257414477711817379152459 331886121716567726068728689)
    ·
      refine ⟨248914591287425794551546517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331886121716567726068728689 248914591287425794551546517)
      ·
        refine ⟨11667871466598084119603743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 248914591287425794551546517 11667871466598084119603743)
        ·
          refine ⟨17501807199897126179405615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11667871466598084119603743 17501807199897126179405615)
          ·
            refine ⟨26252710799845689269108423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17501807199897126179405615 26252710799845689269108423)
            ·
              refine ⟨39379066199768533903662635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26252710799845689269108423 39379066199768533903662635)
              ·
                refine ⟨59068599299652800855493953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39379066199768533903662635 59068599299652800855493953)
                ·
                  refine ⟨44301449474739600641620465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59068599299652800855493953 44301449474739600641620465)
                  ·
                    refine ⟨33226087106054700481215349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44301449474739600641620465 33226087106054700481215349)
                    ·
                      refine ⟨3114945666192628170113939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33226087106054700481215349 3114945666192628170113939)
                      ·
                        rfl

theorem cell23_6066335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6066335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066335 prefixEnd_6066335 := by exact prefixLift 6066335
  have htrace : WordTrace (prefixWord ++ tailWord_6066335) baseStart_6066335 baseEnd_6066335 := by
    simpa [prefixWord, tailWord_6066335, baseEnd_6066335] using wordTrace_append hprefix tailTrace_6066335
  have hstable : (prefixWord ++ tailWord_6066335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066335).length < 2 ^ (prefixWord ++ tailWord_6066335).sum := by decide
  have hdescent : baseEnd_6066335 < baseStart_6066335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066340 : List Nat := [2, 3, 1, 2, 5, 1, 1, 3, 1, 2, 2]
def baseStart_6066340 : Nat := 118140960795 + 6066340 * 2 ^ 59
def prefixEnd_6066340 : Nat := 4983230072969 + 3 ^ 40 * 6066340 * 2
def baseEnd_6066340 : Nat := 3114948233595900650551417

theorem tailTrace_6066340 : CollatzResearch.WordTrace tailWord_6066340 prefixEnd_6066340 3114948233595900650551417 := by
  unfold tailWord_6066340
  simp only [CollatzResearch.WordTrace]
  refine ⟨110628798421346851616542237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147505064561795802155389649 110628798421346851616542237)
  ·
    refine ⟨41485799408005069356203339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110628798421346851616542237 41485799408005069356203339)
    ·
      refine ⟨62228699112007604034305009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41485799408005069356203339 62228699112007604034305009)
      ·
        refine ⟨46671524334005703025728757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62228699112007604034305009 46671524334005703025728757)
        ·
          refine ⟨4375455406313034658662071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46671524334005703025728757 4375455406313034658662071)
          ·
            refine ⟨6563183109469551987993107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375455406313034658662071 6563183109469551987993107)
            ·
              refine ⟨9844774664204327981989661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563183109469551987993107 9844774664204327981989661)
              ·
                refine ⟨3691790499076622993246123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9844774664204327981989661 3691790499076622993246123)
                ·
                  refine ⟨5537685748614934489869185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3691790499076622993246123 5537685748614934489869185)
                  ·
                    refine ⟨4153264311461200867401889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5537685748614934489869185 4153264311461200867401889)
                    ·
                      refine ⟨3114948233595900650551417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153264311461200867401889 3114948233595900650551417)
                      ·
                        rfl

theorem cell23_6066340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_6066340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066340 prefixEnd_6066340 := by exact prefixLift 6066340
  have htrace : WordTrace (prefixWord ++ tailWord_6066340) baseStart_6066340 baseEnd_6066340 := by
    simpa [prefixWord, tailWord_6066340, baseEnd_6066340] using wordTrace_append hprefix tailTrace_6066340
  have hstable : (prefixWord ++ tailWord_6066340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066340).length < 2 ^ (prefixWord ++ tailWord_6066340).sum := by decide
  have hdescent : baseEnd_6066340 < baseStart_6066340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066365 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_6066365 : Nat := 118140960795 + 6066365 * 2 ^ 59
def prefixEnd_6066365 : Nat := 4983230072969 + 3 ^ 40 * 6066365 * 2
def baseEnd_6066365 : Nat := 3114961070612263052738801

theorem tailTrace_6066365 : CollatzResearch.WordTrace tailWord_6066365 prefixEnd_6066365 3114961070612263052738801 := by
  unfold tailWord_6066365
  simp only [CollatzResearch.WordTrace]
  refine ⟨221258508667603132502744549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147505672445068755001829699 221258508667603132502744549)
  ·
    refine ⟨41485970375175587344264603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221258508667603132502744549 41485970375175587344264603)
    ·
      refine ⟨62228955562763381016396905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41485970375175587344264603 62228955562763381016396905)
      ·
        refine ⟨46671716672072535762297679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62228955562763381016396905 46671716672072535762297679)
        ·
          refine ⟨70007575008108803643446519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46671716672072535762297679 70007575008108803643446519)
          ·
            refine ⟨105011362512163205465169779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70007575008108803643446519 105011362512163205465169779)
            ·
              refine ⟨157517043768244808197754669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105011362512163205465169779 157517043768244808197754669)
              ·
                refine ⟨59068891413091803074158001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157517043768244808197754669 59068891413091803074158001)
                ·
                  refine ⟨44301668559818852305618501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59068891413091803074158001 44301668559818852305618501)
                  ·
                    refine ⟨8306562854966034807303469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44301668559818852305618501 8306562854966034807303469)
                    ·
                      refine ⟨3114961070612263052738801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8306562854966034807303469 3114961070612263052738801)
                      ·
                        rfl

theorem cell23_6066365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_6066365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066365 prefixEnd_6066365 := by exact prefixLift 6066365
  have htrace : WordTrace (prefixWord ++ tailWord_6066365) baseStart_6066365 baseEnd_6066365 := by
    simpa [prefixWord, tailWord_6066365, baseEnd_6066365] using wordTrace_append hprefix tailTrace_6066365
  have hstable : (prefixWord ++ tailWord_6066365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066365).length < 2 ^ (prefixWord ++ tailWord_6066365).sum := by decide
  have hdescent : baseEnd_6066365 < baseStart_6066365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066379 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 2, 2, 2]
def baseStart_6066379 : Nat := 118140960795 + 6066379 * 2 ^ 59
def prefixEnd_6066379 : Nat := 4983230072969 + 3 ^ 40 * 6066379 * 2
def baseEnd_6066379 : Nat := 3114968259341425997963737

theorem tailTrace_6066379 : CollatzResearch.WordTrace tailWord_6066379 prefixEnd_6066379 3114968259341425997963737 := by
  unfold tailWord_6066379
  simp only [CollatzResearch.WordTrace]
  refine ⟨221259019289552412893754191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147506012859701608595836127 221259019289552412893754191)
  ·
    refine ⟨331888528934328619340631287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221259019289552412893754191 331888528934328619340631287)
    ·
      refine ⟨497832793401492929010946931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331888528934328619340631287 497832793401492929010946931)
      ·
        refine ⟨746749190102239393516420397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497832793401492929010946931 746749190102239393516420397)
        ·
          refine ⟨280030946288339772568657649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 746749190102239393516420397 280030946288339772568657649)
          ·
            refine ⟨210023209716254829426493237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280030946288339772568657649 210023209716254829426493237)
            ·
              refine ⟨19689675910898890258733741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210023209716254829426493237 19689675910898890258733741)
              ·
                refine ⟨7383628466587083847025153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19689675910898890258733741 7383628466587083847025153)
                ·
                  refine ⟨5537721349940312885268865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7383628466587083847025153 5537721349940312885268865)
                  ·
                    refine ⟨4153291012455234663951649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5537721349940312885268865 4153291012455234663951649)
                    ·
                      refine ⟨3114968259341425997963737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153291012455234663951649 3114968259341425997963737)
                      ·
                        rfl

theorem cell23_6066379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 2, 2].length) (baseStart_6066379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066379 prefixEnd_6066379 := by exact prefixLift 6066379
  have htrace : WordTrace (prefixWord ++ tailWord_6066379) baseStart_6066379 baseEnd_6066379 := by
    simpa [prefixWord, tailWord_6066379, baseEnd_6066379] using wordTrace_append hprefix tailTrace_6066379
  have hstable : (prefixWord ++ tailWord_6066379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066379).length < 2 ^ (prefixWord ++ tailWord_6066379).sum := by decide
  have hdescent : baseEnd_6066379 < baseStart_6066379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066413 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_6066413 : Nat := 118140960795 + 6066413 * 2 ^ 59
def prefixEnd_6066413 : Nat := 4983230072969 + 3 ^ 40 * 6066413 * 2
def baseEnd_6066413 : Nat := 3114985717683678864938581

theorem tailTrace_6066413 : CollatzResearch.WordTrace tailWord_6066413 prefixEnd_6066413 3114985717683678864938581 := by
  unfold tailWord_6066413
  simp only [CollatzResearch.WordTrace]
  refine ⟨221260259371429236700491893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147506839580952824466994595 221260259371429236700491893)
  ·
    refine ⟨20743149316071490940671115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221260259371429236700491893 20743149316071490940671115)
    ·
      refine ⟨31114723974107236411006673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20743149316071490940671115 31114723974107236411006673)
      ·
        refine ⟨23336042980580427308255005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31114723974107236411006673 23336042980580427308255005)
        ·
          refine ⟨8751016117717660240595627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23336042980580427308255005 8751016117717660240595627)
          ·
            refine ⟨13126524176576490360893441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751016117717660240595627 13126524176576490360893441)
            ·
              refine ⟨9844893132432367770670081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13126524176576490360893441 9844893132432367770670081)
              ·
                refine ⟨7383669849324275828002561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9844893132432367770670081 7383669849324275828002561)
                ·
                  refine ⟨5537752386993206871001921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7383669849324275828002561 5537752386993206871001921)
                  ·
                    refine ⟨4153314290244905153251441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5537752386993206871001921 4153314290244905153251441)
                    ·
                      refine ⟨3114985717683678864938581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153314290244905153251441 3114985717683678864938581)
                      ·
                        rfl

theorem cell23_6066413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_6066413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066413 prefixEnd_6066413 := by exact prefixLift 6066413
  have htrace : WordTrace (prefixWord ++ tailWord_6066413) baseStart_6066413 baseEnd_6066413 := by
    simpa [prefixWord, tailWord_6066413, baseEnd_6066413] using wordTrace_append hprefix tailTrace_6066413
  have hstable : (prefixWord ++ tailWord_6066413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066413).length < 2 ^ (prefixWord ++ tailWord_6066413).sum := by decide
  have hdescent : baseEnd_6066413 < baseStart_6066413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066435 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 4]
def baseStart_6066435 : Nat := 118140960795 + 6066435 * 2 ^ 59
def prefixEnd_6066435 : Nat := 4983230072969 + 3 ^ 40 * 6066435 * 2
def baseEnd_6066435 : Nat := 3114997014258077778863479

theorem tailTrace_6066435 : CollatzResearch.WordTrace tailWord_6066435 prefixEnd_6066435 3114997014258077778863479 := by
  unfold tailWord_6066435
  simp only [CollatzResearch.WordTrace]
  refine ⟨221261061777349534457792759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147507374518233022971861839 221261061777349534457792759)
  ·
    refine ⟨331891592666024301686689139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221261061777349534457792759 331891592666024301686689139)
    ·
      refine ⟨497837388999036452530033709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331891592666024301686689139 497837388999036452530033709)
      ·
        refine ⟨186689020874638669698762641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497837388999036452530033709 186689020874638669698762641)
        ·
          refine ⟨140016765655979002274071981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186689020874638669698762641 140016765655979002274071981)
          ·
            refine ⟨52506287120992125852776993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140016765655979002274071981 52506287120992125852776993)
            ·
              refine ⟨39379715340744094389582745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52506287120992125852776993 39379715340744094389582745)
              ·
                refine ⟨29534786505558070792187059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39379715340744094389582745 29534786505558070792187059)
                ·
                  refine ⟨44302179758337106188280589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29534786505558070792187059 44302179758337106188280589)
                  ·
                    refine ⟨16613317409376414820605221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44302179758337106188280589 16613317409376414820605221)
                    ·
                      refine ⟨3114997014258077778863479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16613317409376414820605221 3114997014258077778863479)
                      ·
                        rfl

theorem cell23_6066435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_6066435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066435 prefixEnd_6066435 := by exact prefixLift 6066435
  have htrace : WordTrace (prefixWord ++ tailWord_6066435) baseStart_6066435 baseEnd_6066435 := by
    simpa [prefixWord, tailWord_6066435, baseEnd_6066435] using wordTrace_append hprefix tailTrace_6066435
  have hstable : (prefixWord ++ tailWord_6066435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066435).length < 2 ^ (prefixWord ++ tailWord_6066435).sum := by decide
  have hdescent : baseEnd_6066435 < baseStart_6066435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066465 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_6066465 : Nat := 118140960795 + 6066465 * 2 ^ 59
def prefixEnd_6066465 : Nat := 4983230072969 + 3 ^ 40 * 6066465 * 2
def baseEnd_6066465 : Nat := 3115012418677712661488341

theorem tailTrace_6066465 : CollatzResearch.WordTrace tailWord_6066465 prefixEnd_6066465 3115012418677712661488341 := by
  unfold tailWord_6066465
  simp only [CollatzResearch.WordTrace]
  refine ⟨221262155967240849581384849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147508103978160566387589899 221262155967240849581384849)
  ·
    refine ⟨165946616975430637186038637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221262155967240849581384849 165946616975430637186038637)
    ·
      refine ⟨62229981365786488944764489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165946616975430637186038637 62229981365786488944764489)
      ·
        refine ⟨46672486024339866708573367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62229981365786488944764489 46672486024339866708573367)
        ·
          refine ⟨70008729036509800062860051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46672486024339866708573367 70008729036509800062860051)
          ·
            refine ⟨105013093554764700094290077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70008729036509800062860051 105013093554764700094290077)
            ·
              refine ⟨39379910083036762535358779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105013093554764700094290077 39379910083036762535358779)
              ·
                refine ⟨59069865124555143803038169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39379910083036762535358779 59069865124555143803038169)
                ·
                  refine ⟨44302398843416357852278627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59069865124555143803038169 44302398843416357852278627)
                  ·
                    refine ⟨66453598265124536778417941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44302398843416357852278627 66453598265124536778417941)
                    ·
                      refine ⟨3115012418677712661488341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66453598265124536778417941 3115012418677712661488341)
                      ·
                        rfl

theorem cell23_6066465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_6066465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066465 prefixEnd_6066465 := by exact prefixLift 6066465
  have htrace : WordTrace (prefixWord ++ tailWord_6066465) baseStart_6066465 baseEnd_6066465 := by
    simpa [prefixWord, tailWord_6066465, baseEnd_6066465] using wordTrace_append hprefix tailTrace_6066465
  have hstable : (prefixWord ++ tailWord_6066465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066465).length < 2 ^ (prefixWord ++ tailWord_6066465).sum := by decide
  have hdescent : baseEnd_6066465 < baseStart_6066465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066479 : List Nat := [1, 1, 2, 1, 2, 1, 6, 4, 1, 4]
def baseStart_6066479 : Nat := 118140960795 + 6066479 * 2 ^ 59
def prefixEnd_6066479 : Nat := 4983230072969 + 3 ^ 40 * 6066479 * 2
def baseEnd_6066479 : Nat := 1038339869135625202237759

theorem tailTrace_6066479 : CollatzResearch.WordTrace tailWord_6066479 prefixEnd_6066479 1038339869135625202237759 := by
  unfold tailWord_6066479
  simp only [CollatzResearch.WordTrace]
  refine ⟨221262666589190129972394491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147508444392793419981596327 221262666589190129972394491)
  ·
    refine ⟨331893999883785194958591737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221262666589190129972394491 331893999883785194958591737)
    ·
      refine ⟨248920499912838896218943803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331893999883785194958591737 248920499912838896218943803)
      ·
        refine ⟨373380749869258344328415705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248920499912838896218943803 373380749869258344328415705)
        ·
          refine ⟨280035562401943758246311779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373380749869258344328415705 280035562401943758246311779)
          ·
            refine ⟨420053343602915637369467669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280035562401943758246311779 420053343602915637369467669)
            ·
              refine ⟨19690000481386670501693797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 420053343602915637369467669 19690000481386670501693797)
              ·
                refine ⟨3691875090260000719067587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19690000481386670501693797 3691875090260000719067587)
                ·
                  refine ⟨5537812635390001078601381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3691875090260000719067587 5537812635390001078601381)
                  ·
                    refine ⟨1038339869135625202237759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5537812635390001078601381 1038339869135625202237759)
                    ·
                      rfl

theorem cell23_6066479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 4].length) (baseStart_6066479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066479 prefixEnd_6066479 := by exact prefixLift 6066479
  have htrace : WordTrace (prefixWord ++ tailWord_6066479) baseStart_6066479 baseEnd_6066479 := by
    simpa [prefixWord, tailWord_6066479, baseEnd_6066479] using wordTrace_append hprefix tailTrace_6066479
  have hstable : (prefixWord ++ tailWord_6066479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066479).length < 2 ^ (prefixWord ++ tailWord_6066479).sum := by decide
  have hdescent : baseEnd_6066479 < baseStart_6066479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066495 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_6066495 : Nat := 118140960795 + 6066495 * 2 ^ 59
def prefixEnd_6066495 : Nat := 4983230072969 + 3 ^ 40 * 6066495 * 2
def baseEnd_6066495 : Nat := 3115027823097347544113203

theorem tailTrace_6066495 : CollatzResearch.WordTrace tailWord_6066495 prefixEnd_6066495 3115027823097347544113203 := by
  unfold tailWord_6066495
  simp only [CollatzResearch.WordTrace]
  refine ⟨221263250157132164704976939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147508833438088109803317959 221263250157132164704976939)
  ·
    refine ⟨331894875235698247057465409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221263250157132164704976939 331894875235698247057465409)
    ·
      refine ⟨248921156426773685293099057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331894875235698247057465409 248921156426773685293099057)
      ·
        refine ⟨186690867320080263969824293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248921156426773685293099057 186690867320080263969824293)
        ·
          refine ⟨35004537622515049494342055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186690867320080263969824293 35004537622515049494342055)
          ·
            refine ⟨52506806433772574241513083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35004537622515049494342055 52506806433772574241513083)
            ·
              refine ⟨78760209650658861362269625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52506806433772574241513083 78760209650658861362269625)
              ·
                refine ⟨59070157237994146021702219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78760209650658861362269625 59070157237994146021702219)
                ·
                  refine ⟨88605235856991219032553329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59070157237994146021702219 88605235856991219032553329)
                  ·
                    refine ⟨66453926892743414274414997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88605235856991219032553329 66453926892743414274414997)
                    ·
                      refine ⟨3115027823097347544113203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66453926892743414274414997 3115027823097347544113203)
                      ·
                        rfl

theorem cell23_6066495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_6066495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066495 prefixEnd_6066495 := by exact prefixLift 6066495
  have htrace : WordTrace (prefixWord ++ tailWord_6066495) baseStart_6066495 baseEnd_6066495 := by
    simpa [prefixWord, tailWord_6066495, baseEnd_6066495] using wordTrace_append hprefix tailTrace_6066495
  have hstable : (prefixWord ++ tailWord_6066495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066495).length < 2 ^ (prefixWord ++ tailWord_6066495).sum := by decide
  have hdescent : baseEnd_6066495 < baseStart_6066495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066536 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_6066536 : Nat := 118140960795 + 6066536 * 2 ^ 59
def prefixEnd_6066536 : Nat := 4983230072969 + 3 ^ 40 * 6066536 * 2
def baseEnd_6066536 : Nat := 3115048875804181883700515

theorem tailTrace_6066536 : CollatzResearch.WordTrace tailWord_6066536 prefixEnd_6066536 3115048875804181883700515 := by
  unfold tailWord_6066536
  simp only [CollatzResearch.WordTrace]
  refine ⟨110632372774991814353609731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147509830366655752471479641 110632372774991814353609731)
  ·
    refine ⟨165948559162487721530414597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110632372774991814353609731 165948559162487721530414597)
    ·
      refine ⟨31115354842966447786952737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165948559162487721530414597 31115354842966447786952737)
      ·
        refine ⟨23336516132224835840214553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31115354842966447786952737 23336516132224835840214553)
        ·
          refine ⟨17502387099168626880160915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23336516132224835840214553 17502387099168626880160915)
          ·
            refine ⟨26253580648752940320241373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17502387099168626880160915 26253580648752940320241373)
            ·
              refine ⟨9845092743282352620090515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26253580648752940320241373 9845092743282352620090515)
              ·
                refine ⟨14767639114923528930135773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9845092743282352620090515 14767639114923528930135773)
                ·
                  refine ⟨5537864668096323348800915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14767639114923528930135773 5537864668096323348800915)
                  ·
                    refine ⟨8306797002144485023201373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5537864668096323348800915 8306797002144485023201373)
                    ·
                      refine ⟨3115048875804181883700515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8306797002144485023201373 3115048875804181883700515)
                      ·
                        rfl

theorem cell23_6066536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_6066536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066536 prefixEnd_6066536 := by exact prefixLift 6066536
  have htrace : WordTrace (prefixWord ++ tailWord_6066536) baseStart_6066536 baseEnd_6066536 := by
    simpa [prefixWord, tailWord_6066536, baseEnd_6066536] using wordTrace_append hprefix tailTrace_6066536
  have hstable : (prefixWord ++ tailWord_6066536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066536).length < 2 ^ (prefixWord ++ tailWord_6066536).sum := by decide
  have hdescent : baseEnd_6066536 < baseStart_6066536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066572 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_6066572 : Nat := 118140960795 + 6066572 * 2 ^ 59
def prefixEnd_6066572 : Nat := 4983230072969 + 3 ^ 40 * 6066572 * 2
def baseEnd_6066572 : Nat := 3115067361107743742850349

theorem tailTrace_6066572 : CollatzResearch.WordTrace tailWord_6066572 prefixEnd_6066572 3115067361107743742850349 := by
  unfold tailWord_6066572
  simp only [CollatzResearch.WordTrace]
  refine ⟨110633029288926603427764985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147510705718568804570353313 110633029288926603427764985)
  ·
    refine ⟨82974771966694952570823739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110633029288926603427764985 82974771966694952570823739)
    ·
      refine ⟨124462157950042428856235609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82974771966694952570823739 124462157950042428856235609)
      ·
        refine ⟨93346618462531821642176707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124462157950042428856235609 93346618462531821642176707)
        ·
          refine ⟨140019927693797732463265061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93346618462531821642176707 140019927693797732463265061)
          ·
            refine ⟨26253736442587074836862199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140019927693797732463265061 26253736442587074836862199)
            ·
              refine ⟨39380604663880612255293299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26253736442587074836862199 39380604663880612255293299)
              ·
                refine ⟨59070906995820918382939949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39380604663880612255293299 59070906995820918382939949)
                ·
                  refine ⟨22151590123432844393602481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59070906995820918382939949 22151590123432844393602481)
                  ·
                    refine ⟨16613692592574633295201861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22151590123432844393602481 16613692592574633295201861)
                    ·
                      refine ⟨3115067361107743742850349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16613692592574633295201861 3115067361107743742850349)
                      ·
                        rfl

theorem cell23_6066572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_6066572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066572 prefixEnd_6066572 := by exact prefixLift 6066572
  have htrace : WordTrace (prefixWord ++ tailWord_6066572) baseStart_6066572 baseEnd_6066572 := by
    simpa [prefixWord, tailWord_6066572, baseEnd_6066572] using wordTrace_append hprefix tailTrace_6066572
  have hstable : (prefixWord ++ tailWord_6066572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066572).length < 2 ^ (prefixWord ++ tailWord_6066572).sum := by decide
  have hdescent : baseEnd_6066572 < baseStart_6066572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066586 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_6066586 : Nat := 118140960795 + 6066586 * 2 ^ 59
def prefixEnd_6066586 : Nat := 4983230072969 + 3 ^ 40 * 6066586 * 2
def baseEnd_6066586 : Nat := 1038358183278968896025095

theorem tailTrace_6066586 : CollatzResearch.WordTrace tailWord_6066586 prefixEnd_6066586 1038358183278968896025095 := by
  unfold tailWord_6066586
  simp only [CollatzResearch.WordTrace]
  refine ⟨55316642299950621811634903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147511046133201658164359741 55316642299950621811634903)
  ·
    refine ⟨82974963449925932717452355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55316642299950621811634903 82974963449925932717452355)
    ·
      refine ⟨124462445174888899076178533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82974963449925932717452355 124462445174888899076178533)
      ·
        refine ⟨23336708470291668576783475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124462445174888899076178533 23336708470291668576783475)
        ·
          refine ⟨35005062705437502865175213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23336708470291668576783475 35005062705437502865175213)
          ·
            refine ⟨13126898514539063574440705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35005062705437502865175213 13126898514539063574440705)
            ·
              refine ⟨9845173885904297680830529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13126898514539063574440705 9845173885904297680830529)
              ·
                refine ⟨7383880414428223260622897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9845173885904297680830529 7383880414428223260622897)
                ·
                  refine ⟨5537910310821167445467173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7383880414428223260622897 5537910310821167445467173)
                  ·
                    refine ⟨1038358183278968896025095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5537910310821167445467173 1038358183278968896025095)
                    ·
                      rfl

theorem cell23_6066586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_6066586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066586 prefixEnd_6066586 := by exact prefixLift 6066586
  have htrace : WordTrace (prefixWord ++ tailWord_6066586) baseStart_6066586 baseEnd_6066586 := by
    simpa [prefixWord, tailWord_6066586, baseEnd_6066586] using wordTrace_append hprefix tailTrace_6066586
  have hstable : (prefixWord ++ tailWord_6066586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066586).length < 2 ^ (prefixWord ++ tailWord_6066586).sum := by decide
  have hdescent : baseEnd_6066586 < baseStart_6066586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066599 : List Nat := [1, 1, 6, 1, 1, 4, 1, 8]
def baseStart_6066599 : Nat := 118140960795 + 6066599 * 2 ^ 59
def prefixEnd_6066599 : Nat := 4983230072969 + 3 ^ 40 * 6066599 * 2
def baseEnd_6066599 : Nat := 115373378706867227304175

theorem tailTrace_6066599 : CollatzResearch.WordTrace tailWord_6066599 prefixEnd_6066599 115373378706867227304175 := by
  unfold tailWord_6066599
  simp only [CollatzResearch.WordTrace]
  refine ⟨221267043348755390466762851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147511362232503593644508567 221267043348755390466762851)
  ·
    refine ⟨331900565023133085700144277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221267043348755390466762851 331900565023133085700144277)
    ·
      refine ⟨15557838985459363392194263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 331900565023133085700144277 15557838985459363392194263)
      ·
        refine ⟨23336758478189045088291395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15557838985459363392194263 23336758478189045088291395)
        ·
          refine ⟨35005137717283567632437093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23336758478189045088291395 35005137717283567632437093)
          ·
            refine ⟨6563463321990668931081955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35005137717283567632437093 6563463321990668931081955)
            ·
              refine ⟨9845194982986003396622933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563463321990668931081955 9845194982986003396622933)
              ·
                refine ⟨115373378706867227304175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9845194982986003396622933 115373378706867227304175)
                ·
                  rfl

theorem cell23_6066599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 8].length) (baseStart_6066599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066599 prefixEnd_6066599 := by exact prefixLift 6066599
  have htrace : WordTrace (prefixWord ++ tailWord_6066599) baseStart_6066599 baseEnd_6066599 := by
    simpa [prefixWord, tailWord_6066599, baseEnd_6066599] using wordTrace_append hprefix tailTrace_6066599
  have hstable : (prefixWord ++ tailWord_6066599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066599).length < 2 ^ (prefixWord ++ tailWord_6066599).sum := by decide
  have hdescent : baseEnd_6066599 < baseStart_6066599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066609 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_6066609 : Nat := 118140960795 + 6066609 * 2 ^ 59
def prefixEnd_6066609 : Nat := 4983230072969 + 3 ^ 40 * 6066609 * 2
def baseEnd_6066609 : Nat := 3115086359891960098087679

theorem tailTrace_6066609 : CollatzResearch.WordTrace tailWord_6066609 prefixEnd_6066609 3115086359891960098087679 := by
  unfold tailWord_6066609
  simp only [CollatzResearch.WordTrace]
  refine ⟨221267408078719162174626881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147511605385812774783084587 221267408078719162174626881)
  ·
    refine ⟨165950556059039371630970161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221267408078719162174626881 165950556059039371630970161)
    ·
      refine ⟨124462917044279528723227621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165950556059039371630970161 124462917044279528723227621)
      ·
        refine ⟨23336796945802411635605179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124462917044279528723227621 23336796945802411635605179)
        ·
          refine ⟨35005195418703617453407769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23336796945802411635605179 35005195418703617453407769)
          ·
            refine ⟨26253896564027713090055827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35005195418703617453407769 26253896564027713090055827)
            ·
              refine ⟨39380844846041569635083741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26253896564027713090055827 39380844846041569635083741)
              ·
                refine ⟨14767816817265588613156403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39380844846041569635083741 14767816817265588613156403)
                ·
                  refine ⟨22151725225898382919734605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14767816817265588613156403 22151725225898382919734605)
                  ·
                    refine ⟨8306896959711893594900477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22151725225898382919734605 8306896959711893594900477)
                    ·
                      refine ⟨3115086359891960098087679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8306896959711893594900477 3115086359891960098087679)
                      ·
                        rfl

theorem cell23_6066609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_6066609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066609 prefixEnd_6066609 := by exact prefixLift 6066609
  have htrace : WordTrace (prefixWord ++ tailWord_6066609) baseStart_6066609 baseEnd_6066609 := by
    simpa [prefixWord, tailWord_6066609, baseEnd_6066609] using wordTrace_append hprefix tailTrace_6066609
  have hstable : (prefixWord ++ tailWord_6066609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066609).length < 2 ^ (prefixWord ++ tailWord_6066609).sum := by decide
  have hdescent : baseEnd_6066609 < baseStart_6066609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066672 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 7]
def baseStart_6066672 : Nat := 118140960795 + 6066672 * 2 ^ 59
def prefixEnd_6066672 : Nat := 4983230072969 + 3 ^ 40 * 6066672 * 2
def baseEnd_6066672 : Nat := 346124301019243705733321

theorem tailTrace_6066672 : CollatzResearch.WordTrace tailWord_6066672 prefixEnd_6066672 346124301019243705733321 := by
  unfold tailWord_6066672
  simp only [CollatzResearch.WordTrace]
  refine ⟨110634852938745461967085135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147513137251660615956113513 110634852938745461967085135)
  ·
    refine ⟨165952279408118192950627703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110634852938745461967085135 165952279408118192950627703)
    ·
      refine ⟨248928419112177289425941555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165952279408118192950627703 248928419112177289425941555)
      ·
        refine ⟨373392628668265934138912333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248928419112177289425941555 373392628668265934138912333)
        ·
          refine ⟨140022235750599725302092125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373392628668265934138912333 140022235750599725302092125)
          ·
            refine ⟨52508338406474896988284547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140022235750599725302092125 52508338406474896988284547)
            ·
              refine ⟨78762507609712345482426821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52508338406474896988284547 78762507609712345482426821)
              ·
                refine ⟨14767970176821064777955029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78762507609712345482426821 14767970176821064777955029)
                ·
                  refine ⟨346124301019243705733321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14767970176821064777955029 346124301019243705733321)
                  ·
                    rfl

theorem cell23_6066672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 7].length) (baseStart_6066672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066672 prefixEnd_6066672 := by exact prefixLift 6066672
  have htrace : WordTrace (prefixWord ++ tailWord_6066672) baseStart_6066672 baseEnd_6066672 := by
    simpa [prefixWord, tailWord_6066672, baseEnd_6066672] using wordTrace_append hprefix tailTrace_6066672
  have hstable : (prefixWord ++ tailWord_6066672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066672).length < 2 ^ (prefixWord ++ tailWord_6066672).sum := by decide
  have hdescent : baseEnd_6066672 < baseStart_6066672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066717 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_6066717 : Nat := 118140960795 + 6066717 * 2 ^ 59
def prefixEnd_6066717 : Nat := 4983230072969 + 3 ^ 40 * 6066717 * 2
def baseEnd_6066717 : Nat := 3115141815802645675537183

theorem tailTrace_6066717 : CollatzResearch.WordTrace tailWord_6066717 prefixEnd_6066717 3115141815802645675537183 := by
  unfold tailWord_6066717
  simp only [CollatzResearch.WordTrace]
  refine ⟨221271347162327896619558405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147514231441551931079705603 221271347162327896619558405)
  ·
    refine ⟨41488377592936480616167201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221271347162327896619558405 41488377592936480616167201)
    ·
      refine ⟨31116283194702360462125401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41488377592936480616167201 31116283194702360462125401)
      ·
        refine ⟨23337212396026770346594051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31116283194702360462125401 23337212396026770346594051)
        ·
          refine ⟨35005818594040155519891077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23337212396026770346594051 35005818594040155519891077)
          ·
            refine ⟨6563590986382529159979577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35005818594040155519891077 6563590986382529159979577)
            ·
              refine ⟨4922693239786896869984683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6563590986382529159979577 4922693239786896869984683)
              ·
                refine ⟨7384039859680345304977025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4922693239786896869984683 7384039859680345304977025)
                ·
                  refine ⟨5538029894760258978732769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7384039859680345304977025 5538029894760258978732769)
                  ·
                    refine ⟨4153522421070194234049577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5538029894760258978732769 4153522421070194234049577)
                    ·
                      refine ⟨3115141815802645675537183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153522421070194234049577 3115141815802645675537183)
                      ·
                        rfl

theorem cell23_6066717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_6066717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066717 prefixEnd_6066717 := by exact prefixLift 6066717
  have htrace : WordTrace (prefixWord ++ tailWord_6066717) baseStart_6066717 baseEnd_6066717 := by
    simpa [prefixWord, tailWord_6066717, baseEnd_6066717] using wordTrace_append hprefix tailTrace_6066717
  have hstable : (prefixWord ++ tailWord_6066717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066717).length < 2 ^ (prefixWord ++ tailWord_6066717).sum := by decide
  have hdescent : baseEnd_6066717 < baseStart_6066717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066732 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_6066732 : Nat := 118140960795 + 6066732 * 2 ^ 59
def prefixEnd_6066732 : Nat := 4983230072969 + 3 ^ 40 * 6066732 * 2
def baseEnd_6066732 : Nat := 1038383172670821038949871

theorem tailTrace_6066732 : CollatzResearch.WordTrace tailWord_6066732 prefixEnd_6066732 1038383172670821038949871 := by
  unfold tailWord_6066732
  simp only [CollatzResearch.WordTrace]
  refine ⟨110635947128636777090677225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147514596171515702787569633 110635947128636777090677225)
  ·
    refine ⟨82976960346477582818007919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110635947128636777090677225 82976960346477582818007919)
    ·
      refine ⟨124465440519716374227011879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82976960346477582818007919 124465440519716374227011879)
      ·
        refine ⟨186698160779574561340517819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124465440519716374227011879 186698160779574561340517819)
        ·
          refine ⟨280047241169361842010776729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186698160779574561340517819 280047241169361842010776729)
          ·
            refine ⟨210035430877021381508082547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280047241169361842010776729 210035430877021381508082547)
            ·
              refine ⟨315053146315532072262123821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210035430877021381508082547 315053146315532072262123821)
              ·
                refine ⟨118144929868324527098296433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315053146315532072262123821 118144929868324527098296433)
                ·
                  refine ⟨88608697401243395323722325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118144929868324527098296433 88608697401243395323722325)
                  ·
                    refine ⟨1038383172670821038949871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88608697401243395323722325 1038383172670821038949871)
                    ·
                      rfl

theorem cell23_6066732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_6066732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066732 prefixEnd_6066732 := by exact prefixLift 6066732
  have htrace : WordTrace (prefixWord ++ tailWord_6066732) baseStart_6066732 baseEnd_6066732 := by
    simpa [prefixWord, tailWord_6066732, baseEnd_6066732] using wordTrace_append hprefix tailTrace_6066732
  have hstable : (prefixWord ++ tailWord_6066732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066732).length < 2 ^ (prefixWord ++ tailWord_6066732).sum := by decide
  have hdescent : baseEnd_6066732 < baseStart_6066732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066800 : List Nat := [2, 1, 1, 1, 7, 1, 2, 3, 1, 4]
def baseStart_6066800 : Nat := 118140960795 + 6066800 * 2 ^ 59
def prefixEnd_6066800 : Nat := 4983230072969 + 3 ^ 40 * 6066800 * 2
def baseEnd_6066800 : Nat := 1038394811565656283599767

theorem tailTrace_6066800 : CollatzResearch.WordTrace tailWord_6066800 prefixEnd_6066800 1038394811565656283599767 := by
  unfold tailWord_6066800
  simp only [CollatzResearch.WordTrace]
  refine ⟨110637187210513600897414927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147516249614018134529886569 110637187210513600897414927)
  ·
    refine ⟨165955780815770401346122391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110637187210513600897414927 165955780815770401346122391)
    ·
      refine ⟨248933671223655602019183587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165955780815770401346122391 248933671223655602019183587)
      ·
        refine ⟨373400506835483403028775381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248933671223655602019183587 373400506835483403028775381)
        ·
          refine ⟨8751574378956642258486923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 373400506835483403028775381 8751574378956642258486923)
          ·
            refine ⟨13127361568434963387730385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751574378956642258486923 13127361568434963387730385)
            ·
              refine ⟨9845521176326222540797789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13127361568434963387730385 9845521176326222540797789)
              ·
                refine ⟨3692070441122333452799171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9845521176326222540797789 3692070441122333452799171)
                ·
                  refine ⟨5538105661683500179198757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692070441122333452799171 5538105661683500179198757)
                  ·
                    refine ⟨1038394811565656283599767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5538105661683500179198757 1038394811565656283599767)
                    ·
                      rfl

theorem cell23_6066800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 4].length) (baseStart_6066800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066800 prefixEnd_6066800 := by exact prefixLift 6066800
  have htrace : WordTrace (prefixWord ++ tailWord_6066800) baseStart_6066800 baseEnd_6066800 := by
    simpa [prefixWord, tailWord_6066800, baseEnd_6066800] using wordTrace_append hprefix tailTrace_6066800
  have hstable : (prefixWord ++ tailWord_6066800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066800).length < 2 ^ (prefixWord ++ tailWord_6066800).sum := by decide
  have hdescent : baseEnd_6066800 < baseStart_6066800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066813 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 6]
def baseStart_6066813 : Nat := 118140960795 + 6066813 * 2 ^ 59
def prefixEnd_6066813 : Nat := 4983230072969 + 3 ^ 40 * 6066813 * 2
def baseEnd_6066813 : Nat := 346132345549497477770749

theorem tailTrace_6066813 : CollatzResearch.WordTrace tailWord_6066813 prefixEnd_6066813 346132345549497477770749 := by
  unfold tailWord_6066813
  simp only [CollatzResearch.WordTrace]
  refine ⟨221274848569980105015053093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147516565713320070010035395 221274848569980105015053093)
  ·
    refine ⟨41489034106871269690322455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221274848569980105015053093 41489034106871269690322455)
    ·
      refine ⟨62233551160306904535483683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41489034106871269690322455 62233551160306904535483683)
      ·
        refine ⟨93350326740460356803225525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62233551160306904535483683 93350326740460356803225525)
        ·
          refine ⟨8751593131918158450302393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93350326740460356803225525 8751593131918158450302393)
          ·
            refine ⟨6563694848938618837726795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8751593131918158450302393 6563694848938618837726795)
            ·
              refine ⟨9845542273407928256590193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563694848938618837726795 9845542273407928256590193)
              ·
                refine ⟨7384156705055946192442645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9845542273407928256590193 7384156705055946192442645)
                ·
                  refine ⟨346132345549497477770749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7384156705055946192442645 346132345549497477770749)
                  ·
                    rfl

theorem cell23_6066813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_6066813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066813 prefixEnd_6066813 := by exact prefixLift 6066813
  have htrace : WordTrace (prefixWord ++ tailWord_6066813) baseStart_6066813 baseEnd_6066813 := by
    simpa [prefixWord, tailWord_6066813, baseEnd_6066813] using wordTrace_append hprefix tailTrace_6066813
  have hstable : (prefixWord ++ tailWord_6066813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066813).length < 2 ^ (prefixWord ++ tailWord_6066813).sum := by decide
  have hdescent : baseEnd_6066813 < baseStart_6066813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066823 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_6066823 : Nat := 118140960795 + 6066823 * 2 ^ 59
def prefixEnd_6066823 : Nat := 4983230072969 + 3 ^ 40 * 6066823 * 2
def baseEnd_6066823 : Nat := 3115196244752022260811695

theorem tailTrace_6066823 : CollatzResearch.WordTrace tailWord_6066823 prefixEnd_6066823 3115196244752022260811695 := by
  unfold tailWord_6066823
  simp only [CollatzResearch.WordTrace]
  refine ⟨221275213299943876722917123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147516808866629251148611415 221275213299943876722917123)
  ·
    refine ⟨331912819949915815084375685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221275213299943876722917123 331912819949915815084375685)
    ·
      refine ⟨62233653740609215328320441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331912819949915815084375685 62233653740609215328320441)
      ·
        refine ⟨46675240305456911496240331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62233653740609215328320441 46675240305456911496240331)
        ·
          refine ⟨70012860458185367244360497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46675240305456911496240331 70012860458185367244360497)
          ·
            refine ⟨52509645343639025433270373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70012860458185367244360497 52509645343639025433270373)
            ·
              refine ⟨9845558501932317268738195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52509645343639025433270373 9845558501932317268738195)
              ·
                refine ⟨14768337752898475903107293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9845558501932317268738195 14768337752898475903107293)
                ·
                  refine ⟨5538126657336928463665235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14768337752898475903107293 5538126657336928463665235)
                  ·
                    refine ⟨8307189986005392695497853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5538126657336928463665235 8307189986005392695497853)
                    ·
                      refine ⟨3115196244752022260811695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8307189986005392695497853 3115196244752022260811695)
                      ·
                        rfl

theorem cell23_6066823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_6066823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066823 prefixEnd_6066823 := by exact prefixLift 6066823
  have htrace : WordTrace (prefixWord ++ tailWord_6066823) baseStart_6066823 baseEnd_6066823 := by
    simpa [prefixWord, tailWord_6066823, baseEnd_6066823] using wordTrace_append hprefix tailTrace_6066823
  have hstable : (prefixWord ++ tailWord_6066823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066823).length < 2 ^ (prefixWord ++ tailWord_6066823).sum := by decide
  have hdescent : baseEnd_6066823 < baseStart_6066823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066866 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_6066866 : Nat := 118140960795 + 6066866 * 2 ^ 59
def prefixEnd_6066866 : Nat := 4983230072969 + 3 ^ 40 * 6066866 * 2
def baseEnd_6066866 : Nat := 3115218324420165592573997

theorem tailTrace_6066866 : CollatzResearch.WordTrace tailWord_6066866 prefixEnd_6066866 3115218324420165592573997 := by
  unfold tailWord_6066866
  simp only [CollatzResearch.WordTrace]
  refine ⟨55319195409697023766683113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147517854425858730044488301 55319195409697023766683113)
  ·
    refine ⟨41489396557272767825012335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55319195409697023766683113 41489396557272767825012335)
    ·
      refine ⟨62234094835909151737518503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41489396557272767825012335 62234094835909151737518503)
      ·
        refine ⟨93351142253863727606277755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62234094835909151737518503 93351142253863727606277755)
        ·
          refine ⟨140026713380795591409416633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93351142253863727606277755 140026713380795591409416633)
          ·
            refine ⟨105020035035596693557062475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140026713380795591409416633 105020035035596693557062475)
            ·
              refine ⟨157530052553395040335593713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105020035035596693557062475 157530052553395040335593713)
              ·
                refine ⟨118147539415046280251695285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157530052553395040335593713 118147539415046280251695285)
                ·
                  refine ⟨11076331820160588773596433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118147539415046280251695285 11076331820160588773596433)
                  ·
                    refine ⟨8307248865120441580197325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11076331820160588773596433 8307248865120441580197325)
                    ·
                      refine ⟨3115218324420165592573997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8307248865120441580197325 3115218324420165592573997)
                      ·
                        rfl

theorem cell23_6066866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_6066866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066866 prefixEnd_6066866 := by exact prefixLift 6066866
  have htrace : WordTrace (prefixWord ++ tailWord_6066866) baseStart_6066866 baseEnd_6066866 := by
    simpa [prefixWord, tailWord_6066866, baseEnd_6066866] using wordTrace_append hprefix tailTrace_6066866
  have hstable : (prefixWord ++ tailWord_6066866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066866).length < 2 ^ (prefixWord ++ tailWord_6066866).sum := by decide
  have hdescent : baseEnd_6066866 < baseStart_6066866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066880 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 3, 2, 2]
def baseStart_6066880 : Nat := 118140960795 + 6066880 * 2 ^ 59
def prefixEnd_6066880 : Nat := 4983230072969 + 3 ^ 40 * 6066880 * 2
def baseEnd_6066880 : Nat := 3115225513149328537798933

theorem tailTrace_6066880 : CollatzResearch.WordTrace tailWord_6066880 prefixEnd_6066880 3115225513149328537798933 := by
  unfold tailWord_6066880
  simp only [CollatzResearch.WordTrace]
  refine ⟨110638646130368687728871047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147518194840491583638494729 110638646130368687728871047)
  ·
    refine ⟨165957969195553031593306571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110638646130368687728871047 165957969195553031593306571)
    ·
      refine ⟨248936953793329547389959857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165957969195553031593306571 248936953793329547389959857)
      ·
        refine ⟨186702715344997160542469893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248936953793329547389959857 186702715344997160542469893)
        ·
          refine ⟨35006759127186967601713105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186702715344997160542469893 35006759127186967601713105)
          ·
            refine ⟨26255069345390225701284829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35006759127186967601713105 26255069345390225701284829)
            ·
              refine ⟨9845651004521334637981811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26255069345390225701284829 9845651004521334637981811)
              ·
                refine ⟨14768476506782001956972717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9845651004521334637981811 14768476506782001956972717)
                ·
                  refine ⟨5538178690043250733864769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14768476506782001956972717 5538178690043250733864769)
                  ·
                    refine ⟨4153634017532438050398577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5538178690043250733864769 4153634017532438050398577)
                    ·
                      refine ⟨3115225513149328537798933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153634017532438050398577 3115225513149328537798933)
                      ·
                        rfl

theorem cell23_6066880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_6066880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066880 prefixEnd_6066880 := by exact prefixLift 6066880
  have htrace : WordTrace (prefixWord ++ tailWord_6066880) baseStart_6066880 baseEnd_6066880 := by
    simpa [prefixWord, tailWord_6066880, baseEnd_6066880] using wordTrace_append hprefix tailTrace_6066880
  have hstable : (prefixWord ++ tailWord_6066880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066880).length < 2 ^ (prefixWord ++ tailWord_6066880).sum := by decide
  have hdescent : baseEnd_6066880 < baseStart_6066880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066890 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_6066890 : Nat := 118140960795 + 6066890 * 2 ^ 59
def prefixEnd_6066890 : Nat := 4983230072969 + 3 ^ 40 * 6066890 * 2
def baseEnd_6066890 : Nat := 1038410215985291166224629

theorem tailTrace_6066890 : CollatzResearch.WordTrace tailWord_6066890 prefixEnd_6066890 1038410215985291166224629 := by
  unfold tailWord_6066890
  simp only [CollatzResearch.WordTrace]
  refine ⟨55319414247675286791401531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147518437993800764777070749 55319414247675286791401531)
  ·
    refine ⟨82979121371512930187102297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55319414247675286791401531 82979121371512930187102297)
    ·
      refine ⟨62234341028634697640326723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82979121371512930187102297 62234341028634697640326723)
      ·
        refine ⟨93351511542952046460490085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62234341028634697640326723 93351511542952046460490085)
        ·
          refine ⟨17503408414303508711341891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93351511542952046460490085 17503408414303508711341891)
          ·
            refine ⟨26255112621455263067012837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17503408414303508711341891 26255112621455263067012837)
            ·
              refine ⟨4922833616522861825064907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26255112621455263067012837 4922833616522861825064907)
              ·
                refine ⟨7384250424784292737597361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4922833616522861825064907 7384250424784292737597361)
                ·
                  refine ⟨5538187818588219553198021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7384250424784292737597361 5538187818588219553198021)
                  ·
                    refine ⟨1038410215985291166224629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5538187818588219553198021 1038410215985291166224629)
                    ·
                      rfl

theorem cell23_6066890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_6066890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066890 prefixEnd_6066890 := by exact prefixLift 6066890
  have htrace : WordTrace (prefixWord ++ tailWord_6066890) baseStart_6066890 baseEnd_6066890 := by
    simpa [prefixWord, tailWord_6066890, baseEnd_6066890] using wordTrace_append hprefix tailTrace_6066890
  have hstable : (prefixWord ++ tailWord_6066890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066890).length < 2 ^ (prefixWord ++ tailWord_6066890).sum := by decide
  have hdescent : baseEnd_6066890 < baseStart_6066890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066900 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6066900 : Nat := 118140960795 + 6066900 * 2 ^ 59
def prefixEnd_6066900 : Nat := 4983230072969 + 3 ^ 40 * 6066900 * 2
def baseEnd_6066900 : Nat := 3115235782762418459548841

theorem tailTrace_6066900 : CollatzResearch.WordTrace tailWord_6066900 prefixEnd_6066900 3115235782762418459548841 := by
  unfold tailWord_6066900
  simp only [CollatzResearch.WordTrace]
  refine ⟨110639010860332459436735077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147518681147109945915646769 110639010860332459436735077)
  ·
    refine ⟨20744814536312336144387827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110639010860332459436735077 20744814536312336144387827)
    ·
      refine ⟨31117221804468504216581741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20744814536312336144387827 31117221804468504216581741)
      ·
        refine ⟨11668958176675689081218153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31117221804468504216581741 11668958176675689081218153)
        ·
          refine ⟨8751718632506766810913615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11668958176675689081218153 8751718632506766810913615)
          ·
            refine ⟨13127577948760150216370423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751718632506766810913615 13127577948760150216370423)
            ·
              refine ⟨19691366923140225324555635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13127577948760150216370423 19691366923140225324555635)
              ·
                refine ⟨29537050384710337986833453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19691366923140225324555635 29537050384710337986833453)
                ·
                  refine ⟨11076393894266376745062545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29537050384710337986833453 11076393894266376745062545)
                  ·
                    refine ⟨8307295420699782558796909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11076393894266376745062545 8307295420699782558796909)
                    ·
                      refine ⟨3115235782762418459548841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8307295420699782558796909 3115235782762418459548841)
                      ·
                        rfl

theorem cell23_6066900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6066900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066900 prefixEnd_6066900 := by exact prefixLift 6066900
  have htrace : WordTrace (prefixWord ++ tailWord_6066900) baseStart_6066900 baseEnd_6066900 := by
    simpa [prefixWord, tailWord_6066900, baseEnd_6066900] using wordTrace_append hprefix tailTrace_6066900
  have hstable : (prefixWord ++ tailWord_6066900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066900).length < 2 ^ (prefixWord ++ tailWord_6066900).sum := by decide
  have hdescent : baseEnd_6066900 < baseStart_6066900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066913 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_6066913 : Nat := 118140960795 + 6066913 * 2 ^ 59
def prefixEnd_6066913 : Nat := 4983230072969 + 3 ^ 40 * 6066913 * 2
def baseEnd_6066913 : Nat := 3115242458010926908686281

theorem tailTrace_6066913 : CollatzResearch.WordTrace tailWord_6066913 prefixEnd_6066913 3115242458010926908686281 := by
  unfold tailWord_6066913
  simp only [CollatzResearch.WordTrace]
  refine ⟨221278495869617822093693393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147518997246411881395795595 221278495869617822093693393)
  ·
    refine ⟨165958871902213366570270045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221278495869617822093693393 165958871902213366570270045)
    ·
      refine ⟨62234576963330012463851267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165958871902213366570270045 62234576963330012463851267)
      ·
        refine ⟨93351865444995018695776901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62234576963330012463851267 93351865444995018695776901)
        ·
          refine ⟨17503474770936566005458169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93351865444995018695776901 17503474770936566005458169)
          ·
            refine ⟨13127606078202424504093627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17503474770936566005458169 13127606078202424504093627)
            ·
              refine ⟨19691409117303636756140441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13127606078202424504093627 19691409117303636756140441)
              ·
                refine ⟨14768556837977727567105331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19691409117303636756140441 14768556837977727567105331)
                ·
                  refine ⟨22152835256966591350657997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14768556837977727567105331 22152835256966591350657997)
                  ·
                    refine ⟨8307313221362471756496749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22152835256966591350657997 8307313221362471756496749)
                    ·
                      refine ⟨3115242458010926908686281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8307313221362471756496749 3115242458010926908686281)
                      ·
                        rfl

theorem cell23_6066913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_6066913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066913 prefixEnd_6066913 := by exact prefixLift 6066913
  have htrace : WordTrace (prefixWord ++ tailWord_6066913) baseStart_6066913 baseEnd_6066913 := by
    simpa [prefixWord, tailWord_6066913, baseEnd_6066913] using wordTrace_append hprefix tailTrace_6066913
  have hstable : (prefixWord ++ tailWord_6066913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066913).length < 2 ^ (prefixWord ++ tailWord_6066913).sum := by decide
  have hdescent : baseEnd_6066913 < baseStart_6066913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066930 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_6066930 : Nat := 118140960795 + 6066930 * 2 ^ 59
def prefixEnd_6066930 : Nat := 4983230072969 + 3 ^ 40 * 6066930 * 2
def baseEnd_6066930 : Nat := 3115251187182053342173703

theorem tailTrace_6066930 : CollatzResearch.WordTrace tailWord_6066930 prefixEnd_6066930 3115251187182053342173703 := by
  unfold tailWord_6066930
  simp only [CollatzResearch.WordTrace]
  refine ⟨55319778977639058499265561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147519410607037489331374829 55319778977639058499265561)
  ·
    refine ⟨41489834233229293874449171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55319778977639058499265561 41489834233229293874449171)
    ·
      refine ⟨62234751349843940811673757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41489834233229293874449171 62234751349843940811673757)
      ·
        refine ⟨23338031756191477804377659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62234751349843940811673757 23338031756191477804377659)
        ·
          refine ⟨35007047634287216706566489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23338031756191477804377659 35007047634287216706566489)
          ·
            refine ⟨26255285725715412529924867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35007047634287216706566489 26255285725715412529924867)
            ·
              refine ⟨39382928588573118794887301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26255285725715412529924867 39382928588573118794887301)
              ·
                refine ⟨7384299110357459774041369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39382928588573118794887301 7384299110357459774041369)
                ·
                  refine ⟨5538224332768094830531027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7384299110357459774041369 5538224332768094830531027)
                  ·
                    refine ⟨8307336499152142245796541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5538224332768094830531027 8307336499152142245796541)
                    ·
                      refine ⟨3115251187182053342173703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8307336499152142245796541 3115251187182053342173703)
                      ·
                        rfl

theorem cell23_6066930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_6066930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066930 prefixEnd_6066930 := by exact prefixLift 6066930
  have htrace : WordTrace (prefixWord ++ tailWord_6066930) baseStart_6066930 baseEnd_6066930 := by
    simpa [prefixWord, tailWord_6066930, baseEnd_6066930] using wordTrace_append hprefix tailTrace_6066930
  have hstable : (prefixWord ++ tailWord_6066930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066930).length < 2 ^ (prefixWord ++ tailWord_6066930).sum := by decide
  have hdescent : baseEnd_6066930 < baseStart_6066930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066953 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 1, 4, 2]
def baseStart_6066953 : Nat := 118140960795 + 6066953 * 2 ^ 59
def prefixEnd_6066953 : Nat := 4983230072969 + 3 ^ 40 * 6066953 * 2
def baseEnd_6066953 : Nat := 3115262997237106752186097

theorem tailTrace_6066953 : CollatzResearch.WordTrace tailWord_6066953 prefixEnd_6066953 3115262997237106752186097 := by
  unfold tailWord_6066953
  simp only [CollatzResearch.WordTrace]
  refine ⟨221279954789472908925149513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147519969859648605950099675 221279954789472908925149513)
  ·
    refine ⟨165959966092104681693862135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221279954789472908925149513 165959966092104681693862135)
    ·
      refine ⟨248939949138157022540793203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165959966092104681693862135 248939949138157022540793203)
      ·
        refine ⟨373409923707235533811189805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248939949138157022540793203 373409923707235533811189805)
        ·
          refine ⟨140028721390213325179196177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373409923707235533811189805 140028721390213325179196177)
          ·
            refine ⟨105021541042659993884397133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140028721390213325179196177 105021541042659993884397133)
            ·
              refine ⟨39383077890997497706648925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105021541042659993884397133 39383077890997497706648925)
              ·
                refine ⟨14768654209124061639993347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39383077890997497706648925 14768654209124061639993347)
                ·
                  refine ⟨22152981313686092459990021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14768654209124061639993347 22152981313686092459990021)
                  ·
                    refine ⟨4153683996316142336248129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22152981313686092459990021 4153683996316142336248129)
                    ·
                      refine ⟨3115262997237106752186097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153683996316142336248129 3115262997237106752186097)
                      ·
                        rfl

theorem cell23_6066953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 4, 2].length) (baseStart_6066953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066953 prefixEnd_6066953 := by exact prefixLift 6066953
  have htrace : WordTrace (prefixWord ++ tailWord_6066953) baseStart_6066953 baseEnd_6066953 := by
    simpa [prefixWord, tailWord_6066953, baseEnd_6066953] using wordTrace_append hprefix tailTrace_6066953
  have hstable : (prefixWord ++ tailWord_6066953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066953).length < 2 ^ (prefixWord ++ tailWord_6066953).sum := by decide
  have hdescent : baseEnd_6066953 < baseStart_6066953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066956 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_6066956 : Nat := 118140960795 + 6066956 * 2 ^ 59
def prefixEnd_6066956 : Nat := 4983230072969 + 3 ^ 40 * 6066956 * 2
def baseEnd_6066956 : Nat := 3115264537679070240448583

theorem tailTrace_6066956 : CollatzResearch.WordTrace tailWord_6066956 prefixEnd_6066956 3115264537679070240448583 := by
  unfold tailWord_6066956
  simp only [CollatzResearch.WordTrace]
  refine ⟨110640032104231020218754361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147520042805641360291672481 110640032104231020218754361)
  ·
    refine ⟨82980024078173265164065771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110640032104231020218754361 82980024078173265164065771)
    ·
      refine ⟨124470036117259897746098657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82980024078173265164065771 124470036117259897746098657)
      ·
        refine ⟨93352527087944923309573993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124470036117259897746098657 93352527087944923309573993)
        ·
          refine ⟨70014395315958692482180495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93352527087944923309573993 70014395315958692482180495)
          ·
            refine ⟨105021592973938038723270743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70014395315958692482180495 105021592973938038723270743)
            ·
              refine ⟨157532389460907058084906115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105021592973938038723270743 157532389460907058084906115)
              ·
                refine ⟨236298584191360587127359173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157532389460907058084906115 236298584191360587127359173)
                ·
                  refine ⟨44305984535880110086379845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236298584191360587127359173 44305984535880110086379845)
                  ·
                    refine ⟨8307372100477520641196221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44305984535880110086379845 8307372100477520641196221)
                    ·
                      refine ⟨3115264537679070240448583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8307372100477520641196221 3115264537679070240448583)
                      ·
                        rfl

theorem cell23_6066956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_6066956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066956 prefixEnd_6066956 := by exact prefixLift 6066956
  have htrace : WordTrace (prefixWord ++ tailWord_6066956) baseStart_6066956 baseEnd_6066956 := by
    simpa [prefixWord, tailWord_6066956, baseEnd_6066956] using wordTrace_append hprefix tailTrace_6066956
  have hstable : (prefixWord ++ tailWord_6066956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066956).length < 2 ^ (prefixWord ++ tailWord_6066956).sum := by decide
  have hdescent : baseEnd_6066956 < baseStart_6066956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066970 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2]
def baseStart_6066970 : Nat := 118140960795 + 6066970 * 2 ^ 59
def prefixEnd_6066970 : Nat := 4983230072969 + 3 ^ 40 * 6066970 * 2
def baseEnd_6066970 : Nat := 3115271726408233185673519

theorem tailTrace_6066970 : CollatzResearch.WordTrace tailWord_6066970 prefixEnd_6066970 3115271726408233185673519 := by
  unfold tailWord_6066970
  simp only [CollatzResearch.WordTrace]
  refine ⟨55320143707602830207129591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147520383220274213885678909 55320143707602830207129591)
  ·
    refine ⟨82980215561404245310694387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55320143707602830207129591 82980215561404245310694387)
    ·
      refine ⟨124470323342106367966041581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82980215561404245310694387 124470323342106367966041581)
      ·
        refine ⟨46676371253289887987265593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124470323342106367966041581 46676371253289887987265593)
        ·
          refine ⟨35007278439967415990449195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46676371253289887987265593 35007278439967415990449195)
          ·
            refine ⟨52510917659951123985673793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35007278439967415990449195 52510917659951123985673793)
            ·
              refine ⟨39383188244963342989255345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52510917659951123985673793 39383188244963342989255345)
              ·
                refine ⟨29537391183722507241941509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39383188244963342989255345 29537391183722507241941509)
                ·
                  refine ⟨5538260846947970107864033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29537391183722507241941509 5538260846947970107864033)
                  ·
                    refine ⟨4153695635210977580898025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5538260846947970107864033 4153695635210977580898025)
                    ·
                      refine ⟨3115271726408233185673519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153695635210977580898025 3115271726408233185673519)
                      ·
                        rfl

theorem cell23_6066970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_6066970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066970 prefixEnd_6066970 := by exact prefixLift 6066970
  have htrace : WordTrace (prefixWord ++ tailWord_6066970) baseStart_6066970 baseEnd_6066970 := by
    simpa [prefixWord, tailWord_6066970, baseEnd_6066970] using wordTrace_append hprefix tailTrace_6066970
  have hstable : (prefixWord ++ tailWord_6066970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066970).length < 2 ^ (prefixWord ++ tailWord_6066970).sum := by decide
  have hdescent : baseEnd_6066970 < baseStart_6066970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6066993 : List Nat := [1, 2, 2, 3, 2, 1, 1, 6, 5]
def baseStart_6066993 : Nat := 118140960795 + 6066993 * 2 ^ 59
def prefixEnd_6066993 : Nat := 4983230072969 + 3 ^ 40 * 6066993 * 2
def baseEnd_6066993 : Nat := 346142615162587399520657

theorem tailTrace_6066993 : CollatzResearch.WordTrace tailWord_6066993 prefixEnd_6066993 346142615162587399520657 := by
  unfold tailWord_6066993
  simp only [CollatzResearch.WordTrace]
  refine ⟨221281413709327995756605633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147520942472885330504403755 221281413709327995756605633)
  ·
    refine ⟨165961060281995996817454225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221281413709327995756605633 165961060281995996817454225)
    ·
      refine ⟨124470795211496997613090669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165961060281995996817454225 124470795211496997613090669)
      ·
        refine ⟨46676548204311374104909001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124470795211496997613090669 46676548204311374104909001)
        ·
          refine ⟨35007411153233530578681751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46676548204311374104909001 35007411153233530578681751)
          ·
            refine ⟨52511116729850295868022627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35007411153233530578681751 52511116729850295868022627)
            ·
              refine ⟨78766675094775443802033941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52511116729850295868022627 78766675094775443802033941)
              ·
                refine ⟨3692187895067598928220341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78766675094775443802033941 3692187895067598928220341)
                ·
                  refine ⟨346142615162587399520657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3692187895067598928220341 346142615162587399520657)
                  ·
                    rfl

theorem cell23_6066993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 5].length) (baseStart_6066993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6066993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6066993 prefixEnd_6066993 := by exact prefixLift 6066993
  have htrace : WordTrace (prefixWord ++ tailWord_6066993) baseStart_6066993 baseEnd_6066993 := by
    simpa [prefixWord, tailWord_6066993, baseEnd_6066993] using wordTrace_append hprefix tailTrace_6066993
  have hstable : (prefixWord ++ tailWord_6066993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6066993).length < 2 ^ (prefixWord ++ tailWord_6066993).sum := by decide
  have hdescent : baseEnd_6066993 < baseStart_6066993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6066993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067043 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 4]
def baseStart_6067043 : Nat := 118140960795 + 6067043 * 2 ^ 59
def prefixEnd_6067043 : Nat := 4983230072969 + 3 ^ 40 * 6067043 * 2
def baseEnd_6067043 : Nat := 3115309210496011400060683

theorem tailTrace_6067043 : CollatzResearch.WordTrace tailWord_6067043 prefixEnd_6067043 3115309210496011400060683 := by
  unfold tailWord_6067043
  simp only [CollatzResearch.WordTrace]
  refine ⟨221283237359146854295925783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147522158239431236197283855 221283237359146854295925783)
  ·
    refine ⟨331924856038720281443888675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221283237359146854295925783 331924856038720281443888675)
    ·
      refine ⟨497887284058080422165833013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331924856038720281443888675 497887284058080422165833013)
      ·
        refine ⟨46676932880445039578046845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 497887284058080422165833013 46676932880445039578046845)
        ·
          refine ⟨17503849830166889841767567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46676932880445039578046845 17503849830166889841767567)
          ·
            refine ⟨26255774745250334762651351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17503849830166889841767567 26255774745250334762651351)
            ·
              refine ⟨39383662117875502143977027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26255774745250334762651351 39383662117875502143977027)
              ·
                refine ⟨59075493176813253215965541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39383662117875502143977027 59075493176813253215965541)
                ·
                  refine ⟨11076654970652484977993539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59075493176813253215965541 11076654970652484977993539)
                  ·
                    refine ⟨16614982455978727466990309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11076654970652484977993539 16614982455978727466990309)
                    ·
                      refine ⟨3115309210496011400060683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16614982455978727466990309 3115309210496011400060683)
                      ·
                        rfl

theorem cell23_6067043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_6067043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067043 prefixEnd_6067043 := by exact prefixLift 6067043
  have htrace : WordTrace (prefixWord ++ tailWord_6067043) baseStart_6067043 baseEnd_6067043 := by
    simpa [prefixWord, tailWord_6067043, baseEnd_6067043] using wordTrace_append hprefix tailTrace_6067043
  have hstable : (prefixWord ++ tailWord_6067043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067043).length < 2 ^ (prefixWord ++ tailWord_6067043).sum := by decide
  have hdescent : baseEnd_6067043 < baseStart_6067043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067056 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_6067056 : Nat := 118140960795 + 6067056 * 2 ^ 59
def prefixEnd_6067056 : Nat := 4983230072969 + 3 ^ 40 * 6067056 * 2
def baseEnd_6067056 : Nat := 3115315885744519849198123

theorem tailTrace_6067056 : CollatzResearch.WordTrace tailWord_6067056 prefixEnd_6067056 3115315885744519849198123 := by
  unfold tailWord_6067056
  simp only [CollatzResearch.WordTrace]
  refine ⟨110641855754049878758074511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147522474338733171677432681 110641855754049878758074511)
  ·
    refine ⟨165962783631074818137111767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110641855754049878758074511 165962783631074818137111767)
    ·
      refine ⟨248944175446612227205667651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165962783631074818137111767 248944175446612227205667651)
      ·
        refine ⟨373416263169918340808501477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248944175446612227205667651 373416263169918340808501477)
        ·
          refine ⟨70015549344359688901594027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 373416263169918340808501477 70015549344359688901594027)
          ·
            refine ⟨105023324016539533352391041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70015549344359688901594027 105023324016539533352391041)
            ·
              refine ⟨78767493012404650014293281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105023324016539533352391041 78767493012404650014293281)
              ·
                refine ⟨59075619759303487510719961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78767493012404650014293281 59075619759303487510719961)
                ·
                  refine ⟨44306714819477615633039971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59075619759303487510719961 44306714819477615633039971)
                  ·
                    refine ⟨66460072229216423449559957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44306714819477615633039971 66460072229216423449559957)
                    ·
                      refine ⟨3115315885744519849198123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66460072229216423449559957 3115315885744519849198123)
                      ·
                        rfl

theorem cell23_6067056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_6067056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067056 prefixEnd_6067056 := by exact prefixLift 6067056
  have htrace : WordTrace (prefixWord ++ tailWord_6067056) baseStart_6067056 baseEnd_6067056 := by
    simpa [prefixWord, tailWord_6067056, baseEnd_6067056] using wordTrace_append hprefix tailTrace_6067056
  have hstable : (prefixWord ++ tailWord_6067056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067056).length < 2 ^ (prefixWord ++ tailWord_6067056).sum := by decide
  have hdescent : baseEnd_6067056 < baseStart_6067056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067074 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6067074 : Nat := 118140960795 + 6067074 * 2 ^ 59
def prefixEnd_6067074 : Nat := 4983230072969 + 3 ^ 40 * 6067074 * 2
def baseEnd_6067074 : Nat := 1038441709465433592924347

theorem tailTrace_6067074 : CollatzResearch.WordTrace tailWord_6067074 prefixEnd_6067074 1038441709465433592924347 := by
  unfold tailWord_6067074
  simp only [CollatzResearch.WordTrace]
  refine ⟨55321092005508636647576069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147522912014689697726869517 55321092005508636647576069)
  ·
    refine ⟨10372704751032869371420513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55321092005508636647576069 10372704751032869371420513)
    ·
      refine ⟨7779528563274652028565385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10372704751032869371420513 7779528563274652028565385)
      ·
        refine ⟨5834646422455989021424039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7779528563274652028565385 5834646422455989021424039)
        ·
          refine ⟨8751969633683983532136059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5834646422455989021424039 8751969633683983532136059)
          ·
            refine ⟨13127954450525975298204089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751969633683983532136059 13127954450525975298204089)
            ·
              refine ⟨9845965837894481473653067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13127954450525975298204089 9845965837894481473653067)
              ·
                refine ⟨14768948756841722210479601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9845965837894481473653067 14768948756841722210479601)
                ·
                  refine ⟨11076711567631291657859701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14768948756841722210479601 11076711567631291657859701)
                  ·
                    refine ⟨1038441709465433592924347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11076711567631291657859701 1038441709465433592924347)
                    ·
                      rfl

theorem cell23_6067074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6067074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067074 prefixEnd_6067074 := by exact prefixLift 6067074
  have htrace : WordTrace (prefixWord ++ tailWord_6067074) baseStart_6067074 baseEnd_6067074 := by
    simpa [prefixWord, tailWord_6067074, baseEnd_6067074] using wordTrace_append hprefix tailTrace_6067074
  have hstable : (prefixWord ++ tailWord_6067074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067074).length < 2 ^ (prefixWord ++ tailWord_6067074).sum := by decide
  have hdescent : baseEnd_6067074 < baseStart_6067074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067080 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_6067080 : Nat := 118140960795 + 6067080 * 2 ^ 59
def prefixEnd_6067080 : Nat := 4983230072969 + 3 ^ 40 * 6067080 * 2
def baseEnd_6067080 : Nat := 3115328209280227755298013

theorem tailTrace_6067080 : CollatzResearch.WordTrace tailWord_6067080 prefixEnd_6067080 3115328209280227755298013 := by
  unfold tailWord_6067080
  simp only [CollatzResearch.WordTrace]
  refine ⟨110642293430006404807511347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147523057906675206410015129 110642293430006404807511347)
  ·
    refine ⟨165963440145009607211267021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110642293430006404807511347 165963440145009607211267021)
    ·
      refine ⟨62236290054378602704225133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165963440145009607211267021 62236290054378602704225133)
      ·
        refine ⟨23338608770391976014084425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62236290054378602704225133 23338608770391976014084425)
        ·
          refine ⟨17503956577793982010563319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23338608770391976014084425 17503956577793982010563319)
          ·
            refine ⟨26255934866690973015844979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17503956577793982010563319 26255934866690973015844979)
            ·
              refine ⟨39383902300036459523767469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26255934866690973015844979 39383902300036459523767469)
              ·
                refine ⟨14768963362513672321412801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39383902300036459523767469 14768963362513672321412801)
                ·
                  refine ⟨11076722521885254241059601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14768963362513672321412801 11076722521885254241059601)
                  ·
                    refine ⟨8307541891413940680794701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11076722521885254241059601 8307541891413940680794701)
                    ·
                      refine ⟨3115328209280227755298013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8307541891413940680794701 3115328209280227755298013)
                      ·
                        rfl

theorem cell23_6067080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_6067080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067080 prefixEnd_6067080 := by exact prefixLift 6067080
  have htrace : WordTrace (prefixWord ++ tailWord_6067080) baseStart_6067080 baseEnd_6067080 := by
    simpa [prefixWord, tailWord_6067080, baseEnd_6067080] using wordTrace_append hprefix tailTrace_6067080
  have hstable : (prefixWord ++ tailWord_6067080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067080).length < 2 ^ (prefixWord ++ tailWord_6067080).sum := by decide
  have hdescent : baseEnd_6067080 < baseStart_6067080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067094 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6067094 : Nat := 118140960795 + 6067094 * 2 ^ 59
def prefixEnd_6067094 : Nat := 4983230072969 + 3 ^ 40 * 6067094 * 2
def baseEnd_6067094 : Nat := 3115335398009390700522949

theorem tailTrace_6067094 : CollatzResearch.WordTrace tailWord_6067094 prefixEnd_6067094 3115335398009390700522949 := by
  unfold tailWord_6067094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13830318592622630625377021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147523398321308060004021557 13830318592622630625377021)
  ·
    refine ⟨5186369472233486484516383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13830318592622630625377021 5186369472233486484516383)
    ·
      refine ⟨7779554208350229726774575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5186369472233486484516383 7779554208350229726774575)
      ·
        refine ⟨11669331312525344590161863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7779554208350229726774575 11669331312525344590161863)
        ·
          refine ⟨17503996968788016885242795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11669331312525344590161863 17503996968788016885242795)
          ·
            refine ⟨26255995453182025327864193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17503996968788016885242795 26255995453182025327864193)
            ·
              refine ⟨19691996589886518995898145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26255995453182025327864193 19691996589886518995898145)
              ·
                refine ⟨14768997442414889246923609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19691996589886518995898145 14768997442414889246923609)
                ·
                  refine ⟨11076748081811166935192707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14768997442414889246923609 11076748081811166935192707)
                  ·
                    refine ⟨16615122122716750402789061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11076748081811166935192707 16615122122716750402789061)
                    ·
                      refine ⟨3115335398009390700522949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16615122122716750402789061 3115335398009390700522949)
                      ·
                        rfl

theorem cell23_6067094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6067094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067094 prefixEnd_6067094 := by exact prefixLift 6067094
  have htrace : WordTrace (prefixWord ++ tailWord_6067094) baseStart_6067094 baseEnd_6067094 := by
    simpa [prefixWord, tailWord_6067094, baseEnd_6067094] using wordTrace_append hprefix tailTrace_6067094
  have hstable : (prefixWord ++ tailWord_6067094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067094).length < 2 ^ (prefixWord ++ tailWord_6067094).sum := by decide
  have hdescent : baseEnd_6067094 < baseStart_6067094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067143 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 1, 6]
def baseStart_6067143 : Nat := 118140960795 + 6067143 * 2 ^ 59
def prefixEnd_6067143 : Nat := 4983230072969 + 3 ^ 40 * 6067143 * 2
def baseEnd_6067143 : Nat := 1038453519520487002936741

theorem tailTrace_6067143 : CollatzResearch.WordTrace tailWord_6067143 prefixEnd_6067143 1038453519520487002936741 := by
  unfold tailWord_6067143
  simp only [CollatzResearch.WordTrace]
  refine ⟨221286884658784571374566083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147524589772523047583044055 221286884658784571374566083)
  ·
    refine ⟨331930326988176857061849125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221286884658784571374566083 331930326988176857061849125)
    ·
      refine ⟨62236936310283160699096711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331930326988176857061849125 62236936310283160699096711)
      ·
        refine ⟨93355404465424741048645067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62236936310283160699096711 93355404465424741048645067)
        ·
          refine ⟨140033106698137111572967601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93355404465424741048645067 140033106698137111572967601)
          ·
            refine ⟨105024830023602833679725701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140033106698137111572967601 105024830023602833679725701)
            ·
              refine ⟨19692155629425531314948569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105024830023602833679725701 19692155629425531314948569)
              ·
                refine ⟨14769116722069148486211427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19692155629425531314948569 14769116722069148486211427)
                ·
                  refine ⟨22153675083103722729317141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14769116722069148486211427 22153675083103722729317141)
                  ·
                    refine ⟨1038453519520487002936741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22153675083103722729317141 1038453519520487002936741)
                    ·
                      rfl

theorem cell23_6067143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_6067143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067143 prefixEnd_6067143 := by exact prefixLift 6067143
  have htrace : WordTrace (prefixWord ++ tailWord_6067143) baseStart_6067143 baseEnd_6067143 := by
    simpa [prefixWord, tailWord_6067143, baseEnd_6067143] using wordTrace_append hprefix tailTrace_6067143
  have hstable : (prefixWord ++ tailWord_6067143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067143).length < 2 ^ (prefixWord ++ tailWord_6067143).sum := by decide
  have hdescent : baseEnd_6067143 < baseStart_6067143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067147 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 1, 5]
def baseStart_6067147 : Nat := 118140960795 + 6067147 * 2 ^ 59
def prefixEnd_6067147 : Nat := 4983230072969 + 3 ^ 40 * 6067147 * 2
def baseEnd_6067147 : Nat := 1038454204161359664386735

theorem tailTrace_6067147 : CollatzResearch.WordTrace tailWord_6067147 prefixEnd_6067147 1038454204161359664386735 := by
  unfold tailWord_6067147
  simp only [CollatzResearch.WordTrace]
  refine ⟨221287030550770080057711695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147524687033846720038474463 221287030550770080057711695)
  ·
    refine ⟨331930545826155120086567543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221287030550770080057711695 331930545826155120086567543)
    ·
      refine ⟨497895818739232680129851315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331930545826155120086567543 497895818739232680129851315)
      ·
        refine ⟨746843728108849020194776973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497895818739232680129851315 746843728108849020194776973)
        ·
          refine ⟨280066398040818382573041365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 746843728108849020194776973 280066398040818382573041365)
          ·
            refine ⟨6564056204081680841555657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 280066398040818382573041365 6564056204081680841555657)
            ·
              refine ⟨4923042153061260631166743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6564056204081680841555657 4923042153061260631166743)
              ·
                refine ⟨7384563229591890946750115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923042153061260631166743 7384563229591890946750115)
                ·
                  refine ⟨11076844844387836420125173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7384563229591890946750115 11076844844387836420125173)
                  ·
                    refine ⟨1038454204161359664386735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11076844844387836420125173 1038454204161359664386735)
                    ·
                      rfl

theorem cell23_6067147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 5].length) (baseStart_6067147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067147 prefixEnd_6067147 := by exact prefixLift 6067147
  have htrace : WordTrace (prefixWord ++ tailWord_6067147) baseStart_6067147 baseEnd_6067147 := by
    simpa [prefixWord, tailWord_6067147, baseEnd_6067147] using wordTrace_append hprefix tailTrace_6067147
  have hstable : (prefixWord ++ tailWord_6067147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067147).length < 2 ^ (prefixWord ++ tailWord_6067147).sum := by decide
  have hdescent : baseEnd_6067147 < baseStart_6067147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067153 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_6067153 : Nat := 118140960795 + 6067153 * 2 ^ 59
def prefixEnd_6067153 : Nat := 4983230072969 + 3 ^ 40 * 6067153 * 2
def baseEnd_6067153 : Nat := 3115365693368005969685177

theorem tailTrace_6067153 : CollatzResearch.WordTrace tailWord_6067153 prefixEnd_6067153 3115365693368005969685177 := by
  unfold tailWord_6067153
  simp only [CollatzResearch.WordTrace]
  refine ⟨221287249388748343082430113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147524832925832228721620075 221287249388748343082430113)
  ·
    refine ⟨165965437041561257311822585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221287249388748343082430113 165965437041561257311822585)
    ·
      refine ⟨124474077781170942983866939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165965437041561257311822585 124474077781170942983866939)
      ·
        refine ⟨186711116671756414475800409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124474077781170942983866939 186711116671756414475800409)
        ·
          refine ⟨140033337503817310856850307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186711116671756414475800409 140033337503817310856850307)
          ·
            refine ⟨210050006255725966285275461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140033337503817310856850307 210050006255725966285275461)
            ·
              refine ⟨39384376172948618678489149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210050006255725966285275461 39384376172948618678489149)
              ·
                refine ⟨14769141064855732004433431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39384376172948618678489149 14769141064855732004433431)
                ·
                  refine ⟨22153711597283598006650147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14769141064855732004433431 22153711597283598006650147)
                  ·
                    refine ⟨33230567395925397009975221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22153711597283598006650147 33230567395925397009975221)
                    ·
                      refine ⟨3115365693368005969685177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33230567395925397009975221 3115365693368005969685177)
                      ·
                        rfl

theorem cell23_6067153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_6067153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067153 prefixEnd_6067153 := by exact prefixLift 6067153
  have htrace : WordTrace (prefixWord ++ tailWord_6067153) baseStart_6067153 baseEnd_6067153 := by
    simpa [prefixWord, tailWord_6067153, baseEnd_6067153] using wordTrace_append hprefix tailTrace_6067153
  have hstable : (prefixWord ++ tailWord_6067153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067153).length < 2 ^ (prefixWord ++ tailWord_6067153).sum := by decide
  have hdescent : baseEnd_6067153 < baseStart_6067153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067160 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 4, 4]
def baseStart_6067160 : Nat := 118140960795 + 6067160 * 2 ^ 59
def prefixEnd_6067160 : Nat := 4983230072969 + 3 ^ 40 * 6067160 * 2
def baseEnd_6067160 : Nat := 1038456429244195814099215

theorem tailTrace_6067160 : CollatzResearch.WordTrace tailWord_6067160 prefixEnd_6067160 1038456429244195814099215 := by
  unfold tailWord_6067160
  simp only [CollatzResearch.WordTrace]
  refine ⟨110643752349861491638967467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147525003133148655518623289 110643752349861491638967467)
  ·
    refine ⟨165965628524792237458451201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110643752349861491638967467 165965628524792237458451201)
    ·
      refine ⟨124474221393594178093838401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165965628524792237458451201 124474221393594178093838401)
      ·
        refine ⟨93355666045195633570378801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124474221393594178093838401 93355666045195633570378801)
        ·
          refine ⟨70016749533896725177784101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93355666045195633570378801 70016749533896725177784101)
          ·
            refine ⟨13128140537605635970834519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70016749533896725177784101 13128140537605635970834519)
            ·
              refine ⟨19692210806408453956251779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13128140537605635970834519 19692210806408453956251779)
              ·
                refine ⟨29538316209612680934377669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19692210806408453956251779 29538316209612680934377669)
                ·
                  refine ⟨5538434289302377675195813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29538316209612680934377669 5538434289302377675195813)
                  ·
                    refine ⟨1038456429244195814099215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5538434289302377675195813 1038456429244195814099215)
                    ·
                      rfl

theorem cell23_6067160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_6067160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067160 prefixEnd_6067160 := by exact prefixLift 6067160
  have htrace : WordTrace (prefixWord ++ tailWord_6067160) baseStart_6067160 baseEnd_6067160 := by
    simpa [prefixWord, tailWord_6067160, baseEnd_6067160] using wordTrace_append hprefix tailTrace_6067160
  have hstable : (prefixWord ++ tailWord_6067160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067160).length < 2 ^ (prefixWord ++ tailWord_6067160).sum := by decide
  have hdescent : baseEnd_6067160 < baseStart_6067160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067190 : List Nat := [5, 1, 1, 1, 3, 2, 1, 9]
def baseStart_6067190 : Nat := 118140960795 + 6067190 * 2 ^ 59
def prefixEnd_6067190 : Nat := 4983230072969 + 3 ^ 40 * 6067190 * 2
def baseEnd_6067190 : Nat := 115384618227860086108241

theorem tailTrace_6067190 : CollatzResearch.WordTrace tailWord_6067190 prefixEnd_6067190 115384618227860086108241 := by
  unfold tailWord_6067190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13830537430600893650095439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147525732593076198934351349 13830537430600893650095439)
  ·
    refine ⟨20745806145901340475143159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13830537430600893650095439 20745806145901340475143159)
    ·
      refine ⟨31118709218852010712714739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20745806145901340475143159 31118709218852010712714739)
      ·
        refine ⟨46678063828278016069072109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31118709218852010712714739 46678063828278016069072109)
        ·
          refine ⟨17504273935604256025902041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46678063828278016069072109 17504273935604256025902041)
          ·
            refine ⟨13128205451703192019426531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17504273935604256025902041 13128205451703192019426531)
            ·
              refine ⟨19692308177554788029139797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13128205451703192019426531 19692308177554788029139797)
              ·
                refine ⟨115384618227860086108241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19692308177554788029139797 115384618227860086108241)
                ·
                  rfl

theorem cell23_6067190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_6067190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067190 prefixEnd_6067190 := by exact prefixLift 6067190
  have htrace : WordTrace (prefixWord ++ tailWord_6067190) baseStart_6067190 baseEnd_6067190 := by
    simpa [prefixWord, tailWord_6067190, baseEnd_6067190] using wordTrace_append hprefix tailTrace_6067190
  have hstable : (prefixWord ++ tailWord_6067190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067190).length < 2 ^ (prefixWord ++ tailWord_6067190).sum := by decide
  have hdescent : baseEnd_6067190 < baseStart_6067190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067201 : List Nat := [1, 2, 4, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_6067201 : Nat := 118140960795 + 6067201 * 2 ^ 59
def prefixEnd_6067201 : Nat := 4983230072969 + 3 ^ 40 * 6067201 * 2
def baseEnd_6067201 : Nat := 3115390340439421781884957

theorem tailTrace_6067201 : CollatzResearch.WordTrace tailWord_6067201 prefixEnd_6067201 3115390340439421781884957 := by
  unfold tailWord_6067201
  simp only [CollatzResearch.WordTrace]
  refine ⟨221289000092574447280177457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147526000061716298186784971 221289000092574447280177457)
  ·
    refine ⟨165966750069430835460133093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221289000092574447280177457 165966750069430835460133093)
    ·
      refine ⟨31118765638018281648774955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165966750069430835460133093 31118765638018281648774955)
      ·
        refine ⟨46678148457027422473162433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31118765638018281648774955 46678148457027422473162433)
        ·
          refine ⟨35008611342770566854871825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46678148457027422473162433 35008611342770566854871825)
          ·
            refine ⟨26256458507077925141153869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35008611342770566854871825 26256458507077925141153869)
            ·
              refine ⟨9846171940154221927932701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26256458507077925141153869 9846171940154221927932701)
              ·
                refine ⟨3692314477557833222974763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9846171940154221927932701 3692314477557833222974763)
                ·
                  refine ⟨5538471716336749834462145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692314477557833222974763 5538471716336749834462145)
                  ·
                    refine ⟨4153853787252562375846609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5538471716336749834462145 4153853787252562375846609)
                    ·
                      refine ⟨3115390340439421781884957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153853787252562375846609 3115390340439421781884957)
                      ·
                        rfl

theorem cell23_6067201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_6067201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067201 prefixEnd_6067201 := by exact prefixLift 6067201
  have htrace : WordTrace (prefixWord ++ tailWord_6067201) baseStart_6067201 baseEnd_6067201 := by
    simpa [prefixWord, tailWord_6067201, baseEnd_6067201] using wordTrace_append hprefix tailTrace_6067201
  have hstable : (prefixWord ++ tailWord_6067201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067201).length < 2 ^ (prefixWord ++ tailWord_6067201).sum := by decide
  have hdescent : baseEnd_6067201 < baseStart_6067201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067234 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_6067234 : Nat := 118140960795 + 6067234 * 2 ^ 59
def prefixEnd_6067234 : Nat := 4983230072969 + 3 ^ 40 * 6067234 * 2
def baseEnd_6067234 : Nat := 3115407285301020152772305

theorem tailTrace_6067234 : CollatzResearch.WordTrace tailWord_6067234 prefixEnd_6067234 3115407285301020152772305 := by
  unfold tailWord_6067234
  simp only [CollatzResearch.WordTrace]
  refine ⟨55322550925363723479032189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147526802467636595944085837 55322550925363723479032189)
  ·
    refine ⟨20745956597011396304637071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55322550925363723479032189 20745956597011396304637071)
    ·
      refine ⟨31118934895517094456955607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20745956597011396304637071 31118934895517094456955607)
      ·
        refine ⟨46678402343275641685433411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31118934895517094456955607 46678402343275641685433411)
        ·
          refine ⟨70017603514913462528150117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46678402343275641685433411 70017603514913462528150117)
          ·
            refine ⟨13128300659046274224028147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70017603514913462528150117 13128300659046274224028147)
            ·
              refine ⟨19692450988569411336042221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13128300659046274224028147 19692450988569411336042221)
              ·
                refine ⟨7384669120713529251015833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19692450988569411336042221 7384669120713529251015833)
                ·
                  refine ⟨5538501840535146938261875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7384669120713529251015833 5538501840535146938261875)
                  ·
                    refine ⟨8307752760802720407392813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5538501840535146938261875 8307752760802720407392813)
                    ·
                      refine ⟨3115407285301020152772305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8307752760802720407392813 3115407285301020152772305)
                      ·
                        rfl

theorem cell23_6067234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_6067234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067234 prefixEnd_6067234 := by exact prefixLift 6067234
  have htrace : WordTrace (prefixWord ++ tailWord_6067234) baseStart_6067234 baseEnd_6067234 := by
    simpa [prefixWord, tailWord_6067234, baseEnd_6067234] using wordTrace_append hprefix tailTrace_6067234
  have hstable : (prefixWord ++ tailWord_6067234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067234).length < 2 ^ (prefixWord ++ tailWord_6067234).sum := by decide
  have hdescent : baseEnd_6067234 < baseStart_6067234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067243 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 5]
def baseStart_6067243 : Nat := 118140960795 + 6067243 * 2 ^ 59
def prefixEnd_6067243 : Nat := 4983230072969 + 3 ^ 40 * 6067243 * 2
def baseEnd_6067243 : Nat := 3115411906626910617559763

theorem tailTrace_6067243 : CollatzResearch.WordTrace tailWord_6067243 prefixEnd_6067243 3115411906626910617559763 := by
  unfold tailWord_6067243
  simp only [CollatzResearch.WordTrace]
  refine ⟨221290531958422288453206383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147527021305614858968804255 221290531958422288453206383)
  ·
    refine ⟨331935797937633432679809575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221290531958422288453206383 331935797937633432679809575)
    ·
      refine ⟨497903696906450149019714363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331935797937633432679809575 497903696906450149019714363)
      ·
        refine ⟨746855545359675223529571545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497903696906450149019714363 746855545359675223529571545)
        ·
          refine ⟨560141659019756417647178659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746855545359675223529571545 560141659019756417647178659)
          ·
            refine ⟨840212488529634626470767989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560141659019756417647178659 840212488529634626470767989)
            ·
              refine ⟨78769920799653246231634499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 840212488529634626470767989 78769920799653246231634499)
              ·
                refine ⟨118154881199479869347451749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78769920799653246231634499 118154881199479869347451749)
                ·
                  refine ⟨22154040224902475502647203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118154881199479869347451749 22154040224902475502647203)
                  ·
                    refine ⟨33231060337353713253970805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22154040224902475502647203 33231060337353713253970805)
                    ·
                      refine ⟨3115411906626910617559763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33231060337353713253970805 3115411906626910617559763)
                      ·
                        rfl

theorem cell23_6067243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 5].length) (baseStart_6067243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067243 prefixEnd_6067243 := by exact prefixLift 6067243
  have htrace : WordTrace (prefixWord ++ tailWord_6067243) baseStart_6067243 baseEnd_6067243 := by
    simpa [prefixWord, tailWord_6067243, baseEnd_6067243] using wordTrace_append hprefix tailTrace_6067243
  have hstable : (prefixWord ++ tailWord_6067243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067243).length < 2 ^ (prefixWord ++ tailWord_6067243).sum := by decide
  have hdescent : baseEnd_6067243 < baseStart_6067243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067257 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 3, 4, 2]
def baseStart_6067257 : Nat := 118140960795 + 6067257 * 2 ^ 59
def prefixEnd_6067257 : Nat := 4983230072969 + 3 ^ 40 * 6067257 * 2
def baseEnd_6067257 : Nat := 3115419095356073562784699

theorem tailTrace_6067257 : CollatzResearch.WordTrace tailWord_6067257 prefixEnd_6067257 3115419095356073562784699 := by
  unfold tailWord_6067257
  simp only [CollatzResearch.WordTrace]
  refine ⟨221291042580371568844216025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147527361720247712562810683 221291042580371568844216025)
  ·
    refine ⟨165968281935278676633162019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221291042580371568844216025 165968281935278676633162019)
    ·
      refine ⟨248952422902918014949743029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165968281935278676633162019 248952422902918014949743029)
      ·
        refine ⟨23339289647148563901538409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248952422902918014949743029 23339289647148563901538409)
        ·
          refine ⟨17504467235361422926153807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23339289647148563901538409 17504467235361422926153807)
          ·
            refine ⟨26256700853042134389230711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17504467235361422926153807 26256700853042134389230711)
            ·
              refine ⟨39385051279563201583846067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26256700853042134389230711 39385051279563201583846067)
              ·
                refine ⟨59077576919344802375769101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39385051279563201583846067 59077576919344802375769101)
                ·
                  refine ⟨22154091344754300890913413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59077576919344802375769101 22154091344754300890913413)
                  ·
                    refine ⟨4153892127141431417046265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22154091344754300890913413 4153892127141431417046265)
                    ·
                      refine ⟨3115419095356073562784699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153892127141431417046265 3115419095356073562784699)
                      ·
                        rfl

theorem cell23_6067257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_6067257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067257 prefixEnd_6067257 := by exact prefixLift 6067257
  have htrace : WordTrace (prefixWord ++ tailWord_6067257) baseStart_6067257 baseEnd_6067257 := by
    simpa [prefixWord, tailWord_6067257, baseEnd_6067257] using wordTrace_append hprefix tailTrace_6067257
  have hstable : (prefixWord ++ tailWord_6067257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067257).length < 2 ^ (prefixWord ++ tailWord_6067257).sum := by decide
  have hdescent : baseEnd_6067257 < baseStart_6067257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067260 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_6067260 : Nat := 118140960795 + 6067260 * 2 ^ 59
def prefixEnd_6067260 : Nat := 4983230072969 + 3 ^ 40 * 6067260 * 2
def baseEnd_6067260 : Nat := 3115420635798037051047185

theorem tailTrace_6067260 : CollatzResearch.WordTrace tailWord_6067260 prefixEnd_6067260 3115420635798037051047185 := by
  unfold tailWord_6067260
  simp only [CollatzResearch.WordTrace]
  refine ⟨110645575999680350178287617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147527434666240466904383489 110645575999680350178287617)
  ·
    refine ⟨82984181999760262633715713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110645575999680350178287617 82984181999760262633715713)
    ·
      refine ⟨62238136499820196975286785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82984181999760262633715713 62238136499820196975286785)
      ·
        refine ⟨46678602374865147731465089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62238136499820196975286785 46678602374865147731465089)
        ·
          refine ⟨35008951781148860798598817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46678602374865147731465089 35008951781148860798598817)
          ·
            refine ⟨26256713835861645598949113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35008951781148860798598817 26256713835861645598949113)
            ·
              refine ⟨19692535376896234199211835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26256713835861645598949113 19692535376896234199211835)
              ·
                refine ⟨29538803065344351298817753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19692535376896234199211835 29538803065344351298817753)
                ·
                  refine ⟨22154102299008263474113315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29538803065344351298817753 22154102299008263474113315)
                  ·
                    refine ⟨33231153448512395211169973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22154102299008263474113315 33231153448512395211169973)
                    ·
                      refine ⟨3115420635798037051047185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33231153448512395211169973 3115420635798037051047185)
                      ·
                        rfl

theorem cell23_6067260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_6067260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067260 prefixEnd_6067260 := by exact prefixLift 6067260
  have htrace : WordTrace (prefixWord ++ tailWord_6067260) baseStart_6067260 baseEnd_6067260 := by
    simpa [prefixWord, tailWord_6067260, baseEnd_6067260] using wordTrace_append hprefix tailTrace_6067260
  have hstable : (prefixWord ++ tailWord_6067260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067260).length < 2 ^ (prefixWord ++ tailWord_6067260).sum := by decide
  have hdescent : baseEnd_6067260 < baseStart_6067260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067261 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_6067261 : Nat := 118140960795 + 6067261 * 2 ^ 59
def prefixEnd_6067261 : Nat := 4983230072969 + 3 ^ 40 * 6067261 * 2
def baseEnd_6067261 : Nat := 3115421149278691547134681

theorem tailTrace_6067261 : CollatzResearch.WordTrace tailWord_6067261 prefixEnd_6067261 3115421149278691547134681 := by
  unfold tailWord_6067261
  simp only [CollatzResearch.WordTrace]
  refine ⟨221291188472357077527361637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147527458981571385018241091 221291188472357077527361637)
  ·
    refine ⟨41492097838566952036380307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221291188472357077527361637 41492097838566952036380307)
    ·
      refine ⟨62238146757850428054570461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41492097838566952036380307 62238146757850428054570461)
      ·
        refine ⟨23339305034193910520463923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62238146757850428054570461 23339305034193910520463923)
        ·
          refine ⟨35008957551290865780695885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23339305034193910520463923 35008957551290865780695885)
          ·
            refine ⟨13128359081734074667760957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35008957551290865780695885 13128359081734074667760957)
            ·
              refine ⟨4923134655650278000410359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13128359081734074667760957 4923134655650278000410359)
              ·
                refine ⟨7384701983475417000615539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923134655650278000410359 7384701983475417000615539)
                ·
                  refine ⟨11077052975213125500923309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7384701983475417000615539 11077052975213125500923309)
                  ·
                    refine ⟨4153894865704922062846241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11077052975213125500923309 4153894865704922062846241)
                    ·
                      refine ⟨3115421149278691547134681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153894865704922062846241 3115421149278691547134681)
                      ·
                        rfl

theorem cell23_6067261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_6067261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067261 prefixEnd_6067261 := by exact prefixLift 6067261
  have htrace : WordTrace (prefixWord ++ tailWord_6067261) baseStart_6067261 baseEnd_6067261 := by
    simpa [prefixWord, tailWord_6067261, baseEnd_6067261] using wordTrace_append hprefix tailTrace_6067261
  have hstable : (prefixWord ++ tailWord_6067261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067261).length < 2 ^ (prefixWord ++ tailWord_6067261).sum := by decide
  have hdescent : baseEnd_6067261 < baseStart_6067261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067274 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_6067274 : Nat := 118140960795 + 6067274 * 2 ^ 59
def prefixEnd_6067274 : Nat := 4983230072969 + 3 ^ 40 * 6067274 * 2
def baseEnd_6067274 : Nat := 3115427824527199996272121

theorem tailTrace_6067274 : CollatzResearch.WordTrace tailWord_6067274 prefixEnd_6067274 3115427824527199996272121 := by
  unfold tailWord_6067274
  simp only [CollatzResearch.WordTrace]
  refine ⟨55322915655327495186896219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147527775080873320498389917 55322915655327495186896219)
  ·
    refine ⟨82984373482991242780344329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55322915655327495186896219 82984373482991242780344329)
    ·
      refine ⟨62238280112243432085258247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82984373482991242780344329 62238280112243432085258247)
      ·
        refine ⟨93357420168365148127887371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62238280112243432085258247 93357420168365148127887371)
        ·
          refine ⟨140036130252547722191831057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93357420168365148127887371 140036130252547722191831057)
          ·
            refine ⟨105027097689410791643873293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140036130252547722191831057 105027097689410791643873293)
            ·
              refine ⟨39385161633529046866452485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105027097689410791643873293 39385161633529046866452485)
              ·
                refine ⟨7384717806286696287459841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39385161633529046866452485 7384717806286696287459841)
                ·
                  refine ⟨5538538354715022215594881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7384717806286696287459841 5538538354715022215594881)
                  ·
                    refine ⟨4153903766036266661696161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5538538354715022215594881 4153903766036266661696161)
                    ·
                      refine ⟨3115427824527199996272121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153903766036266661696161 3115427824527199996272121)
                      ·
                        rfl

theorem cell23_6067274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_6067274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067274 prefixEnd_6067274 := by exact prefixLift 6067274
  have htrace : WordTrace (prefixWord ++ tailWord_6067274) baseStart_6067274 baseEnd_6067274 := by
    simpa [prefixWord, tailWord_6067274, baseEnd_6067274] using wordTrace_append hprefix tailTrace_6067274
  have hstable : (prefixWord ++ tailWord_6067274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067274).length < 2 ^ (prefixWord ++ tailWord_6067274).sum := by decide
  have hdescent : baseEnd_6067274 < baseStart_6067274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067277 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_6067277 : Nat := 118140960795 + 6067277 * 2 ^ 59
def prefixEnd_6067277 : Nat := 4983230072969 + 3 ^ 40 * 6067277 * 2
def baseEnd_6067277 : Nat := 3115429364969163484534607

theorem tailTrace_6067277 : CollatzResearch.WordTrace tailWord_6067277 prefixEnd_6067277 3115429364969163484534607 := by
  unfold tailWord_6067277
  simp only [CollatzResearch.WordTrace]
  refine ⟨221291772040299112259944085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147527848026866074839962723 221291772040299112259944085)
  ·
    refine ⟨10373051814389020887184879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221291772040299112259944085 10373051814389020887184879)
    ·
      refine ⟨15559577721583531330777319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10373051814389020887184879 15559577721583531330777319)
      ·
        refine ⟨23339366582375296996165979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15559577721583531330777319 23339366582375296996165979)
        ·
          refine ⟨35009049873562945494248969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23339366582375296996165979 35009049873562945494248969)
          ·
            refine ⟨26256787405172209120686727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35009049873562945494248969 26256787405172209120686727)
            ·
              refine ⟨39385181107758313681030091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26256787405172209120686727 39385181107758313681030091)
              ·
                refine ⟨59077771661637470521545137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39385181107758313681030091 59077771661637470521545137)
                ·
                  refine ⟨44308328746228102891158853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59077771661637470521545137 44308328746228102891158853)
                  ·
                    refine ⟨8307811639917769292092285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44308328746228102891158853 8307811639917769292092285)
                    ·
                      refine ⟨3115429364969163484534607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8307811639917769292092285 3115429364969163484534607)
                      ·
                        rfl

theorem cell23_6067277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_6067277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067277 prefixEnd_6067277 := by exact prefixLift 6067277
  have htrace : WordTrace (prefixWord ++ tailWord_6067277) baseStart_6067277 baseEnd_6067277 := by
    simpa [prefixWord, tailWord_6067277, baseEnd_6067277] using wordTrace_append hprefix tailTrace_6067277
  have hstable : (prefixWord ++ tailWord_6067277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067277).length < 2 ^ (prefixWord ++ tailWord_6067277).sum := by decide
  have hdescent : baseEnd_6067277 < baseStart_6067277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067323 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 1, 10]
def baseStart_6067323 : Nat := 118140960795 + 6067323 * 2 ^ 59
def prefixEnd_6067323 : Nat := 4983230072969 + 3 ^ 40 * 6067323 * 2
def baseEnd_6067323 : Nat := 1038484328359756768186465

theorem tailTrace_6067323 : CollatzResearch.WordTrace tailWord_6067323 prefixEnd_6067323 1038484328359756768186465 := by
  unfold tailWord_6067323
  simp only [CollatzResearch.WordTrace]
  refine ⟨221293449798132462116118623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147528966532088308077412415 221293449798132462116118623)
  ·
    refine ⟨331940174697198693174177935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221293449798132462116118623 331940174697198693174177935)
    ·
      refine ⟨497910262045798039761266903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331940174697198693174177935 497910262045798039761266903)
      ·
        refine ⟨746865393068697059641900355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497910262045798039761266903 746865393068697059641900355)
        ·
          refine ⟨1120298089603045589462850533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746865393068697059641900355 1120298089603045589462850533)
          ·
            refine ⟨210055891800571048024284475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1120298089603045589462850533 210055891800571048024284475)
            ·
              refine ⟨315083837700856572036426713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210055891800571048024284475 315083837700856572036426713)
              ·
                refine ⟨236312878275642429027320035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315083837700856572036426713 236312878275642429027320035)
                ·
                  refine ⟨354469317413463643540980053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236312878275642429027320035 354469317413463643540980053)
                  ·
                    refine ⟨1038484328359756768186465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 354469317413463643540980053 1038484328359756768186465)
                    ·
                      rfl

theorem cell23_6067323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 10].length) (baseStart_6067323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067323 prefixEnd_6067323 := by exact prefixLift 6067323
  have htrace : WordTrace (prefixWord ++ tailWord_6067323) baseStart_6067323 baseEnd_6067323 := by
    simpa [prefixWord, tailWord_6067323, baseEnd_6067323] using wordTrace_append hprefix tailTrace_6067323
  have hstable : (prefixWord ++ tailWord_6067323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067323).length < 2 ^ (prefixWord ++ tailWord_6067323).sum := by decide
  have hdescent : baseEnd_6067323 < baseStart_6067323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067347 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 2, 4, 2]
def baseStart_6067347 : Nat := 118140960795 + 6067347 * 2 ^ 59
def prefixEnd_6067347 : Nat := 4983230072969 + 3 ^ 40 * 6067347 * 2
def baseEnd_6067347 : Nat := 3115465308614978210659285

theorem tailTrace_6067347 : CollatzResearch.WordTrace tailWord_6067347 prefixEnd_6067347 3115465308614978210659285 := by
  unfold tailWord_6067347
  simp only [CollatzResearch.WordTrace]
  refine ⟨221294325150045514214992295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147529550100030342809994863 221294325150045514214992295)
  ·
    refine ⟨331941487725068271322488443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221294325150045514214992295 331941487725068271322488443)
    ·
      refine ⟨497912231587602406983732665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331941487725068271322488443 497912231587602406983732665)
      ·
        refine ⟨373434173690701805237799499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497912231587602406983732665 373434173690701805237799499)
        ·
          refine ⟨560151260536052707856699249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373434173690701805237799499 560151260536052707856699249)
          ·
            refine ⟨420113445402039530892524437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560151260536052707856699249 420113445402039530892524437)
            ·
              refine ⟨19692817753220603010587083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 420113445402039530892524437 19692817753220603010587083)
              ·
                refine ⟨29539226629830904515880625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19692817753220603010587083 29539226629830904515880625)
                ·
                  refine ⟨22154419972373178386910469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29539226629830904515880625 22154419972373178386910469)
                  ·
                    refine ⟨4153953744819970947545713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22154419972373178386910469 4153953744819970947545713)
                    ·
                      refine ⟨3115465308614978210659285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153953744819970947545713 3115465308614978210659285)
                      ·
                        rfl

theorem cell23_6067347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 4, 2].length) (baseStart_6067347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067347 prefixEnd_6067347 := by exact prefixLift 6067347
  have htrace : WordTrace (prefixWord ++ tailWord_6067347) baseStart_6067347 baseEnd_6067347 := by
    simpa [prefixWord, tailWord_6067347, baseEnd_6067347] using wordTrace_append hprefix tailTrace_6067347
  have hstable : (prefixWord ++ tailWord_6067347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067347).length < 2 ^ (prefixWord ++ tailWord_6067347).sum := by decide
  have hdescent : baseEnd_6067347 < baseStart_6067347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067357 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_6067357 : Nat := 118140960795 + 6067357 * 2 ^ 59
def prefixEnd_6067357 : Nat := 4983230072969 + 3 ^ 40 * 6067357 * 2
def baseEnd_6067357 : Nat := 1038490147807174390511413

theorem tailTrace_6067357 : CollatzResearch.WordTrace tailWord_6067357 prefixEnd_6067357 1038490147807174390511413 := by
  unfold tailWord_6067357
  simp only [CollatzResearch.WordTrace]
  refine ⟨221294689880009285922856325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147529793253339523948570883 221294689880009285922856325)
  ·
    refine ⟨41492754352501741110535561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221294689880009285922856325 41492754352501741110535561)
    ·
      refine ⟨31119565764376305832901671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41492754352501741110535561 31119565764376305832901671)
      ·
        refine ⟨46679348646564458749352507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31119565764376305832901671 46679348646564458749352507)
        ·
          refine ⟨70019022969846688124028761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46679348646564458749352507 70019022969846688124028761)
          ·
            refine ⟨52514267227385016093021571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70019022969846688124028761 52514267227385016093021571)
            ·
              refine ⟨78771400841077524139532357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52514267227385016093021571 78771400841077524139532357)
              ·
                refine ⟨14769637657702035776162317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78771400841077524139532357 14769637657702035776162317)
                ·
                  refine ⟨5538614121638263416060869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14769637657702035776162317 5538614121638263416060869)
                  ·
                    refine ⟨1038490147807174390511413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5538614121638263416060869 1038490147807174390511413)
                    ·
                      rfl

theorem cell23_6067357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_6067357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067357 prefixEnd_6067357 := by exact prefixLift 6067357
  have htrace : WordTrace (prefixWord ++ tailWord_6067357) baseStart_6067357 baseEnd_6067357 := by
    simpa [prefixWord, tailWord_6067357, baseEnd_6067357] using wordTrace_append hprefix tailTrace_6067357
  have hstable : (prefixWord ++ tailWord_6067357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067357).length < 2 ^ (prefixWord ++ tailWord_6067357).sum := by decide
  have hdescent : baseEnd_6067357 < baseStart_6067357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067360 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_6067360 : Nat := 118140960795 + 6067360 * 2 ^ 59
def prefixEnd_6067360 : Nat := 4983230072969 + 3 ^ 40 * 6067360 * 2
def baseEnd_6067360 : Nat := 3115471983863486659796725

theorem tailTrace_6067360 : CollatzResearch.WordTrace tailWord_6067360 prefixEnd_6067360 3115471983863486659796725 := by
  unfold tailWord_6067360
  simp only [CollatzResearch.WordTrace]
  refine ⟨110647399649499208717607767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147529866199332278290143689 110647399649499208717607767)
  ·
    refine ⟨165971099474248813076411651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110647399649499208717607767 165971099474248813076411651)
    ·
      refine ⟨248956649211373219614617477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165971099474248813076411651 248956649211373219614617477)
      ·
        refine ⟨46679371727132478677740777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248956649211373219614617477 46679371727132478677740777)
        ·
          refine ⟨35009528795349359008305583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46679371727132478677740777 35009528795349359008305583)
          ·
            refine ⟨52514293193024038512458375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35009528795349359008305583 52514293193024038512458375)
            ·
              refine ⟨78771439789536057768687563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52514293193024038512458375 78771439789536057768687563)
              ·
                refine ⟨118157159684304086653031345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78771439789536057768687563 118157159684304086653031345)
                ·
                  refine ⟨88617869763228064989773509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118157159684304086653031345 88617869763228064989773509)
                  ·
                    refine ⟨16615850580605262185582533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88617869763228064989773509 16615850580605262185582533)
                    ·
                      refine ⟨3115471983863486659796725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16615850580605262185582533 3115471983863486659796725)
                      ·
                        rfl

theorem cell23_6067360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_6067360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067360 prefixEnd_6067360 := by exact prefixLift 6067360
  have htrace : WordTrace (prefixWord ++ tailWord_6067360) baseStart_6067360 baseEnd_6067360 := by
    simpa [prefixWord, tailWord_6067360, baseEnd_6067360] using wordTrace_append hprefix tailTrace_6067360
  have hstable : (prefixWord ++ tailWord_6067360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067360).length < 2 ^ (prefixWord ++ tailWord_6067360).sum := by decide
  have hdescent : baseEnd_6067360 < baseStart_6067360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067407 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 1, 5, 2]
def baseStart_6067407 : Nat := 118140960795 + 6067407 * 2 ^ 59
def prefixEnd_6067407 : Nat := 4983230072969 + 3 ^ 40 * 6067407 * 2
def baseEnd_6067407 : Nat := 3115496117454247975909009

theorem tailTrace_6067407 : CollatzResearch.WordTrace tailWord_6067407 prefixEnd_6067407 3115496117454247975909009 := by
  unfold tailWord_6067407
  simp only [CollatzResearch.WordTrace]
  refine ⟨221296513529828144462176475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147531009019885429641450983 221296513529828144462176475)
  ·
    refine ⟨331944770294742216693264713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221296513529828144462176475 331944770294742216693264713)
    ·
      refine ⟨248958577721056662519948535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331944770294742216693264713 248958577721056662519948535)
      ·
        refine ⟨373437866581584993779922803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248958577721056662519948535 373437866581584993779922803)
        ·
          refine ⟨560156799872377490669884205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373437866581584993779922803 560156799872377490669884205)
          ·
            refine ⟨210058799952141559001206577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560156799872377490669884205 210058799952141559001206577)
            ·
              refine ⟨157544099964106169250904933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210058799952141559001206577 157544099964106169250904933)
              ·
                refine ⟨29539518743269906734544675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157544099964106169250904933 29539518743269906734544675)
                ·
                  refine ⟨44309278114904860101817013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29539518743269906734544675 44309278114904860101817013)
                  ·
                    refine ⟨4153994823272330634545345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44309278114904860101817013 4153994823272330634545345)
                    ·
                      refine ⟨3115496117454247975909009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4153994823272330634545345 3115496117454247975909009)
                      ·
                        rfl

theorem cell23_6067407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 5, 2].length) (baseStart_6067407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067407 prefixEnd_6067407 := by exact prefixLift 6067407
  have htrace : WordTrace (prefixWord ++ tailWord_6067407) baseStart_6067407 baseEnd_6067407 := by
    simpa [prefixWord, tailWord_6067407, baseEnd_6067407] using wordTrace_append hprefix tailTrace_6067407
  have hstable : (prefixWord ++ tailWord_6067407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067407).length < 2 ^ (prefixWord ++ tailWord_6067407).sum := by decide
  have hdescent : baseEnd_6067407 < baseStart_6067407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067424 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 2, 3, 2]
def baseStart_6067424 : Nat := 118140960795 + 6067424 * 2 ^ 59
def prefixEnd_6067424 : Nat := 4983230072969 + 3 ^ 40 * 6067424 * 2
def baseEnd_6067424 : Nat := 3115504846625374409396431

theorem tailTrace_6067424 : CollatzResearch.WordTrace tailWord_6067424 prefixEnd_6067424 3115504846625374409396431 := by
  unfold tailWord_6067424
  simp only [CollatzResearch.WordTrace]
  refine ⟨110648566785383278182772663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147531422380511037577030217 110648566785383278182772663)
  ·
    refine ⟨165972850178074917274158995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110648566785383278182772663 165972850178074917274158995)
    ·
      refine ⟨248959275267112375911238493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165972850178074917274158995 248959275267112375911238493)
      ·
        refine ⟨93359728225167140966714435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248959275267112375911238493 93359728225167140966714435)
        ·
          refine ⟨140039592337750711450071653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93359728225167140966714435 140039592337750711450071653)
          ·
            refine ⟨26257423563328258396888435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140039592337750711450071653 26257423563328258396888435)
            ·
              refine ⟨39386135344992387595332653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26257423563328258396888435 39386135344992387595332653)
              ·
                refine ⟨14769800754372145348249745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39386135344992387595332653 14769800754372145348249745)
                ·
                  refine ⟨11077350565779109011187309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14769800754372145348249745 11077350565779109011187309)
                  ·
                    refine ⟨4154006462167165879195241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11077350565779109011187309 4154006462167165879195241)
                    ·
                      refine ⟨3115504846625374409396431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154006462167165879195241 3115504846625374409396431)
                      ·
                        rfl

theorem cell23_6067424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_6067424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067424 prefixEnd_6067424 := by exact prefixLift 6067424
  have htrace : WordTrace (prefixWord ++ tailWord_6067424) baseStart_6067424 baseEnd_6067424 := by
    simpa [prefixWord, tailWord_6067424, baseEnd_6067424] using wordTrace_append hprefix tailTrace_6067424
  have hstable : (prefixWord ++ tailWord_6067424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067424).length < 2 ^ (prefixWord ++ tailWord_6067424).sum := by decide
  have hdescent : baseEnd_6067424 < baseStart_6067424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067454 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_6067454 : Nat := 118140960795 + 6067454 * 2 ^ 59
def prefixEnd_6067454 : Nat := 4983230072969 + 3 ^ 40 * 6067454 * 2
def baseEnd_6067454 : Nat := 3115520251045009292021293

theorem tailTrace_6067454 : CollatzResearch.WordTrace tailWord_6067454 prefixEnd_6067454 3115520251045009292021293 := by
  unfold tailWord_6067454
  simp only [CollatzResearch.WordTrace]
  refine ⟨27662278470082233936142177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147532151840438580992758277 27662278470082233936142177)
  ·
    refine ⟨20746708852561675452106633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27662278470082233936142177 20746708852561675452106633)
    ·
      refine ⟨15560031639421256589079975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20746708852561675452106633 15560031639421256589079975)
      ·
        refine ⟨23340047459131884883619963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15560031639421256589079975 23340047459131884883619963)
        ·
          refine ⟨35010071188697827325429945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23340047459131884883619963 35010071188697827325429945)
          ·
            refine ⟨26257553391523370494072459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35010071188697827325429945 26257553391523370494072459)
            ·
              refine ⟨39386330087285055741108689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26257553391523370494072459 39386330087285055741108689)
              ·
                refine ⟨29539747565463791805831517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39386330087285055741108689 29539747565463791805831517)
                ·
                  refine ⟨11077405337048921927186819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29539747565463791805831517 11077405337048921927186819)
                  ·
                    refine ⟨16616108005573382890780229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11077405337048921927186819 16616108005573382890780229)
                    ·
                      refine ⟨3115520251045009292021293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16616108005573382890780229 3115520251045009292021293)
                      ·
                        rfl

theorem cell23_6067454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_6067454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067454 prefixEnd_6067454 := by exact prefixLift 6067454
  have htrace : WordTrace (prefixWord ++ tailWord_6067454) baseStart_6067454 baseEnd_6067454 := by
    simpa [prefixWord, tailWord_6067454, baseEnd_6067454] using wordTrace_append hprefix tailTrace_6067454
  have hstable : (prefixWord ++ tailWord_6067454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067454).length < 2 ^ (prefixWord ++ tailWord_6067454).sum := by decide
  have hdescent : baseEnd_6067454 < baseStart_6067454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067464 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 1, 6]
def baseStart_6067464 : Nat := 118140960795 + 6067464 * 2 ^ 59
def prefixEnd_6067464 : Nat := 4983230072969 + 3 ^ 40 * 6067464 * 2
def baseEnd_6067464 : Nat := 1038508461950518084298749

theorem tailTrace_6067464 : CollatzResearch.WordTrace tailWord_6067464 prefixEnd_6067464 1038508461950518084298749 := by
  unfold tailWord_6067464
  simp only [CollatzResearch.WordTrace]
  refine ⟨110649296245310821598500723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147532394993747762131334297 110649296245310821598500723)
  ·
    refine ⟨165973944367966232397751085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110649296245310821598500723 165973944367966232397751085)
    ·
      refine ⟨62240229137987337149156657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165973944367966232397751085 62240229137987337149156657)
      ·
        refine ⟨46680171853490502861867493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62240229137987337149156657 46680171853490502861867493)
        ·
          refine ⟨8752532222529469286600155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46680171853490502861867493 8752532222529469286600155)
          ·
            refine ⟨13128798333794203929900233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8752532222529469286600155 13128798333794203929900233)
            ·
              refine ⟨9846598750345652947425175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13128798333794203929900233 9846598750345652947425175)
              ·
                refine ⟨14769898125518479421137763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9846598750345652947425175 14769898125518479421137763)
                ·
                  refine ⟨22154847188277719131706645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14769898125518479421137763 22154847188277719131706645)
                  ·
                    refine ⟨1038508461950518084298749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22154847188277719131706645 1038508461950518084298749)
                    ·
                      rfl

theorem cell23_6067464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_6067464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067464 prefixEnd_6067464 := by exact prefixLift 6067464
  have htrace : WordTrace (prefixWord ++ tailWord_6067464) baseStart_6067464 baseEnd_6067464 := by
    simpa [prefixWord, tailWord_6067464, baseEnd_6067464] using wordTrace_append hprefix tailTrace_6067464
  have hstable : (prefixWord ++ tailWord_6067464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067464).length < 2 ^ (prefixWord ++ tailWord_6067464).sum := by decide
  have hdescent : baseEnd_6067464 < baseStart_6067464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067467 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 4]
def baseStart_6067467 : Nat := 118140960795 + 6067467 * 2 ^ 59
def prefixEnd_6067467 : Nat := 4983230072969 + 3 ^ 40 * 6067467 * 2
def baseEnd_6067467 : Nat := 3115526926293517741158733

theorem tailTrace_6067467 : CollatzResearch.WordTrace tailWord_6067467 prefixEnd_6067467 3115526926293517741158733 := by
  unfold tailWord_6067467
  simp only [CollatzResearch.WordTrace]
  refine ⟨221298701909610774709360655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147532467939740516472907103 221298701909610774709360655)
  ·
    refine ⟨331948052864416162064040983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221298701909610774709360655 331948052864416162064040983)
    ·
      refine ⟨497922079296624243096061475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331948052864416162064040983 497922079296624243096061475)
      ·
        refine ⟨746883118944936364644092213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497922079296624243096061475 746883118944936364644092213)
        ·
          refine ⟨70020292401087784185383645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 746883118944936364644092213 70020292401087784185383645)
          ·
            refine ⟨26257609650407919069518867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70020292401087784185383645 26257609650407919069518867)
            ·
              refine ⟨39386414475611878604278301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26257609650407919069518867 39386414475611878604278301)
              ·
                refine ⟨14769905428354454476604363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39386414475611878604278301 14769905428354454476604363)
                ·
                  refine ⟨22154858142531681714906545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14769905428354454476604363 22154858142531681714906545)
                  ·
                    refine ⟨16616143606898761286179909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22154858142531681714906545 16616143606898761286179909)
                    ·
                      refine ⟨3115526926293517741158733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16616143606898761286179909 3115526926293517741158733)
                      ·
                        rfl

theorem cell23_6067467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 4].length) (baseStart_6067467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067467 prefixEnd_6067467 := by exact prefixLift 6067467
  have htrace : WordTrace (prefixWord ++ tailWord_6067467) baseStart_6067467 baseEnd_6067467 := by
    simpa [prefixWord, tailWord_6067467, baseEnd_6067467] using wordTrace_append hprefix tailTrace_6067467
  have hstable : (prefixWord ++ tailWord_6067467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067467).length < 2 ^ (prefixWord ++ tailWord_6067467).sum := by decide
  have hdescent : baseEnd_6067467 < baseStart_6067467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067488 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 1, 1, 4]
def baseStart_6067488 : Nat := 118140960795 + 6067488 * 2 ^ 59
def prefixEnd_6067488 : Nat := 4983230072969 + 3 ^ 40 * 6067488 * 2
def baseEnd_6067488 : Nat := 3115537709387262158996137

theorem tailTrace_6067488 : CollatzResearch.WordTrace tailWord_6067488 prefixEnd_6067488 3115537709387262158996137 := by
  unfold tailWord_6067488
  simp only [CollatzResearch.WordTrace]
  refine ⟨110649733921267347647937559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147532978561689796863916745 110649733921267347647937559)
  ·
    refine ⟨165974600881901021471906339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110649733921267347647937559 165974600881901021471906339)
    ·
      refine ⟨248961901322851532207859509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165974600881901021471906339 248961901322851532207859509)
      ·
        refine ⟨23340178249017331144486829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248961901322851532207859509 23340178249017331144486829)
        ·
          refine ⟨8752566843381499179182561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23340178249017331144486829 8752566843381499179182561)
          ·
            refine ⟨6564425132536124384386921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8752566843381499179182561 6564425132536124384386921)
            ·
              refine ⟨4923318849402093288290191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6564425132536124384386921 4923318849402093288290191)
              ·
                refine ⟨7384978274103139932435287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923318849402093288290191 7384978274103139932435287)
                ·
                  refine ⟨11077467411154709898652931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7384978274103139932435287 11077467411154709898652931)
                  ·
                    refine ⟨16616201116732064847979397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11077467411154709898652931 16616201116732064847979397)
                    ·
                      refine ⟨3115537709387262158996137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16616201116732064847979397 3115537709387262158996137)
                      ·
                        rfl

theorem cell23_6067488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_6067488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067488 prefixEnd_6067488 := by exact prefixLift 6067488
  have htrace : WordTrace (prefixWord ++ tailWord_6067488) baseStart_6067488 baseEnd_6067488 := by
    simpa [prefixWord, tailWord_6067488, baseEnd_6067488] using wordTrace_append hprefix tailTrace_6067488
  have hstable : (prefixWord ++ tailWord_6067488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067488).length < 2 ^ (prefixWord ++ tailWord_6067488).sum := by decide
  have hdescent : baseEnd_6067488 < baseStart_6067488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067491 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 1, 2, 3]
def baseStart_6067491 : Nat := 118140960795 + 6067491 * 2 ^ 59
def prefixEnd_6067491 : Nat := 4983230072969 + 3 ^ 40 * 6067491 * 2
def baseEnd_6067491 : Nat := 3115539249829225647258623

theorem tailTrace_6067491 : CollatzResearch.WordTrace tailWord_6067491 prefixEnd_6067491 3115539249829225647258623 := by
  unfold tailWord_6067491
  simp only [CollatzResearch.WordTrace]
  refine ⟨221299577261523826808234327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147533051507682551205489551 221299577261523826808234327)
  ·
    refine ⟨331949365892285740212351491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221299577261523826808234327 331949365892285740212351491)
    ·
      refine ⟨497924048838428610318527237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331949365892285740212351491 497924048838428610318527237)
      ·
        refine ⟨93360759157205364434723857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 497924048838428610318527237 93360759157205364434723857)
        ·
          refine ⟨70020569367904023326042893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93360759157205364434723857 70020569367904023326042893)
          ·
            refine ⟨26257713512964008747266085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70020569367904023326042893 26257713512964008747266085)
            ·
              refine ⟨4923321283680751640112391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26257713512964008747266085 4923321283680751640112391)
              ·
                refine ⟨7384981925521127460168587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923321283680751640112391 7384981925521127460168587)
                ·
                  refine ⟨11077472888281691190252881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7384981925521127460168587 11077472888281691190252881)
                  ·
                    refine ⟨8308104666211268392689661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11077472888281691190252881 8308104666211268392689661)
                    ·
                      refine ⟨3115539249829225647258623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8308104666211268392689661 3115539249829225647258623)
                      ·
                        rfl

theorem cell23_6067491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_6067491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067491 prefixEnd_6067491 := by exact prefixLift 6067491
  have htrace : WordTrace (prefixWord ++ tailWord_6067491) baseStart_6067491 baseEnd_6067491 := by
    simpa [prefixWord, tailWord_6067491, baseEnd_6067491] using wordTrace_append hprefix tailTrace_6067491
  have hstable : (prefixWord ++ tailWord_6067491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067491).length < 2 ^ (prefixWord ++ tailWord_6067491).sum := by decide
  have hdescent : baseEnd_6067491 < baseStart_6067491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067498 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_6067498 : Nat := 118140960795 + 6067498 * 2 ^ 59
def prefixEnd_6067498 : Nat := 4983230072969 + 3 ^ 40 * 6067498 * 2
def baseEnd_6067498 : Nat := 1038514281397935706623697

theorem tailTrace_6067498 : CollatzResearch.WordTrace tailWord_6067498 prefixEnd_6067498 1038514281397935706623697 := by
  unfold tailWord_6067498
  simp only [CollatzResearch.WordTrace]
  refine ⟨55324958143124616750934787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147533221714998978002492765 55324958143124616750934787)
  ·
    refine ⟨82987437214686925126402181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55324958143124616750934787 82987437214686925126402181)
    ·
      refine ⟨15560144477753798461200409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82987437214686925126402181 15560144477753798461200409)
      ·
        refine ⟨11670108358315348845900307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15560144477753798461200409 11670108358315348845900307)
        ·
          refine ⟨17505162537473023268850461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11670108358315348845900307 17505162537473023268850461)
          ·
            refine ⟨6564435951552383725818923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17505162537473023268850461 6564435951552383725818923)
            ·
              refine ⟨9846653927328575588728385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6564435951552383725818923 9846653927328575588728385)
              ·
                refine ⟨7384990445496431691546289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9846653927328575588728385 7384990445496431691546289)
                ·
                  refine ⟨5538742834122323768659717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7384990445496431691546289 5538742834122323768659717)
                  ·
                    refine ⟨1038514281397935706623697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5538742834122323768659717 1038514281397935706623697)
                    ·
                      rfl

theorem cell23_6067498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_6067498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067498 prefixEnd_6067498 := by exact prefixLift 6067498
  have htrace : WordTrace (prefixWord ++ tailWord_6067498) baseStart_6067498 baseEnd_6067498 := by
    simpa [prefixWord, tailWord_6067498, baseEnd_6067498] using wordTrace_append hprefix tailTrace_6067498
  have hstable : (prefixWord ++ tailWord_6067498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067498).length < 2 ^ (prefixWord ++ tailWord_6067498).sum := by decide
  have hdescent : baseEnd_6067498 < baseStart_6067498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067504 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 4, 1, 3]
def baseStart_6067504 : Nat := 118140960795 + 6067504 * 2 ^ 59
def prefixEnd_6067504 : Nat := 4983230072969 + 3 ^ 40 * 6067504 * 2
def baseEnd_6067504 : Nat := 3115545925077734096396063

theorem tailTrace_6067504 : CollatzResearch.WordTrace tailWord_6067504 prefixEnd_6067504 3115545925077734096396063 := by
  unfold tailWord_6067504
  simp only [CollatzResearch.WordTrace]
  refine ⟨110650025705238365014228783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147533367606984486685638377 110650025705238365014228783)
  ·
    refine ⟨165975038557857547521343175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110650025705238365014228783 165975038557857547521343175)
    ·
      refine ⟨248962557836786321282014763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165975038557857547521343175 248962557836786321282014763)
      ·
        refine ⟨373443836755179481923022145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248962557836786321282014763 373443836755179481923022145)
        ·
          refine ⟨280082877566384611442266609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373443836755179481923022145 280082877566384611442266609)
          ·
            refine ⟨210062158174788458581699957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280082877566384611442266609 210062158174788458581699957)
            ·
              refine ⟨19693327328886417992034371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210062158174788458581699957 19693327328886417992034371)
              ·
                refine ⟨29539990993329626988051557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19693327328886417992034371 29539990993329626988051557)
                ·
                  refine ⟨5538748311249305060259667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29539990993329626988051557 5538748311249305060259667)
                  ·
                    refine ⟨8308122466873957590389501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5538748311249305060259667 8308122466873957590389501)
                    ·
                      refine ⟨3115545925077734096396063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8308122466873957590389501 3115545925077734096396063)
                      ·
                        rfl

theorem cell23_6067504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4, 1, 3].length) (baseStart_6067504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067504 prefixEnd_6067504 := by exact prefixLift 6067504
  have htrace : WordTrace (prefixWord ++ tailWord_6067504) baseStart_6067504 baseEnd_6067504 := by
    simpa [prefixWord, tailWord_6067504, baseEnd_6067504] using wordTrace_append hprefix tailTrace_6067504
  have hstable : (prefixWord ++ tailWord_6067504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067504).length < 2 ^ (prefixWord ++ tailWord_6067504).sum := by decide
  have hdescent : baseEnd_6067504 < baseStart_6067504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067521 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6067521 : Nat := 118140960795 + 6067521 * 2 ^ 59
def prefixEnd_6067521 : Nat := 4983230072969 + 3 ^ 40 * 6067521 * 2
def baseEnd_6067521 : Nat := 3115554654248860529883485

theorem tailTrace_6067521 : CollatzResearch.WordTrace tailWord_6067521 prefixEnd_6067521 3115554654248860529883485 := by
  unfold tailWord_6067521
  simp only [CollatzResearch.WordTrace]
  refine ⟨221300671451415141931826417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147533780967610094621217611 221300671451415141931826417)
  ·
    refine ⟨165975503588561356448869813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221300671451415141931826417 165975503588561356448869813)
    ·
      refine ⟨15560203461427627167081545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165975503588561356448869813 15560203461427627167081545)
      ·
        refine ⟨11670152596070720375311159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15560203461427627167081545 11670152596070720375311159)
        ·
          refine ⟨17505228894106080562966739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11670152596070720375311159 17505228894106080562966739)
          ·
            refine ⟨26257843341159120844450109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17505228894106080562966739 26257843341159120844450109)
            ·
              refine ⟨9846691252934670316668791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26257843341159120844450109 9846691252934670316668791)
              ·
                refine ⟨14770036879402005475003187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9846691252934670316668791 14770036879402005475003187)
                ·
                  refine ⟨22155055319103008212504781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14770036879402005475003187 22155055319103008212504781)
                  ·
                    refine ⟨8308145744663628079689293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22155055319103008212504781 8308145744663628079689293)
                    ·
                      refine ⟨3115554654248860529883485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8308145744663628079689293 3115554654248860529883485)
                      ·
                        rfl

theorem cell23_6067521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6067521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067521 prefixEnd_6067521 := by exact prefixLift 6067521
  have htrace : WordTrace (prefixWord ++ tailWord_6067521) baseStart_6067521 baseEnd_6067521 := by
    simpa [prefixWord, tailWord_6067521, baseEnd_6067521] using wordTrace_append hprefix tailTrace_6067521
  have hstable : (prefixWord ++ tailWord_6067521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067521).length < 2 ^ (prefixWord ++ tailWord_6067521).sum := by decide
  have hdescent : baseEnd_6067521 < baseStart_6067521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067544 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 3, 4, 2]
def baseStart_6067544 : Nat := 118140960795 + 6067544 * 2 ^ 59
def prefixEnd_6067544 : Nat := 4983230072969 + 3 ^ 40 * 6067544 * 2
def baseEnd_6067544 : Nat := 3115566464303913939895879

theorem tailTrace_6067544 : CollatzResearch.WordTrace tailWord_6067544 prefixEnd_6067544 3115566464303913939895879 := by
  unfold tailWord_6067544
  simp only [CollatzResearch.WordTrace]
  refine ⟨110650755165165908429956843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147534340220221211239942457 110650755165165908429956843)
  ·
    refine ⟨165976132747748862644935265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110650755165165908429956843 165976132747748862644935265)
    ·
      refine ⟨124482099560811646983701449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165976132747748862644935265 124482099560811646983701449)
      ·
        refine ⟨93361574670608735237776087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124482099560811646983701449 93361574670608735237776087)
        ·
          refine ⟨140042362005913102856664131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93361574670608735237776087 140042362005913102856664131)
          ·
            refine ⟨210063543008869654284996197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140042362005913102856664131 210063543008869654284996197)
            ·
              refine ⟨39386914314163060178436787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210063543008869654284996197 39386914314163060178436787)
              ·
                refine ⟨59080371471244590267655181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39386914314163060178436787 59080371471244590267655181)
                ·
                  refine ⟨22155139301716721350370693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59080371471244590267655181 22155139301716721350370693)
                  ·
                    refine ⟨4154088619071885253194505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22155139301716721350370693 4154088619071885253194505)
                    ·
                      refine ⟨3115566464303913939895879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154088619071885253194505 3115566464303913939895879)
                      ·
                        rfl

theorem cell23_6067544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_6067544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067544 prefixEnd_6067544 := by exact prefixLift 6067544
  have htrace : WordTrace (prefixWord ++ tailWord_6067544) baseStart_6067544 baseEnd_6067544 := by
    simpa [prefixWord, tailWord_6067544, baseEnd_6067544] using wordTrace_append hprefix tailTrace_6067544
  have hstable : (prefixWord ++ tailWord_6067544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067544).length < 2 ^ (prefixWord ++ tailWord_6067544).sum := by decide
  have hdescent : baseEnd_6067544 < baseStart_6067544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067612 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6067612 : Nat := 118140960795 + 6067612 * 2 ^ 59
def prefixEnd_6067612 : Nat := 4983230072969 + 3 ^ 40 * 6067612 * 2
def baseEnd_6067612 : Nat := 3115601380988419673845567

theorem tailTrace_6067612 : CollatzResearch.WordTrace tailWord_6067612 prefixEnd_6067612 3115601380988419673845567 := by
  unfold tailWord_6067612
  simp only [CollatzResearch.WordTrace]
  refine ⟨110651995247042732236694545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147535993662723642982259393 110651995247042732236694545)
  ·
    refine ⟨82988996435282049177520909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110651995247042732236694545 82988996435282049177520909)
    ·
      refine ⟨31120873663230768441570341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82988996435282049177520909 31120873663230768441570341)
      ·
        refine ⟨5835163811855769082794439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31120873663230768441570341 5835163811855769082794439)
        ·
          refine ⟨8752745717783653624191659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5835163811855769082794439 8752745717783653624191659)
          ·
            refine ⟨13129118576675480436287489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8752745717783653624191659 13129118576675480436287489)
            ·
              refine ⟨9846838932506610327215617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13129118576675480436287489 9846838932506610327215617)
              ·
                refine ⟨7385129199379957745411713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9846838932506610327215617 7385129199379957745411713)
                ·
                  refine ⟨5538846899534968309058785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7385129199379957745411713 5538846899534968309058785)
                  ·
                    refine ⟨4154135174651226231794089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5538846899534968309058785 4154135174651226231794089)
                    ·
                      refine ⟨3115601380988419673845567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154135174651226231794089 3115601380988419673845567)
                      ·
                        rfl

theorem cell23_6067612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6067612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067612 prefixEnd_6067612 := by exact prefixLift 6067612
  have htrace : WordTrace (prefixWord ++ tailWord_6067612) baseStart_6067612 baseEnd_6067612 := by
    simpa [prefixWord, tailWord_6067612, baseEnd_6067612] using wordTrace_append hprefix tailTrace_6067612
  have hstable : (prefixWord ++ tailWord_6067612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067612).length < 2 ^ (prefixWord ++ tailWord_6067612).sum := by decide
  have hdescent : baseEnd_6067612 < baseStart_6067612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067618 : List Nat := [3, 3, 1, 2, 1, 2, 4, 2, 5]
def baseStart_6067618 : Nat := 118140960795 + 6067618 * 2 ^ 59
def prefixEnd_6067618 : Nat := 4983230072969 + 3 ^ 40 * 6067618 * 2
def baseEnd_6067618 : Nat := 346178273541371850041171

theorem tailTrace_6067618 : CollatzResearch.WordTrace tailWord_6067618 prefixEnd_6067618 346178273541371850041171 := by
  unfold tailWord_6067618
  simp only [CollatzResearch.WordTrace]
  refine ⟨55326052333015931874526877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147536139554709151665405005 55326052333015931874526877)
  ·
    refine ⟨20747269624880974452947579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55326052333015931874526877 20747269624880974452947579)
    ·
      refine ⟨31120904437321461679421369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20747269624880974452947579 31120904437321461679421369)
      ·
        refine ⟨23340678327991096259566027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31120904437321461679421369 23340678327991096259566027)
        ·
          refine ⟨35011017491986644389349041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23340678327991096259566027 35011017491986644389349041)
          ·
            refine ⟨26258263118989983292011781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35011017491986644389349041 26258263118989983292011781)
            ·
              refine ⟨4923424334810621867252209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26258263118989983292011781 4923424334810621867252209)
              ·
                refine ⟨3692568251107966400439157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923424334810621867252209 3692568251107966400439157)
                ·
                  refine ⟨346178273541371850041171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3692568251107966400439157 346178273541371850041171)
                  ·
                    rfl

theorem cell23_6067618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_6067618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067618 prefixEnd_6067618 := by exact prefixLift 6067618
  have htrace : WordTrace (prefixWord ++ tailWord_6067618) baseStart_6067618 baseEnd_6067618 := by
    simpa [prefixWord, tailWord_6067618, baseEnd_6067618] using wordTrace_append hprefix tailTrace_6067618
  have hstable : (prefixWord ++ tailWord_6067618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067618).length < 2 ^ (prefixWord ++ tailWord_6067618).sum := by decide
  have hdescent : baseEnd_6067618 < baseStart_6067618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067647 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_6067647 : Nat := 118140960795 + 6067647 * 2 ^ 59
def prefixEnd_6067647 : Nat := 4983230072969 + 3 ^ 40 * 6067647 * 2
def baseEnd_6067647 : Nat := 3115619352811327036907905

theorem tailTrace_6067647 : CollatzResearch.WordTrace tailWord_6067647 prefixEnd_6067647 3115619352811327036907905 := by
  unfold tailWord_6067647
  simp only [CollatzResearch.WordTrace]
  refine ⟨221305267048958665450913195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147536844699305776967275463 221305267048958665450913195)
  ·
    refine ⟨331957900573437998176369793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221305267048958665450913195 331957900573437998176369793)
    ·
      refine ⟨248968425430078498632277345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331957900573437998176369793 248968425430078498632277345)
      ·
        refine ⟨186726319072558873974208009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248968425430078498632277345 186726319072558873974208009)
        ·
          refine ⟨140044739304419155480656007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186726319072558873974208009 140044739304419155480656007)
          ·
            refine ⟨210067108956628733220984011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140044739304419155480656007 210067108956628733220984011)
            ·
              refine ⟨315100663434943099831476017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210067108956628733220984011 315100663434943099831476017)
              ·
                refine ⟨236325497576207324873607013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315100663434943099831476017 236325497576207324873607013)
                ·
                  refine ⟨44311030795538873413801315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236325497576207324873607013 44311030795538873413801315)
                  ·
                    refine ⟨66466546193308310120701973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44311030795538873413801315 66466546193308310120701973)
                    ·
                      refine ⟨3115619352811327036907905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66466546193308310120701973 3115619352811327036907905)
                      ·
                        rfl

theorem cell23_6067647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_6067647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067647 prefixEnd_6067647 := by exact prefixLift 6067647
  have htrace : WordTrace (prefixWord ++ tailWord_6067647) baseStart_6067647 baseEnd_6067647 := by
    simpa [prefixWord, tailWord_6067647, baseEnd_6067647] using wordTrace_append hprefix tailTrace_6067647
  have hstable : (prefixWord ++ tailWord_6067647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067647).length < 2 ^ (prefixWord ++ tailWord_6067647).sum := by decide
  have hdescent : baseEnd_6067647 < baseStart_6067647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067657 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 8]
def baseStart_6067657 : Nat := 118140960795 + 6067657 * 2 ^ 59
def prefixEnd_6067657 : Nat := 4983230072969 + 3 ^ 40 * 6067657 * 2
def baseEnd_6067657 : Nat := 346180498624207999753651

theorem tailTrace_6067657 : CollatzResearch.WordTrace tailWord_6067657 prefixEnd_6067657 346180498624207999753651 := by
  unfold tailWord_6067657
  simp only [CollatzResearch.WordTrace]
  refine ⟨221305631778922437158777225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147537087852614958105851483 221305631778922437158777225)
  ·
    refine ⟨165979223834191827869082919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221305631778922437158777225 165979223834191827869082919)
    ·
      refine ⟨248968835751287741803624379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165979223834191827869082919 248968835751287741803624379)
      ·
        refine ⟨373453253626931612705436569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248968835751287741803624379 373453253626931612705436569)
        ·
          refine ⟨280089940220198709529077427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373453253626931612705436569 280089940220198709529077427)
          ·
            refine ⟨420134910330298064293616141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280089940220198709529077427 420134910330298064293616141)
            ·
              refine ⟨157550591373861774110106053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420134910330298064293616141 157550591373861774110106053)
              ·
                refine ⟨29540735882599082645644885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157550591373861774110106053 29540735882599082645644885)
                ·
                  refine ⟨346180498624207999753651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29540735882599082645644885 346180498624207999753651)
                  ·
                    rfl

theorem cell23_6067657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 8].length) (baseStart_6067657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067657 prefixEnd_6067657 := by exact prefixLift 6067657
  have htrace : WordTrace (prefixWord ++ tailWord_6067657) baseStart_6067657 baseEnd_6067657 := by
    simpa [prefixWord, tailWord_6067657, baseEnd_6067657] using wordTrace_append hprefix tailTrace_6067657
  have hstable : (prefixWord ++ tailWord_6067657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067657).length < 2 ^ (prefixWord ++ tailWord_6067657).sum := by decide
  have hdescent : baseEnd_6067657 < baseStart_6067657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067674 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 8]
def baseStart_6067674 : Nat := 118140960795 + 6067674 * 2 ^ 59
def prefixEnd_6067674 : Nat := 4983230072969 + 3 ^ 40 * 6067674 * 2
def baseEnd_6067674 : Nat := 346181468532110936807809

theorem tailTrace_6067674 : CollatzResearch.WordTrace tailWord_6067674 prefixEnd_6067674 346181468532110936807809 := by
  unfold tailWord_6067674
  simp only [CollatzResearch.WordTrace]
  refine ⟨55326562954965212265536519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147537501213240566041430717 55326562954965212265536519)
  ·
    refine ⟨82989844432447818398304779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55326562954965212265536519 82989844432447818398304779)
    ·
      refine ⟨124484766648671727597457169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82989844432447818398304779 124484766648671727597457169)
      ·
        refine ⟨93363574986503795698092877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124484766648671727597457169 93363574986503795698092877)
        ·
          refine ⟨35011340619938923386784829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93363574986503795698092877 35011340619938923386784829)
          ·
            refine ⟨13129252732477096270044311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35011340619938923386784829 13129252732477096270044311)
            ·
              refine ⟨19693879098715644405066467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13129252732477096270044311 19693879098715644405066467)
              ·
                refine ⟨29540818648073466607599701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19693879098715644405066467 29540818648073466607599701)
                ·
                  refine ⟨346181468532110936807809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29540818648073466607599701 346181468532110936807809)
                  ·
                    rfl

theorem cell23_6067674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_6067674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067674 prefixEnd_6067674 := by exact prefixLift 6067674
  have htrace : WordTrace (prefixWord ++ tailWord_6067674) baseStart_6067674 baseEnd_6067674 := by
    simpa [prefixWord, tailWord_6067674, baseEnd_6067674] using wordTrace_append hprefix tailTrace_6067674
  have hstable : (prefixWord ++ tailWord_6067674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067674).length < 2 ^ (prefixWord ++ tailWord_6067674).sum := by decide
  have hdescent : baseEnd_6067674 < baseStart_6067674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067694 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_6067694 : Nat := 118140960795 + 6067694 * 2 ^ 59
def prefixEnd_6067694 : Nat := 4983230072969 + 3 ^ 40 * 6067694 * 2
def baseEnd_6067694 : Nat := 3115643486402088353020189

theorem tailTrace_6067694 : CollatzResearch.WordTrace tailWord_6067694 prefixEnd_6067694 3115643486402088353020189 := by
  unfold tailWord_6067694
  simp only [CollatzResearch.WordTrace]
  refine ⟨27663372659973549059734267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147537987519858928318582757 27663372659973549059734267)
  ·
    refine ⟨41495058989960323589601401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27663372659973549059734267 41495058989960323589601401)
    ·
      refine ⟨31121294242470242692201051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41495058989960323589601401 31121294242470242692201051)
      ·
        refine ⟨46681941363705364038301577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31121294242470242692201051 46681941363705364038301577)
        ·
          refine ⟨35011456022779023028726183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46681941363705364038301577 35011456022779023028726183)
          ·
            refine ⟨52517184034168534543089275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35011456022779023028726183 52517184034168534543089275)
            ·
              refine ⟨78775776051252801814633913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52517184034168534543089275 78775776051252801814633913)
              ·
                refine ⟨59081832038439601360975435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78775776051252801814633913 59081832038439601360975435)
                ·
                  refine ⟨88622748057659402041463153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59081832038439601360975435 88622748057659402041463153)
                  ·
                    refine ⟨66467061043244551531097365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88622748057659402041463153 66467061043244551531097365)
                    ·
                      refine ⟨3115643486402088353020189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66467061043244551531097365 3115643486402088353020189)
                      ·
                        rfl

theorem cell23_6067694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_6067694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067694 prefixEnd_6067694 := by exact prefixLift 6067694
  have htrace : WordTrace (prefixWord ++ tailWord_6067694) baseStart_6067694 baseEnd_6067694 := by
    simpa [prefixWord, tailWord_6067694, baseEnd_6067694] using wordTrace_append hprefix tailTrace_6067694
  have hstable : (prefixWord ++ tailWord_6067694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067694).length < 2 ^ (prefixWord ++ tailWord_6067694).sum := by decide
  have hdescent : baseEnd_6067694 < baseStart_6067694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067741 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_6067741 : Nat := 118140960795 + 6067741 * 2 ^ 59
def prefixEnd_6067741 : Nat := 4983230072969 + 3 ^ 40 * 6067741 * 2
def baseEnd_6067741 : Nat := 3115667619992849669132473

theorem tailTrace_6067741 : CollatzResearch.WordTrace tailWord_6067741 prefixEnd_6067741 3115667619992849669132473 := by
  unfold tailWord_6067741
  simp only [CollatzResearch.WordTrace]
  refine ⟨221308695510618119504835077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147539130340412079669890051 221308695510618119504835077)
  ·
    refine ⟨41495380408240897407156577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221308695510618119504835077 41495380408240897407156577)
    ·
      refine ⟨31121535306180673055367433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41495380408240897407156577 31121535306180673055367433)
      ·
        refine ⟨23341151479635504791525575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31121535306180673055367433 23341151479635504791525575)
        ·
          refine ⟨35011727219453257187288363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23341151479635504791525575 35011727219453257187288363)
          ·
            refine ⟨52517590829179885780932545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35011727219453257187288363 52517590829179885780932545)
            ·
              refine ⟨39388193121884914335699409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52517590829179885780932545 39388193121884914335699409)
              ·
                refine ⟨29541144841413685751774557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39388193121884914335699409 29541144841413685751774557)
                ·
                  refine ⟨11077929315530132156915459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29541144841413685751774557 11077929315530132156915459)
                  ·
                    refine ⟨16616893973295198235373189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11077929315530132156915459 16616893973295198235373189)
                    ·
                      refine ⟨3115667619992849669132473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16616893973295198235373189 3115667619992849669132473)
                      ·
                        rfl

theorem cell23_6067741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_6067741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067741 prefixEnd_6067741 := by exact prefixLift 6067741
  have htrace : WordTrace (prefixWord ++ tailWord_6067741) baseStart_6067741 baseEnd_6067741 := by
    simpa [prefixWord, tailWord_6067741, baseEnd_6067741] using wordTrace_append hprefix tailTrace_6067741
  have hstable : (prefixWord ++ tailWord_6067741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067741).length < 2 ^ (prefixWord ++ tailWord_6067741).sum := by decide
  have hdescent : baseEnd_6067741 < baseStart_6067741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067742 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_6067742 : Nat := 118140960795 + 6067742 * 2 ^ 59
def prefixEnd_6067742 : Nat := 4983230072969 + 3 ^ 40 * 6067742 * 2
def baseEnd_6067742 : Nat := 346185348163722685024441

theorem tailTrace_6067742 : CollatzResearch.WordTrace tailWord_6067742 prefixEnd_6067742 346185348163722685024441 := by
  unfold tailWord_6067742
  simp only [CollatzResearch.WordTrace]
  refine ⟨27663591497951812084452685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147539154655742997783747653 27663591497951812084452685)
  ·
    refine ⟨10373846811731929531669757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27663591497951812084452685 10373846811731929531669757)
    ·
      refine ⟨3890192554399473574376159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10373846811731929531669757 3890192554399473574376159)
      ·
        refine ⟨5835288831599210361564239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3890192554399473574376159 5835288831599210361564239)
        ·
          refine ⟨8752933247398815542346359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5835288831599210361564239 8752933247398815542346359)
          ·
            refine ⟨13129399871098223313519539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8752933247398815542346359 13129399871098223313519539)
            ·
              refine ⟨19694099806647334970279309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13129399871098223313519539 19694099806647334970279309)
              ·
                refine ⟨7385287427492750613854741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19694099806647334970279309 7385287427492750613854741)
                ·
                  refine ⟨346185348163722685024441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7385287427492750613854741 346185348163722685024441)
                  ·
                    rfl

theorem cell23_6067742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_6067742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067742 prefixEnd_6067742 := by exact prefixLift 6067742
  have htrace : WordTrace (prefixWord ++ tailWord_6067742) baseStart_6067742 baseEnd_6067742 := by
    simpa [prefixWord, tailWord_6067742, baseEnd_6067742] using wordTrace_append hprefix tailTrace_6067742
  have hstable : (prefixWord ++ tailWord_6067742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067742).length < 2 ^ (prefixWord ++ tailWord_6067742).sum := by decide
  have hdescent : baseEnd_6067742 < baseStart_6067742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067758 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6067758 : Nat := 118140960795 + 6067758 * 2 ^ 59
def prefixEnd_6067758 : Nat := 4983230072969 + 3 ^ 40 * 6067758 * 2
def baseEnd_6067758 : Nat := 3115676349163976102619895

theorem tailTrace_6067758 : CollatzResearch.WordTrace tailWord_6067758 prefixEnd_6067758 3115676349163976102619895 := by
  unfold tailWord_6067758
  simp only [CollatzResearch.WordTrace]
  refine ⟨27663664443944566426025491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147539543701037687605469285 27663664443944566426025491)
  ·
    refine ⟨41495496665916849639038237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27663664443944566426025491 41495496665916849639038237)
    ·
      refine ⟨15560811249718818614639339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41495496665916849639038237 15560811249718818614639339)
      ·
        refine ⟨23341216874578227921959009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15560811249718818614639339 23341216874578227921959009)
        ·
          refine ⟨17505912655933670941469257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23341216874578227921959009 17505912655933670941469257)
          ·
            refine ⟨13129434491950253206101943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17505912655933670941469257 13129434491950253206101943)
            ·
              refine ⟨19694151737925379809152915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13129434491950253206101943 19694151737925379809152915)
              ·
                refine ⟨29541227606888069713729373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19694151737925379809152915 29541227606888069713729373)
                ·
                  refine ⟨11077960352583026142648515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29541227606888069713729373 11077960352583026142648515)
                  ·
                    refine ⟨16616940528874539213972773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11077960352583026142648515 16616940528874539213972773)
                    ·
                      refine ⟨3115676349163976102619895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16616940528874539213972773 3115676349163976102619895)
                      ·
                        rfl

theorem cell23_6067758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6067758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067758 prefixEnd_6067758 := by exact prefixLift 6067758
  have htrace : WordTrace (prefixWord ++ tailWord_6067758) baseStart_6067758 baseEnd_6067758 := by
    simpa [prefixWord, tailWord_6067758, baseEnd_6067758] using wordTrace_append hprefix tailTrace_6067758
  have hstable : (prefixWord ++ tailWord_6067758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067758).length < 2 ^ (prefixWord ++ tailWord_6067758).sum := by decide
  have hdescent : baseEnd_6067758 < baseStart_6067758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067841 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 2, 6]
def baseStart_6067841 : Nat := 118140960795 + 6067841 * 2 ^ 59
def prefixEnd_6067841 : Nat := 4983230072969 + 3 ^ 40 * 6067841 * 2
def baseEnd_6067841 : Nat := 1038572989352766425960671

theorem tailTrace_6067841 : CollatzResearch.WordTrace tailWord_6067841 prefixEnd_6067841 1038572989352766425960671 := by
  unfold tailWord_6067841
  simp only [CollatzResearch.WordTrace]
  refine ⟨221312342810255836583475377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147541561873503891055650251 221312342810255836583475377)
  ·
    refine ⟨165984257107691877437606533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221312342810255836583475377 165984257107691877437606533)
    ·
      refine ⟨31122048207692227019551225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165984257107691877437606533 31122048207692227019551225)
      ·
        refine ⟨23341536155769170264663419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31122048207692227019551225 23341536155769170264663419)
        ·
          refine ⟨35012304233653755396995129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23341536155769170264663419 35012304233653755396995129)
          ·
            refine ⟨26259228175240316547746347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35012304233653755396995129 26259228175240316547746347)
            ·
              refine ⟨39388842262860474821619521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26259228175240316547746347 39388842262860474821619521)
              ·
                refine ⟨29541631697145356116214641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39388842262860474821619521 29541631697145356116214641)
                ·
                  refine ⟨22156223772859017087160981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29541631697145356116214641 22156223772859017087160981)
                  ·
                    refine ⟨1038572989352766425960671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22156223772859017087160981 1038572989352766425960671)
                    ·
                      rfl

theorem cell23_6067841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_6067841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067841 prefixEnd_6067841 := by exact prefixLift 6067841
  have htrace : WordTrace (prefixWord ++ tailWord_6067841) baseStart_6067841 baseEnd_6067841 := by
    simpa [prefixWord, tailWord_6067841, baseEnd_6067841] using wordTrace_append hprefix tailTrace_6067841
  have hstable : (prefixWord ++ tailWord_6067841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067841).length < 2 ^ (prefixWord ++ tailWord_6067841).sum := by decide
  have hdescent : baseEnd_6067841 < baseStart_6067841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067888 : List Nat := [2, 1, 1, 1, 2, 1, 7, 3, 5]
def baseStart_6067888 : Nat := 118140960795 + 6067888 * 2 ^ 59
def prefixEnd_6067888 : Nat := 4983230072969 + 3 ^ 40 * 6067888 * 2
def baseEnd_6067888 : Nat := 346193677961006732666033

theorem tailTrace_6067888 : CollatzResearch.WordTrace tailWord_6067888 prefixEnd_6067888 346193677961006732666033 := by
  unfold tailWord_6067888
  simp only [CollatzResearch.WordTrace]
  refine ⟨110657028520542781805218159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147542704694057042406957545 110657028520542781805218159)
  ·
    refine ⟨165985542780814172707827239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110657028520542781805218159 165985542780814172707827239)
    ·
      refine ⟨248978314171221259061740859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165985542780814172707827239 248978314171221259061740859)
      ·
        refine ⟨373467471256831888592611289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248978314171221259061740859 373467471256831888592611289)
        ·
          refine ⟨280100603442623916444458467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373467471256831888592611289 280100603442623916444458467)
          ·
            refine ⟨420150905163935874666687701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280100603442623916444458467 420150905163935874666687701)
            ·
              refine ⟨9847286839779747062500493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 420150905163935874666687701 9847286839779747062500493)
              ·
                refine ⟨3692732564917405148437685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9847286839779747062500493 3692732564917405148437685)
                ·
                  refine ⟨346193677961006732666033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3692732564917405148437685 346193677961006732666033)
                  ·
                    rfl

theorem cell23_6067888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 5].length) (baseStart_6067888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067888 prefixEnd_6067888 := by exact prefixLift 6067888
  have htrace : WordTrace (prefixWord ++ tailWord_6067888) baseStart_6067888 baseEnd_6067888 := by
    simpa [prefixWord, tailWord_6067888, baseEnd_6067888] using wordTrace_append hprefix tailTrace_6067888
  have hstable : (prefixWord ++ tailWord_6067888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067888).length < 2 ^ (prefixWord ++ tailWord_6067888).sum := by decide
  have hdescent : baseEnd_6067888 < baseStart_6067888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067911 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_6067911 : Nat := 118140960795 + 6067911 * 2 ^ 59
def prefixEnd_6067911 : Nat := 4983230072969 + 3 ^ 40 * 6067911 * 2
def baseEnd_6067911 : Nat := 3115754911704114004006691

theorem tailTrace_6067911 : CollatzResearch.WordTrace tailWord_6067911 prefixEnd_6067911 3115754911704114004006691 := by
  unfold tailWord_6067911
  simp only [CollatzResearch.WordTrace]
  refine ⟨221314895920002238538523587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147543263946668159025682391 221314895920002238538523587)
  ·
    refine ⟨331972343880003357807785381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221314895920002238538523587 331972343880003357807785381)
    ·
      refine ⟨62244814477500629588959759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331972343880003357807785381 62244814477500629588959759)
      ·
        refine ⟨93367221716250944383439639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62244814477500629588959759 93367221716250944383439639)
        ·
          refine ⟨140050832574376416575159459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93367221716250944383439639 140050832574376416575159459)
          ·
            refine ⟨210076248861564624862739189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140050832574376416575159459 210076248861564624862739189)
            ·
              refine ⟨19694648330771683580881799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210076248861564624862739189 19694648330771683580881799)
              ·
                refine ⟨29541972496157525371322699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19694648330771683580881799 29541972496157525371322699)
                ·
                  refine ⟨44312958744236288056984049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29541972496157525371322699 44312958744236288056984049)
                  ·
                    refine ⟨33234719058177216042738037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44312958744236288056984049 33234719058177216042738037)
                    ·
                      refine ⟨3115754911704114004006691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33234719058177216042738037 3115754911704114004006691)
                      ·
                        rfl

theorem cell23_6067911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_6067911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067911 prefixEnd_6067911 := by exact prefixLift 6067911
  have htrace : WordTrace (prefixWord ++ tailWord_6067911) baseStart_6067911 baseEnd_6067911 := by
    simpa [prefixWord, tailWord_6067911, baseEnd_6067911] using wordTrace_append hprefix tailTrace_6067911
  have hstable : (prefixWord ++ tailWord_6067911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067911).length < 2 ^ (prefixWord ++ tailWord_6067911).sum := by decide
  have hdescent : baseEnd_6067911 < baseStart_6067911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067916 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6067916 : Nat := 118140960795 + 6067916 * 2 ^ 59
def prefixEnd_6067916 : Nat := 4983230072969 + 3 ^ 40 * 6067916 * 2
def baseEnd_6067916 : Nat := 3115757479107386484444169

theorem tailTrace_6067916 : CollatzResearch.WordTrace tailWord_6067916 prefixEnd_6067916 3115757479107386484444169 := by
  unfold tailWord_6067916
  simp only [CollatzResearch.WordTrace]
  refine ⟨110657539142492062196227801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147543385523322749594970401 110657539142492062196227801)
  ·
    refine ⟨82993154356869046647170851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110657539142492062196227801 82993154356869046647170851)
    ·
      refine ⟨124489731535303569970756277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82993154356869046647170851 124489731535303569970756277)
      ·
        refine ⟨11670912331434709684758401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124489731535303569970756277 11670912331434709684758401)
        ·
          refine ⟨8753184248576032263568801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11670912331434709684758401 8753184248576032263568801)
          ·
            refine ⟨6564888186432024197676601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8753184248576032263568801 6564888186432024197676601)
            ·
              refine ⟨4923666139824018148257451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6564888186432024197676601 4923666139824018148257451)
              ·
                refine ⟨7385499209736027222386177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923666139824018148257451 7385499209736027222386177)
                ·
                  refine ⟨5539124407302020416789633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7385499209736027222386177 5539124407302020416789633)
                  ·
                    refine ⟨4154343305476515312592225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5539124407302020416789633 4154343305476515312592225)
                    ·
                      refine ⟨3115757479107386484444169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154343305476515312592225 3115757479107386484444169)
                      ·
                        rfl

theorem cell23_6067916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6067916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067916 prefixEnd_6067916 := by exact prefixLift 6067916
  have htrace : WordTrace (prefixWord ++ tailWord_6067916) baseStart_6067916 baseEnd_6067916 := by
    simpa [prefixWord, tailWord_6067916, baseEnd_6067916] using wordTrace_append hprefix tailTrace_6067916
  have hstable : (prefixWord ++ tailWord_6067916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067916).length < 2 ^ (prefixWord ++ tailWord_6067916).sum := by decide
  have hdescent : baseEnd_6067916 < baseStart_6067916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067951 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_6067951 : Nat := 118140960795 + 6067951 * 2 ^ 59
def prefixEnd_6067951 : Nat := 4983230072969 + 3 ^ 40 * 6067951 * 2
def baseEnd_6067951 : Nat := 3115775450930293847506507

theorem tailTrace_6067951 : CollatzResearch.WordTrace tailWord_6067951 prefixEnd_6067951 3115775450930293847506507 := by
  unfold tailWord_6067951
  simp only [CollatzResearch.WordTrace]
  refine ⟨221316354839857325369979707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147544236559904883579986471 221316354839857325369979707)
  ·
    refine ⟨331974532259785988054969561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221316354839857325369979707 331974532259785988054969561)
    ·
      refine ⟨248980899194839491041227171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331974532259785988054969561 248980899194839491041227171)
      ·
        refine ⟨373471348792259236561840757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248980899194839491041227171 373471348792259236561840757)
        ·
          refine ⟨35012938949274303427672571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 373471348792259236561840757 35012938949274303427672571)
          ·
            refine ⟨52519408423911455141508857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35012938949274303427672571 52519408423911455141508857)
            ·
              refine ⟨39389556317933591356131643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52519408423911455141508857 39389556317933591356131643)
              ·
                refine ⟨59084334476900387034197465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39389556317933591356131643 59084334476900387034197465)
                ·
                  refine ⟨44313250857675290275648099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59084334476900387034197465 44313250857675290275648099)
                  ·
                    refine ⟨66469876286512935413472149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44313250857675290275648099 66469876286512935413472149)
                    ·
                      refine ⟨3115775450930293847506507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66469876286512935413472149 3115775450930293847506507)
                      ·
                        rfl

theorem cell23_6067951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_6067951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067951 prefixEnd_6067951 := by exact prefixLift 6067951
  have htrace : WordTrace (prefixWord ++ tailWord_6067951) baseStart_6067951 baseEnd_6067951 := by
    simpa [prefixWord, tailWord_6067951, baseEnd_6067951] using wordTrace_append hprefix tailTrace_6067951
  have hstable : (prefixWord ++ tailWord_6067951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067951).length < 2 ^ (prefixWord ++ tailWord_6067951).sum := by decide
  have hdescent : baseEnd_6067951 < baseStart_6067951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067956 : List Nat := [2, 6, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6067956 : Nat := 118140960795 + 6067956 * 2 ^ 59
def prefixEnd_6067956 : Nat := 4983230072969 + 3 ^ 40 * 6067956 * 2
def baseEnd_6067956 : Nat := 346197557592618480882665

theorem tailTrace_6067956 : CollatzResearch.WordTrace tailWord_6067956 prefixEnd_6067956 346197557592618480882665 := by
  unfold tailWord_6067956
  simp only [CollatzResearch.WordTrace]
  refine ⟨110658268602419605611955861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147544358136559474149274481 110658268602419605611955861)
  ·
    refine ⟨5187106340738419013060431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110658268602419605611955861 5187106340738419013060431)
    ·
      refine ⟨7780659511107628519590647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5187106340738419013060431 7780659511107628519590647)
      ·
        refine ⟨11670989266661442779385971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7780659511107628519590647 11670989266661442779385971)
        ·
          refine ⟨17506483899992164169078957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11670989266661442779385971 17506483899992164169078957)
          ·
            refine ⟨6564931462497061563404609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17506483899992164169078957 6564931462497061563404609)
            ·
              refine ⟨4923698596872796172553457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6564931462497061563404609 4923698596872796172553457)
              ·
                refine ⟨3692773947654597129415093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923698596872796172553457 3692773947654597129415093)
                ·
                  refine ⟨346197557592618480882665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3692773947654597129415093 346197557592618480882665)
                  ·
                    rfl

theorem cell23_6067956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6067956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067956 prefixEnd_6067956 := by exact prefixLift 6067956
  have htrace : WordTrace (prefixWord ++ tailWord_6067956) baseStart_6067956 baseEnd_6067956 := by
    simpa [prefixWord, tailWord_6067956, baseEnd_6067956] using wordTrace_append hprefix tailTrace_6067956
  have hstable : (prefixWord ++ tailWord_6067956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067956).length < 2 ^ (prefixWord ++ tailWord_6067956).sum := by decide
  have hdescent : baseEnd_6067956 < baseStart_6067956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6067978 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 6]
def baseStart_6067978 : Nat := 118140960795 + 6067978 * 2 ^ 59
def prefixEnd_6067978 : Nat := 4983230072969 + 3 ^ 40 * 6067978 * 2
def baseEnd_6067978 : Nat := 346198812767551693540987

theorem tailTrace_6067978 : CollatzResearch.WordTrace tailWord_6067978 prefixEnd_6067978 346198812767551693540987 := by
  unfold tailWord_6067978
  simp only [CollatzResearch.WordTrace]
  refine ⟨55329334902689877245303147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147544893073839672654141725 55329334902689877245303147)
  ·
    refine ⟨82994002354034815867954721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55329334902689877245303147 82994002354034815867954721)
    ·
      refine ⟨62245501765526111900966041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82994002354034815867954721 62245501765526111900966041)
      ·
        refine ⟨46684126324144583925724531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62245501765526111900966041 46684126324144583925724531)
        ·
          refine ⟨70026189486216875888586797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46684126324144583925724531 70026189486216875888586797)
          ·
            refine ⟨26259821057331328458220049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70026189486216875888586797 26259821057331328458220049)
            ·
              refine ⟨19694865792998496343665037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26259821057331328458220049 19694865792998496343665037)
              ·
                refine ⟨7385574672374436128874389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19694865792998496343665037 7385574672374436128874389)
                ·
                  refine ⟨346198812767551693540987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7385574672374436128874389 346198812767551693540987)
                  ·
                    rfl

theorem cell23_6067978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_6067978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6067978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6067978 prefixEnd_6067978 := by exact prefixLift 6067978
  have htrace : WordTrace (prefixWord ++ tailWord_6067978) baseStart_6067978 baseEnd_6067978 := by
    simpa [prefixWord, tailWord_6067978, baseEnd_6067978] using wordTrace_append hprefix tailTrace_6067978
  have hstable : (prefixWord ++ tailWord_6067978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6067978).length < 2 ^ (prefixWord ++ tailWord_6067978).sum := by decide
  have hdescent : baseEnd_6067978 < baseStart_6067978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6067978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068011 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 4]
def baseStart_6068011 : Nat := 118140960795 + 6068011 * 2 ^ 59
def prefixEnd_6068011 : Nat := 4983230072969 + 3 ^ 40 * 6068011 * 2
def baseEnd_6068011 : Nat := 3115806259769563612756231

theorem tailTrace_6068011 : CollatzResearch.WordTrace tailWord_6068011 prefixEnd_6068011 3115806259769563612756231 := by
  unfold tailWord_6068011
  simp only [CollatzResearch.WordTrace]
  refine ⟨221318543219639955617163887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147545695479759970411442591 221318543219639955617163887)
  ·
    refine ⟨331977814829459933425745831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221318543219639955617163887 331977814829459933425745831)
    ·
      refine ⟨497966722244189900138618747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331977814829459933425745831 497966722244189900138618747)
      ·
        refine ⟨746950083366284850207928121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497966722244189900138618747 746950083366284850207928121)
        ·
          refine ⟨560212562524713637655946091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746950083366284850207928121 560212562524713637655946091)
          ·
            refine ⟨840318843787070456483919137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560212562524713637655946091 840318843787070456483919137)
            ·
              refine ⟨630239132840302842362939353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840318843787070456483919137 630239132840302842362939353)
              ·
                refine ⟨472679349630227131772204515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630239132840302842362939353 472679349630227131772204515)
                ·
                  refine ⟨709019024445340697658306773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472679349630227131772204515 709019024445340697658306773)
                  ·
                    refine ⟨16617633385437672601366565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 709019024445340697658306773 16617633385437672601366565)
                    ·
                      refine ⟨3115806259769563612756231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16617633385437672601366565 3115806259769563612756231)
                      ·
                        rfl

theorem cell23_6068011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 4].length) (baseStart_6068011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068011 prefixEnd_6068011 := by exact prefixLift 6068011
  have htrace : WordTrace (prefixWord ++ tailWord_6068011) baseStart_6068011 baseEnd_6068011 := by
    simpa [prefixWord, tailWord_6068011, baseEnd_6068011] using wordTrace_append hprefix tailTrace_6068011
  have hstable : (prefixWord ++ tailWord_6068011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068011).length < 2 ^ (prefixWord ++ tailWord_6068011).sum := by decide
  have hdescent : baseEnd_6068011 < baseStart_6068011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068028 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_6068028 : Nat := 118140960795 + 6068028 * 2 ^ 59
def prefixEnd_6068028 : Nat := 4983230072969 + 3 ^ 40 * 6068028 * 2
def baseEnd_6068028 : Nat := 3115814988940690046243653

theorem tailTrace_6068028 : CollatzResearch.WordTrace tailWord_6068028 prefixEnd_6068028 3115814988940690046243653 := by
  unfold tailWord_6068028
  simp only [CollatzResearch.WordTrace]
  refine ⟨110659581630289183760266369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147546108840385578347021825 110659581630289183760266369)
  ·
    refine ⟨82994686222716887820199777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110659581630289183760266369 82994686222716887820199777)
    ·
      refine ⟨62246014667037665865149833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82994686222716887820199777 62246014667037665865149833)
      ·
        refine ⟨46684511000278249398862375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62246014667037665865149833 46684511000278249398862375)
        ·
          refine ⟨70026766500417374098293563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46684511000278249398862375 70026766500417374098293563)
          ·
            refine ⟨105040149750626061147440345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70026766500417374098293563 105040149750626061147440345)
            ·
              refine ⟨78780112312969545860580259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105040149750626061147440345 78780112312969545860580259)
              ·
                refine ⟨118170168469454318790870389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78780112312969545860580259 118170168469454318790870389)
                ·
                  refine ⟨11078453294011342386644099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118170168469454318790870389 11078453294011342386644099)
                  ·
                    refine ⟨16617679941017013579966149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11078453294011342386644099 16617679941017013579966149)
                    ·
                      refine ⟨3115814988940690046243653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16617679941017013579966149 3115814988940690046243653)
                      ·
                        rfl

theorem cell23_6068028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_6068028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068028 prefixEnd_6068028 := by exact prefixLift 6068028
  have htrace : WordTrace (prefixWord ++ tailWord_6068028) baseStart_6068028 baseEnd_6068028 := by
    simpa [prefixWord, tailWord_6068028, baseEnd_6068028] using wordTrace_append hprefix tailTrace_6068028
  have hstable : (prefixWord ++ tailWord_6068028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068028).length < 2 ^ (prefixWord ++ tailWord_6068028).sum := by decide
  have hdescent : baseEnd_6068028 < baseStart_6068028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068058 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_6068058 : Nat := 118140960795 + 6068058 * 2 ^ 59
def prefixEnd_6068058 : Nat := 4983230072969 + 3 ^ 40 * 6068058 * 2
def baseEnd_6068058 : Nat := 3115830393360324928868515

theorem tailTrace_6068058 : CollatzResearch.WordTrace tailWord_6068058 prefixEnd_6068058 3115830393360324928868515 := by
  unfold tailWord_6068058
  simp only [CollatzResearch.WordTrace]
  refine ⟨55330064362617420661031207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147546838300313121762749885 55330064362617420661031207)
  ·
    refine ⟨82995096543926130991546811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55330064362617420661031207 82995096543926130991546811)
    ·
      refine ⟨124492644815889196487320217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82995096543926130991546811 124492644815889196487320217)
      ·
        refine ⟨93369483611916897365490163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124492644815889196487320217 93369483611916897365490163)
        ·
          refine ⟨140054225417875346048235245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93369483611916897365490163 140054225417875346048235245)
          ·
            refine ⟨52520334531703254768088217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140054225417875346048235245 52520334531703254768088217)
            ·
              refine ⟨39390250898777441076066163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52520334531703254768088217 39390250898777441076066163)
              ·
                refine ⟨59085376348166161614099245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39390250898777441076066163 59085376348166161614099245)
                ·
                  refine ⟨22157016130562310605287217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59085376348166161614099245 22157016130562310605287217)
                  ·
                    refine ⟨16617762097921732953965413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22157016130562310605287217 16617762097921732953965413)
                    ·
                      refine ⟨3115830393360324928868515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16617762097921732953965413 3115830393360324928868515)
                      ·
                        rfl

theorem cell23_6068058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_6068058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068058 prefixEnd_6068058 := by exact prefixLift 6068058
  have htrace : WordTrace (prefixWord ++ tailWord_6068058) baseStart_6068058 baseEnd_6068058 := by
    simpa [prefixWord, tailWord_6068058, baseEnd_6068058] using wordTrace_append hprefix tailTrace_6068058
  have hstable : (prefixWord ++ tailWord_6068058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068058).length < 2 ^ (prefixWord ++ tailWord_6068058).sum := by decide
  have hdescent : baseEnd_6068058 < baseStart_6068058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068065 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_6068065 : Nat := 118140960795 + 6068065 * 2 ^ 59
def prefixEnd_6068065 : Nat := 4983230072969 + 3 ^ 40 * 6068065 * 2
def baseEnd_6068065 : Nat := 3115833987724906401480983

theorem tailTrace_6068065 : CollatzResearch.WordTrace tailWord_6068065 prefixEnd_6068065 3115833987724906401480983 := by
  unfold tailWord_6068065
  simp only [CollatzResearch.WordTrace]
  refine ⟨221320512761444322839629649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147547008507629548559753099 221320512761444322839629649)
  ·
    refine ⟨165990384571083242129722237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221320512761444322839629649 165990384571083242129722237)
    ·
      refine ⟨62246394214156215798645839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165990384571083242129722237 62246394214156215798645839)
      ·
        refine ⟨93369591321234323697968759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62246394214156215798645839 93369591321234323697968759)
        ·
          refine ⟨140054386981851485546953139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93369591321234323697968759 140054386981851485546953139)
          ·
            refine ⟨210081580472777228320429709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140054386981851485546953139 210081580472777228320429709)
            ·
              refine ⟨78780592677291460620161141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210081580472777228320429709 78780592677291460620161141)
              ·
                refine ⟨7385680563496074433140107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78780592677291460620161141 7385680563496074433140107)
                ·
                  refine ⟨11078520845244111649710161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7385680563496074433140107 11078520845244111649710161)
                  ·
                    refine ⟨8308890633933083737282621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11078520845244111649710161 8308890633933083737282621)
                    ·
                      refine ⟨3115833987724906401480983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8308890633933083737282621 3115833987724906401480983)
                      ·
                        rfl

theorem cell23_6068065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_6068065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068065 prefixEnd_6068065 := by exact prefixLift 6068065
  have htrace : WordTrace (prefixWord ++ tailWord_6068065) baseStart_6068065 baseEnd_6068065 := by
    simpa [prefixWord, tailWord_6068065, baseEnd_6068065] using wordTrace_append hprefix tailTrace_6068065
  have hstable : (prefixWord ++ tailWord_6068065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068065).length < 2 ^ (prefixWord ++ tailWord_6068065).sum := by decide
  have hdescent : baseEnd_6068065 < baseStart_6068065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068128 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 2, 6]
def baseStart_6068128 : Nat := 118140960795 + 6068128 * 2 ^ 59
def prefixEnd_6068128 : Nat := 4983230072969 + 3 ^ 40 * 6068128 * 2
def baseEnd_6068128 : Nat := 1038622112335379884997731

theorem tailTrace_6068128 : CollatzResearch.WordTrace tailWord_6068128 prefixEnd_6068128 1038622112335379884997731 := by
  unfold tailWord_6068128
  simp only [CollatzResearch.WordTrace]
  refine ⟨110661405280108042299586519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147548540373477389732782025 110661405280108042299586519)
  ·
    refine ⟨165992107920162063449379779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110661405280108042299586519 165992107920162063449379779)
    ·
      refine ⟨248988161880243095174069669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165992107920162063449379779 248988161880243095174069669)
      ·
        refine ⟨46685280352545580345138063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248988161880243095174069669 46685280352545580345138063)
        ·
          refine ⟨70027920528818370517707095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46685280352545580345138063 70027920528818370517707095)
          ·
            refine ⟨105041880793227555776560643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70027920528818370517707095 105041880793227555776560643)
            ·
              refine ⟨157562821189841333664840965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105041880793227555776560643 157562821189841333664840965)
              ·
                refine ⟨29543028973095250062157681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157562821189841333664840965 29543028973095250062157681)
                ·
                  refine ⟨22157271729821437546618261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29543028973095250062157681 22157271729821437546618261)
                  ·
                    refine ⟨1038622112335379884997731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22157271729821437546618261 1038622112335379884997731)
                    ·
                      rfl

theorem cell23_6068128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_6068128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068128 prefixEnd_6068128 := by exact prefixLift 6068128
  have htrace : WordTrace (prefixWord ++ tailWord_6068128) baseStart_6068128 baseEnd_6068128 := by
    simpa [prefixWord, tailWord_6068128, baseEnd_6068128] using wordTrace_append hprefix tailTrace_6068128
  have hstable : (prefixWord ++ tailWord_6068128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068128).length < 2 ^ (prefixWord ++ tailWord_6068128).sum := by decide
  have hdescent : baseEnd_6068128 < baseStart_6068128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068130 : List Nat := [3, 3, 1, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_6068130 : Nat := 118140960795 + 6068130 * 2 ^ 59
def prefixEnd_6068130 : Nat := 4983230072969 + 3 ^ 40 * 6068130 * 2
def baseEnd_6068130 : Nat := 3115867363967448647168185

theorem tailTrace_6068130 : CollatzResearch.WordTrace tailWord_6068130 prefixEnd_6068130 3115867363967448647168185 := by
  unfold tailWord_6068130
  simp only [CollatzResearch.WordTrace]
  refine ⟨55330720876552209735186461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147548589004139225960497229 55330720876552209735186461)
  ·
    refine ⟨20749020328707078650694923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55330720876552209735186461 20749020328707078650694923)
    ·
      refine ⟨31123530493060617976042385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20749020328707078650694923 31123530493060617976042385)
      ·
        refine ⟨23342647869795463482031789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31123530493060617976042385 23342647869795463482031789)
        ·
          refine ⟨8753492951173298805761921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23342647869795463482031789 8753492951173298805761921)
          ·
            refine ⟨6565119713379974104321441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8753492951173298805761921 6565119713379974104321441)
            ·
              refine ⟨4923839785034980578241081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6565119713379974104321441 4923839785034980578241081)
              ·
                refine ⟨3692879838776235433680811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923839785034980578241081 3692879838776235433680811)
                ·
                  refine ⟨5539319758164353150521217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692879838776235433680811 5539319758164353150521217)
                  ·
                    refine ⟨4154489818623264862890913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5539319758164353150521217 4154489818623264862890913)
                    ·
                      refine ⟨3115867363967448647168185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154489818623264862890913 3115867363967448647168185)
                      ·
                        rfl

theorem cell23_6068130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_6068130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068130 prefixEnd_6068130 := by exact prefixLift 6068130
  have htrace : WordTrace (prefixWord ++ tailWord_6068130) baseStart_6068130 baseEnd_6068130 := by
    simpa [prefixWord, tailWord_6068130, baseEnd_6068130] using wordTrace_append hprefix tailTrace_6068130
  have hstable : (prefixWord ++ tailWord_6068130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068130).length < 2 ^ (prefixWord ++ tailWord_6068130).sum := by decide
  have hdescent : baseEnd_6068130 < baseStart_6068130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068135 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_6068135 : Nat := 118140960795 + 6068135 * 2 ^ 59
def prefixEnd_6068135 : Nat := 4983230072969 + 3 ^ 40 * 6068135 * 2
def baseEnd_6068135 : Nat := 3115869931370721127605661

theorem tailTrace_6068135 : CollatzResearch.WordTrace tailWord_6068135 prefixEnd_6068135 3115869931370721127605661 := by
  unfold tailWord_6068135
  simp only [CollatzResearch.WordTrace]
  refine ⟨221323065871190724794677859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147548710580793816529785239 221323065871190724794677859)
  ·
    refine ⟨331984598806786087192016789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221323065871190724794677859 331984598806786087192016789)
    ·
      refine ⟨15561778069068097837125787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 331984598806786087192016789 15561778069068097837125787)
      ·
        refine ⟨23342667103602146755688681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15561778069068097837125787 23342667103602146755688681)
        ·
          refine ⟨17507000327701610066766511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23342667103602146755688681 17507000327701610066766511)
          ·
            refine ⟨26260500491552415100149767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17507000327701610066766511 26260500491552415100149767)
            ·
              refine ⟨39390750737328622650224651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26260500491552415100149767 39390750737328622650224651)
              ·
                refine ⟨59086126105992933975336977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39390750737328622650224651 59086126105992933975336977)
                ·
                  refine ⟨44314594579494700481502733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59086126105992933975336977 44314594579494700481502733)
                  ·
                    refine ⟨16617972967310512680563525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44314594579494700481502733 16617972967310512680563525)
                    ·
                      refine ⟨3115869931370721127605661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16617972967310512680563525 3115869931370721127605661)
                      ·
                        rfl

theorem cell23_6068135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_6068135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068135 prefixEnd_6068135 := by exact prefixLift 6068135
  have htrace : WordTrace (prefixWord ++ tailWord_6068135) baseStart_6068135 baseEnd_6068135 := by
    simpa [prefixWord, tailWord_6068135, baseEnd_6068135] using wordTrace_append hprefix tailTrace_6068135
  have hstable : (prefixWord ++ tailWord_6068135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068135).length < 2 ^ (prefixWord ++ tailWord_6068135).sum := by decide
  have hdescent : baseEnd_6068135 < baseStart_6068135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068145 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 2, 6]
def baseStart_6068145 : Nat := 118140960795 + 6068145 * 2 ^ 59
def prefixEnd_6068145 : Nat := 4983230072969 + 3 ^ 40 * 6068145 * 2
def baseEnd_6068145 : Nat := 1038625022059088696160205

theorem tailTrace_6068145 : CollatzResearch.WordTrace tailWord_6068145 prefixEnd_6068145 1038625022059088696160205 := by
  unfold tailWord_6068145
  simp only [CollatzResearch.WordTrace]
  refine ⟨221323430601154496502541889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147548953734102997668361259 221323430601154496502541889)
  ·
    refine ⟨165992572950865872376906417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221323430601154496502541889 165992572950865872376906417)
    ·
      refine ⟨124494429713149404282679813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165992572950865872376906417 124494429713149404282679813)
      ·
        refine ⟨23342705571215513303002465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124494429713149404282679813 23342705571215513303002465)
        ·
          refine ⟨17507029178411634977251849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23342705571215513303002465 17507029178411634977251849)
          ·
            refine ⟨13130271883808726232938887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17507029178411634977251849 13130271883808726232938887)
            ·
              refine ⟨19695407825713089349408331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13130271883808726232938887 19695407825713089349408331)
              ·
                refine ⟨29543111738569634024112497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19695407825713089349408331 29543111738569634024112497)
                ·
                  refine ⟨22157333803927225518084373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29543111738569634024112497 22157333803927225518084373)
                  ·
                    refine ⟨1038625022059088696160205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22157333803927225518084373 1038625022059088696160205)
                    ·
                      rfl

theorem cell23_6068145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_6068145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068145 prefixEnd_6068145 := by exact prefixLift 6068145
  have htrace : WordTrace (prefixWord ++ tailWord_6068145) baseStart_6068145 baseEnd_6068145 := by
    simpa [prefixWord, tailWord_6068145, baseEnd_6068145] using wordTrace_append hprefix tailTrace_6068145
  have hstable : (prefixWord ++ tailWord_6068145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068145).length < 2 ^ (prefixWord ++ tailWord_6068145).sum := by decide
  have hdescent : baseEnd_6068145 < baseStart_6068145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068152 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 1, 4, 2]
def baseStart_6068152 : Nat := 118140960795 + 6068152 * 2 ^ 59
def prefixEnd_6068152 : Nat := 4983230072969 + 3 ^ 40 * 6068152 * 2
def baseEnd_6068152 : Nat := 3115878660541847561093083

theorem tailTrace_6068152 : CollatzResearch.WordTrace tailWord_6068152 prefixEnd_6068152 3115878660541847561093083 := by
  unfold tailWord_6068152
  simp only [CollatzResearch.WordTrace]
  refine ⟨110661842956064568349023355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147549123941419424465364473 110661842956064568349023355)
  ·
    refine ⟨165992764434096852523535033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110661842956064568349023355 165992764434096852523535033)
    ·
      refine ⟨124494573325572639392651275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165992764434096852523535033 124494573325572639392651275)
      ·
        refine ⟨186741859988358959088976913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124494573325572639392651275 186741859988358959088976913)
        ·
          refine ⟨140056394991269219316732685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186741859988358959088976913 140056394991269219316732685)
          ·
            refine ⟨52521148121725957243774757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140056394991269219316732685 52521148121725957243774757)
            ·
              refine ⟨9847715272823616983207767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52521148121725957243774757 9847715272823616983207767)
              ·
                refine ⟨14771572909235425474811651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9847715272823616983207767 14771572909235425474811651)
                ·
                  refine ⟨22157359363853138212217477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14771572909235425474811651 22157359363853138212217477)
                  ·
                    refine ⟨4154504880722463414790777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22157359363853138212217477 4154504880722463414790777)
                    ·
                      refine ⟨3115878660541847561093083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154504880722463414790777 3115878660541847561093083)
                      ·
                        rfl

theorem cell23_6068152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_6068152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068152 prefixEnd_6068152 := by exact prefixLift 6068152
  have htrace : WordTrace (prefixWord ++ tailWord_6068152) baseStart_6068152 baseEnd_6068152 := by
    simpa [prefixWord, tailWord_6068152, baseEnd_6068152] using wordTrace_append hprefix tailTrace_6068152
  have hstable : (prefixWord ++ tailWord_6068152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068152).length < 2 ^ (prefixWord ++ tailWord_6068152).sum := by decide
  have hdescent : baseEnd_6068152 < baseStart_6068152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068222 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_6068222 : Nat := 118140960795 + 6068222 * 2 ^ 59
def prefixEnd_6068222 : Nat := 4983230072969 + 3 ^ 40 * 6068222 * 2
def baseEnd_6068222 : Nat := 1038638201395887429072587

theorem tailTrace_6068222 : CollatzResearch.WordTrace tailWord_6068222 prefixEnd_6068222 1038638201395887429072587 := by
  unfold tailWord_6068222
  simp only [CollatzResearch.WordTrace]
  refine ⟨27665779877734442331636865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147550826014583692435396613 27665779877734442331636865)
  ·
    refine ⟨20749334908300831748727649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27665779877734442331636865 20749334908300831748727649)
    ·
      refine ⟨15562001181225623811545737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20749334908300831748727649 15562001181225623811545737)
      ·
        refine ⟨11671500885919217858659303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15562001181225623811545737 11671500885919217858659303)
        ·
          refine ⟨17507251328878826787988955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11671500885919217858659303 17507251328878826787988955)
          ·
            refine ⟨26260876993318240181983433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17507251328878826787988955 26260876993318240181983433)
            ·
              refine ⟨19695657744988680136487575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26260876993318240181983433 19695657744988680136487575)
              ·
                refine ⟨29543486617483020204731363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19695657744988680136487575 29543486617483020204731363)
                ·
                  refine ⟨44315229926224530307097045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29543486617483020204731363 44315229926224530307097045)
                  ·
                    refine ⟨1038638201395887429072587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44315229926224530307097045 1038638201395887429072587)
                    ·
                      rfl

theorem cell23_6068222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_6068222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068222 prefixEnd_6068222 := by exact prefixLift 6068222
  have htrace : WordTrace (prefixWord ++ tailWord_6068222) baseStart_6068222 baseEnd_6068222 := by
    simpa [prefixWord, tailWord_6068222, baseEnd_6068222] using wordTrace_append hprefix tailTrace_6068222
  have hstable : (prefixWord ++ tailWord_6068222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068222).length < 2 ^ (prefixWord ++ tailWord_6068222).sum := by decide
  have hdescent : baseEnd_6068222 < baseStart_6068222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068225 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_6068225 : Nat := 118140960795 + 6068225 * 2 ^ 59
def prefixEnd_6068225 : Nat := 4983230072969 + 3 ^ 40 * 6068225 * 2
def baseEnd_6068225 : Nat := 3115916144629625775480247

theorem tailTrace_6068225 : CollatzResearch.WordTrace tailWord_6068225 prefixEnd_6068225 3115916144629625775480247 := by
  unfold tailWord_6068225
  simp only [CollatzResearch.WordTrace]
  refine ⟨221326348440864670165454129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147550898960576446776969419 221326348440864670165454129)
  ·
    refine ⟨165994761330648502624090597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221326348440864670165454129 165994761330648502624090597)
    ·
      refine ⟨31124017749496594242016987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165994761330648502624090597 31124017749496594242016987)
      ·
        refine ⟨46686026624244891363025481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31124017749496594242016987 46686026624244891363025481)
        ·
          refine ⟨35014519968183668522269111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46686026624244891363025481 35014519968183668522269111)
          ·
            refine ⟨52521779952275502783403667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35014519968183668522269111 52521779952275502783403667)
            ·
              refine ⟨78782669928413254175105501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52521779952275502783403667 78782669928413254175105501)
              ·
                refine ⟨29543501223154970315664563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78782669928413254175105501 29543501223154970315664563)
                ·
                  refine ⟨44315251834732455473496845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29543501223154970315664563 44315251834732455473496845)
                  ·
                    refine ⟨16618219438024670802561317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44315251834732455473496845 16618219438024670802561317)
                    ·
                      refine ⟨3115916144629625775480247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16618219438024670802561317 3115916144629625775480247)
                      ·
                        rfl

theorem cell23_6068225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_6068225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068225 prefixEnd_6068225 := by exact prefixLift 6068225
  have htrace : WordTrace (prefixWord ++ tailWord_6068225) baseStart_6068225 baseEnd_6068225 := by
    simpa [prefixWord, tailWord_6068225, baseEnd_6068225] using wordTrace_append hprefix tailTrace_6068225
  have hstable : (prefixWord ++ tailWord_6068225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068225).length < 2 ^ (prefixWord ++ tailWord_6068225).sum := by decide
  have hdescent : baseEnd_6068225 < baseStart_6068225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068275 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 3]
def baseStart_6068275 : Nat := 118140960795 + 6068275 * 2 ^ 59
def prefixEnd_6068275 : Nat := 4983230072969 + 3 ^ 40 * 6068275 * 2
def baseEnd_6068275 : Nat := 3115941818662350579855017

theorem tailTrace_6068275 : CollatzResearch.WordTrace tailWord_6068275 prefixEnd_6068275 3115941818662350579855017 := by
  unfold tailWord_6068275
  simp only [CollatzResearch.WordTrace]
  refine ⟨221328172090683528704774279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147552114727122352469849519 221328172090683528704774279)
  ·
    refine ⟨331992258136025293057161419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221328172090683528704774279 331992258136025293057161419)
    ·
      refine ⟨497988387204037939585742129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331992258136025293057161419 497988387204037939585742129)
      ·
        refine ⟨373491290403028454689306597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497988387204037939585742129 373491290403028454689306597)
        ·
          refine ⟨70029616950567835254244987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 373491290403028454689306597 70029616950567835254244987)
          ·
            refine ⟨105044425425851752881367481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70029616950567835254244987 105044425425851752881367481)
            ·
              refine ⟨78783319069388814661025611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105044425425851752881367481 78783319069388814661025611)
              ·
                refine ⟨118174978604083221991538417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78783319069388814661025611 118174978604083221991538417)
                ·
                  refine ⟨88631233953062416493653813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118174978604083221991538417 88631233953062416493653813)
                  ·
                    refine ⟨8309178183099601546280045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88631233953062416493653813 8309178183099601546280045)
                    ·
                      refine ⟨3115941818662350579855017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8309178183099601546280045 3115941818662350579855017)
                      ·
                        rfl

theorem cell23_6068275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_6068275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068275 prefixEnd_6068275 := by exact prefixLift 6068275
  have htrace : WordTrace (prefixWord ++ tailWord_6068275) baseStart_6068275 baseEnd_6068275 := by
    simpa [prefixWord, tailWord_6068275, baseEnd_6068275] using wordTrace_append hprefix tailTrace_6068275
  have hstable : (prefixWord ++ tailWord_6068275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068275).length < 2 ^ (prefixWord ++ tailWord_6068275).sum := by decide
  have hdescent : baseEnd_6068275 < baseStart_6068275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068276 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6068276 : Nat := 118140960795 + 6068276 * 2 ^ 59
def prefixEnd_6068276 : Nat := 4983230072969 + 3 ^ 40 * 6068276 * 2
def baseEnd_6068276 : Nat := 3115942332143005075942513

theorem tailTrace_6068276 : CollatzResearch.WordTrace tailWord_6068276 prefixEnd_6068276 3115942332143005075942513 := by
  unfold tailWord_6068276
  simp only [CollatzResearch.WordTrace]
  refine ⟨110664104281839952937780341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147552139042453270583707121 110664104281839952937780341)
  ·
    refine ⟨10374759776422495587916907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110664104281839952937780341 10374759776422495587916907)
    ·
      refine ⟨15562139664633743381875361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10374759776422495587916907 15562139664633743381875361)
      ·
        refine ⟨11671604748475307536406521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15562139664633743381875361 11671604748475307536406521)
        ·
          refine ⟨8753703561356480652304891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11671604748475307536406521 8753703561356480652304891)
          ·
            refine ⟨13130555342034720978457337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8753703561356480652304891 13130555342034720978457337)
            ·
              refine ⟨9847916506526040733843003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13130555342034720978457337 9847916506526040733843003)
              ·
                refine ⟨14771874759789061100764505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9847916506526040733843003 14771874759789061100764505)
                ·
                  refine ⟨11078906069841795825573379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14771874759789061100764505 11078906069841795825573379)
                  ·
                    refine ⟨16618359104762693738360069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11078906069841795825573379 16618359104762693738360069)
                    ·
                      refine ⟨3115942332143005075942513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16618359104762693738360069 3115942332143005075942513)
                      ·
                        rfl

theorem cell23_6068276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6068276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068276 prefixEnd_6068276 := by exact prefixLift 6068276
  have htrace : WordTrace (prefixWord ++ tailWord_6068276) baseStart_6068276 baseEnd_6068276 := by
    simpa [prefixWord, tailWord_6068276, baseEnd_6068276] using wordTrace_append hprefix tailTrace_6068276
  have hstable : (prefixWord ++ tailWord_6068276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068276).length < 2 ^ (prefixWord ++ tailWord_6068276).sum := by decide
  have hdescent : baseEnd_6068276 < baseStart_6068276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068332 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_6068332 : Nat := 118140960795 + 6068332 * 2 ^ 59
def prefixEnd_6068332 : Nat := 4983230072969 + 3 ^ 40 * 6068332 * 2
def baseEnd_6068332 : Nat := 3115971087059656856842255

theorem tailTrace_6068332 : CollatzResearch.WordTrace tailWord_6068332 prefixEnd_6068332 3115971087059656856842255 := by
  unfold tailWord_6068332
  simp only [CollatzResearch.WordTrace]
  refine ⟨110665125525738513719799625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147553500700984684959732833 110665125525738513719799625)
  ·
    refine ⟨82998844144303885289849719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110665125525738513719799625 82998844144303885289849719)
    ·
      refine ⟨124498266216455827934774579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82998844144303885289849719 124498266216455827934774579)
      ·
        refine ⟨186747399324683741902161869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124498266216455827934774579 186747399324683741902161869)
        ·
          refine ⟨70030274746756403213310701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186747399324683741902161869 70030274746756403213310701)
          ·
            refine ⟨26261353030033651204991513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70030274746756403213310701 26261353030033651204991513)
            ·
              refine ⟨19696014772525238403743635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26261353030033651204991513 19696014772525238403743635)
              ·
                refine ⟨29544022158787857605615453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19696014772525238403743635 29544022158787857605615453)
                ·
                  refine ⟨11079008309545446602105795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29544022158787857605615453 11079008309545446602105795)
                  ·
                    refine ⟨16618512464318169903158693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11079008309545446602105795 16618512464318169903158693)
                    ·
                      refine ⟨3115971087059656856842255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16618512464318169903158693 3115971087059656856842255)
                      ·
                        rfl

theorem cell23_6068332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_6068332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068332 prefixEnd_6068332 := by exact prefixLift 6068332
  have htrace : WordTrace (prefixWord ++ tailWord_6068332) baseStart_6068332 baseEnd_6068332 := by
    simpa [prefixWord, tailWord_6068332, baseEnd_6068332] using wordTrace_append hprefix tailTrace_6068332
  have hstable : (prefixWord ++ tailWord_6068332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068332).length < 2 ^ (prefixWord ++ tailWord_6068332).sum := by decide
  have hdescent : baseEnd_6068332 < baseStart_6068332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068336 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 2, 3, 2]
def baseStart_6068336 : Nat := 118140960795 + 6068336 * 2 ^ 59
def prefixEnd_6068336 : Nat := 4983230072969 + 3 ^ 40 * 6068336 * 2
def baseEnd_6068336 : Nat := 3115973140982274841192237

theorem tailTrace_6068336 : CollatzResearch.WordTrace tailWord_6068336 prefixEnd_6068336 3115973140982274841192237 := by
  unfold tailWord_6068336
  simp only [CollatzResearch.WordTrace]
  refine ⟨110665198471731268061372431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147553597962308357415163241 110665198471731268061372431)
  ·
    refine ⟨165997797707596902092058647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110665198471731268061372431 165997797707596902092058647)
    ·
      refine ⟨248996696561395353138087971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165997797707596902092058647 248996696561395353138087971)
      ·
        refine ⟨373495044842093029707131957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248996696561395353138087971 373495044842093029707131957)
        ·
          refine ⟨35015160453946221535043621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 373495044842093029707131957 35015160453946221535043621)
          ·
            refine ⟨6565342585114916537820679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35015160453946221535043621 6565342585114916537820679)
            ·
              refine ⟨9848013877672374806731019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565342585114916537820679 9848013877672374806731019)
              ·
                refine ⟨14772020816508562210096529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9848013877672374806731019 14772020816508562210096529)
                ·
                  refine ⟨11079015612381421657572397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14772020816508562210096529 11079015612381421657572397)
                  ·
                    refine ⟨4154630854643033121589649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11079015612381421657572397 4154630854643033121589649)
                    ·
                      refine ⟨3115973140982274841192237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154630854643033121589649 3115973140982274841192237)
                      ·
                        rfl

theorem cell23_6068336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 3, 2].length) (baseStart_6068336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068336 prefixEnd_6068336 := by exact prefixLift 6068336
  have htrace : WordTrace (prefixWord ++ tailWord_6068336) baseStart_6068336 baseEnd_6068336 := by
    simpa [prefixWord, tailWord_6068336, baseEnd_6068336] using wordTrace_append hprefix tailTrace_6068336
  have hstable : (prefixWord ++ tailWord_6068336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068336).length < 2 ^ (prefixWord ++ tailWord_6068336).sum := by decide
  have hdescent : baseEnd_6068336 < baseStart_6068336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068349 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_6068349 : Nat := 118140960795 + 6068349 * 2 ^ 59
def prefixEnd_6068349 : Nat := 4983230072969 + 3 ^ 40 * 6068349 * 2
def baseEnd_6068349 : Nat := 3115979816230783290329677

theorem tailTrace_6068349 : CollatzResearch.WordTrace tailWord_6068349 prefixEnd_6068349 3115979816230783290329677 := by
  unfold tailWord_6068349
  simp only [CollatzResearch.WordTrace]
  refine ⟨221330871092415439342968101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147553914061610292895312067 221330871092415439342968101)
  ·
    refine ⟨41499538329827894876806519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221330871092415439342968101 41499538329827894876806519)
    ·
      refine ⟨62249307494741842315209779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41499538329827894876806519 62249307494741842315209779)
      ·
        refine ⟨93373961242112763472814669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62249307494741842315209779 93373961242112763472814669)
        ·
          refine ⟨35015235465792286302305501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93373961242112763472814669 35015235465792286302305501)
          ·
            refine ⟨13130713299672107363364563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35015235465792286302305501 13130713299672107363364563)
            ·
              refine ⟨19696069949508161045046845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13130713299672107363364563 19696069949508161045046845)
              ·
                refine ⟨7386026231065560391892567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19696069949508161045046845 7386026231065560391892567)
                ·
                  refine ⟨11079039346598340587838851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7386026231065560391892567 11079039346598340587838851)
                  ·
                    refine ⟨16618559019897510881758277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11079039346598340587838851 16618559019897510881758277)
                    ·
                      refine ⟨3115979816230783290329677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16618559019897510881758277 3115979816230783290329677)
                      ·
                        rfl

theorem cell23_6068349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_6068349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068349 prefixEnd_6068349 := by exact prefixLift 6068349
  have htrace : WordTrace (prefixWord ++ tailWord_6068349) baseStart_6068349 baseEnd_6068349 := by
    simpa [prefixWord, tailWord_6068349, baseEnd_6068349] using wordTrace_append hprefix tailTrace_6068349
  have hstable : (prefixWord ++ tailWord_6068349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068349).length < 2 ^ (prefixWord ++ tailWord_6068349).sum := by decide
  have hdescent : baseEnd_6068349 < baseStart_6068349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068355 : List Nat := [1, 1, 1, 3, 3, 4, 10]
def baseStart_6068355 : Nat := 118140960795 + 6068355 * 2 ^ 59
def prefixEnd_6068355 : Nat := 4983230072969 + 3 ^ 40 * 6068355 * 2
def baseEnd_6068355 : Nat := 38468924655737163788329

theorem tailTrace_6068355 : CollatzResearch.WordTrace tailWord_6068355 prefixEnd_6068355 38468924655737163788329 := by
  unfold tailWord_6068355
  simp only [CollatzResearch.WordTrace]
  refine ⟨221331089930393702367686519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147554059953595801578457679 221331089930393702367686519)
  ·
    refine ⟨331996634895590553551529779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221331089930393702367686519 331996634895590553551529779)
    ·
      refine ⟨497994952343385830327294669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331996634895590553551529779 497994952343385830327294669)
      ·
        refine ⟨186748107128769686372735501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497994952343385830327294669 186748107128769686372735501)
        ·
          refine ⟨70030540173288632389775813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186748107128769686372735501 70030540173288632389775813)
          ·
            refine ⟨13130726282491618573082965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70030540173288632389775813 13130726282491618573082965)
            ·
              refine ⟨38468924655737163788329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13130726282491618573082965 38468924655737163788329)
              ·
                rfl

theorem cell23_6068355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 10].length) (baseStart_6068355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068355 prefixEnd_6068355 := by exact prefixLift 6068355
  have htrace : WordTrace (prefixWord ++ tailWord_6068355) baseStart_6068355 baseEnd_6068355 := by
    simpa [prefixWord, tailWord_6068355, baseEnd_6068355] using wordTrace_append hprefix tailTrace_6068355
  have hstable : (prefixWord ++ tailWord_6068355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068355).length < 2 ^ (prefixWord ++ tailWord_6068355).sum := by decide
  have hdescent : baseEnd_6068355 < baseStart_6068355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068359 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 2, 4]
def baseStart_6068359 : Nat := 118140960795 + 6068359 * 2 ^ 59
def prefixEnd_6068359 : Nat := 4983230072969 + 3 ^ 40 * 6068359 * 2
def baseEnd_6068359 : Nat := 1038661650345776083734877

theorem tailTrace_6068359 : CollatzResearch.WordTrace tailWord_6068359 prefixEnd_6068359 1038661650345776083734877 := by
  unfold tailWord_6068359
  simp only [CollatzResearch.WordTrace]
  refine ⟨221331235822379211050832131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147554157214919474033888087 221331235822379211050832131)
  ·
    refine ⟨331996853733568816576248197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221331235822379211050832131 331996853733568816576248197)
    ·
      refine ⟨62249410075044153108046537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331996853733568816576248197 62249410075044153108046537)
      ·
        refine ⟨46687057556283114831034903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62249410075044153108046537 46687057556283114831034903)
        ·
          refine ⟨70030586334424672246552355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46687057556283114831034903 70030586334424672246552355)
          ·
            refine ⟨105045879501637008369828533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70030586334424672246552355 105045879501637008369828533)
            ·
              refine ⟨9848051203278469534671425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105045879501637008369828533 9848051203278469534671425)
              ·
                refine ⟨7386038402458852151003569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9848051203278469534671425 7386038402458852151003569)
                ·
                  refine ⟨5539528801844139113252677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7386038402458852151003569 5539528801844139113252677)
                  ·
                    refine ⟨1038661650345776083734877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5539528801844139113252677 1038661650345776083734877)
                    ·
                      rfl

theorem cell23_6068359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_6068359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068359 prefixEnd_6068359 := by exact prefixLift 6068359
  have htrace : WordTrace (prefixWord ++ tailWord_6068359) baseStart_6068359 baseEnd_6068359 := by
    simpa [prefixWord, tailWord_6068359, baseEnd_6068359] using wordTrace_append hprefix tailTrace_6068359
  have hstable : (prefixWord ++ tailWord_6068359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068359).length < 2 ^ (prefixWord ++ tailWord_6068359).sum := by decide
  have hdescent : baseEnd_6068359 < baseStart_6068359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068376 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 1, 6]
def baseStart_6068376 : Nat := 118140960795 + 6068376 * 2 ^ 59
def prefixEnd_6068376 : Nat := 4983230072969 + 3 ^ 40 * 6068376 * 2
def baseEnd_6068376 : Nat := 1038664560069484894897351

theorem tailTrace_6068376 : CollatzResearch.WordTrace tailWord_6068376 prefixEnd_6068376 1038664560069484894897351 := by
  unfold tailWord_6068376
  simp only [CollatzResearch.WordTrace]
  refine ⟨110665927931658811477100491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147554570575545081969467321 110665927931658811477100491)
  ·
    refine ⟨165998891897488217215650737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110665927931658811477100491 165998891897488217215650737)
    ·
      refine ⟨124499168923116162911738053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165998891897488217215650737 124499168923116162911738053)
      ·
        refine ⟨23343594173084280545950885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124499168923116162911738053 23343594173084280545950885)
        ·
          refine ⟨4376923907453302602365791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23343594173084280545950885 4376923907453302602365791)
          ·
            refine ⟨6565385861179953903548687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4376923907453302602365791 6565385861179953903548687)
            ·
              refine ⟨9848078791769930855323031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565385861179953903548687 9848078791769930855323031)
              ·
                refine ⟨14772118187654896282984547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9848078791769930855323031 14772118187654896282984547)
                ·
                  refine ⟨22158177281482344424476821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14772118187654896282984547 22158177281482344424476821)
                  ·
                    refine ⟨1038664560069484894897351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22158177281482344424476821 1038664560069484894897351)
                    ·
                      rfl

theorem cell23_6068376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_6068376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068376 prefixEnd_6068376 := by exact prefixLift 6068376
  have htrace : WordTrace (prefixWord ++ tailWord_6068376) baseStart_6068376 baseEnd_6068376 := by
    simpa [prefixWord, tailWord_6068376, baseEnd_6068376] using wordTrace_append hprefix tailTrace_6068376
  have hstable : (prefixWord ++ tailWord_6068376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068376).length < 2 ^ (prefixWord ++ tailWord_6068376).sum := by decide
  have hdescent : baseEnd_6068376 < baseStart_6068376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068386 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_6068386 : Nat := 118140960795 + 6068386 * 2 ^ 59
def prefixEnd_6068386 : Nat := 4983230072969 + 3 ^ 40 * 6068386 * 2
def baseEnd_6068386 : Nat := 3115998815014999645567007

theorem tailTrace_6068386 : CollatzResearch.WordTrace tailWord_6068386 prefixEnd_6068386 3115998815014999645567007 := by
  unfold tailWord_6068386
  simp only [CollatzResearch.WordTrace]
  refine ⟨55333055148320348665516253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147554813728854263108043341 55333055148320348665516253)
  ·
    refine ⟨20749895680620130749568595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55333055148320348665516253 20749895680620130749568595)
    ·
      refine ⟨31124843520930196124352893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20749895680620130749568595 31124843520930196124352893)
      ·
        refine ⟨11671816320348823546632335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31124843520930196124352893 11671816320348823546632335)
        ·
          refine ⟨17507724480523235319948503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11671816320348823546632335 17507724480523235319948503)
          ·
            refine ⟨26261586720784852979922755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17507724480523235319948503 26261586720784852979922755)
            ·
              refine ⟨39392380081177279469884133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26261586720784852979922755 39392380081177279469884133)
              ·
                refine ⟨7386071265220739900603275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39392380081177279469884133 7386071265220739900603275)
                ·
                  refine ⟨11079106897831109850904913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7386071265220739900603275 11079106897831109850904913)
                  ·
                    refine ⟨8309330173373332388178685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11079106897831109850904913 8309330173373332388178685)
                    ·
                      refine ⟨3115998815014999645567007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8309330173373332388178685 3115998815014999645567007)
                      ·
                        rfl

theorem cell23_6068386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_6068386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068386 prefixEnd_6068386 := by exact prefixLift 6068386
  have htrace : WordTrace (prefixWord ++ tailWord_6068386) baseStart_6068386 baseEnd_6068386 := by
    simpa [prefixWord, tailWord_6068386, baseEnd_6068386] using wordTrace_append hprefix tailTrace_6068386
  have hstable : (prefixWord ++ tailWord_6068386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068386).length < 2 ^ (prefixWord ++ tailWord_6068386).sum := by decide
  have hdescent : baseEnd_6068386 < baseStart_6068386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068417 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6068417 : Nat := 118140960795 + 6068417 * 2 ^ 59
def prefixEnd_6068417 : Nat := 4983230072969 + 3 ^ 40 * 6068417 * 2
def baseEnd_6068417 : Nat := 3116014732915289024279365

theorem tailTrace_6068417 : CollatzResearch.WordTrace tailWord_6068417 prefixEnd_6068417 3116014732915289024279365 := by
  unfold tailWord_6068417
  simp only [CollatzResearch.WordTrace]
  refine ⟨221333351256169086956443505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147555567504112724637629003 221333351256169086956443505)
  ·
    refine ⟨166000013442126815217332629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221333351256169086956443505 166000013442126815217332629)
    ·
      refine ⟨7781250630099694463312467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166000013442126815217332629 7781250630099694463312467)
      ·
        refine ⟨11671875945149541694968701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7781250630099694463312467 11671875945149541694968701)
        ·
          refine ⟨4376953479431078135613263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11671875945149541694968701 4376953479431078135613263)
          ·
            refine ⟨6565430219146617203419895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4376953479431078135613263 6565430219146617203419895)
            ·
              refine ⟨9848145328719925805129843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565430219146617203419895 9848145328719925805129843)
              ·
                refine ⟨14772217993079888707694765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9848145328719925805129843 14772217993079888707694765)
                ·
                  refine ⟨5539581747404958265385537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14772217993079888707694765 5539581747404958265385537)
                  ·
                    refine ⟨4154686310553718699039153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5539581747404958265385537 4154686310553718699039153)
                    ·
                      refine ⟨3116014732915289024279365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154686310553718699039153 3116014732915289024279365)
                      ·
                        rfl

theorem cell23_6068417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6068417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068417 prefixEnd_6068417 := by exact prefixLift 6068417
  have htrace : WordTrace (prefixWord ++ tailWord_6068417) baseStart_6068417 baseEnd_6068417 := by
    simpa [prefixWord, tailWord_6068417, baseEnd_6068417] using wordTrace_append hprefix tailTrace_6068417
  have hstable : (prefixWord ++ tailWord_6068417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068417).length < 2 ^ (prefixWord ++ tailWord_6068417).sum := by decide
  have hdescent : baseEnd_6068417 < baseStart_6068417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068439 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 1, 4, 2]
def baseStart_6068439 : Nat := 118140960795 + 6068439 * 2 ^ 59
def prefixEnd_6068439 : Nat := 4983230072969 + 3 ^ 40 * 6068439 * 2
def baseEnd_6068439 : Nat := 3116026029489687938204263

theorem tailTrace_6068439 : CollatzResearch.WordTrace tailWord_6068439 prefixEnd_6068439 3116026029489687938204263 := by
  unfold tailWord_6068439
  simp only [CollatzResearch.WordTrace]
  refine ⟨221334153662089384713744371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147556102441392923142496247 221334153662089384713744371)
  ·
    refine ⟨332001230493134077070616557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221334153662089384713744371 332001230493134077070616557)
    ·
      refine ⟨124500461434925278901481209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332001230493134077070616557 124500461434925278901481209)
      ·
        refine ⟨93375346076193959176110907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124500461434925278901481209 93375346076193959176110907)
        ·
          refine ⟨140063019114290938764166361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93375346076193959176110907 140063019114290938764166361)
          ·
            refine ⟨105047264335718204073124771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140063019114290938764166361 105047264335718204073124771)
            ·
              refine ⟨157570896503577306109687157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105047264335718204073124771 157570896503577306109687157)
              ·
                refine ⟨14772271547210372447783171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157570896503577306109687157 14772271547210372447783171)
                ·
                  refine ⟨22158407320815558671674757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14772271547210372447783171 22158407320815558671674757)
                  ·
                    refine ⟨4154701372652917250939017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22158407320815558671674757 4154701372652917250939017)
                    ·
                      refine ⟨3116026029489687938204263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154701372652917250939017 3116026029489687938204263)
                      ·
                        rfl

theorem cell23_6068439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_6068439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068439 prefixEnd_6068439 := by exact prefixLift 6068439
  have htrace : WordTrace (prefixWord ++ tailWord_6068439) baseStart_6068439 baseEnd_6068439 := by
    simpa [prefixWord, tailWord_6068439, baseEnd_6068439] using wordTrace_append hprefix tailTrace_6068439
  have hstable : (prefixWord ++ tailWord_6068439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068439).length < 2 ^ (prefixWord ++ tailWord_6068439).sum := by decide
  have hdescent : baseEnd_6068439 < baseStart_6068439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068442 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_6068442 : Nat := 118140960795 + 6068442 * 2 ^ 59
def prefixEnd_6068442 : Nat := 4983230072969 + 3 ^ 40 * 6068442 * 2
def baseEnd_6068442 : Nat := 3116027569931651426466749

theorem tailTrace_6068442 : CollatzResearch.WordTrace tailWord_6068442 prefixEnd_6068442 3116027569931651426466749 := by
  unfold tailWord_6068442
  simp only [CollatzResearch.WordTrace]
  refine ⟨55333565770269629056525895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147556175387385677484069053 55333565770269629056525895)
  ·
    refine ⟨83000348655404443584788843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55333565770269629056525895 83000348655404443584788843)
    ·
      refine ⟨124500522983106665377183265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83000348655404443584788843 124500522983106665377183265)
      ·
        refine ⟨93375392237329999032887449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124500522983106665377183265 93375392237329999032887449)
        ·
          refine ⟨70031544177997499274665587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93375392237329999032887449 70031544177997499274665587)
          ·
            refine ⟨105047316266996248911998381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70031544177997499274665587 105047316266996248911998381)
            ·
              refine ⟨39392743600123593341999393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105047316266996248911998381 39392743600123593341999393)
              ·
                refine ⟨29544557700092695006499545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39392743600123593341999393 29544557700092695006499545)
                ·
                  refine ⟨22158418275069521254874659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29544557700092695006499545 22158418275069521254874659)
                  ·
                    refine ⟨33237627412604281882311989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22158418275069521254874659 33237627412604281882311989)
                    ·
                      refine ⟨3116027569931651426466749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33237627412604281882311989 3116027569931651426466749)
                      ·
                        rfl

theorem cell23_6068442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_6068442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068442 prefixEnd_6068442 := by exact prefixLift 6068442
  have htrace : WordTrace (prefixWord ++ tailWord_6068442) baseStart_6068442 baseEnd_6068442 := by
    simpa [prefixWord, tailWord_6068442, baseEnd_6068442] using wordTrace_append hprefix tailTrace_6068442
  have hstable : (prefixWord ++ tailWord_6068442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068442).length < 2 ^ (prefixWord ++ tailWord_6068442).sum := by decide
  have hdescent : baseEnd_6068442 < baseStart_6068442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
