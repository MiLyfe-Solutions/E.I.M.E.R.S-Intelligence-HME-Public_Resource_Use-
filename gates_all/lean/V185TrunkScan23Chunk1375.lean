import V185TrunkScan23Chunk1374

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8144070 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_8144070 : Nat := 118140960795 + 8144070 * 2 ^ 59
def prefixEnd_8144070 : Nat := 4983230072969 + 3 ^ 40 * 8144070 * 2
def baseEnd_8144070 : Nat := 4181822393862056522371111

theorem tailTrace_8144070 : CollatzResearch.WordTrace tailWord_8144070 prefixEnd_8144070 4181822393862056522371111 := by
  unfold tailWord_8144070
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282457362669773789568427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198025757070288507510793109 9282457362669773789568427)
  ·
    refine ⟨13923686044004660684352641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9282457362669773789568427 13923686044004660684352641)
    ·
      refine ⟨10442764533003495513264481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13923686044004660684352641 10442764533003495513264481)
      ·
        refine ⟨7832073399752621634948361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10442764533003495513264481 7832073399752621634948361)
        ·
          refine ⟨5874055049814466226211271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7832073399752621634948361 5874055049814466226211271)
          ·
            refine ⟨8811082574721699339316907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5874055049814466226211271 8811082574721699339316907)
            ·
              refine ⟨13216623862082549008975361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8811082574721699339316907 13216623862082549008975361)
              ·
                refine ⟨9912467896561911756731521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13216623862082549008975361 9912467896561911756731521)
                ·
                  refine ⟨7434350922421433817548641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9912467896561911756731521 7434350922421433817548641)
                  ·
                    refine ⟨5575763191816075363161481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7434350922421433817548641 5575763191816075363161481)
                    ·
                      refine ⟨4181822393862056522371111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575763191816075363161481 4181822393862056522371111)
                      ·
                        rfl

theorem cell23_8144070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_8144070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144070 prefixEnd_8144070 := by exact prefixLift 8144070
  have htrace : WordTrace (prefixWord ++ tailWord_8144070) baseStart_8144070 baseEnd_8144070 := by
    simpa [prefixWord, tailWord_8144070, baseEnd_8144070] using wordTrace_append hprefix tailTrace_8144070
  have hstable : (prefixWord ++ tailWord_8144070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144070).length < 2 ^ (prefixWord ++ tailWord_8144070).sum := by decide
  have hdescent : baseEnd_8144070 < baseStart_8144070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144085 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_8144085 : Nat := 118140960795 + 8144085 * 2 ^ 59
def prefixEnd_8144085 : Nat := 4983230072969 + 3 ^ 40 * 8144085 * 2
def baseEnd_8144085 : Nat := 1393943365357291321227847

theorem tailTrace_8144085 : CollatzResearch.WordTrace tailWord_8144085 prefixEnd_8144085 1393943365357291321227847 := by
  unfold tailWord_8144085
  simp only [CollatzResearch.WordTrace]
  refine ⟨297039182700378418827985709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198026121800252279218657139 297039182700378418827985709)
  ·
    refine ⟨111389693512641907060494641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297039182700378418827985709 111389693512641907060494641)
    ·
      refine ⟨83542270134481430295370981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111389693512641907060494641 83542270134481430295370981)
      ·
        refine ⟨15664175650215268180382059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83542270134481430295370981 15664175650215268180382059)
        ·
          refine ⟨23496263475322902270573089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15664175650215268180382059 23496263475322902270573089)
          ·
            refine ⟨17622197606492176702929817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23496263475322902270573089 17622197606492176702929817)
            ·
              refine ⟨13216648204869132527197363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17622197606492176702929817 13216648204869132527197363)
              ·
                refine ⟨19824972307303698790796045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13216648204869132527197363 19824972307303698790796045)
                ·
                  refine ⟨7434364615238887046548517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19824972307303698790796045 7434364615238887046548517)
                  ·
                    refine ⟨1393943365357291321227847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7434364615238887046548517 1393943365357291321227847)
                    ·
                      rfl

theorem cell23_8144085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_8144085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144085 prefixEnd_8144085 := by exact prefixLift 8144085
  have htrace : WordTrace (prefixWord ++ tailWord_8144085) baseStart_8144085 baseEnd_8144085 := by
    simpa [prefixWord, tailWord_8144085, baseEnd_8144085] using wordTrace_append hprefix tailTrace_8144085
  have hstable : (prefixWord ++ tailWord_8144085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144085).length < 2 ^ (prefixWord ++ tailWord_8144085).sum := by decide
  have hdescent : baseEnd_8144085 < baseStart_8144085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144142 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_8144142 : Nat := 118140960795 + 8144142 * 2 ^ 59
def prefixEnd_8144142 : Nat := 4983230072969 + 3 ^ 40 * 8144142 * 2
def baseEnd_8144142 : Nat := 4181859364469180240670779

theorem tailTrace_8144142 : CollatzResearch.WordTrace tailWord_8144142 prefixEnd_8144142 4181859364469180240670779 := by
  unfold tailWord_8144142
  simp only [CollatzResearch.WordTrace]
  refine ⟨37130157707646489695351335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198027507774114611708540453 37130157707646489695351335)
  ·
    refine ⟨55695236561469734543027003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37130157707646489695351335 55695236561469734543027003)
    ·
      refine ⟨83542854842204601814540505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55695236561469734543027003 83542854842204601814540505)
      ·
        refine ⟨62657141131653451360905379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83542854842204601814540505 62657141131653451360905379)
        ·
          refine ⟨93985711697480177041358069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62657141131653451360905379 93985711697480177041358069)
          ·
            refine ⟨8811160471638766597627319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93985711697480177041358069 8811160471638766597627319)
            ·
              refine ⟨13216740707458149896440979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8811160471638766597627319 13216740707458149896440979)
              ·
                refine ⟨19825111061187224844661469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13216740707458149896440979 19825111061187224844661469)
                ·
                  refine ⟨7434416647945209316748051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19825111061187224844661469 7434416647945209316748051)
                  ·
                    refine ⟨11151624971917813975122077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7434416647945209316748051 11151624971917813975122077)
                    ·
                      refine ⟨4181859364469180240670779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11151624971917813975122077 4181859364469180240670779)
                      ·
                        rfl

theorem cell23_8144142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_8144142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144142 prefixEnd_8144142 := by exact prefixLift 8144142
  have htrace : WordTrace (prefixWord ++ tailWord_8144142) baseStart_8144142 baseEnd_8144142 := by
    simpa [prefixWord, tailWord_8144142, baseEnd_8144142] using wordTrace_append hprefix tailTrace_8144142
  have hstable : (prefixWord ++ tailWord_8144142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144142).length < 2 ^ (prefixWord ++ tailWord_8144142).sum := by decide
  have hdescent : baseEnd_8144142 < baseStart_8144142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144162 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_8144162 : Nat := 118140960795 + 8144162 * 2 ^ 59
def prefixEnd_8144162 : Nat := 4983230072969 + 3 ^ 40 * 8144162 * 2
def baseEnd_8144162 : Nat := 1393956544694090054140229

theorem tailTrace_8144162 : CollatzResearch.WordTrace tailWord_8144162 prefixEnd_8144162 1393956544694090054140229 := by
  unfold tailWord_8144162
  simp only [CollatzResearch.WordTrace]
  refine ⟨74260497780274865244634685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198027994080732973985692493 74260497780274865244634685)
  ·
    refine ⟨27847686667603074466738007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74260497780274865244634685 27847686667603074466738007)
    ·
      refine ⟨41771530001404611700107011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27847686667603074466738007 41771530001404611700107011)
      ·
        refine ⟨62657295002106917550160517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41771530001404611700107011 62657295002106917550160517)
        ·
          refine ⟨11748242812895047040655097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62657295002106917550160517 11748242812895047040655097)
          ·
            refine ⟨8811182109671285280491323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11748242812895047040655097 8811182109671285280491323)
            ·
              refine ⟨13216773164506927920736985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8811182109671285280491323 13216773164506927920736985)
              ·
                refine ⟨9912579873380195940552739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13216773164506927920736985 9912579873380195940552739)
                ·
                  refine ⟨14868869810070293910829109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9912579873380195940552739 14868869810070293910829109)
                  ·
                    refine ⟨1393956544694090054140229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14868869810070293910829109 1393956544694090054140229)
                    ·
                      rfl

theorem cell23_8144162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_8144162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144162 prefixEnd_8144162 := by exact prefixLift 8144162
  have htrace : WordTrace (prefixWord ++ tailWord_8144162) baseStart_8144162 baseEnd_8144162 := by
    simpa [prefixWord, tailWord_8144162, baseEnd_8144162] using wordTrace_append hprefix tailTrace_8144162
  have hstable : (prefixWord ++ tailWord_8144162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144162).length < 2 ^ (prefixWord ++ tailWord_8144162).sum := by decide
  have hdescent : baseEnd_8144162 < baseStart_8144162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144165 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 4]
def baseStart_8144165 : Nat := 118140960795 + 8144165 * 2 ^ 59
def prefixEnd_8144165 : Nat := 4983230072969 + 3 ^ 40 * 8144165 * 2
def baseEnd_8144165 : Nat := 4181871174524233650683173

theorem tailTrace_8144165 : CollatzResearch.WordTrace tailWord_8144165 prefixEnd_8144165 4181871174524233650683173 := by
  unfold tailWord_8144165
  simp only [CollatzResearch.WordTrace]
  refine ⟨297042100540088592490897949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198028067026725728327265299 297042100540088592490897949)
  ·
    refine ⟨111390787702533222184086731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297042100540088592490897949 111390787702533222184086731)
    ·
      refine ⟨167086181553799833276130097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111390787702533222184086731 167086181553799833276130097)
      ·
        refine ⟨125314636165349874957097573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167086181553799833276130097 125314636165349874957097573)
        ·
          refine ⟨23496494281003101554455795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125314636165349874957097573 23496494281003101554455795)
          ·
            refine ⟨35244741421504652331683693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23496494281003101554455795 35244741421504652331683693)
            ·
              refine ⟨13216778033064244624381385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35244741421504652331683693 13216778033064244624381385)
              ·
                refine ⟨9912583524798183468286039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13216778033064244624381385 9912583524798183468286039)
                ·
                  refine ⟨14868875287197275202429059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9912583524798183468286039 14868875287197275202429059)
                  ·
                    refine ⟨22303312930795912803643589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14868875287197275202429059 22303312930795912803643589)
                    ·
                      refine ⟨4181871174524233650683173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22303312930795912803643589 4181871174524233650683173)
                      ·
                        rfl

theorem cell23_8144165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_8144165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144165 prefixEnd_8144165 := by exact prefixLift 8144165
  have htrace : WordTrace (prefixWord ++ tailWord_8144165) baseStart_8144165 baseEnd_8144165 := by
    simpa [prefixWord, tailWord_8144165, baseEnd_8144165] using wordTrace_append hprefix tailTrace_8144165
  have hstable : (prefixWord ++ tailWord_8144165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144165).length < 2 ^ (prefixWord ++ tailWord_8144165).sum := by decide
  have hdescent : baseEnd_8144165 < baseStart_8144165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144178 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_8144178 : Nat := 118140960795 + 8144178 * 2 ^ 59
def prefixEnd_8144178 : Nat := 4983230072969 + 3 ^ 40 * 8144178 * 2
def baseEnd_8144178 : Nat := 4181877849772742099820613

theorem tailTrace_8144178 : CollatzResearch.WordTrace tailWord_8144178 prefixEnd_8144178 4181877849772742099820613 := by
  unfold tailWord_8144178
  simp only [CollatzResearch.WordTrace]
  refine ⟨74260643672260373927780297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198028383126027663807414125 74260643672260373927780297)
  ·
    refine ⟨55695482754195280445835223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74260643672260373927780297 55695482754195280445835223)
    ·
      refine ⟨83543224131292920668752835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55695482754195280445835223 83543224131292920668752835)
      ·
        refine ⟨125314836196939381003129253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83543224131292920668752835 125314836196939381003129253)
        ·
          refine ⟨23496531786926133938086735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125314836196939381003129253 23496531786926133938086735)
          ·
            refine ⟨35244797680389200907130103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23496531786926133938086735 35244797680389200907130103)
            ·
              refine ⟨52867196520583801360695155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35244797680389200907130103 52867196520583801360695155)
              ·
                refine ⟨79300794780875702041042733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52867196520583801360695155 79300794780875702041042733)
                ·
                  refine ⟨29737798042828388265391025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79300794780875702041042733 29737798042828388265391025)
                  ·
                    refine ⟨22303348532121291199043269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29737798042828388265391025 22303348532121291199043269)
                    ·
                      refine ⟨4181877849772742099820613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22303348532121291199043269 4181877849772742099820613)
                      ·
                        rfl

theorem cell23_8144178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_8144178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144178 prefixEnd_8144178 := by exact prefixLift 8144178
  have htrace : WordTrace (prefixWord ++ tailWord_8144178) baseStart_8144178 baseEnd_8144178 := by
    simpa [prefixWord, tailWord_8144178, baseEnd_8144178] using wordTrace_append hprefix tailTrace_8144178
  have hstable : (prefixWord ++ tailWord_8144178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144178).length < 2 ^ (prefixWord ++ tailWord_8144178).sum := by decide
  have hdescent : baseEnd_8144178 < baseStart_8144178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144199 : List Nat := [1, 1, 4, 1, 2, 4, 1, 4, 1, 2, 2]
def baseStart_8144199 : Nat := 118140960795 + 8144199 * 2 ^ 59
def prefixEnd_8144199 : Nat := 4983230072969 + 3 ^ 40 * 8144199 * 2
def baseEnd_8144199 : Nat := 4181888632866486517658017

theorem tailTrace_8144199 : CollatzResearch.WordTrace tailWord_8144199 prefixEnd_8144199 4181888632866486517658017 := by
  unfold tailWord_8144199
  simp only [CollatzResearch.WordTrace]
  refine ⟨297043340621965416297635651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198028893747976944198423767 297043340621965416297635651)
  ·
    refine ⟨445565010932948124446453477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297043340621965416297635651 445565010932948124446453477)
    ·
      refine ⟨83543439549927773333710027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 445565010932948124446453477 83543439549927773333710027)
      ·
        refine ⟨125315159324891660000565041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83543439549927773333710027 125315159324891660000565041)
        ·
          refine ⟨93986369493668745000423781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125315159324891660000565041 93986369493668745000423781)
          ·
            refine ⟨17622444280062889687579459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93986369493668745000423781 17622444280062889687579459)
            ·
              refine ⟨26433666420094334531369189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17622444280062889687579459 26433666420094334531369189)
              ·
                refine ⟨4956312453767687724631723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26433666420094334531369189 4956312453767687724631723)
                ·
                  refine ⟨7434468680651531586947585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4956312453767687724631723 7434468680651531586947585)
                  ·
                    refine ⟨5575851510488648690210689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7434468680651531586947585 5575851510488648690210689)
                    ·
                      refine ⟨4181888632866486517658017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575851510488648690210689 4181888632866486517658017)
                      ·
                        rfl

theorem cell23_8144199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_8144199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144199 prefixEnd_8144199 := by exact prefixLift 8144199
  have htrace : WordTrace (prefixWord ++ tailWord_8144199) baseStart_8144199 baseEnd_8144199 := by
    simpa [prefixWord, tailWord_8144199, baseEnd_8144199] using wordTrace_append hprefix tailTrace_8144199
  have hstable : (prefixWord ++ tailWord_8144199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144199).length < 2 ^ (prefixWord ++ tailWord_8144199).sum := by decide
  have hdescent : baseEnd_8144199 < baseStart_8144199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144201 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 2, 7]
def baseStart_8144201 : Nat := 118140960795 + 8144201 * 2 ^ 59
def prefixEnd_8144201 : Nat := 4983230072969 + 3 ^ 40 * 8144201 * 2
def baseEnd_8144201 : Nat := 1393963219942598503277669

theorem tailTrace_8144201 : CollatzResearch.WordTrace tailWord_8144201 prefixEnd_8144201 1393963219942598503277669 := by
  unfold tailWord_8144201
  simp only [CollatzResearch.WordTrace]
  refine ⟨297043413567958170639208457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198028942378638780426138971 297043413567958170639208457)
  ·
    refine ⟨222782560175968627979406343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297043413567958170639208457 222782560175968627979406343)
    ·
      refine ⟨334173840263952941969109515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222782560175968627979406343 334173840263952941969109515)
      ·
        refine ⟨501260760395929412953664273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334173840263952941969109515 501260760395929412953664273)
        ·
          refine ⟨375945570296947059715248205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501260760395929412953664273 375945570296947059715248205)
          ·
            refine ⟨140979588861355147393218077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375945570296947059715248205 140979588861355147393218077)
            ·
              refine ⟨52867345823008180272456779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140979588861355147393218077 52867345823008180272456779)
              ·
                refine ⟨79301018734512270408685169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52867345823008180272456779 79301018734512270408685169)
                ·
                  refine ⟨59475764050884202806513877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79301018734512270408685169 59475764050884202806513877)
                  ·
                    refine ⟨1393963219942598503277669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59475764050884202806513877 1393963219942598503277669)
                    ·
                      rfl

theorem cell23_8144201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_8144201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144201 prefixEnd_8144201 := by exact prefixLift 8144201
  have htrace : WordTrace (prefixWord ++ tailWord_8144201) baseStart_8144201 baseEnd_8144201 := by
    simpa [prefixWord, tailWord_8144201, baseEnd_8144201] using wordTrace_append hprefix tailTrace_8144201
  have hstable : (prefixWord ++ tailWord_8144201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144201).length < 2 ^ (prefixWord ++ tailWord_8144201).sum := by decide
  have hdescent : baseEnd_8144201 < baseStart_8144201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144215 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_8144215 : Nat := 118140960795 + 8144215 * 2 ^ 59
def prefixEnd_8144215 : Nat := 4983230072969 + 3 ^ 40 * 8144215 * 2
def baseEnd_8144215 : Nat := 4181896848556958455057943

theorem tailTrace_8144215 : CollatzResearch.WordTrace tailWord_8144215 prefixEnd_8144215 4181896848556958455057943 := by
  unfold tailWord_8144215
  simp only [CollatzResearch.WordTrace]
  refine ⟨297043924189907451030218099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198029282793271634020145399 297043924189907451030218099)
  ·
    refine ⟨445565886284861176545327149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297043924189907451030218099 445565886284861176545327149)
    ·
      refine ⟨167087207356822941204497681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445565886284861176545327149 167087207356822941204497681)
      ·
        refine ⟨125315405517617205903373261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167087207356822941204497681 125315405517617205903373261)
        ·
          refine ⟨46993277069106452213764973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125315405517617205903373261 46993277069106452213764973)
          ·
            refine ⟨17622478900914919580161865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46993277069106452213764973 17622478900914919580161865)
            ·
              refine ⟨13216859175686189685121399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17622478900914919580161865 13216859175686189685121399)
              ·
                refine ⟨19825288763529284527682099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13216859175686189685121399 19825288763529284527682099)
                ·
                  refine ⟨29737933145293926791523149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19825288763529284527682099 29737933145293926791523149)
                  ·
                    refine ⟨11151724929485222546821181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29737933145293926791523149 11151724929485222546821181)
                    ·
                      refine ⟨4181896848556958455057943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11151724929485222546821181 4181896848556958455057943)
                      ·
                        rfl

theorem cell23_8144215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_8144215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144215 prefixEnd_8144215 := by exact prefixLift 8144215
  have htrace : WordTrace (prefixWord ++ tailWord_8144215) baseStart_8144215 baseEnd_8144215 := by
    simpa [prefixWord, tailWord_8144215, baseEnd_8144215] using wordTrace_append hprefix tailTrace_8144215
  have hstable : (prefixWord ++ tailWord_8144215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144215).length < 2 ^ (prefixWord ++ tailWord_8144215).sum := by decide
  have hdescent : baseEnd_8144215 < baseStart_8144215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144242 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_8144242 : Nat := 118140960795 + 8144242 * 2 ^ 59
def prefixEnd_8144242 : Nat := 4983230072969 + 3 ^ 40 * 8144242 * 2
def baseEnd_8144242 : Nat := 4181910712534629849420319

theorem tailTrace_8144242 : CollatzResearch.WordTrace tailWord_8144242 prefixEnd_8144242 4181910712534629849420319 := by
  unfold tailWord_8144242
  simp only [CollatzResearch.WordTrace]
  refine ⟨74261227240202408660362745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198029939307206423094300653 74261227240202408660362745)
  ·
    refine ⟨55695920430151806495272059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74261227240202408660362745 55695920430151806495272059)
    ·
      refine ⟨83543880645227709742908089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55695920430151806495272059 83543880645227709742908089)
      ·
        refine ⟨62657910483920782307181067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83543880645227709742908089 62657910483920782307181067)
        ·
          refine ⟨93986865725881173460771601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62657910483920782307181067 93986865725881173460771601)
          ·
            refine ⟨70490149294410880095578701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93986865725881173460771601 70490149294410880095578701)
            ·
              refine ⟨26433805985404080035842013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70490149294410880095578701 26433805985404080035842013)
              ·
                refine ⟨9912677244526530013440755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26433805985404080035842013 9912677244526530013440755)
                ·
                  refine ⟨14869015866789795020161133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9912677244526530013440755 14869015866789795020161133)
                  ·
                    refine ⟨5575880950046173132560425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14869015866789795020161133 5575880950046173132560425)
                    ·
                      refine ⟨4181910712534629849420319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5575880950046173132560425 4181910712534629849420319)
                      ·
                        rfl

theorem cell23_8144242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_8144242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144242 prefixEnd_8144242 := by exact prefixLift 8144242
  have htrace : WordTrace (prefixWord ++ tailWord_8144242) baseStart_8144242 baseEnd_8144242 := by
    simpa [prefixWord, tailWord_8144242, baseEnd_8144242] using wordTrace_append hprefix tailTrace_8144242
  have hstable : (prefixWord ++ tailWord_8144242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144242).length < 2 ^ (prefixWord ++ tailWord_8144242).sum := by decide
  have hdescent : baseEnd_8144242 < baseStart_8144242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144268 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_8144268 : Nat := 118140960795 + 8144268 * 2 ^ 59
def prefixEnd_8144268 : Nat := 4983230072969 + 3 ^ 40 * 8144268 * 2
def baseEnd_8144268 : Nat := 4181924063031646747695199

theorem tailTrace_8144268 : CollatzResearch.WordTrace tailWord_8144268 prefixEnd_8144268 4181924063031646747695199 := by
  unfold tailWord_8144268
  simp only [CollatzResearch.WordTrace]
  refine ⟨148522928629357720540948729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198030571505810294054598305 148522928629357720540948729)
  ·
    refine ⟨111392196472018290405711547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148522928629357720540948729 111392196472018290405711547)
    ·
      refine ⟨167088294708027435608567321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111392196472018290405711547 167088294708027435608567321)
      ·
        refine ⟨125316221031020576706425491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167088294708027435608567321 125316221031020576706425491)
        ·
          refine ⟨187974331546530865059638237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125316221031020576706425491 187974331546530865059638237)
          ·
            refine ⟨70490374329949074397364339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187974331546530865059638237 70490374329949074397364339)
            ·
              refine ⟨105735561494923611596046509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70490374329949074397364339 105735561494923611596046509)
              ·
                refine ⟨39650835560596354348517441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105735561494923611596046509 39650835560596354348517441)
                ·
                  refine ⟨29738126670447265761388081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39650835560596354348517441 29738126670447265761388081)
                  ·
                    refine ⟨22303595002835449321041061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29738126670447265761388081 22303595002835449321041061)
                    ·
                      refine ⟨4181924063031646747695199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22303595002835449321041061 4181924063031646747695199)
                      ·
                        rfl

theorem cell23_8144268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_8144268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144268 prefixEnd_8144268 := by exact prefixLift 8144268
  have htrace : WordTrace (prefixWord ++ tailWord_8144268) baseStart_8144268 baseEnd_8144268 := by
    simpa [prefixWord, tailWord_8144268, baseEnd_8144268] using wordTrace_append hprefix tailTrace_8144268
  have hstable : (prefixWord ++ tailWord_8144268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144268).length < 2 ^ (prefixWord ++ tailWord_8144268).sum := by decide
  have hdescent : baseEnd_8144268 < baseStart_8144268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144342 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_8144342 : Nat := 118140960795 + 8144342 * 2 ^ 59
def prefixEnd_8144342 : Nat := 4983230072969 + 3 ^ 40 * 8144342 * 2
def baseEnd_8144342 : Nat := 1393987353533359819389953

theorem tailTrace_8144342 : CollatzResearch.WordTrace tailWord_8144342 prefixEnd_8144342 1393987353533359819389953 := by
  unfold tailWord_8144342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18565534766277959482505705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198032370840298234480060853 18565534766277959482505705)
  ·
    refine ⟨13924151074708469611879279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18565534766277959482505705 13924151074708469611879279)
    ·
      refine ⟨20886226612062704417818919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13924151074708469611879279 20886226612062704417818919)
      ·
        refine ⟨31329339918094056626728379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20886226612062704417818919 31329339918094056626728379)
        ·
          refine ⟨46994009877141084940092569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31329339918094056626728379 46994009877141084940092569)
          ·
            refine ⟨35245507407855813705069427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46994009877141084940092569 35245507407855813705069427)
            ·
              refine ⟨52868261111783720557604141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35245507407855813705069427 52868261111783720557604141)
              ·
                refine ⟨19825597916918895209101553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52868261111783720557604141 19825597916918895209101553)
                ·
                  refine ⟨14869198437689171406826165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19825597916918895209101553 14869198437689171406826165)
                  ·
                    refine ⟨1393987353533359819389953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14869198437689171406826165 1393987353533359819389953)
                    ·
                      rfl

theorem cell23_8144342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_8144342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144342 prefixEnd_8144342 := by exact prefixLift 8144342
  have htrace : WordTrace (prefixWord ++ tailWord_8144342) baseStart_8144342 baseEnd_8144342 := by
    simpa [prefixWord, tailWord_8144342, baseEnd_8144342] using wordTrace_append hprefix tailTrace_8144342
  have hstable : (prefixWord ++ tailWord_8144342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144342).length < 2 ^ (prefixWord ++ tailWord_8144342).sum := by decide
  have hdescent : baseEnd_8144342 < baseStart_8144342 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144345 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_8144345 : Nat := 118140960795 + 8144345 * 2 ^ 59
def prefixEnd_8144345 : Nat := 4983230072969 + 3 ^ 40 * 8144345 * 2
def baseEnd_8144345 : Nat := 4181963601042042946432345

theorem tailTrace_8144345 : CollatzResearch.WordTrace tailWord_8144345 prefixEnd_8144345 4181963601042042946432345 := by
  unfold tailWord_8144345
  simp only [CollatzResearch.WordTrace]
  refine ⟨297048665679436483232450489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198032443786290988821633659 297048665679436483232450489)
  ·
    refine ⟨222786499259577362424337867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297048665679436483232450489 222786499259577362424337867)
    ·
      refine ⟨334179748889366043636506801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222786499259577362424337867 334179748889366043636506801)
      ·
        refine ⟨250634811667024532727380101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334179748889366043636506801 250634811667024532727380101)
        ·
          refine ⟨46994027187567099886383769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250634811667024532727380101 46994027187567099886383769)
          ·
            refine ⟨35245520390675324914787827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46994027187567099886383769 35245520390675324914787827)
            ·
              refine ⟨52868280586012987372181741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35245520390675324914787827 52868280586012987372181741)
              ·
                refine ⟨19825605219754870264568153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52868280586012987372181741 19825605219754870264568153)
                ·
                  refine ⟨14869203914816152698426115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19825605219754870264568153 14869203914816152698426115)
                  ·
                    refine ⟨22303805872224229047639173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14869203914816152698426115 22303805872224229047639173)
                    ·
                      refine ⟨4181963601042042946432345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22303805872224229047639173 4181963601042042946432345)
                      ·
                        rfl

theorem cell23_8144345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_8144345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144345 prefixEnd_8144345 := by exact prefixLift 8144345
  have htrace : WordTrace (prefixWord ++ tailWord_8144345) baseStart_8144345 baseEnd_8144345 := by
    simpa [prefixWord, tailWord_8144345, baseEnd_8144345] using wordTrace_append hprefix tailTrace_8144345
  have hstable : (prefixWord ++ tailWord_8144345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144345).length < 2 ^ (prefixWord ++ tailWord_8144345).sum := by decide
  have hdescent : baseEnd_8144345 < baseStart_8144345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144412 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_8144412 : Nat := 118140960795 + 8144412 * 2 ^ 59
def prefixEnd_8144412 : Nat := 4983230072969 + 3 ^ 40 * 8144412 * 2
def baseEnd_8144412 : Nat := 4181998004245894184294537

theorem tailTrace_8144412 : CollatzResearch.WordTrace tailWord_8144412 prefixEnd_8144412 4181998004245894184294537 := by
  unfold tailWord_8144412
  simp only [CollatzResearch.WordTrace]
  refine ⟨148525554685096876837569745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198034072913462502450092993 148525554685096876837569745)
  ·
    refine ⟨111394166013822657628177309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148525554685096876837569745 111394166013822657628177309)
    ·
      refine ⟨41772812255183496610566491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111394166013822657628177309 41772812255183496610566491)
      ·
        refine ⟨62659218382775244915849737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41772812255183496610566491 62659218382775244915849737)
        ·
          refine ⟨46994413787081433686887303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62659218382775244915849737 46994413787081433686887303)
          ·
            refine ⟨70491620680622150530330955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46994413787081433686887303 70491620680622150530330955)
            ·
              refine ⟨105737431020933225795496433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70491620680622150530330955 105737431020933225795496433)
              ·
                refine ⟨79303073265699919346622325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105737431020933225795496433 79303073265699919346622325)
                ·
                  refine ⟨7434663118659367438745843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79303073265699919346622325 7434663118659367438745843)
                  ·
                    refine ⟨11151994677989051158118765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7434663118659367438745843 11151994677989051158118765)
                    ·
                      refine ⟨4181998004245894184294537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11151994677989051158118765 4181998004245894184294537)
                      ·
                        rfl

theorem cell23_8144412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_8144412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144412 prefixEnd_8144412 := by exact prefixLift 8144412
  have htrace : WordTrace (prefixWord ++ tailWord_8144412) baseStart_8144412 baseEnd_8144412 := by
    simpa [prefixWord, tailWord_8144412, baseEnd_8144412] using wordTrace_append hprefix tailTrace_8144412
  have hstable : (prefixWord ++ tailWord_8144412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144412).length < 2 ^ (prefixWord ++ tailWord_8144412).sum := by decide
  have hdescent : baseEnd_8144412 < baseStart_8144412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144419 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 6]
def baseStart_8144419 : Nat := 118140960795 + 8144419 * 2 ^ 59
def prefixEnd_8144419 : Nat := 4983230072969 + 3 ^ 40 * 8144419 * 2
def baseEnd_8144419 : Nat := 464666844290052850767445

theorem tailTrace_8144419 : CollatzResearch.WordTrace tailWord_8144419 prefixEnd_8144419 464666844290052850767445 := by
  unfold tailWord_8144419
  simp only [CollatzResearch.WordTrace]
  refine ⟨297051364681168393870644311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198034243120778929247096207 297051364681168393870644311)
  ·
    refine ⟨445577047021752590805966467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297051364681168393870644311 445577047021752590805966467)
    ·
      refine ⟨668365570532628886208949701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445577047021752590805966467 668365570532628886208949701)
      ·
        refine ⟨125318544474867916164178069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 668365570532628886208949701 125318544474867916164178069)
        ·
          refine ⟨5874306772259433570195847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125318544474867916164178069 5874306772259433570195847)
          ·
            refine ⟨8811460158389150355293771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5874306772259433570195847 8811460158389150355293771)
            ·
              refine ⟨13217190237583725532940657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8811460158389150355293771 13217190237583725532940657)
              ·
                refine ⟨9912892678187794149705493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13217190237583725532940657 9912892678187794149705493)
                ·
                  refine ⟨464666844290052850767445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9912892678187794149705493 464666844290052850767445)
                  ·
                    rfl

theorem cell23_8144419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 6].length) (baseStart_8144419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144419 prefixEnd_8144419 := by exact prefixLift 8144419
  have htrace : WordTrace (prefixWord ++ tailWord_8144419) baseStart_8144419 baseEnd_8144419 := by
    simpa [prefixWord, tailWord_8144419, baseEnd_8144419] using wordTrace_append hprefix tailTrace_8144419
  have hstable : (prefixWord ++ tailWord_8144419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144419).length < 2 ^ (prefixWord ++ tailWord_8144419).sum := by decide
  have hdescent : baseEnd_8144419 < baseStart_8144419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144428 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_8144428 : Nat := 118140960795 + 8144428 * 2 ^ 59
def prefixEnd_8144428 : Nat := 4983230072969 + 3 ^ 40 * 8144428 * 2
def baseEnd_8144428 : Nat := 1394002073312122040564821

theorem tailTrace_8144428 : CollatzResearch.WordTrace tailWord_8144428 prefixEnd_8144428 1394002073312122040564821 := by
  unfold tailWord_8144428
  simp only [CollatzResearch.WordTrace]
  refine ⟨148525846469067894203860969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198034461958757192271814625 148525846469067894203860969)
  ·
    refine ⟨111394384851800920652895727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148525846469067894203860969 111394384851800920652895727)
    ·
      refine ⟨167091577277701380979343591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111394384851800920652895727 167091577277701380979343591)
      ·
        refine ⟨250637365916552071469015387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167091577277701380979343591 250637365916552071469015387)
        ·
          refine ⟨375956048874828107203523081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250637365916552071469015387 375956048874828107203523081)
          ·
            refine ⟨281967036656121080402642311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375956048874828107203523081 281967036656121080402642311)
            ·
              refine ⟨422950554984181620603963467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281967036656121080402642311 422950554984181620603963467)
              ·
                refine ⟨634425832476272430905945201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422950554984181620603963467 634425832476272430905945201)
                ·
                  refine ⟨475819374357204323179458901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634425832476272430905945201 475819374357204323179458901)
                  ·
                    refine ⟨1394002073312122040564821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 475819374357204323179458901 1394002073312122040564821)
                    ·
                      rfl

theorem cell23_8144428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_8144428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144428 prefixEnd_8144428 := by exact prefixLift 8144428
  have htrace : WordTrace (prefixWord ++ tailWord_8144428) baseStart_8144428 baseEnd_8144428 := by
    simpa [prefixWord, tailWord_8144428, baseEnd_8144428] using wordTrace_append hprefix tailTrace_8144428
  have hstable : (prefixWord ++ tailWord_8144428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144428).length < 2 ^ (prefixWord ++ tailWord_8144428).sum := by decide
  have hdescent : baseEnd_8144428 < baseStart_8144428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144465 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_8144465 : Nat := 118140960795 + 8144465 * 2 ^ 59
def prefixEnd_8144465 : Nat := 4983230072969 + 3 ^ 40 * 8144465 * 2
def baseEnd_8144465 : Nat := 4182025218720582476931793

theorem tailTrace_8144465 : CollatzResearch.WordTrace tailWord_8144465 prefixEnd_8144465 4182025218720582476931793 := by
  unfold tailWord_8144465
  simp only [CollatzResearch.WordTrace]
  refine ⟨297053042439001743726818849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198035361626001162484545899 297053042439001743726818849)
  ·
    refine ⟨222789781829251307795114137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297053042439001743726818849 222789781829251307795114137)
    ·
      refine ⟨167092336371938480846335603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222789781829251307795114137 167092336371938480846335603)
      ·
        refine ⟨250638504557907721269503405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167092336371938480846335603 250638504557907721269503405)
        ·
          refine ⟨93989439209215395476063777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250638504557907721269503405 93989439209215395476063777)
          ·
            refine ⟨70492079406911546607047833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93989439209215395476063777 70492079406911546607047833)
            ·
              refine ⟨52869059555183659955285875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70492079406911546607047833 52869059555183659955285875)
              ·
                refine ⟨79303589332775489932928813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52869059555183659955285875 79303589332775489932928813)
                ·
                  refine ⟨29738845999790808724848305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79303589332775489932928813 29738845999790808724848305)
                  ·
                    refine ⟨22304134499843106543636229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29738845999790808724848305 22304134499843106543636229)
                    ·
                      refine ⟨4182025218720582476931793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22304134499843106543636229 4182025218720582476931793)
                      ·
                        rfl

theorem cell23_8144465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_8144465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144465 prefixEnd_8144465 := by exact prefixLift 8144465
  have htrace : WordTrace (prefixWord ++ tailWord_8144465) baseStart_8144465 baseEnd_8144465 := by
    simpa [prefixWord, tailWord_8144465, baseEnd_8144465] using wordTrace_append hprefix tailTrace_8144465
  have hstable : (prefixWord ++ tailWord_8144465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144465).length < 2 ^ (prefixWord ++ tailWord_8144465).sum := by decide
  have hdescent : baseEnd_8144465 < baseStart_8144465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144496 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 2, 4]
def baseStart_8144496 : Nat := 118140960795 + 8144496 * 2 ^ 59
def prefixEnd_8144496 : Nat := 4983230072969 + 3 ^ 40 * 8144496 * 2
def baseEnd_8144496 : Nat := 1394013712206957285214717

theorem tailTrace_8144496 : CollatzResearch.WordTrace tailWord_8144496 prefixEnd_8144496 1394013712206957285214717 := by
  unfold tailWord_8144496
  simp only [CollatzResearch.WordTrace]
  refine ⟨148527086550944718010598671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198036115401259624014131561 148527086550944718010598671)
  ·
    refine ⟨222790629826417077015898007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148527086550944718010598671 222790629826417077015898007)
    ·
      refine ⟨334185944739625615523847011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222790629826417077015898007 334185944739625615523847011)
      ·
        refine ⟨501278917109438423285770517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334185944739625615523847011 501278917109438423285770517)
        ·
          refine ⟨23497449239504926091520493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 501278917109438423285770517 23497449239504926091520493)
          ·
            refine ⟨8811543464814347284320185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23497449239504926091520493 8811543464814347284320185)
            ·
              refine ⟨6608657598610760463240139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8811543464814347284320185 6608657598610760463240139)
              ·
                refine ⟨9912986397916140694860209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6608657598610760463240139 9912986397916140694860209)
                ·
                  refine ⟨7434739798437105521145157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9912986397916140694860209 7434739798437105521145157)
                  ·
                    refine ⟨1394013712206957285214717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7434739798437105521145157 1394013712206957285214717)
                    ·
                      rfl

theorem cell23_8144496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 4].length) (baseStart_8144496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144496 prefixEnd_8144496 := by exact prefixLift 8144496
  have htrace : WordTrace (prefixWord ++ tailWord_8144496) baseStart_8144496 baseEnd_8144496 := by
    simpa [prefixWord, tailWord_8144496, baseEnd_8144496] using wordTrace_append hprefix tailTrace_8144496
  have hstable : (prefixWord ++ tailWord_8144496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144496).length < 2 ^ (prefixWord ++ tailWord_8144496).sum := by decide
  have hdescent : baseEnd_8144496 < baseStart_8144496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144536 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 2, 1, 3]
def baseStart_8144536 : Nat := 118140960795 + 8144536 * 2 ^ 59
def prefixEnd_8144536 : Nat := 4983230072969 + 3 ^ 40 * 8144536 * 2
def baseEnd_8144536 : Nat := 4182061675847051699143967

theorem tailTrace_8144536 : CollatzResearch.WordTrace tailWord_8144536 prefixEnd_8144536 4182061675847051699143967 := by
  unfold tailWord_8144536
  simp only [CollatzResearch.WordTrace]
  refine ⟨148527816010872261426326731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198037088014496348568435641 148527816010872261426326731)
  ·
    refine ⟨222791724016308392139490097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148527816010872261426326731 222791724016308392139490097)
    ·
      refine ⟨167093793012231294104617573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222791724016308392139490097 167093793012231294104617573)
      ·
        refine ⟨31330086189793367644615795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167093793012231294104617573 31330086189793367644615795)
        ·
          refine ⟨46995129284690051466923693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31330086189793367644615795 46995129284690051466923693)
          ·
            refine ⟨17623173481758769300096385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46995129284690051466923693 17623173481758769300096385)
            ·
              refine ⟨13217380111319076975072289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17623173481758769300096385 13217380111319076975072289)
              ·
                refine ⟨9913035083489307731304217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13217380111319076975072289 9913035083489307731304217)
                ·
                  refine ⟨7434776312616980798478163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9913035083489307731304217 7434776312616980798478163)
                  ·
                    refine ⟨11152164468925471197717245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7434776312616980798478163 11152164468925471197717245)
                    ·
                      refine ⟨4182061675847051699143967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11152164468925471197717245 4182061675847051699143967)
                      ·
                        rfl

theorem cell23_8144536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_8144536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144536 prefixEnd_8144536 := by exact prefixLift 8144536
  have htrace : WordTrace (prefixWord ++ tailWord_8144536) baseStart_8144536 baseEnd_8144536 := by
    simpa [prefixWord, tailWord_8144536, baseEnd_8144536] using wordTrace_append hprefix tailTrace_8144536
  have hstable : (prefixWord ++ tailWord_8144536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144536).length < 2 ^ (prefixWord ++ tailWord_8144536).sum := by decide
  have hdescent : baseEnd_8144536 < baseStart_8144536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144559 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 1, 4, 2]
def baseStart_8144559 : Nat := 118140960795 + 8144559 * 2 ^ 59
def prefixEnd_8144559 : Nat := 4983230072969 + 3 ^ 40 * 8144559 * 2
def baseEnd_8144559 : Nat := 4182073485902105109156361

theorem tailTrace_8144559 : CollatzResearch.WordTrace tailWord_8144559 prefixEnd_8144559 4182073485902105109156361 := by
  unfold tailWord_8144559
  simp only [CollatzResearch.WordTrace]
  refine ⟨297056470900661197780740731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198037647267107465187160487 297056470900661197780740731)
  ·
    refine ⟨445584706350991796671111097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297056470900661197780740731 445584706350991796671111097)
    ·
      refine ⟨334188529763243847503333323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445584706350991796671111097 334188529763243847503333323)
      ·
        refine ⟨501282794644865771254999985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334188529763243847503333323 501282794644865771254999985)
        ·
          refine ⟨375962095983649328441249989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501282794644865771254999985 375962095983649328441249989)
          ·
            refine ⟨70492892996934249082734373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375962095983649328441249989 70492892996934249082734373)
            ·
              refine ⟨13217417436925171703012695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70492892996934249082734373 13217417436925171703012695)
              ·
                refine ⟨19826126155387757554519043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13217417436925171703012695 19826126155387757554519043)
                ·
                  refine ⟨29739189233081636331778565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19826126155387757554519043 29739189233081636331778565)
                  ·
                    refine ⟨5576097981202806812208481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29739189233081636331778565 5576097981202806812208481)
                    ·
                      refine ⟨4182073485902105109156361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576097981202806812208481 4182073485902105109156361)
                      ·
                        rfl

theorem cell23_8144559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 4, 2].length) (baseStart_8144559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144559 prefixEnd_8144559 := by exact prefixLift 8144559
  have htrace : WordTrace (prefixWord ++ tailWord_8144559) baseStart_8144559 baseEnd_8144559 := by
    simpa [prefixWord, tailWord_8144559, baseEnd_8144559] using wordTrace_append hprefix tailTrace_8144559
  have hstable : (prefixWord ++ tailWord_8144559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144559).length < 2 ^ (prefixWord ++ tailWord_8144559).sum := by decide
  have hdescent : baseEnd_8144559 < baseStart_8144559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144593 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 2, 2, 2]
def baseStart_8144593 : Nat := 118140960795 + 8144593 * 2 ^ 59
def prefixEnd_8144593 : Nat := 4983230072969 + 3 ^ 40 * 8144593 * 2
def baseEnd_8144593 : Nat := 4182090944244357976131205

theorem tailTrace_8144593 : CollatzResearch.WordTrace tailWord_8144593 prefixEnd_8144593 4182090944244357976131205 := by
  unfold tailWord_8144593
  simp only [CollatzResearch.WordTrace]
  refine ⟨297057710982538021587478433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198038473988358681058318955 297057710982538021587478433)
  ·
    refine ⟨222793283236903516190608825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297057710982538021587478433 222793283236903516190608825)
    ·
      refine ⟨167094962427677637142956619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222793283236903516190608825 167094962427677637142956619)
      ·
        refine ⟨250642443641516455714434929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167094962427677637142956619 250642443641516455714434929)
        ·
          refine ⟨187981832731137341785826197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250642443641516455714434929 187981832731137341785826197)
          ·
            refine ⟨8811648409272062896210603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187981832731137341785826197 8811648409272062896210603)
            ·
              refine ⟨13217472613908094344315905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8811648409272062896210603 13217472613908094344315905)
              ·
                refine ⟨9913104460431070758236929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13217472613908094344315905 9913104460431070758236929)
                ·
                  refine ⟨7434828345323303068677697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9913104460431070758236929 7434828345323303068677697)
                  ·
                    refine ⟨5576121258992477301508273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7434828345323303068677697 5576121258992477301508273)
                    ·
                      refine ⟨4182090944244357976131205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576121258992477301508273 4182090944244357976131205)
                      ·
                        rfl

theorem cell23_8144593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_8144593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144593 prefixEnd_8144593 := by exact prefixLift 8144593
  have htrace : WordTrace (prefixWord ++ tailWord_8144593) baseStart_8144593 baseEnd_8144593 := by
    simpa [prefixWord, tailWord_8144593, baseEnd_8144593] using wordTrace_append hprefix tailTrace_8144593
  have hstable : (prefixWord ++ tailWord_8144593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144593).length < 2 ^ (prefixWord ++ tailWord_8144593).sum := by decide
  have hdescent : baseEnd_8144593 < baseStart_8144593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144749 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_8144749 : Nat := 118140960795 + 8144749 * 2 ^ 59
def prefixEnd_8144749 : Nat := 4983230072969 + 3 ^ 40 * 8144749 * 2
def baseEnd_8144749 : Nat := 1394057015742153121926829

theorem tailTrace_8144749 : CollatzResearch.WordTrace tailWord_8144749 prefixEnd_8144749 1394057015742153121926829 := by
  unfold tailWord_8144749
  simp only [CollatzResearch.WordTrace]
  refine ⟨297063400769972860230157301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198042267179981906820104867 297063400769972860230157301)
  ·
    refine ⟨27849693822184955646577247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297063400769972860230157301 27849693822184955646577247)
    ·
      refine ⟨41774540733277433469865871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27849693822184955646577247 41774540733277433469865871)
      ·
        refine ⟨62661811099916150204798807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41774540733277433469865871 62661811099916150204798807)
        ·
          refine ⟨93992716649874225307198211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62661811099916150204798807 93992716649874225307198211)
          ·
            refine ⟨140989074974811337960797317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93992716649874225307198211 140989074974811337960797317)
            ·
              refine ⟨26435451557777125867649497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140989074974811337960797317 26435451557777125867649497)
              ·
                refine ⟨19826588668332844400737123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26435451557777125867649497 19826588668332844400737123)
                ·
                  refine ⟨29739883002499266601105685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19826588668332844400737123 29739883002499266601105685)
                  ·
                    refine ⟨1394057015742153121926829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29739883002499266601105685 1394057015742153121926829)
                    ·
                      rfl

theorem cell23_8144749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_8144749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144749 prefixEnd_8144749 := by exact prefixLift 8144749
  have htrace : WordTrace (prefixWord ++ tailWord_8144749) baseStart_8144749 baseEnd_8144749 := by
    simpa [prefixWord, tailWord_8144749, baseEnd_8144749] using wordTrace_append hprefix tailTrace_8144749
  have hstable : (prefixWord ++ tailWord_8144749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144749).length < 2 ^ (prefixWord ++ tailWord_8144749).sum := by decide
  have hdescent : baseEnd_8144749 < baseStart_8144749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144750 : List Nat := [4, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_8144750 : Nat := 118140960795 + 8144750 * 2 ^ 59
def prefixEnd_8144750 : Nat := 4983230072969 + 3 ^ 40 * 8144750 * 2
def baseEnd_8144750 : Nat := 4182171560707113861867983

theorem tailTrace_8144750 : CollatzResearch.WordTrace tailWord_8144750 prefixEnd_8144750 4182171560707113861867983 := by
  unfold tailWord_8144750
  simp only [CollatzResearch.WordTrace]
  refine ⟨37132929655371154675117963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198042291495312824933962469 37132929655371154675117963)
  ·
    refine ⟨55699394483056732012676945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37132929655371154675117963 55699394483056732012676945)
    ·
      refine ⟨41774545862292549009507709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55699394483056732012676945 41774545862292549009507709)
      ·
        refine ⟨15665454698359705878565391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41774545862292549009507709 15665454698359705878565391)
        ·
          refine ⟨23498182047539558817848087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15665454698359705878565391 23498182047539558817848087)
          ·
            refine ⟨35247273071309338226772131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23498182047539558817848087 35247273071309338226772131)
            ·
              refine ⟨52870909606964007340158197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35247273071309338226772131 52870909606964007340158197)
              ·
                refine ⟨4956647775652875688139831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52870909606964007340158197 4956647775652875688139831)
                ·
                  refine ⟨7434971663479313532209747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4956647775652875688139831 7434971663479313532209747)
                  ·
                    refine ⟨11152457495218970298314621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7434971663479313532209747 11152457495218970298314621)
                    ·
                      refine ⟨4182171560707113861867983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11152457495218970298314621 4182171560707113861867983)
                      ·
                        rfl

theorem cell23_8144750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_8144750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144750 prefixEnd_8144750 := by exact prefixLift 8144750
  have htrace : WordTrace (prefixWord ++ tailWord_8144750) baseStart_8144750 baseEnd_8144750 := by
    simpa [prefixWord, tailWord_8144750, baseEnd_8144750] using wordTrace_append hprefix tailTrace_8144750
  have hstable : (prefixWord ++ tailWord_8144750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144750).length < 2 ^ (prefixWord ++ tailWord_8144750).sum := by decide
  have hdescent : baseEnd_8144750 < baseStart_8144750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144752 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_8144752 : Nat := 118140960795 + 8144752 * 2 ^ 59
def prefixEnd_8144752 : Nat := 4983230072969 + 3 ^ 40 * 8144752 * 2
def baseEnd_8144752 : Nat := 4182172587668422854042973

theorem tailTrace_8144752 : CollatzResearch.WordTrace tailWord_8144752 prefixEnd_8144752 4182172587668422854042973 := by
  unfold tailWord_8144752
  simp only [CollatzResearch.WordTrace]
  refine ⟨148531755094480995871258255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198042340125974661161677673 148531755094480995871258255)
  ·
    refine ⟨222797632641721493806887383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148531755094480995871258255 222797632641721493806887383)
    ·
      refine ⟨334196448962582240710331075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222797632641721493806887383 334196448962582240710331075)
      ·
        refine ⟨501294673443873361065496613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334196448962582240710331075 501294673443873361065496613)
        ·
          refine ⟨93992751270726255199780615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501294673443873361065496613 93992751270726255199780615)
          ·
            refine ⟨140989126906089382799670923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93992751270726255199780615 140989126906089382799670923)
            ·
              refine ⟨211483690359134074199506385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140989126906089382799670923 211483690359134074199506385)
              ·
                refine ⟨158612767769350555649629789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211483690359134074199506385 158612767769350555649629789)
                ·
                  refine ⟨59479787913506458368611171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158612767769350555649629789 59479787913506458368611171)
                  ·
                    refine ⟨89219681870259687552916757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59479787913506458368611171 89219681870259687552916757)
                    ·
                      refine ⟨4182172587668422854042973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89219681870259687552916757 4182172587668422854042973)
                      ·
                        rfl

theorem cell23_8144752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_8144752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144752 prefixEnd_8144752 := by exact prefixLift 8144752
  have htrace : WordTrace (prefixWord ++ tailWord_8144752) baseStart_8144752 baseEnd_8144752 := by
    simpa [prefixWord, tailWord_8144752, baseEnd_8144752] using wordTrace_append hprefix tailTrace_8144752
  have hstable : (prefixWord ++ tailWord_8144752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144752).length < 2 ^ (prefixWord ++ tailWord_8144752).sum := by decide
  have hdescent : baseEnd_8144752 < baseStart_8144752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144773 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 3, 2, 2]
def baseStart_8144773 : Nat := 118140960795 + 8144773 * 2 ^ 59
def prefixEnd_8144773 : Nat := 4983230072969 + 3 ^ 40 * 8144773 * 2
def baseEnd_8144773 : Nat := 4182183370762167271880377

theorem tailTrace_8144773 : CollatzResearch.WordTrace tailWord_8144773 prefixEnd_8144773 4182183370762167271880377 := by
  unfold tailWord_8144773
  simp only [CollatzResearch.WordTrace]
  refine ⟨297064276121885912329030973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198042850747923941552687315 297064276121885912329030973)
  ·
    refine ⟨111399103545707217123386615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297064276121885912329030973 111399103545707217123386615)
    ·
      refine ⟨167098655318560825685079923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111399103545707217123386615 167098655318560825685079923)
      ·
        refine ⟨250647982977841238527619885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167098655318560825685079923 250647982977841238527619885)
        ·
          refine ⟨93992993616690464447857457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250647982977841238527619885 93992993616690464447857457)
          ·
            refine ⟨70494745212517848335893093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93992993616690464447857457 70494745212517848335893093)
            ·
              refine ⟨13217764727347096562979955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70494745212517848335893093 13217764727347096562979955)
              ·
                refine ⟨19826647091020644844469933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13217764727347096562979955 19826647091020644844469933)
                ·
                  refine ⟨7434992659132741816676225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19826647091020644844469933 7434992659132741816676225)
                  ·
                    refine ⟨5576244494349556362507169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7434992659132741816676225 5576244494349556362507169)
                    ·
                      refine ⟨4182183370762167271880377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576244494349556362507169 4182183370762167271880377)
                      ·
                        rfl

theorem cell23_8144773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_8144773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144773 prefixEnd_8144773 := by exact prefixLift 8144773
  have htrace : WordTrace (prefixWord ++ tailWord_8144773) baseStart_8144773 baseEnd_8144773 := by
    simpa [prefixWord, tailWord_8144773, baseEnd_8144773] using wordTrace_append hprefix tailTrace_8144773
  have hstable : (prefixWord ++ tailWord_8144773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144773).length < 2 ^ (prefixWord ++ tailWord_8144773).sum := by decide
  have hdescent : baseEnd_8144773 < baseStart_8144773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144776 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_8144776 : Nat := 118140960795 + 8144776 * 2 ^ 59
def prefixEnd_8144776 : Nat := 4983230072969 + 3 ^ 40 * 8144776 * 2
def baseEnd_8144776 : Nat := 4182184911204130760142863

theorem tailTrace_8144776 : CollatzResearch.WordTrace tailWord_8144776 prefixEnd_8144776 4182184911204130760142863 := by
  unfold tailWord_8144776
  simp only [CollatzResearch.WordTrace]
  refine ⟨148532192770437521920695091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198042923693916695894260121 148532192770437521920695091)
  ·
    refine ⟨222798289155656282881042637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148532192770437521920695091 222798289155656282881042637)
    ·
      refine ⟨83549358433371106080390989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222798289155656282881042637 83549358433371106080390989)
      ·
        refine ⟨31331009412514164780146621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83549358433371106080390989 31331009412514164780146621)
        ·
          refine ⟨11749128529692811792554983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31331009412514164780146621 11749128529692811792554983)
          ·
            refine ⟨17623692794539217688832475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11749128529692811792554983 17623692794539217688832475)
            ·
              refine ⟨26435539191808826533248713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17623692794539217688832475 26435539191808826533248713)
              ·
                refine ⟨19826654393856619899936535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26435539191808826533248713 19826654393856619899936535)
                ·
                  refine ⟨29739981590784929849904803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19826654393856619899936535 29739981590784929849904803)
                  ·
                    refine ⟨44609972386177394774857205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29739981590784929849904803 44609972386177394774857205)
                    ·
                      refine ⟨4182184911204130760142863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44609972386177394774857205 4182184911204130760142863)
                      ·
                        rfl

theorem cell23_8144776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_8144776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144776 prefixEnd_8144776 := by exact prefixLift 8144776
  have htrace : WordTrace (prefixWord ++ tailWord_8144776) baseStart_8144776 baseEnd_8144776 := by
    simpa [prefixWord, tailWord_8144776, baseEnd_8144776] using wordTrace_append hprefix tailTrace_8144776
  have hstable : (prefixWord ++ tailWord_8144776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144776).length < 2 ^ (prefixWord ++ tailWord_8144776).sum := by decide
  have hdescent : baseEnd_8144776 < baseStart_8144776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144786 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_8144786 : Nat := 118140960795 + 8144786 * 2 ^ 59
def prefixEnd_8144786 : Nat := 4983230072969 + 3 ^ 40 * 8144786 * 2
def baseEnd_8144786 : Nat := 4182190046010675721017817

theorem tailTrace_8144786 : CollatzResearch.WordTrace tailWord_8144786 prefixEnd_8144786 4182190046010675721017817 := by
  unfold tailWord_8144786
  simp only [CollatzResearch.WordTrace]
  refine ⟨74266187567709703887313553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198043166847225877032836141 74266187567709703887313553)
  ·
    refine ⟨55699640675782277915485165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74266187567709703887313553 55699640675782277915485165)
    ·
      refine ⟨20887365253418354218306937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55699640675782277915485165 20887365253418354218306937)
      ·
        refine ⟨15665523940063765663730203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20887365253418354218306937 15665523940063765663730203)
        ·
          refine ⟨23498285910095648495595305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15665523940063765663730203 23498285910095648495595305)
          ·
            refine ⟨17623714432571736371696479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23498285910095648495595305 17623714432571736371696479)
            ·
              refine ⟨26435571648857604557544719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17623714432571736371696479 26435571648857604557544719)
              ·
                refine ⟨39653357473286406836317079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26435571648857604557544719 39653357473286406836317079)
                ·
                  refine ⟨59480036209929610254475619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39653357473286406836317079 59480036209929610254475619)
                  ·
                    refine ⟨89220054314894415381713429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59480036209929610254475619 89220054314894415381713429)
                    ·
                      refine ⟨4182190046010675721017817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89220054314894415381713429 4182190046010675721017817)
                      ·
                        rfl

theorem cell23_8144786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_8144786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144786 prefixEnd_8144786 := by exact prefixLift 8144786
  have htrace : WordTrace (prefixWord ++ tailWord_8144786) baseStart_8144786 baseEnd_8144786 := by
    simpa [prefixWord, tailWord_8144786, baseEnd_8144786] using wordTrace_append hprefix tailTrace_8144786
  have hstable : (prefixWord ++ tailWord_8144786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144786).length < 2 ^ (prefixWord ++ tailWord_8144786).sum := by decide
  have hdescent : baseEnd_8144786 < baseStart_8144786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144796 : List Nat := [2, 2, 3, 3, 1, 1, 4, 7]
def baseStart_8144796 : Nat := 118140960795 + 8144796 * 2 ^ 59
def prefixEnd_8144796 : Nat := 4983230072969 + 3 ^ 40 * 8144796 * 2
def baseEnd_8144796 : Nat := 154896117808045210440473

theorem tailTrace_8144796 : CollatzResearch.WordTrace tailWord_8144796 prefixEnd_8144796 154896117808045210440473 := by
  unfold tailWord_8144796
  simp only [CollatzResearch.WordTrace]
  refine ⟨148532557500401293628559121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198043410000535058171412161 148532557500401293628559121)
  ·
    refine ⟨111399418125300970221419341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148532557500401293628559121 111399418125300970221419341)
    ·
      refine ⟨41774781796987863833032253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111399418125300970221419341 41774781796987863833032253)
      ·
        refine ⟨15665543173870448937387095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41774781796987863833032253 15665543173870448937387095)
        ·
          refine ⟨23498314760805673406080643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15665543173870448937387095 23498314760805673406080643)
          ·
            refine ⟨35247472141208510109120965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23498314760805673406080643 35247472141208510109120965)
            ·
              refine ⟨6608901026476595645460181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35247472141208510109120965 6608901026476595645460181)
              ·
                refine ⟨154896117808045210440473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6608901026476595645460181 154896117808045210440473)
                ·
                  rfl

theorem cell23_8144796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 7].length) (baseStart_8144796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144796 prefixEnd_8144796 := by exact prefixLift 8144796
  have htrace : WordTrace (prefixWord ++ tailWord_8144796) baseStart_8144796 baseEnd_8144796 := by
    simpa [prefixWord, tailWord_8144796, baseEnd_8144796] using wordTrace_append hprefix tailTrace_8144796
  have hstable : (prefixWord ++ tailWord_8144796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144796).length < 2 ^ (prefixWord ++ tailWord_8144796).sum := by decide
  have hdescent : baseEnd_8144796 < baseStart_8144796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144807 : List Nat := [1, 1, 6, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_8144807 : Nat := 118140960795 + 8144807 * 2 ^ 59
def prefixEnd_8144807 : Nat := 4983230072969 + 3 ^ 40 * 8144807 * 2
def baseEnd_8144807 : Nat := 4182200829104420138855221

theorem tailTrace_8144807 : CollatzResearch.WordTrace tailWord_8144807 prefixEnd_8144807 4182200829104420138855221 := by
  unfold tailWord_8144807
  simp only [CollatzResearch.WordTrace]
  refine ⟨297065516203762736135768675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198043677469175157423845783 297065516203762736135768675)
  ·
    refine ⟨445598274305644104203653013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297065516203762736135768675 445598274305644104203653013)
    ·
      refine ⟨20887419108077067384546235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 445598274305644104203653013 20887419108077067384546235)
      ·
        refine ⟨31331128662115601076819353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20887419108077067384546235 31331128662115601076819353)
        ·
          refine ⟨23498346496586700807614515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31331128662115601076819353 23498346496586700807614515)
          ·
            refine ⟨35247519744880051211421773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23498346496586700807614515 35247519744880051211421773)
            ·
              refine ⟨13217819904330019204283165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35247519744880051211421773 13217819904330019204283165)
              ·
                refine ⟨4956682464123757201606187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13217819904330019204283165 4956682464123757201606187)
                ·
                  refine ⟨7435023696185635802409281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4956682464123757201606187 7435023696185635802409281)
                  ·
                    refine ⟨5576267772139226851806961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7435023696185635802409281 5576267772139226851806961)
                    ·
                      refine ⟨4182200829104420138855221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576267772139226851806961 4182200829104420138855221)
                      ·
                        rfl

theorem cell23_8144807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_8144807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144807 prefixEnd_8144807 := by exact prefixLift 8144807
  have htrace : WordTrace (prefixWord ++ tailWord_8144807) baseStart_8144807 baseEnd_8144807 := by
    simpa [prefixWord, tailWord_8144807, baseEnd_8144807] using wordTrace_append hprefix tailTrace_8144807
  have hstable : (prefixWord ++ tailWord_8144807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144807).length < 2 ^ (prefixWord ++ tailWord_8144807).sum := by decide
  have hdescent : baseEnd_8144807 < baseStart_8144807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144840 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_8144840 : Nat := 118140960795 + 8144840 * 2 ^ 59
def prefixEnd_8144840 : Nat := 4983230072969 + 3 ^ 40 * 8144840 * 2
def baseEnd_8144840 : Nat := 4182217773966018509742569

theorem tailTrace_8144840 : CollatzResearch.WordTrace tailWord_8144840 prefixEnd_8144840 4182217773966018509742569 := by
  unfold tailWord_8144840
  simp only [CollatzResearch.WordTrace]
  refine ⟨148533359906321591385859987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198044479875095455181146649 148533359906321591385859987)
  ·
    refine ⟨222800039859482387078789981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148533359906321591385859987 222800039859482387078789981)
    ·
      refine ⟨83550014947305895154546243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222800039859482387078789981 83550014947305895154546243)
      ·
        refine ⟨125325022420958842731819365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83550014947305895154546243 125325022420958842731819365)
        ·
          refine ⟨23498441703929783012216131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125325022420958842731819365 23498441703929783012216131)
          ·
            refine ⟨35247662555894674518324197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23498441703929783012216131 35247662555894674518324197)
            ·
              refine ⟨6608936729230251472185787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35247662555894674518324197 6608936729230251472185787)
              ·
                refine ⟨9913405093845377208278681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6608936729230251472185787 9913405093845377208278681)
                ·
                  refine ⟨7435053820384032906209011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9913405093845377208278681 7435053820384032906209011)
                  ·
                    refine ⟨11152580730576049359313517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7435053820384032906209011 11152580730576049359313517)
                    ·
                      refine ⟨4182217773966018509742569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11152580730576049359313517 4182217773966018509742569)
                      ·
                        rfl

theorem cell23_8144840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_8144840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144840 prefixEnd_8144840 := by exact prefixLift 8144840
  have htrace : WordTrace (prefixWord ++ tailWord_8144840) baseStart_8144840 baseEnd_8144840 := by
    simpa [prefixWord, tailWord_8144840, baseEnd_8144840] using wordTrace_append hprefix tailTrace_8144840
  have hstable : (prefixWord ++ tailWord_8144840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144840).length < 2 ^ (prefixWord ++ tailWord_8144840).sum := by decide
  have hdescent : baseEnd_8144840 < baseStart_8144840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144849 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_8144849 : Nat := 118140960795 + 8144849 * 2 ^ 59
def prefixEnd_8144849 : Nat := 4983230072969 + 3 ^ 40 * 8144849 * 2
def baseEnd_8144849 : Nat := 4182222395291908974530027

theorem tailTrace_8144849 : CollatzResearch.WordTrace tailWord_8144849 prefixEnd_8144849 4182222395291908974530027 := by
  unfold tailWord_8144849
  simp only [CollatzResearch.WordTrace]
  refine ⟨297067048069610577308797601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198044698713073718205865067 297067048069610577308797601)
  ·
    refine ⟨222800286052207932981598201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297067048069610577308797601 222800286052207932981598201)
    ·
      refine ⟨167100214539155949736198651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222800286052207932981598201 167100214539155949736198651)
      ·
        refine ⟨250650321808733924604297977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167100214539155949736198651 250650321808733924604297977)
        ·
          refine ⟨187987741356550443453223483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250650321808733924604297977 187987741356550443453223483)
          ·
            refine ⟨281981612034825665179835225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187987741356550443453223483 281981612034825665179835225)
            ·
              refine ⟨211486209026119248884876419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281981612034825665179835225 211486209026119248884876419)
              ·
                refine ⟨317229313539178873327314629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211486209026119248884876419 317229313539178873327314629)
                ·
                  refine ⟨59480496288596038748871493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317229313539178873327314629 59480496288596038748871493)
                  ·
                    refine ⟨11152593054111757265413405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59480496288596038748871493 11152593054111757265413405)
                    ·
                      refine ⟨4182222395291908974530027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11152593054111757265413405 4182222395291908974530027)
                      ·
                        rfl

theorem cell23_8144849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_8144849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144849 prefixEnd_8144849 := by exact prefixLift 8144849
  have htrace : WordTrace (prefixWord ++ tailWord_8144849) baseStart_8144849 baseEnd_8144849 := by
    simpa [prefixWord, tailWord_8144849, baseEnd_8144849] using wordTrace_append hprefix tailTrace_8144849
  have hstable : (prefixWord ++ tailWord_8144849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144849).length < 2 ^ (prefixWord ++ tailWord_8144849).sum := by decide
  have hdescent : baseEnd_8144849 < baseStart_8144849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144850 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_8144850 : Nat := 118140960795 + 8144850 * 2 ^ 59
def prefixEnd_8144850 : Nat := 4983230072969 + 3 ^ 40 * 8144850 * 2
def baseEnd_8144850 : Nat := 4182222908772563470617523

theorem tailTrace_8144850 : CollatzResearch.WordTrace tailWord_8144850 prefixEnd_8144850 4182222908772563470617523 := by
  unfold tailWord_8144850
  simp only [CollatzResearch.WordTrace]
  refine ⟨74266771135651738619896001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198044723028404636319722669 74266771135651738619896001)
  ·
    refine ⟨55700078351738803964922001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74266771135651738619896001 55700078351738803964922001)
    ·
      refine ⟨41775058763804102973691501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55700078351738803964922001 41775058763804102973691501)
      ·
        refine ⟨15665647036426538615134313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41775058763804102973691501 15665647036426538615134313)
        ·
          refine ⟨11749235277319903961350735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15665647036426538615134313 11749235277319903961350735)
          ·
            refine ⟨17623852915979855942026103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11749235277319903961350735 17623852915979855942026103)
            ·
              refine ⟨26435779373969783913039155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17623852915979855942026103 26435779373969783913039155)
              ·
                refine ⟨39653669060954675869558733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26435779373969783913039155 39653669060954675869558733)
                ·
                  refine ⟨14870125897858003451084525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39653669060954675869558733 14870125897858003451084525)
                  ·
                    refine ⟨5576297211696751294156697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14870125897858003451084525 5576297211696751294156697)
                    ·
                      refine ⟨4182222908772563470617523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576297211696751294156697 4182222908772563470617523)
                      ·
                        rfl

theorem cell23_8144850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_8144850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144850 prefixEnd_8144850 := by exact prefixLift 8144850
  have htrace : WordTrace (prefixWord ++ tailWord_8144850) baseStart_8144850 baseEnd_8144850 := by
    simpa [prefixWord, tailWord_8144850, baseEnd_8144850] using wordTrace_append hprefix tailTrace_8144850
  have hstable : (prefixWord ++ tailWord_8144850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144850).length < 2 ^ (prefixWord ++ tailWord_8144850).sum := by decide
  have hdescent : baseEnd_8144850 < baseStart_8144850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144863 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 1, 4, 2]
def baseStart_8144863 : Nat := 118140960795 + 8144863 * 2 ^ 59
def prefixEnd_8144863 : Nat := 4983230072969 + 3 ^ 40 * 8144863 * 2
def baseEnd_8144863 : Nat := 4182229584021071919754963

theorem tailTrace_8144863 : CollatzResearch.WordTrace tailWord_8144863 prefixEnd_8144863 4182229584021071919754963 := by
  unfold tailWord_8144863
  simp only [CollatzResearch.WordTrace]
  refine ⟨297067558691559857699807243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198045039127706571799871495 297067558691559857699807243)
  ·
    refine ⟨445601338037339786549710865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297067558691559857699807243 445601338037339786549710865)
    ·
      refine ⟨334201003528004839912283149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445601338037339786549710865 334201003528004839912283149)
      ·
        refine ⟨125325376323001814967106181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334201003528004839912283149 125325376323001814967106181)
        ·
          refine ⟨23498508060562840306332409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125325376323001814967106181 23498508060562840306332409)
          ·
            refine ⟨17623881045422130229749307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23498508060562840306332409 17623881045422130229749307)
            ·
              refine ⟨26435821568133195344623961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17623881045422130229749307 26435821568133195344623961)
              ·
                refine ⟨19826866176099896508467971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26435821568133195344623961 19826866176099896508467971)
                ·
                  refine ⟨29740299264149844762701957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19826866176099896508467971 29740299264149844762701957)
                  ·
                    refine ⟨5576306112028095893006617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29740299264149844762701957 5576306112028095893006617)
                    ·
                      refine ⟨4182229584021071919754963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576306112028095893006617 4182229584021071919754963)
                      ·
                        rfl

theorem cell23_8144863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_8144863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144863 prefixEnd_8144863 := by exact prefixLift 8144863
  have htrace : WordTrace (prefixWord ++ tailWord_8144863) baseStart_8144863 baseEnd_8144863 := by
    simpa [prefixWord, tailWord_8144863, baseEnd_8144863] using wordTrace_append hprefix tailTrace_8144863
  have hstable : (prefixWord ++ tailWord_8144863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144863).length < 2 ^ (prefixWord ++ tailWord_8144863).sum := by decide
  have hdescent : baseEnd_8144863 < baseStart_8144863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144899 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 4, 5]
def baseStart_8144899 : Nat := 118140960795 + 8144899 * 2 ^ 59
def prefixEnd_8144899 : Nat := 4983230072969 + 3 ^ 40 * 8144899 * 2
def baseEnd_8144899 : Nat := 1394082689774877926301599

theorem tailTrace_8144899 : CollatzResearch.WordTrace tailWord_8144899 prefixEnd_8144899 1394082689774877926301599 := by
  unfold tailWord_8144899
  simp only [CollatzResearch.WordTrace]
  refine ⟨297068871719429435848117751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198045914479619623898745167 297068871719429435848117751)
  ·
    refine ⟨445603307579144153772176627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297068871719429435848117751 445603307579144153772176627)
    ·
      refine ⟨668404961368716230658264941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445603307579144153772176627 668404961368716230658264941)
      ·
        refine ⟨250651860513268586496849353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668404961368716230658264941 250651860513268586496849353)
        ·
          refine ⟨187988895384951439872637015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250651860513268586496849353 187988895384951439872637015)
          ·
            refine ⟨281983343077427159808955523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187988895384951439872637015 281983343077427159808955523)
            ·
              refine ⟨422975014616140739713433285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281983343077427159808955523 422975014616140739713433285)
              ·
                refine ⟨79307815240526388696268741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422975014616140739713433285 79307815240526388696268741)
                ·
                  refine ⟨14870215357598697880550389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79307815240526388696268741 14870215357598697880550389)
                  ·
                    refine ⟨1394082689774877926301599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14870215357598697880550389 1394082689774877926301599)
                    ·
                      rfl

theorem cell23_8144899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 5].length) (baseStart_8144899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144899 prefixEnd_8144899 := by exact prefixLift 8144899
  have htrace : WordTrace (prefixWord ++ tailWord_8144899) baseStart_8144899 baseEnd_8144899 := by
    simpa [prefixWord, tailWord_8144899, baseEnd_8144899] using wordTrace_append hprefix tailTrace_8144899
  have hstable : (prefixWord ++ tailWord_8144899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144899).length < 2 ^ (prefixWord ++ tailWord_8144899).sum := by decide
  have hdescent : baseEnd_8144899 < baseStart_8144899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144956 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_8144956 : Nat := 118140960795 + 8144956 * 2 ^ 59
def prefixEnd_8144956 : Nat := 4983230072969 + 3 ^ 40 * 8144956 * 2
def baseEnd_8144956 : Nat := 4182277337721940055892035

theorem tailTrace_8144956 : CollatzResearch.WordTrace tailWord_8144956 prefixEnd_8144956 4182277337721940055892035 := by
  unfold tailWord_8144956
  simp only [CollatzResearch.WordTrace]
  refine ⟨148535475340111467291471361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198047300453481956388628481 148535475340111467291471361)
  ·
    refine ⟨111401606505083600468603521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148535475340111467291471361 111401606505083600468603521)
    ·
      refine ⟨83551204878812700351452641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111401606505083600468603521 83551204878812700351452641)
      ·
        refine ⟨62663403659109525263589481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83551204878812700351452641 62663403659109525263589481)
        ·
          refine ⟨46997552744332143947692111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62663403659109525263589481 46997552744332143947692111)
          ·
            refine ⟨70496329116498215921538167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46997552744332143947692111 70496329116498215921538167)
            ·
              refine ⟨105744493674747323882307251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70496329116498215921538167 105744493674747323882307251)
              ·
                refine ⟨158616740512120985823460877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105744493674747323882307251 158616740512120985823460877)
                ·
                  refine ⟨59481277692045369683797829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158616740512120985823460877 59481277692045369683797829)
                  ·
                    refine ⟨11152739567258506815712093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59481277692045369683797829 11152739567258506815712093)
                    ·
                      refine ⟨4182277337721940055892035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11152739567258506815712093 4182277337721940055892035)
                      ·
                        rfl

theorem cell23_8144956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_8144956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144956 prefixEnd_8144956 := by exact prefixLift 8144956
  have htrace : WordTrace (prefixWord ++ tailWord_8144956) baseStart_8144956 baseEnd_8144956 := by
    simpa [prefixWord, tailWord_8144956, baseEnd_8144956] using wordTrace_append hprefix tailTrace_8144956
  have hstable : (prefixWord ++ tailWord_8144956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144956).length < 2 ^ (prefixWord ++ tailWord_8144956).sum := by decide
  have hdescent : baseEnd_8144956 < baseStart_8144956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144973 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_8144973 : Nat := 118140960795 + 8144973 * 2 ^ 59
def prefixEnd_8144973 : Nat := 4983230072969 + 3 ^ 40 * 8144973 * 2
def baseEnd_8144973 : Nat := 4182286066893066489379457

theorem tailTrace_8144973 : CollatzResearch.WordTrace tailWord_8144973 prefixEnd_8144973 4182286066893066489379457 := by
  unfold tailWord_8144973
  simp only [CollatzResearch.WordTrace]
  refine ⟨297071570721161346486311573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198047713814107564324207715 297071570721161346486311573)
  ·
    refine ⟨13925229877554438116545855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 297071570721161346486311573 13925229877554438116545855)
    ·
      refine ⟨20887844816331657174818783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13925229877554438116545855 20887844816331657174818783)
      ·
        refine ⟨31331767224497485762228175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20887844816331657174818783 31331767224497485762228175)
        ·
          refine ⟨46997650836746228643342263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31331767224497485762228175 46997650836746228643342263)
          ·
            refine ⟨70496476255119342965013395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46997650836746228643342263 70496476255119342965013395)
            ·
              refine ⟨105744714382679014447520093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70496476255119342965013395 105744714382679014447520093)
              ·
                refine ⟨39654267893504630417820035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105744714382679014447520093 39654267893504630417820035)
                ·
                  refine ⟨59481401840256945626730053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39654267893504630417820035 59481401840256945626730053)
                  ·
                    refine ⟨11152762845048177305011885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59481401840256945626730053 11152762845048177305011885)
                    ·
                      refine ⟨4182286066893066489379457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11152762845048177305011885 4182286066893066489379457)
                      ·
                        rfl

theorem cell23_8144973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_8144973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144973 prefixEnd_8144973 := by exact prefixLift 8144973
  have htrace : WordTrace (prefixWord ++ tailWord_8144973) baseStart_8144973 baseEnd_8144973 := by
    simpa [prefixWord, tailWord_8144973, baseEnd_8144973] using wordTrace_append hprefix tailTrace_8144973
  have hstable : (prefixWord ++ tailWord_8144973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144973).length < 2 ^ (prefixWord ++ tailWord_8144973).sum := by decide
  have hdescent : baseEnd_8144973 < baseStart_8144973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144997 : List Nat := [1, 3, 1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_8144997 : Nat := 118140960795 + 8144997 * 2 ^ 59
def prefixEnd_8144997 : Nat := 4983230072969 + 3 ^ 40 * 8144997 * 2
def baseEnd_8144997 : Nat := 1394099463476258131826449

theorem tailTrace_8144997 : CollatzResearch.WordTrace tailWord_8144997 prefixEnd_8144997 1394099463476258131826449 := by
  unfold tailWord_8144997
  simp only [CollatzResearch.WordTrace]
  refine ⟨297072446073074398585185245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198048297382049599056790163 297072446073074398585185245)
  ·
    refine ⟨111402167277402899469444467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297072446073074398585185245 111402167277402899469444467)
    ·
      refine ⟨167103250916104349204166701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111402167277402899469444467 167103250916104349204166701)
      ·
        refine ⟨62663719093539130951562513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167103250916104349204166701 62663719093539130951562513)
        ·
          refine ⟨46997789320154348213671885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62663719093539130951562513 46997789320154348213671885)
          ·
            refine ⟨17624170995057880580126957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46997789320154348213671885 17624170995057880580126957)
            ·
              refine ⟨6609064123146705217547609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17624170995057880580126957 6609064123146705217547609)
              ·
                refine ⟨4956798092360028913160707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6609064123146705217547609 4956798092360028913160707)
                ·
                  refine ⟨7435197138540043369741061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4956798092360028913160707 7435197138540043369741061)
                  ·
                    refine ⟨1394099463476258131826449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7435197138540043369741061 1394099463476258131826449)
                    ·
                      rfl

theorem cell23_8144997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_8144997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8144997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8144997 prefixEnd_8144997 := by exact prefixLift 8144997
  have htrace : WordTrace (prefixWord ++ tailWord_8144997) baseStart_8144997 baseEnd_8144997 := by
    simpa [prefixWord, tailWord_8144997, baseEnd_8144997] using wordTrace_append hprefix tailTrace_8144997
  have hstable : (prefixWord ++ tailWord_8144997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144997).length < 2 ^ (prefixWord ++ tailWord_8144997).sum := by decide
  have hdescent : baseEnd_8144997 < baseStart_8144997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145010 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 6]
def baseStart_8145010 : Nat := 118140960795 + 8145010 * 2 ^ 59
def prefixEnd_8145010 : Nat := 4983230072969 + 3 ^ 40 * 8145010 * 2
def baseEnd_8145010 : Nat := 464700562853031427179643

theorem tailTrace_8145010 : CollatzResearch.WordTrace tailWord_8145010 prefixEnd_8145010 464700562853031427179643 := by
  unfold tailWord_8145010
  simp only [CollatzResearch.WordTrace]
  refine ⟨74268230055506825451352121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198048613481351534536938989 74268230055506825451352121)
  ·
    refine ⟨55701172541630119088514091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74268230055506825451352121 55701172541630119088514091)
    ·
      refine ⟨83551758812445178632771137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55701172541630119088514091 83551758812445178632771137)
      ·
        refine ⟨62663819109333883974578353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83551758812445178632771137 62663819109333883974578353)
        ·
          refine ⟨46997864332000412980933765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62663819109333883974578353 46997864332000412980933765)
          ·
            refine ⟨8812099562250077433925081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46997864332000412980933765 8812099562250077433925081)
            ·
              refine ⟨6609074671687558075443811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8812099562250077433925081 6609074671687558075443811)
              ·
                refine ⟨9913612007531337113165717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6609074671687558075443811 9913612007531337113165717)
                ·
                  refine ⟨464700562853031427179643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9913612007531337113165717 464700562853031427179643)
                  ·
                    rfl

theorem cell23_8145010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_8145010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145010 prefixEnd_8145010 := by exact prefixLift 8145010
  have htrace : WordTrace (prefixWord ++ tailWord_8145010) baseStart_8145010 baseEnd_8145010 := by
    simpa [prefixWord, tailWord_8145010, baseEnd_8145010] using wordTrace_append hprefix tailTrace_8145010
  have hstable : (prefixWord ++ tailWord_8145010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145010).length < 2 ^ (prefixWord ++ tailWord_8145010).sum := by decide
  have hdescent : baseEnd_8145010 < baseStart_8145010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145093 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_8145093 : Nat := 118140960795 + 8145093 * 2 ^ 59
def prefixEnd_8145093 : Nat := 4983230072969 + 3 ^ 40 * 8145093 * 2
def baseEnd_8145093 : Nat := 4182347684571606019878905

theorem tailTrace_8145093 : CollatzResearch.WordTrace tailWord_8145093 prefixEnd_8145093 4182347684571606019878905 := by
  unfold tailWord_8145093
  simp only [CollatzResearch.WordTrace]
  refine ⟨297075947480726606980679933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198050631653817737987119955 297075947480726606980679933)
  ·
    refine ⟨111403480305272477617754975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297075947480726606980679933 111403480305272477617754975)
    ·
      refine ⟨167105220457908716426632463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111403480305272477617754975 167105220457908716426632463)
      ·
        refine ⟨250657830686863074639948695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167105220457908716426632463 250657830686863074639948695)
        ·
          refine ⟨375986746030294611959923043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250657830686863074639948695 375986746030294611959923043)
          ·
            refine ⟨563980119045441917939884565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375986746030294611959923043 563980119045441917939884565)
            ·
              refine ⟨26436568080255089903432089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 563980119045441917939884565 26436568080255089903432089)
              ·
                refine ⟨19827426060191317427574067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26436568080255089903432089 19827426060191317427574067)
                ·
                  refine ⟨29741139090286976141361101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19827426060191317427574067 29741139090286976141361101)
                  ·
                    refine ⟨11152927158857616053010413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29741139090286976141361101 11152927158857616053010413)
                    ·
                      refine ⟨4182347684571606019878905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11152927158857616053010413 4182347684571606019878905)
                      ·
                        rfl

theorem cell23_8145093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_8145093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145093 prefixEnd_8145093 := by exact prefixLift 8145093
  have htrace : WordTrace (prefixWord ++ tailWord_8145093) baseStart_8145093 baseEnd_8145093 := by
    simpa [prefixWord, tailWord_8145093, baseEnd_8145093] using wordTrace_append hprefix tailTrace_8145093
  have hstable : (prefixWord ++ tailWord_8145093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145093).length < 2 ^ (prefixWord ++ tailWord_8145093).sum := by decide
  have hdescent : baseEnd_8145093 < baseStart_8145093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145127 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_8145127 : Nat := 118140960795 + 8145127 * 2 ^ 59
def prefixEnd_8145127 : Nat := 4983230072969 + 3 ^ 40 * 8145127 * 2
def baseEnd_8145127 : Nat := 4182365142913858886853749

theorem tailTrace_8145127 : CollatzResearch.WordTrace tailWord_8145127 prefixEnd_8145127 4182365142913858886853749 := by
  unfold tailWord_8145127
  simp only [CollatzResearch.WordTrace]
  refine ⟨297077187562603430787417635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198051458375068953858278423 297077187562603430787417635)
  ·
    refine ⟨445615781343905146181126453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297077187562603430787417635 445615781343905146181126453)
    ·
      refine ⟨41776479500991107454480605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 445615781343905146181126453 41776479500991107454480605)
      ·
        refine ⟨15666179812871665295430227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41776479500991107454480605 15666179812871665295430227)
        ·
          refine ⟨23499269719307497943145341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15666179812871665295430227 23499269719307497943145341)
          ·
            refine ⟨8812226144740311728679503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23499269719307497943145341 8812226144740311728679503)
            ·
              refine ⟨13218339217110467593019255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812226144740311728679503 13218339217110467593019255)
              ·
                refine ⟨19827508825665701389528883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13218339217110467593019255 19827508825665701389528883)
                ·
                  refine ⟨29741263238498552084293325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19827508825665701389528883 29741263238498552084293325)
                  ·
                    refine ⟨11152973714436957031609997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29741263238498552084293325 11152973714436957031609997)
                    ·
                      refine ⟨4182365142913858886853749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11152973714436957031609997 4182365142913858886853749)
                      ·
                        rfl

theorem cell23_8145127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_8145127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145127 prefixEnd_8145127 := by exact prefixLift 8145127
  have htrace : WordTrace (prefixWord ++ tailWord_8145127) baseStart_8145127 baseEnd_8145127 := by
    simpa [prefixWord, tailWord_8145127, baseEnd_8145127] using wordTrace_append hprefix tailTrace_8145127
  have hstable : (prefixWord ++ tailWord_8145127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145127).length < 2 ^ (prefixWord ++ tailWord_8145127).sum := by decide
  have hdescent : baseEnd_8145127 < baseStart_8145127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145136 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_8145136 : Nat := 118140960795 + 8145136 * 2 ^ 59
def prefixEnd_8145136 : Nat := 4983230072969 + 3 ^ 40 * 8145136 * 2
def baseEnd_8145136 : Nat := 4182369764239749351641207

theorem tailTrace_8145136 : CollatzResearch.WordTrace tailWord_8145136 prefixEnd_8145136 4182369764239749351641207 := by
  unfold tailWord_8145136
  simp only [CollatzResearch.WordTrace]
  refine ⟨148538757909785412662247631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198051677213047216882996841 148538757909785412662247631)
  ·
    refine ⟨222808136864678118993371447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148538757909785412662247631 222808136864678118993371447)
    ·
      refine ⟨334212205297017178490057171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222808136864678118993371447 334212205297017178490057171)
      ·
        refine ⟨501318307945525767735085757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334212205297017178490057171 501318307945525767735085757)
        ·
          refine ⟨187994365479572162900657159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501318307945525767735085757 187994365479572162900657159)
          ·
            refine ⟨281991548219358244350985739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187994365479572162900657159 281991548219358244350985739)
            ·
              refine ⟨422987322329037366526478609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281991548219358244350985739 422987322329037366526478609)
              ·
                refine ⟨317240491746778024894858957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422987322329037366526478609 317240491746778024894858957)
                ·
                  refine ⟨118965184405041759335572109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317240491746778024894858957 118965184405041759335572109)
                  ·
                    refine ⟨44611944151890659750839541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118965184405041759335572109 44611944151890659750839541)
                    ·
                      refine ⟨4182369764239749351641207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44611944151890659750839541 4182369764239749351641207)
                      ·
                        rfl

theorem cell23_8145136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_8145136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145136 prefixEnd_8145136 := by exact prefixLift 8145136
  have htrace : WordTrace (prefixWord ++ tailWord_8145136) baseStart_8145136 baseEnd_8145136 := by
    simpa [prefixWord, tailWord_8145136, baseEnd_8145136] using wordTrace_append hprefix tailTrace_8145136
  have hstable : (prefixWord ++ tailWord_8145136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145136).length < 2 ^ (prefixWord ++ tailWord_8145136).sum := by decide
  have hdescent : baseEnd_8145136 < baseStart_8145136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145153 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_8145153 : Nat := 118140960795 + 8145153 * 2 ^ 59
def prefixEnd_8145153 : Nat := 4983230072969 + 3 ^ 40 * 8145153 * 2
def baseEnd_8145153 : Nat := 4182378493410875785128629

theorem tailTrace_8145153 : CollatzResearch.WordTrace tailWord_8145153 prefixEnd_8145153 4182378493410875785128629 := by
  unfold tailWord_8145153
  simp only [CollatzResearch.WordTrace]
  refine ⟨297078135860509237227864113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198052090573672824818576075 297078135860509237227864113)
  ·
    refine ⟨222808601895381927920898085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297078135860509237227864113 222808601895381927920898085)
    ·
      refine ⟨41776612855384111485168391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222808601895381927920898085 41776612855384111485168391)
      ·
        refine ⟨62664919283076167227752587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41776612855384111485168391 62664919283076167227752587)
        ·
          refine ⟨93997378924614250841628881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62664919283076167227752587 93997378924614250841628881)
          ·
            refine ⟨70498034193460688131221661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93997378924614250841628881 70498034193460688131221661)
            ·
              refine ⟨26436762822547758049208123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70498034193460688131221661 26436762822547758049208123)
              ·
                refine ⟨39655144233821637073812185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26436762822547758049208123 39655144233821637073812185)
                ·
                  refine ⟨29741358175366227805359139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39655144233821637073812185 29741358175366227805359139)
                  ·
                    refine ⟨44612037263049341708038709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29741358175366227805359139 44612037263049341708038709)
                    ·
                      refine ⟨4182378493410875785128629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44612037263049341708038709 4182378493410875785128629)
                      ·
                        rfl

theorem cell23_8145153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_8145153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145153 prefixEnd_8145153 := by exact prefixLift 8145153
  have htrace : WordTrace (prefixWord ++ tailWord_8145153) baseStart_8145153 baseEnd_8145153 := by
    simpa [prefixWord, tailWord_8145153, baseEnd_8145153] using wordTrace_append hprefix tailTrace_8145153
  have hstable : (prefixWord ++ tailWord_8145153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145153).length < 2 ^ (prefixWord ++ tailWord_8145153).sum := by decide
  have hdescent : baseEnd_8145153 < baseStart_8145153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145154 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_8145154 : Nat := 118140960795 + 8145154 * 2 ^ 59
def prefixEnd_8145154 : Nat := 4983230072969 + 3 ^ 40 * 8145154 * 2
def baseEnd_8145154 : Nat := 4182379006891530281216125

theorem tailTrace_8145154 : CollatzResearch.WordTrace tailWord_8145154 prefixEnd_8145154 4182379006891530281216125 := by
  unfold tailWord_8145154
  simp only [CollatzResearch.WordTrace]
  refine ⟨74269543083376403599662629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198052114889003742932433677 74269543083376403599662629)
  ·
    refine ⟨13925539328133075674936743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74269543083376403599662629 13925539328133075674936743)
    ·
      refine ⟨20888308992199613512405115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13925539328133075674936743 20888308992199613512405115)
      ·
        refine ⟨31332463488299420268607673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20888308992199613512405115 31332463488299420268607673)
        ·
          refine ⟨23499347616224565201455755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31332463488299420268607673 23499347616224565201455755)
          ·
            refine ⟨35249021424336847802183633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23499347616224565201455755 35249021424336847802183633)
            ·
              refine ⟨26436766068252635851637725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35249021424336847802183633 26436766068252635851637725)
              ·
                refine ⟨9913787275594738444364147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26436766068252635851637725 9913787275594738444364147)
                ·
                  refine ⟨14870680913392107666546221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9913787275594738444364147 14870680913392107666546221)
                  ·
                    refine ⟨5576505342522040374954833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14870680913392107666546221 5576505342522040374954833)
                    ·
                      refine ⟨4182379006891530281216125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576505342522040374954833 4182379006891530281216125)
                      ·
                        rfl

theorem cell23_8145154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_8145154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145154 prefixEnd_8145154 := by exact prefixLift 8145154
  have htrace : WordTrace (prefixWord ++ tailWord_8145154) baseStart_8145154 baseEnd_8145154 := by
    simpa [prefixWord, tailWord_8145154, baseEnd_8145154] using wordTrace_append hprefix tailTrace_8145154
  have hstable : (prefixWord ++ tailWord_8145154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145154).length < 2 ^ (prefixWord ++ tailWord_8145154).sum := by decide
  have hdescent : baseEnd_8145154 < baseStart_8145154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145173 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 7]
def baseStart_8145173 : Nat := 118140960795 + 8145173 * 2 ^ 59
def prefixEnd_8145173 : Nat := 4983230072969 + 3 ^ 40 * 8145173 * 2
def baseEnd_8145173 : Nat := 464709862558218411875393

theorem tailTrace_8145173 : CollatzResearch.WordTrace tailWord_8145173 prefixEnd_8145173 464709862558218411875393 := by
  unfold tailWord_8145173
  simp only [CollatzResearch.WordTrace]
  refine ⟨297078865320436780643592173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198052576880291187095728115 297078865320436780643592173)
  ·
    refine ⟨111404574495163792741347065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297078865320436780643592173 111404574495163792741347065)
    ·
      refine ⟨83553430871372844556010299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111404574495163792741347065 83553430871372844556010299)
      ·
        refine ⟨125330146307059266834015449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83553430871372844556010299 125330146307059266834015449)
        ·
          refine ⟨93997609730294450125511587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125330146307059266834015449 93997609730294450125511587)
          ·
            refine ⟨140996414595441675188267381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93997609730294450125511587 140996414595441675188267381)
            ·
              refine ⟨13218413868322657048900067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140996414595441675188267381 13218413868322657048900067)
              ·
                refine ⟨19827620802483985573350101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13218413868322657048900067 19827620802483985573350101)
                ·
                  refine ⟨464709862558218411875393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19827620802483985573350101 464709862558218411875393)
                  ·
                    rfl

theorem cell23_8145173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_8145173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145173 prefixEnd_8145173 := by exact prefixLift 8145173
  have htrace : WordTrace (prefixWord ++ tailWord_8145173) baseStart_8145173 baseEnd_8145173 := by
    simpa [prefixWord, tailWord_8145173, baseEnd_8145173] using wordTrace_append hprefix tailTrace_8145173
  have hstable : (prefixWord ++ tailWord_8145173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145173).length < 2 ^ (prefixWord ++ tailWord_8145173).sum := by decide
  have hdescent : baseEnd_8145173 < baseStart_8145173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145184 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 2, 2, 2]
def baseStart_8145184 : Nat := 118140960795 + 8145184 * 2 ^ 59
def prefixEnd_8145184 : Nat := 4983230072969 + 3 ^ 40 * 8145184 * 2
def baseEnd_8145184 : Nat := 4182394411311165163840987

theorem tailTrace_8145184 : CollatzResearch.WordTrace tailWord_8145184 prefixEnd_8145184 4182394411311165163840987 := by
  unfold tailWord_8145184
  simp only [CollatzResearch.WordTrace]
  refine ⟨148539633261698464761121303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198052844348931286348161737 148539633261698464761121303)
  ·
    refine ⟨222809449892547697141681955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148539633261698464761121303 222809449892547697141681955)
    ·
      refine ⟨334214174838821545712522933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222809449892547697141681955 334214174838821545712522933)
      ·
        refine ⟨31332578891139519910549025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334214174838821545712522933 31332578891139519910549025)
        ·
          refine ⟨23499434168354639932911769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31332578891139519910549025 23499434168354639932911769)
          ·
            refine ⟨17624575626265979949683827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23499434168354639932911769 17624575626265979949683827)
            ·
              refine ⟨26436863439398969924525741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17624575626265979949683827 26436863439398969924525741)
              ·
                refine ⟨9913823789774613721697153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26436863439398969924525741 9913823789774613721697153)
                ·
                  refine ⟨7435367842330960291272865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9913823789774613721697153 7435367842330960291272865)
                  ·
                    refine ⟨5576525881748220218454649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7435367842330960291272865 5576525881748220218454649)
                    ·
                      refine ⟨4182394411311165163840987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576525881748220218454649 4182394411311165163840987)
                      ·
                        rfl

theorem cell23_8145184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_8145184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145184 prefixEnd_8145184 := by exact prefixLift 8145184
  have htrace : WordTrace (prefixWord ++ tailWord_8145184) baseStart_8145184 baseEnd_8145184 := by
    simpa [prefixWord, tailWord_8145184, baseEnd_8145184] using wordTrace_append hprefix tailTrace_8145184
  have hstable : (prefixWord ++ tailWord_8145184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145184).length < 2 ^ (prefixWord ++ tailWord_8145184).sum := by decide
  have hdescent : baseEnd_8145184 < baseStart_8145184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145303 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_8145303 : Nat := 118140960795 + 8145303 * 2 ^ 59
def prefixEnd_8145303 : Nat := 4983230072969 + 3 ^ 40 * 8145303 * 2
def baseEnd_8145303 : Nat := 4182455515509050198252939

theorem tailTrace_8145303 : CollatzResearch.WordTrace tailWord_8145303 prefixEnd_8145303 4182455515509050198252939 := by
  unfold tailWord_8145303
  simp only [CollatzResearch.WordTrace]
  refine ⟨297083606809965812845824563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198055737873310541897216375 297083606809965812845824563)
  ·
    refine ⟨445625410214948719268736845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297083606809965812845824563 445625410214948719268736845)
    ·
      refine ⟨167109528830605769725776317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445625410214948719268736845 167109528830605769725776317)
      ·
        refine ⟨62666073311477163647166119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167109528830605769725776317 62666073311477163647166119)
        ·
          refine ⟨93999109967215745470749179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62666073311477163647166119 93999109967215745470749179)
          ·
            refine ⟨140998664950823618206123769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93999109967215745470749179 140998664950823618206123769)
            ·
              refine ⟨105748998713117713654592827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140998664950823618206123769 105748998713117713654592827)
              ·
                refine ⟨158623498069676570481889241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105748998713117713654592827 158623498069676570481889241)
                ·
                  refine ⟨118967623552257427861416931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158623498069676570481889241 118967623552257427861416931)
                  ·
                    refine ⟨178451435328386141792125397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118967623552257427861416931 178451435328386141792125397)
                    ·
                      refine ⟨4182455515509050198252939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178451435328386141792125397 4182455515509050198252939)
                      ·
                        rfl

theorem cell23_8145303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_8145303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145303 prefixEnd_8145303 := by exact prefixLift 8145303
  have htrace : WordTrace (prefixWord ++ tailWord_8145303) baseStart_8145303 baseEnd_8145303 := by
    simpa [prefixWord, tailWord_8145303, baseEnd_8145303] using wordTrace_append hprefix tailTrace_8145303
  have hstable : (prefixWord ++ tailWord_8145303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145303).length < 2 ^ (prefixWord ++ tailWord_8145303).sum := by decide
  have hdescent : baseEnd_8145303 < baseStart_8145303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145317 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 2, 3, 2]
def baseStart_8145317 : Nat := 118140960795 + 8145317 * 2 ^ 59
def prefixEnd_8145317 : Nat := 4983230072969 + 3 ^ 40 * 8145317 * 2
def baseEnd_8145317 : Nat := 4182462704238213143477875

theorem tailTrace_8145317 : CollatzResearch.WordTrace tailWord_8145317 prefixEnd_8145317 4182462704238213143477875 := by
  unfold tailWord_8145317
  simp only [CollatzResearch.WordTrace]
  refine ⟨297084117431915093236834205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198056078287943395491222803 297084117431915093236834205)
  ·
    refine ⟨111406544036968159963812827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297084117431915093236834205 111406544036968159963812827)
    ·
      refine ⟨167109816055452239945719241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111406544036968159963812827 167109816055452239945719241)
      ·
        refine ⟨125332362041589179959289431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167109816055452239945719241 125332362041589179959289431)
        ·
          refine ⟨187998543062383769938934147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125332362041589179959289431 187998543062383769938934147)
          ·
            refine ⟨281997814593575654908401221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187998543062383769938934147 281997814593575654908401221)
            ·
              refine ⟨52874590236295435295325229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281997814593575654908401221 52874590236295435295325229)
              ·
                refine ⟨19827971338610788235746961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52874590236295435295325229 19827971338610788235746961)
                ·
                  refine ⟨14870978503958091176810221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19827971338610788235746961 14870978503958091176810221)
                  ·
                    refine ⟨5576616938984284191303833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14870978503958091176810221 5576616938984284191303833)
                    ·
                      refine ⟨4182462704238213143477875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576616938984284191303833 4182462704238213143477875)
                      ·
                        rfl

theorem cell23_8145317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_8145317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145317 prefixEnd_8145317 := by exact prefixLift 8145317
  have htrace : WordTrace (prefixWord ++ tailWord_8145317) baseStart_8145317 baseEnd_8145317 := by
    simpa [prefixWord, tailWord_8145317, baseEnd_8145317] using wordTrace_append hprefix tailTrace_8145317
  have hstable : (prefixWord ++ tailWord_8145317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145317).length < 2 ^ (prefixWord ++ tailWord_8145317).sum := by decide
  have hdescent : baseEnd_8145317 < baseStart_8145317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145353 : List Nat := [1, 2, 1, 1, 2, 1, 5, 10]
def baseStart_8145353 : Nat := 118140960795 + 8145353 * 2 ^ 59
def prefixEnd_8145353 : Nat := 4983230072969 + 3 ^ 40 * 8145353 * 2
def baseEnd_8145353 : Nat := 154906710723769444541767

theorem tailTrace_8145353 : CollatzResearch.WordTrace tailWord_8145353 prefixEnd_8145353 154906710723769444541767 := by
  unfold tailWord_8145353
  simp only [CollatzResearch.WordTrace]
  refine ⟨297085430459784671385144713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198056953639856447590096475 297085430459784671385144713)
  ·
    refine ⟨222814072844838503538858535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297085430459784671385144713 222814072844838503538858535)
    ·
      refine ⟨334221109267257755308287803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222814072844838503538858535 334221109267257755308287803)
      ·
        refine ⟨501331663900886632962431705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334221109267257755308287803 501331663900886632962431705)
        ·
          refine ⟨375998747925664974721823779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501331663900886632962431705 375998747925664974721823779)
          ·
            refine ⟨563998121888497462082735669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375998747925664974721823779 563998121888497462082735669)
            ·
              refine ⟨52874823927046637070256469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 563998121888497462082735669 52874823927046637070256469)
              ·
                refine ⟨154906710723769444541767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52874823927046637070256469 154906710723769444541767)
                ·
                  rfl

theorem cell23_8145353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 10].length) (baseStart_8145353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145353 prefixEnd_8145353 := by exact prefixLift 8145353
  have htrace : WordTrace (prefixWord ++ tailWord_8145353) baseStart_8145353 baseEnd_8145353 := by
    simpa [prefixWord, tailWord_8145353, baseEnd_8145353] using wordTrace_append hprefix tailTrace_8145353
  have hstable : (prefixWord ++ tailWord_8145353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145353).length < 2 ^ (prefixWord ++ tailWord_8145353).sum := by decide
  have hdescent : baseEnd_8145353 < baseStart_8145353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145364 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_8145364 : Nat := 118140960795 + 8145364 * 2 ^ 59
def prefixEnd_8145364 : Nat := 4983230072969 + 3 ^ 40 * 8145364 * 2
def baseEnd_8145364 : Nat := 4182486837828974459590159

theorem tailTrace_8145364 : CollatzResearch.WordTrace tailWord_8145364 prefixEnd_8145364 4182486837828974459590159 := by
  unfold tailWord_8145364
  simp only [CollatzResearch.WordTrace]
  refine ⟨148542915831372410131897573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198057221108496546842530097 148542915831372410131897573)
  ·
    refine ⟨27851796718382326899730795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148542915831372410131897573 27851796718382326899730795)
    ·
      refine ⟨41777695077573490349596193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27851796718382326899730795 41777695077573490349596193)
      ·
        refine ⟨31333271308180117762197145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41777695077573490349596193 31333271308180117762197145)
        ·
          refine ⟨23499953481135088321647859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31333271308180117762197145 23499953481135088321647859)
          ·
            refine ⟨35249930221702632482471789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23499953481135088321647859 35249930221702632482471789)
            ·
              refine ⟨13218723833138487180926921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35249930221702632482471789 13218723833138487180926921)
              ·
                refine ⟨9914042874853865385695191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13218723833138487180926921 9914042874853865385695191)
                ·
                  refine ⟨14871064312280798078542787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9914042874853865385695191 14871064312280798078542787)
                  ·
                    refine ⟨22306596468421197117814181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14871064312280798078542787 22306596468421197117814181)
                    ·
                      refine ⟨4182486837828974459590159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22306596468421197117814181 4182486837828974459590159)
                      ·
                        rfl

theorem cell23_8145364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_8145364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145364 prefixEnd_8145364 := by exact prefixLift 8145364
  have htrace : WordTrace (prefixWord ++ tailWord_8145364) baseStart_8145364 baseEnd_8145364 := by
    simpa [prefixWord, tailWord_8145364, baseEnd_8145364] using wordTrace_append hprefix tailTrace_8145364
  have hstable : (prefixWord ++ tailWord_8145364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145364).length < 2 ^ (prefixWord ++ tailWord_8145364).sum := by decide
  have hdescent : baseEnd_8145364 < baseStart_8145364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145378 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_8145378 : Nat := 118140960795 + 8145378 * 2 ^ 59
def prefixEnd_8145378 : Nat := 4983230072969 + 3 ^ 40 * 8145378 * 2
def baseEnd_8145378 : Nat := 1394164675519379134938365

theorem tailTrace_8145378 : CollatzResearch.WordTrace tailWord_8145378 prefixEnd_8145378 1394164675519379134938365 := by
  unfold tailWord_8145378
  simp only [CollatzResearch.WordTrace]
  refine ⟨74271585571173525163701197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198057561523129400436536525 74271585571173525163701197)
  ·
    refine ⟨27851844589190071936387949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74271585571173525163701197 27851844589190071936387949)
    ·
      refine ⟨10444441720946276976145481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27851844589190071936387949 10444441720946276976145481)
      ·
        refine ⟨7833331290709707732109111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10444441720946276976145481 7833331290709707732109111)
        ·
          refine ⟨11749996936064561598163667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833331290709707732109111 11749996936064561598163667)
          ·
            refine ⟨17624995404096842397245501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11749996936064561598163667 17624995404096842397245501)
            ·
              refine ⟨6609373276536315898967063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17624995404096842397245501 6609373276536315898967063)
              ·
                refine ⟨9914059914804473848450595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6609373276536315898967063 9914059914804473848450595)
                ·
                  refine ⟨14871089872206710772675893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9914059914804473848450595 14871089872206710772675893)
                  ·
                    refine ⟨1394164675519379134938365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14871089872206710772675893 1394164675519379134938365)
                    ·
                      rfl

theorem cell23_8145378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_8145378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145378 prefixEnd_8145378 := by exact prefixLift 8145378
  have htrace : WordTrace (prefixWord ++ tailWord_8145378) baseStart_8145378 baseEnd_8145378 := by
    simpa [prefixWord, tailWord_8145378, baseEnd_8145378] using wordTrace_append hprefix tailTrace_8145378
  have hstable : (prefixWord ++ tailWord_8145378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145378).length < 2 ^ (prefixWord ++ tailWord_8145378).sum := by decide
  have hdescent : baseEnd_8145378 < baseStart_8145378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145381 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 1, 1, 4]
def baseStart_8145381 : Nat := 118140960795 + 8145381 * 2 ^ 59
def prefixEnd_8145381 : Nat := 4983230072969 + 3 ^ 40 * 8145381 * 2
def baseEnd_8145381 : Nat := 4182495567000100893077581

theorem tailTrace_8145381 : CollatzResearch.WordTrace tailWord_8145381 prefixEnd_8145381 4182495567000100893077581 := by
  unfold tailWord_8145381
  simp only [CollatzResearch.WordTrace]
  refine ⟨297086451703683232167163997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198057634469122154778109331 297086451703683232167163997)
  ·
    refine ⟨111407419388881212062686499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297086451703683232167163997 111407419388881212062686499)
    ·
      refine ⟨167111129083321818094029749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111407419388881212062686499 167111129083321818094029749)
      ·
        refine ⟨15666668351561420446315289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167111129083321818094029749 15666668351561420446315289)
        ·
          refine ⟨11750001263671065334736467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15666668351561420446315289 11750001263671065334736467)
          ·
            refine ⟨17625001895506598002104701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750001263671065334736467 17625001895506598002104701)
            ·
              refine ⟨6609375710814974250789263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17625001895506598002104701 6609375710814974250789263)
              ·
                refine ⟨9914063566222461376183895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6609375710814974250789263 9914063566222461376183895)
                ·
                  refine ⟨14871095349333692064275843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9914063566222461376183895 14871095349333692064275843)
                  ·
                    refine ⟨22306643024000538096413765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14871095349333692064275843 22306643024000538096413765)
                    ·
                      refine ⟨4182495567000100893077581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22306643024000538096413765 4182495567000100893077581)
                      ·
                        rfl

theorem cell23_8145381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_8145381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145381 prefixEnd_8145381 := by exact prefixLift 8145381
  have htrace : WordTrace (prefixWord ++ tailWord_8145381) baseStart_8145381 baseEnd_8145381 := by
    simpa [prefixWord, tailWord_8145381, baseEnd_8145381] using wordTrace_append hprefix tailTrace_8145381
  have hstable : (prefixWord ++ tailWord_8145381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145381).length < 2 ^ (prefixWord ++ tailWord_8145381).sum := by decide
  have hdescent : baseEnd_8145381 < baseStart_8145381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145398 : List Nat := [5, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_8145398 : Nat := 118140960795 + 8145398 * 2 ^ 59
def prefixEnd_8145398 : Nat := 4983230072969 + 3 ^ 40 * 8145398 * 2
def baseEnd_8145398 : Nat := 4182504296171227326565003

theorem tailTrace_8145398 : CollatzResearch.WordTrace tailWord_8145398 prefixEnd_8145398 4182504296171227326565003 := by
  unfold tailWord_8145398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18567941984038852754408303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198058047829747762713688565 18567941984038852754408303)
  ·
    refine ⟨27851912976058279131612455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18567941984038852754408303 27851912976058279131612455)
    ·
      refine ⟨41777869464087418697418683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27851912976058279131612455 41777869464087418697418683)
      ·
        refine ⟨62666804196131128046128025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41777869464087418697418683 62666804196131128046128025)
        ·
          refine ⟨47000103147098346034596019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62666804196131128046128025 47000103147098346034596019)
          ·
            refine ⟨70500154720647519051894029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47000103147098346034596019 70500154720647519051894029)
            ·
              refine ⟨26437558020242819644460261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70500154720647519051894029 26437558020242819644460261)
              ·
                refine ⟨4957042128795528683336299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26437558020242819644460261 4957042128795528683336299)
                ·
                  refine ⟨7435563193193293025004449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957042128795528683336299 7435563193193293025004449)
                  ·
                    refine ⟨5576672394894969768753337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7435563193193293025004449 5576672394894969768753337)
                    ·
                      refine ⟨4182504296171227326565003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576672394894969768753337 4182504296171227326565003)
                      ·
                        rfl

theorem cell23_8145398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_8145398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145398 prefixEnd_8145398 := by exact prefixLift 8145398
  have htrace : WordTrace (prefixWord ++ tailWord_8145398) baseStart_8145398 baseEnd_8145398 := by
    simpa [prefixWord, tailWord_8145398, baseEnd_8145398] using wordTrace_append hprefix tailTrace_8145398
  have hstable : (prefixWord ++ tailWord_8145398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145398).length < 2 ^ (prefixWord ++ tailWord_8145398).sum := by decide
  have hdescent : baseEnd_8145398 < baseStart_8145398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145407 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 5, 3, 2]
def baseStart_8145407 : Nat := 118140960795 + 8145407 * 2 ^ 59
def prefixEnd_8145407 : Nat := 4983230072969 + 3 ^ 40 * 8145407 * 2
def baseEnd_8145407 : Nat := 4182508917497117791352461

theorem tailTrace_8145407 : CollatzResearch.WordTrace tailWord_8145407 prefixEnd_8145407 4182508917497117791352461 := by
  unfold tailWord_8145407
  simp only [CollatzResearch.WordTrace]
  refine ⟨297087400001589038607610475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198058266667726025738406983 297087400001589038607610475)
  ·
    refine ⟨445631100002383557911415713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297087400001589038607610475 445631100002383557911415713)
    ·
      refine ⟨334223325001787668433561785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445631100002383557911415713 334223325001787668433561785)
      ·
        refine ⟨250667493751340751325171339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334223325001787668433561785 250667493751340751325171339)
        ·
          refine ⟨376001240627011126987757009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250667493751340751325171339 376001240627011126987757009)
          ·
            refine ⟨282000930470258345240817757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376001240627011126987757009 282000930470258345240817757)
            ·
              refine ⟨105750348926346879465306659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282000930470258345240817757 105750348926346879465306659)
              ·
                refine ⟨158625523389520319197959989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105750348926346879465306659 158625523389520319197959989)
                ·
                  refine ⟨14871142817767529924808749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158625523389520319197959989 14871142817767529924808749)
                  ·
                    refine ⟨5576678556662823721803281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14871142817767529924808749 5576678556662823721803281)
                    ·
                      refine ⟨4182508917497117791352461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576678556662823721803281 4182508917497117791352461)
                      ·
                        rfl

theorem cell23_8145407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_8145407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145407 prefixEnd_8145407 := by exact prefixLift 8145407
  have htrace : WordTrace (prefixWord ++ tailWord_8145407) baseStart_8145407 baseEnd_8145407 := by
    simpa [prefixWord, tailWord_8145407, baseEnd_8145407] using wordTrace_append hprefix tailTrace_8145407
  have hstable : (prefixWord ++ tailWord_8145407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145407).length < 2 ^ (prefixWord ++ tailWord_8145407).sum := by decide
  have hdescent : baseEnd_8145407 < baseStart_8145407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145421 : List Nat := [1, 7, 1, 1, 1, 2, 3, 7]
def baseStart_8145421 : Nat := 118140960795 + 8145421 * 2 ^ 59
def prefixEnd_8145421 : Nat := 4983230072969 + 3 ^ 40 * 8145421 * 2
def baseEnd_8145421 : Nat := 154908003934306693947311

theorem tailTrace_8145421 : CollatzResearch.WordTrace tailWord_8145421 prefixEnd_8145421 154908003934306693947311 := by
  unfold tailWord_8145421
  simp only [CollatzResearch.WordTrace]
  refine ⟨297087910623538318998620117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198058607082358879332413411 297087910623538318998620117)
  ·
    refine ⟨6962997905239179351530159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 297087910623538318998620117 6962997905239179351530159)
    ·
      refine ⟨10444496857858769027295239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6962997905239179351530159 10444496857858769027295239)
      ·
        refine ⟨15666745286788153540942859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10444496857858769027295239 15666745286788153540942859)
        ·
          refine ⟨23500117930182230311414289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15666745286788153540942859 23500117930182230311414289)
          ·
            refine ⟨17625088447636672733560717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23500117930182230311414289 17625088447636672733560717)
            ·
              refine ⟨6609408167863752275085269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17625088447636672733560717 6609408167863752275085269)
              ·
                refine ⟨154908003934306693947311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6609408167863752275085269 154908003934306693947311)
                ·
                  rfl

theorem cell23_8145421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 7].length) (baseStart_8145421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145421 prefixEnd_8145421 := by exact prefixLift 8145421
  have htrace : WordTrace (prefixWord ++ tailWord_8145421) baseStart_8145421 baseEnd_8145421 := by
    simpa [prefixWord, tailWord_8145421, baseEnd_8145421] using wordTrace_append hprefix tailTrace_8145421
  have hstable : (prefixWord ++ tailWord_8145421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145421).length < 2 ^ (prefixWord ++ tailWord_8145421).sum := by decide
  have hdescent : baseEnd_8145421 < baseStart_8145421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145448 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_8145448 : Nat := 118140960795 + 8145448 * 2 ^ 59
def prefixEnd_8145448 : Nat := 4983230072969 + 3 ^ 40 * 8145448 * 2
def baseEnd_8145448 : Nat := 4182529970203952130939773

theorem tailTrace_8145448 : CollatzResearch.WordTrace tailWord_8145448 prefixEnd_8145448 4182529970203952130939773 := by
  unfold tailWord_8145448
  simp only [CollatzResearch.WordTrace]
  refine ⟨148544447697220251304926499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198059263596293668406568665 148544447697220251304926499)
  ·
    refine ⟨222816671545830376957389749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148544447697220251304926499 222816671545830376957389749)
    ·
      refine ⟨20889062957421597839755289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222816671545830376957389749 20889062957421597839755289)
      ·
        refine ⟨15666797218066198379816467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20889062957421597839755289 15666797218066198379816467)
        ·
          refine ⟨23500195827099297569724701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15666797218066198379816467 23500195827099297569724701)
          ·
            refine ⟨8812573435162236588646763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23500195827099297569724701 8812573435162236588646763)
            ·
              refine ⟨13218860152743354882970145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812573435162236588646763 13218860152743354882970145)
              ·
                refine ⟨9914145114557516162227609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13218860152743354882970145 9914145114557516162227609)
                ·
                  refine ⟨7435608835918137121670707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9914145114557516162227609 7435608835918137121670707)
                  ·
                    refine ⟨11153413253877205682506061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7435608835918137121670707 11153413253877205682506061)
                    ·
                      refine ⟨4182529970203952130939773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11153413253877205682506061 4182529970203952130939773)
                      ·
                        rfl

theorem cell23_8145448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_8145448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145448 prefixEnd_8145448 := by exact prefixLift 8145448
  have htrace : WordTrace (prefixWord ++ tailWord_8145448) baseStart_8145448 baseEnd_8145448 := by
    simpa [prefixWord, tailWord_8145448, baseEnd_8145448] using wordTrace_append hprefix tailTrace_8145448
  have hstable : (prefixWord ++ tailWord_8145448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145448).length < 2 ^ (prefixWord ++ tailWord_8145448).sum := by decide
  have hdescent : baseEnd_8145448 < baseStart_8145448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145497 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 3, 7, 2]
def baseStart_8145497 : Nat := 118140960795 + 8145497 * 2 ^ 59
def prefixEnd_8145497 : Nat := 4983230072969 + 3 ^ 40 * 8145497 * 2
def baseEnd_8145497 : Nat := 4182555130756022439227047

theorem tailTrace_8145497 : CollatzResearch.WordTrace tailWord_8145497 prefixEnd_8145497 4182555130756022439227047 := by
  unfold tailWord_8145497
  simp only [CollatzResearch.WordTrace]
  refine ⟨297090682571262983978386745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198060455047508655985591163 297090682571262983978386745)
  ·
    refine ⟨222818011928447237983790059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297090682571262983978386745 222818011928447237983790059)
    ·
      refine ⟨334227017892670856975685089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222818011928447237983790059 334227017892670856975685089)
      ·
        refine ⟨250670263419503142731763817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334227017892670856975685089 250670263419503142731763817)
        ·
          refine ⟨188002697564627357048822863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250670263419503142731763817 188002697564627357048822863)
          ·
            refine ⟨282004046346941035573234295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188002697564627357048822863 282004046346941035573234295)
            ·
              refine ⟨423006069520411553359851443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282004046346941035573234295 423006069520411553359851443)
              ·
                refine ⟨634509104280617330039777165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423006069520411553359851443 634509104280617330039777165)
                ·
                  refine ⟨237940914105231498764916437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634509104280617330039777165 237940914105231498764916437)
                  ·
                    refine ⟨5576740174341363252302729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 237940914105231498764916437 5576740174341363252302729)
                    ·
                      refine ⟨4182555130756022439227047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576740174341363252302729 4182555130756022439227047)
                      ·
                        rfl

theorem cell23_8145497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_8145497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145497 prefixEnd_8145497 := by exact prefixLift 8145497
  have htrace : WordTrace (prefixWord ++ tailWord_8145497) baseStart_8145497 baseEnd_8145497 := by
    simpa [prefixWord, tailWord_8145497, baseEnd_8145497] using wordTrace_append hprefix tailTrace_8145497
  have hstable : (prefixWord ++ tailWord_8145497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145497).length < 2 ^ (prefixWord ++ tailWord_8145497).sum := by decide
  have hdescent : baseEnd_8145497 < baseStart_8145497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145507 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 2, 5]
def baseStart_8145507 : Nat := 118140960795 + 8145507 * 2 ^ 59
def prefixEnd_8145507 : Nat := 4983230072969 + 3 ^ 40 * 8145507 * 2
def baseEnd_8145507 : Nat := 1394186755187522466700667

theorem tailTrace_8145507 : CollatzResearch.WordTrace tailWord_8145507 prefixEnd_8145507 1394186755187522466700667 := by
  unfold tailWord_8145507
  simp only [CollatzResearch.WordTrace]
  refine ⟨297091047301226755686250775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198060698200817837124167183 297091047301226755686250775)
  ·
    refine ⟨445636570951840133529376163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297091047301226755686250775 445636570951840133529376163)
    ·
      refine ⟨668454856427760200294064245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445636570951840133529376163 668454856427760200294064245)
      ·
        refine ⟨62667642790102518777568523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 668454856427760200294064245 62667642790102518777568523)
        ·
          refine ⟨94001464185153778166352785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62667642790102518777568523 94001464185153778166352785)
          ·
            refine ⟨70501098138865333624764589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94001464185153778166352785 70501098138865333624764589)
            ·
              refine ⟨26437911802074500109286721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70501098138865333624764589 26437911802074500109286721)
              ·
                refine ⟨19828433851555875081965041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26437911802074500109286721 19828433851555875081965041)
                ·
                  refine ⟨14871325388666906311473781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19828433851555875081965041 14871325388666906311473781)
                  ·
                    refine ⟨1394186755187522466700667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14871325388666906311473781 1394186755187522466700667)
                    ·
                      rfl

theorem cell23_8145507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 5].length) (baseStart_8145507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145507 prefixEnd_8145507 := by exact prefixLift 8145507
  have htrace : WordTrace (prefixWord ++ tailWord_8145507) baseStart_8145507 baseEnd_8145507 := by
    simpa [prefixWord, tailWord_8145507, baseEnd_8145507] using wordTrace_append hprefix tailTrace_8145507
  have hstable : (prefixWord ++ tailWord_8145507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145507).length < 2 ^ (prefixWord ++ tailWord_8145507).sum := by decide
  have hdescent : baseEnd_8145507 < baseStart_8145507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145514 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_8145514 : Nat := 118140960795 + 8145514 * 2 ^ 59
def prefixEnd_8145514 : Nat := 4983230072969 + 3 ^ 40 * 8145514 * 2
def baseEnd_8145514 : Nat := 4182563859927148872714469

theorem tailTrace_8145514 : CollatzResearch.WordTrace tailWord_8145514 prefixEnd_8145514 4182563859927148872714469 := by
  unfold tailWord_8145514
  simp only [CollatzResearch.WordTrace]
  refine ⟨74272825653050348970438899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198060868408134263921170397 74272825653050348970438899)
  ·
    refine ⟨111409238479575523455658349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74272825653050348970438899 111409238479575523455658349)
    ·
      refine ⟨41778464429840821295871881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111409238479575523455658349 41778464429840821295871881)
      ·
        refine ⟨31333848322380615971903911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41778464429840821295871881 31333848322380615971903911)
        ·
          refine ⟨47000772483570923957855867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31333848322380615971903911 47000772483570923957855867)
          ·
            refine ⟨70501158725356385936783801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47000772483570923957855867 70501158725356385936783801)
            ·
              refine ⟨52875869044017289452587851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70501158725356385936783801 52875869044017289452587851)
              ·
                refine ⟨79313803566025934178881777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52875869044017289452587851 79313803566025934178881777)
                ·
                  refine ⟨59485352674519450634161333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79313803566025934178881777 59485352674519450634161333)
                  ·
                    refine ⟨5576751813236198496952625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59485352674519450634161333 5576751813236198496952625)
                    ·
                      refine ⟨4182563859927148872714469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576751813236198496952625 4182563859927148872714469)
                      ·
                        rfl

theorem cell23_8145514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_8145514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145514 prefixEnd_8145514 := by exact prefixLift 8145514
  have htrace : WordTrace (prefixWord ++ tailWord_8145514) baseStart_8145514 baseEnd_8145514 := by
    simpa [prefixWord, tailWord_8145514, baseEnd_8145514] using wordTrace_append hprefix tailTrace_8145514
  have hstable : (prefixWord ++ tailWord_8145514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145514).length < 2 ^ (prefixWord ++ tailWord_8145514).sum := by decide
  have hdescent : baseEnd_8145514 < baseStart_8145514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145517 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_8145517 : Nat := 118140960795 + 8145517 * 2 ^ 59
def prefixEnd_8145517 : Nat := 4983230072969 + 3 ^ 40 * 8145517 * 2
def baseEnd_8145517 : Nat := 4182565400369112360976955

theorem tailTrace_8145517 : CollatzResearch.WordTrace tailWord_8145517 prefixEnd_8145517 4182565400369112360976955 := by
  unfold tailWord_8145517
  simp only [CollatzResearch.WordTrace]
  refine ⟨297091412031190527394114805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198060941354127018262743203 297091412031190527394114805)
  ·
    refine ⟨27852319877924111943198263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297091412031190527394114805 27852319877924111943198263)
    ·
      refine ⟨41778479816886167914797395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27852319877924111943198263 41778479816886167914797395)
      ·
        refine ⟨62667719725329251872196093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41778479816886167914797395 62667719725329251872196093)
        ·
          refine ⟨23500394896998469452073535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62667719725329251872196093 23500394896998469452073535)
          ·
            refine ⟨35250592345497704178110303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23500394896998469452073535 35250592345497704178110303)
            ·
              refine ⟨52875888518246556267165455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35250592345497704178110303 52875888518246556267165455)
              ·
                refine ⟨79313832777369834400748183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52875888518246556267165455 79313832777369834400748183)
                ·
                  refine ⟨118970749166054751601122275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79313832777369834400748183 118970749166054751601122275)
                  ·
                    refine ⟨178456123749082127401683413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118970749166054751601122275 178456123749082127401683413)
                    ·
                      refine ⟨4182565400369112360976955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178456123749082127401683413 4182565400369112360976955)
                      ·
                        rfl

theorem cell23_8145517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_8145517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145517 prefixEnd_8145517 := by exact prefixLift 8145517
  have htrace : WordTrace (prefixWord ++ tailWord_8145517) baseStart_8145517 baseEnd_8145517 := by
    simpa [prefixWord, tailWord_8145517, baseEnd_8145517] using wordTrace_append hprefix tailTrace_8145517
  have hstable : (prefixWord ++ tailWord_8145517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145517).length < 2 ^ (prefixWord ++ tailWord_8145517).sum := by decide
  have hdescent : baseEnd_8145517 < baseStart_8145517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145522 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_8145522 : Nat := 118140960795 + 8145522 * 2 ^ 59
def prefixEnd_8145522 : Nat := 4983230072969 + 3 ^ 40 * 8145522 * 2
def baseEnd_8145522 : Nat := 4182567967772384841414433

theorem tailTrace_8145522 : CollatzResearch.WordTrace tailWord_8145522 prefixEnd_8145522 4182567967772384841414433 := by
  unfold tailWord_8145522
  simp only [CollatzResearch.WordTrace]
  refine ⟨74272898599043103312011705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198061062930781608832031213 74272898599043103312011705)
  ·
    refine ⟨55704673949282327484008779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74272898599043103312011705 55704673949282327484008779)
    ·
      refine ⟨83557010923923491226013169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55704673949282327484008779 83557010923923491226013169)
      ·
        refine ⟨62667758192942618419509877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83557010923923491226013169 62667758192942618419509877)
        ·
          refine ⟨5875102330588370476829051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62667758192942618419509877 5875102330588370476829051)
          ·
            refine ⟨8812653495882555715243577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875102330588370476829051 8812653495882555715243577)
            ·
              refine ⟨6609490121911916786432683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8812653495882555715243577 6609490121911916786432683)
              ·
                refine ⟨9914235182867875179649025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6609490121911916786432683 9914235182867875179649025)
                ·
                  refine ⟨7435676387150906384736769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9914235182867875179649025 7435676387150906384736769)
                  ·
                    refine ⟨5576757290363179788552577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7435676387150906384736769 5576757290363179788552577)
                    ·
                      refine ⟨4182567967772384841414433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5576757290363179788552577 4182567967772384841414433)
                      ·
                        rfl

theorem cell23_8145522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_8145522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145522 prefixEnd_8145522 := by exact prefixLift 8145522
  have htrace : WordTrace (prefixWord ++ tailWord_8145522) baseStart_8145522 baseEnd_8145522 := by
    simpa [prefixWord, tailWord_8145522, baseEnd_8145522] using wordTrace_append hprefix tailTrace_8145522
  have hstable : (prefixWord ++ tailWord_8145522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145522).length < 2 ^ (prefixWord ++ tailWord_8145522).sum := by decide
  have hdescent : baseEnd_8145522 < baseStart_8145522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145530 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_8145530 : Nat := 118140960795 + 8145530 * 2 ^ 59
def prefixEnd_8145530 : Nat := 4983230072969 + 3 ^ 40 * 8145530 * 2
def baseEnd_8145530 : Nat := 4182572075617620810114395

theorem tailTrace_8145530 : CollatzResearch.WordTrace tailWord_8145530 prefixEnd_8145530 4182572075617620810114395 := by
  unfold tailWord_8145530
  simp only [CollatzResearch.WordTrace]
  refine ⟨74272971545035857653584511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198061257453428953742892029 74272971545035857653584511)
  ·
    refine ⟨111409457317553786480376767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74272971545035857653584511 111409457317553786480376767)
    ·
      refine ⟨167114185976330679720565151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111409457317553786480376767 167114185976330679720565151)
      ·
        refine ⟨250671278964496019580847727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167114185976330679720565151 250671278964496019580847727)
        ·
          refine ⟨376006918446744029371271591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250671278964496019580847727 376006918446744029371271591)
          ·
            refine ⟨564010377670116044056907387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376006918446744029371271591 564010377670116044056907387)
            ·
              refine ⟨846015566505174066085361081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564010377670116044056907387 846015566505174066085361081)
              ·
                refine ⟨634511674878880549564020811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846015566505174066085361081 634511674878880549564020811)
                ·
                  refine ⟨951767512318320824346031217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634511674878880549564020811 951767512318320824346031217)
                  ·
                    refine ⟨713825634238740618259523413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 951767512318320824346031217 713825634238740618259523413)
                    ·
                      refine ⟨4182572075617620810114395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 713825634238740618259523413 4182572075617620810114395)
                      ·
                        rfl

theorem cell23_8145530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_8145530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145530 prefixEnd_8145530 := by exact prefixLift 8145530
  have htrace : WordTrace (prefixWord ++ tailWord_8145530) baseStart_8145530 baseEnd_8145530 := by
    simpa [prefixWord, tailWord_8145530, baseEnd_8145530] using wordTrace_append hprefix tailTrace_8145530
  have hstable : (prefixWord ++ tailWord_8145530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145530).length < 2 ^ (prefixWord ++ tailWord_8145530).sum := by decide
  have hdescent : baseEnd_8145530 < baseStart_8145530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145618 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 6]
def baseStart_8145618 : Nat := 118140960795 + 8145618 * 2 ^ 59
def prefixEnd_8145618 : Nat := 4983230072969 + 3 ^ 40 * 8145618 * 2
def baseEnd_8145618 : Nat := 464735251323912940645999

theorem tailTrace_8145618 : CollatzResearch.WordTrace tailWord_8145618 prefixEnd_8145618 464735251323912940645999 := by
  unfold tailWord_8145618
  simp only [CollatzResearch.WordTrace]
  refine ⟨74273773950956155410885377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198063397202549747762361005 74273773950956155410885377)
  ·
    refine ⟨55705330463217116558164033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74273773950956155410885377 55705330463217116558164033)
    ·
      refine ⟨41778997847412837418623025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55705330463217116558164033 41778997847412837418623025)
      ·
        refine ⟨31334248385559628063967269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41778997847412837418623025 31334248385559628063967269)
        ·
          refine ⟨5875171572292430261993863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31334248385559628063967269 5875171572292430261993863)
          ·
            refine ⟨8812757358438645392990795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875171572292430261993863 8812757358438645392990795)
            ·
              refine ⟨13219136037657968089486193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812757358438645392990795 13219136037657968089486193)
              ·
                refine ⟨9914352028243476067114645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13219136037657968089486193 9914352028243476067114645)
                ·
                  refine ⟨464735251323912940645999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9914352028243476067114645 464735251323912940645999)
                  ·
                    rfl

theorem cell23_8145618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_8145618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145618 prefixEnd_8145618 := by exact prefixLift 8145618
  have htrace : WordTrace (prefixWord ++ tailWord_8145618) baseStart_8145618 baseEnd_8145618 := by
    simpa [prefixWord, tailWord_8145618, baseEnd_8145618] using wordTrace_append hprefix tailTrace_8145618
  have hstable : (prefixWord ++ tailWord_8145618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145618).length < 2 ^ (prefixWord ++ tailWord_8145618).sum := by decide
  have hdescent : baseEnd_8145618 < baseStart_8145618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145628 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_8145628 : Nat := 118140960795 + 8145628 * 2 ^ 59
def prefixEnd_8145628 : Nat := 4983230072969 + 3 ^ 40 * 8145628 * 2
def baseEnd_8145628 : Nat := 4182622396721761426688945

theorem tailTrace_8145628 : CollatzResearch.WordTrace tailWord_8145628 prefixEnd_8145628 4182622396721761426688945 := by
  unfold tailWord_8145628
  simp only [CollatzResearch.WordTrace]
  refine ⟨148547730266894196675702769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198063640355858928900937025 148547730266894196675702769)
  ·
    refine ⟨111410797700170647506777077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148547730266894196675702769 111410797700170647506777077)
    ·
      refine ⟨10444762284390998203760351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111410797700170647506777077 10444762284390998203760351)
      ·
        refine ⟨15667143426586497305640527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10444762284390998203760351 15667143426586497305640527)
        ·
          refine ⟨23500715139879745958460791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15667143426586497305640527 23500715139879745958460791)
          ·
            refine ⟨35251072709819618937691187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23500715139879745958460791 35251072709819618937691187)
            ·
              refine ⟨52876609064729428406536781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35251072709819618937691187 52876609064729428406536781)
              ·
                refine ⟨19828728399273535652451293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52876609064729428406536781 19828728399273535652451293)
                ·
                  refine ⟨7435773149727575869669235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19828728399273535652451293 7435773149727575869669235)
                  ·
                    refine ⟨11153659724591363804503853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7435773149727575869669235 11153659724591363804503853)
                    ·
                      refine ⟨4182622396721761426688945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11153659724591363804503853 4182622396721761426688945)
                      ·
                        rfl

theorem cell23_8145628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_8145628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145628 prefixEnd_8145628 := by exact prefixLift 8145628
  have htrace : WordTrace (prefixWord ++ tailWord_8145628) baseStart_8145628 baseEnd_8145628 := by
    simpa [prefixWord, tailWord_8145628, baseEnd_8145628] using wordTrace_append hprefix tailTrace_8145628
  have hstable : (prefixWord ++ tailWord_8145628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145628).length < 2 ^ (prefixWord ++ tailWord_8145628).sum := by decide
  have hdescent : baseEnd_8145628 < baseStart_8145628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145654 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_8145654 : Nat := 118140960795 + 8145654 * 2 ^ 59
def prefixEnd_8145654 : Nat := 4983230072969 + 3 ^ 40 * 8145654 * 2
def baseEnd_8145654 : Nat := 4182635747218778324963825

theorem tailTrace_8145654 : CollatzResearch.WordTrace tailWord_8145654 prefixEnd_8145654 4182635747218778324963825 := by
  unfold tailWord_8145654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18568525551980887486990751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198064272554462799861234677 18568525551980887486990751)
  ·
    refine ⟨27852788327971331230486127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18568525551980887486990751 27852788327971331230486127)
    ·
      refine ⟨41779182491956996845729191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27852788327971331230486127 41779182491956996845729191)
      ·
        refine ⟨62668773737935495268593787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41779182491956996845729191 62668773737935495268593787)
        ·
          refine ⟨94003160606903242902890681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62668773737935495268593787 94003160606903242902890681)
          ·
            refine ⟨70502370455177432177168011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94003160606903242902890681 70502370455177432177168011)
            ·
              refine ⟨105753555682766148265752017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70502370455177432177168011 105753555682766148265752017)
              ·
                refine ⟨79315166762074611199314013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105753555682766148265752017 79315166762074611199314013)
                ·
                  refine ⟨29743187535777979199742755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79315166762074611199314013 29743187535777979199742755)
                  ·
                    refine ⟨44614781303666968799614133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29743187535777979199742755 44614781303666968799614133)
                    ·
                      refine ⟨4182635747218778324963825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44614781303666968799614133 4182635747218778324963825)
                      ·
                        rfl

theorem cell23_8145654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_8145654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145654 prefixEnd_8145654 := by exact prefixLift 8145654
  have htrace : WordTrace (prefixWord ++ tailWord_8145654) baseStart_8145654 baseEnd_8145654 := by
    simpa [prefixWord, tailWord_8145654, baseEnd_8145654] using wordTrace_append hprefix tailTrace_8145654
  have hstable : (prefixWord ++ tailWord_8145654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145654).length < 2 ^ (prefixWord ++ tailWord_8145654).sum := by decide
  have hdescent : baseEnd_8145654 < baseStart_8145654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145662 : List Nat := [4, 2, 2, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_8145662 : Nat := 118140960795 + 8145662 * 2 ^ 59
def prefixEnd_8145662 : Nat := 4983230072969 + 3 ^ 40 * 8145662 * 2
def baseEnd_8145662 : Nat := 4182639855064014293663789

theorem tailTrace_8145662 : CollatzResearch.WordTrace tailWord_8145662 prefixEnd_8145662 4182639855064014293663789 := by
  unfold tailWord_8145662
  simp only [CollatzResearch.WordTrace]
  refine ⟨37137087576958152144767905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198064467077110144772095493 37137087576958152144767905)
  ·
    refine ⟨27852815682718614108575929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37137087576958152144767905 27852815682718614108575929)
    ·
      refine ⟨20889611762038960581431947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27852815682718614108575929 20889611762038960581431947)
      ·
        refine ⟨31334417643058440872147921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20889611762038960581431947 31334417643058440872147921)
        ·
          refine ⟨23500813232293830654110941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31334417643058440872147921 23500813232293830654110941)
          ·
            refine ⟨8812804962110186495291603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23500813232293830654110941 8812804962110186495291603)
            ·
              refine ⟨13219207443165279742937405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812804962110186495291603 13219207443165279742937405)
              ·
                refine ⟨4957202791186979903601527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13219207443165279742937405 4957202791186979903601527)
                ·
                  refine ⟨7435804186780469855402291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957202791186979903601527 7435804186780469855402291)
                  ·
                    refine ⟨11153706280170704783103437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7435804186780469855402291 11153706280170704783103437)
                    ·
                      refine ⟨4182639855064014293663789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11153706280170704783103437 4182639855064014293663789)
                      ·
                        rfl

theorem cell23_8145662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_8145662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145662 prefixEnd_8145662 := by exact prefixLift 8145662
  have htrace : WordTrace (prefixWord ++ tailWord_8145662) baseStart_8145662 baseEnd_8145662 := by
    simpa [prefixWord, tailWord_8145662, baseEnd_8145662] using wordTrace_append hprefix tailTrace_8145662
  have hstable : (prefixWord ++ tailWord_8145662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145662).length < 2 ^ (prefixWord ++ tailWord_8145662).sum := by decide
  have hdescent : baseEnd_8145662 < baseStart_8145662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145671 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_8145671 : Nat := 118140960795 + 8145671 * 2 ^ 59
def prefixEnd_8145671 : Nat := 4983230072969 + 3 ^ 40 * 8145671 * 2
def baseEnd_8145671 : Nat := 4182644476389904758451247

theorem tailTrace_8145671 : CollatzResearch.WordTrace tailWord_8145671 prefixEnd_8145671 4182644476389904758451247 := by
  unfold tailWord_8145671
  simp only [CollatzResearch.WordTrace]
  refine ⟨297097028872632611695220867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198064685915088407796813911 297097028872632611695220867)
  ·
    refine ⟨445645543308948917542831301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297097028872632611695220867 445645543308948917542831301)
    ·
      refine ⟨83558539370427922039280869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 445645543308948917542831301 83558539370427922039280869)
      ·
        refine ⟨15667226131955235382365163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83558539370427922039280869 15667226131955235382365163)
        ·
          refine ⟨23500839197932853073547745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15667226131955235382365163 23500839197932853073547745)
          ·
            refine ⟨17625629398449639805160809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23500839197932853073547745 17625629398449639805160809)
            ·
              refine ⟨13219222048837229853870607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17625629398449639805160809 13219222048837229853870607)
              ·
                refine ⟨19828833073255844780805911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13219222048837229853870607 19828833073255844780805911)
                ·
                  refine ⟨29743249609883767171208867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19828833073255844780805911 29743249609883767171208867)
                  ·
                    refine ⟨44614874414825650756813301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29743249609883767171208867 44614874414825650756813301)
                    ·
                      refine ⟨4182644476389904758451247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44614874414825650756813301 4182644476389904758451247)
                      ·
                        rfl

theorem cell23_8145671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_8145671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145671 prefixEnd_8145671 := by exact prefixLift 8145671
  have htrace : WordTrace (prefixWord ++ tailWord_8145671) baseStart_8145671 baseEnd_8145671 := by
    simpa [prefixWord, tailWord_8145671, baseEnd_8145671] using wordTrace_append hprefix tailTrace_8145671
  have hstable : (prefixWord ++ tailWord_8145671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145671).length < 2 ^ (prefixWord ++ tailWord_8145671).sum := by decide
  have hdescent : baseEnd_8145671 < baseStart_8145671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145744 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 3]
def baseStart_8145744 : Nat := 118140960795 + 8145744 * 2 ^ 59
def prefixEnd_8145744 : Nat := 4983230072969 + 3 ^ 40 * 8145744 * 2
def baseEnd_8145744 : Nat := 4182681960477682972838411

theorem tailTrace_8145744 : CollatzResearch.WordTrace tailWord_8145744 prefixEnd_8145744 4182681960477682972838411 := by
  unfold tailWord_8145744
  simp only [CollatzResearch.WordTrace]
  refine ⟨148549845700684072581314143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198066460934245430108418857 148549845700684072581314143)
  ·
    refine ⟨222824768551026108871971215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148549845700684072581314143 222824768551026108871971215)
    ·
      refine ⟨334237152826539163307956823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222824768551026108871971215 334237152826539163307956823)
      ·
        refine ⟨501355729239808744961935235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334237152826539163307956823 501355729239808744961935235)
        ·
          refine ⟨752033593859713117442902853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501355729239808744961935235 752033593859713117442902853)
          ·
            refine ⟨141006298848696209520544285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 752033593859713117442902853 141006298848696209520544285)
            ·
              refine ⟨52877362068261078570204107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141006298848696209520544285 52877362068261078570204107)
              ·
                refine ⟨79316043102391617855306161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52877362068261078570204107 79316043102391617855306161)
                ·
                  refine ⟨59487032326793713391479621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79316043102391617855306161 59487032326793713391479621)
                  ·
                    refine ⟨11153818561273821260902429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59487032326793713391479621 11153818561273821260902429)
                    ·
                      refine ⟨4182681960477682972838411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11153818561273821260902429 4182681960477682972838411)
                      ·
                        rfl

theorem cell23_8145744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_8145744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145744 prefixEnd_8145744 := by exact prefixLift 8145744
  have htrace : WordTrace (prefixWord ++ tailWord_8145744) baseStart_8145744 baseEnd_8145744 := by
    simpa [prefixWord, tailWord_8145744, baseEnd_8145744] using wordTrace_append hprefix tailTrace_8145744
  have hstable : (prefixWord ++ tailWord_8145744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145744).length < 2 ^ (prefixWord ++ tailWord_8145744).sum := by decide
  have hdescent : baseEnd_8145744 < baseStart_8145744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145747 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 11]
def baseStart_8145747 : Nat := 118140960795 + 8145747 * 2 ^ 59
def prefixEnd_8145747 : Nat := 4983230072969 + 3 ^ 40 * 8145747 * 2
def baseEnd_8145747 : Nat := 464742611213294051233433

theorem tailTrace_8145747 : CollatzResearch.WordTrace tailWord_8145747 prefixEnd_8145747 464742611213294051233433 := by
  unfold tailWord_8145747
  simp only [CollatzResearch.WordTrace]
  refine ⟨297099800820357276674987495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198066533880238184449991663 297099800820357276674987495)
  ·
    refine ⟨445649701230535915012481243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297099800820357276674987495 445649701230535915012481243)
    ·
      refine ⟨668474551845803872518721865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445649701230535915012481243 668474551845803872518721865)
      ·
        refine ⟨501355913884352904389041399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668474551845803872518721865 501355913884352904389041399)
        ·
          refine ⟨752033870826529356583562099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501355913884352904389041399 752033870826529356583562099)
          ·
            refine ⟨1128050806239794034875343149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752033870826529356583562099 1128050806239794034875343149)
            ·
              refine ⟨423019052339922763078253681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1128050806239794034875343149 423019052339922763078253681)
              ·
                refine ⟨317264289254942072308690261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423019052339922763078253681 317264289254942072308690261)
                ·
                  refine ⟨464742611213294051233433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 317264289254942072308690261 464742611213294051233433)
                  ·
                    rfl

theorem cell23_8145747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 11].length) (baseStart_8145747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145747 prefixEnd_8145747 := by exact prefixLift 8145747
  have htrace : WordTrace (prefixWord ++ tailWord_8145747) baseStart_8145747 baseEnd_8145747 := by
    simpa [prefixWord, tailWord_8145747, baseEnd_8145747] using wordTrace_append hprefix tailTrace_8145747
  have hstable : (prefixWord ++ tailWord_8145747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145747).length < 2 ^ (prefixWord ++ tailWord_8145747).sum := by decide
  have hdescent : baseEnd_8145747 < baseStart_8145747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145754 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_8145754 : Nat := 118140960795 + 8145754 * 2 ^ 59
def prefixEnd_8145754 : Nat := 4983230072969 + 3 ^ 40 * 8145754 * 2
def baseEnd_8145754 : Nat := 4182687095284227933713365

theorem tailTrace_8145754 : CollatzResearch.WordTrace tailWord_8145754 prefixEnd_8145754 4182687095284227933713365 := by
  unfold tailWord_8145754
  simp only [CollatzResearch.WordTrace]
  refine ⟨74275014032832979217623079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198066704087554611246994877 74275014032832979217623079)
  ·
    refine ⟨111412521049249468826434619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74275014032832979217623079 111412521049249468826434619)
    ·
      refine ⟨167118781573874203239651929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111412521049249468826434619 167118781573874203239651929)
      ·
        refine ⟨125339086180405652429738947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167118781573874203239651929 125339086180405652429738947)
        ·
          refine ⟨188008629270608478644608421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125339086180405652429738947 188008629270608478644608421)
          ·
            refine ⟨35251617988239089745864079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188008629270608478644608421 35251617988239089745864079)
            ·
              refine ⟨52877426982358634618796119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35251617988239089745864079 52877426982358634618796119)
              ·
                refine ⟨79316140473537951928194179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52877426982358634618796119 79316140473537951928194179)
                ·
                  refine ⟨118974210710306927892291269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79316140473537951928194179 118974210710306927892291269)
                  ·
                    refine ⟨22307664508182548979804613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118974210710306927892291269 22307664508182548979804613)
                    ·
                      refine ⟨4182687095284227933713365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22307664508182548979804613 4182687095284227933713365)
                      ·
                        rfl

theorem cell23_8145754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_8145754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145754 prefixEnd_8145754 := by exact prefixLift 8145754
  have htrace : WordTrace (prefixWord ++ tailWord_8145754) baseStart_8145754 baseEnd_8145754 := by
    simpa [prefixWord, tailWord_8145754, baseEnd_8145754] using wordTrace_append hprefix tailTrace_8145754
  have hstable : (prefixWord ++ tailWord_8145754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145754).length < 2 ^ (prefixWord ++ tailWord_8145754).sum := by decide
  have hdescent : baseEnd_8145754 < baseStart_8145754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145764 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 9]
def baseStart_8145764 : Nat := 118140960795 + 8145764 * 2 ^ 59
def prefixEnd_8145764 : Nat := 4983230072969 + 3 ^ 40 * 8145764 * 2
def baseEnd_8145764 : Nat := 464743581121196988287591

theorem tailTrace_8145764 : CollatzResearch.WordTrace tailWord_8145764 prefixEnd_8145764 464743581121196988287591 := by
  unfold tailWord_8145764
  simp only [CollatzResearch.WordTrace]
  refine ⟨148550210430647844289178173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198066947240863792385570897 148550210430647844289178173)
  ·
    refine ⟨55706328911492941608441815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148550210430647844289178173 55706328911492941608441815)
    ·
      refine ⟨83559493367239412412662723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55706328911492941608441815 83559493367239412412662723)
      ·
        refine ⟨125339240050859118618994085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83559493367239412412662723 125339240050859118618994085)
        ·
          refine ⟨23501107509536084741061391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125339240050859118618994085 23501107509536084741061391)
          ·
            refine ⟨35251661264304127111592087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23501107509536084741061391 35251661264304127111592087)
            ·
              refine ⟨52877491896456190667388131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35251661264304127111592087 52877491896456190667388131)
              ·
                refine ⟨79316237844684286001082197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52877491896456190667388131 79316237844684286001082197)
                ·
                  refine ⟨464743581121196988287591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79316237844684286001082197 464743581121196988287591)
                  ·
                    rfl

theorem cell23_8145764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_8145764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145764 prefixEnd_8145764 := by exact prefixLift 8145764
  have htrace : WordTrace (prefixWord ++ tailWord_8145764) baseStart_8145764 baseEnd_8145764 := by
    simpa [prefixWord, tailWord_8145764, baseEnd_8145764] using wordTrace_append hprefix tailTrace_8145764
  have hstable : (prefixWord ++ tailWord_8145764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145764).length < 2 ^ (prefixWord ++ tailWord_8145764).sum := by decide
  have hdescent : baseEnd_8145764 < baseStart_8145764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145804 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_8145804 : Nat := 118140960795 + 8145804 * 2 ^ 59
def prefixEnd_8145804 : Nat := 4983230072969 + 3 ^ 40 * 8145804 * 2
def baseEnd_8145804 : Nat := 4182712769316952738088135

theorem tailTrace_8145804 : CollatzResearch.WordTrace tailWord_8145804 prefixEnd_8145804 4182712769316952738088135 := by
  unfold tailWord_8145804
  simp only [CollatzResearch.WordTrace]
  refine ⟨148550939890575387704906233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198067919854100516939874977 148550939890575387704906233)
  ·
    refine ⟨111413204917931540778679675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148550939890575387704906233 111413204917931540778679675)
    ·
      refine ⟨167119807376897311168019513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111413204917931540778679675 167119807376897311168019513)
      ·
        refine ⟨125339855532672983376014635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167119807376897311168019513 125339855532672983376014635)
        ·
          refine ⟨188009783299009475064021953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125339855532672983376014635 188009783299009475064021953)
          ·
            refine ⟨141007337474257106298016465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188009783299009475064021953 141007337474257106298016465)
            ·
              refine ⟨105755503105692829723512349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141007337474257106298016465 105755503105692829723512349)
              ·
                refine ⟨39658313664634811146317131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105755503105692829723512349 39658313664634811146317131)
                ·
                  refine ⟨59487470496952216719475697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39658313664634811146317131 59487470496952216719475697)
                  ·
                    refine ⟨44615602872714162539606773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59487470496952216719475697 44615602872714162539606773)
                    ·
                      refine ⟨4182712769316952738088135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44615602872714162539606773 4182712769316952738088135)
                      ·
                        rfl

theorem cell23_8145804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_8145804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145804 prefixEnd_8145804 := by exact prefixLift 8145804
  have htrace : WordTrace (prefixWord ++ tailWord_8145804) baseStart_8145804 baseEnd_8145804 := by
    simpa [prefixWord, tailWord_8145804, baseEnd_8145804] using wordTrace_append hprefix tailTrace_8145804
  have hstable : (prefixWord ++ tailWord_8145804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145804).length < 2 ^ (prefixWord ++ tailWord_8145804).sum := by decide
  have hdescent : baseEnd_8145804 < baseStart_8145804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145871 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 6]
def baseStart_8145871 : Nat := 118140960795 + 8145871 * 2 ^ 59
def prefixEnd_8145871 : Nat := 4983230072969 + 3 ^ 40 * 8145871 * 2
def baseEnd_8145871 : Nat := 464749685835644886216703

theorem tailTrace_8145871 : CollatzResearch.WordTrace tailWord_8145871 prefixEnd_8145871 464749685835644886216703 := by
  unfold tailWord_8145871
  simp only [CollatzResearch.WordTrace]
  refine ⟨297104323471908045852501467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198069548981272030568334311 297104323471908045852501467)
  ·
    refine ⟨445656485207862068778752201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297104323471908045852501467 445656485207862068778752201)
    ·
      refine ⟨334242363905896551584064151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445656485207862068778752201 334242363905896551584064151)
      ·
        refine ⟨501363545858844827376096227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334242363905896551584064151 501363545858844827376096227)
        ·
          refine ⟨752045318788267241064144341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501363545858844827376096227 752045318788267241064144341)
          ·
            refine ⟨17626062159100013462440883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 752045318788267241064144341 17626062159100013462440883)
            ·
              refine ⟨26439093238650020193661325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17626062159100013462440883 26439093238650020193661325)
              ·
                refine ⟨9914659964493757572622997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26439093238650020193661325 9914659964493757572622997)
                ·
                  refine ⟨464749685835644886216703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9914659964493757572622997 464749685835644886216703)
                  ·
                    rfl

theorem cell23_8145871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 6].length) (baseStart_8145871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145871 prefixEnd_8145871 := by exact prefixLift 8145871
  have htrace : WordTrace (prefixWord ++ tailWord_8145871) baseStart_8145871 baseEnd_8145871 := by
    simpa [prefixWord, tailWord_8145871, baseEnd_8145871] using wordTrace_append hprefix tailTrace_8145871
  have hstable : (prefixWord ++ tailWord_8145871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145871).length < 2 ^ (prefixWord ++ tailWord_8145871).sum := by decide
  have hdescent : baseEnd_8145871 < baseStart_8145871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145885 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_8145885 : Nat := 118140960795 + 8145885 * 2 ^ 59
def prefixEnd_8145885 : Nat := 4983230072969 + 3 ^ 40 * 8145885 * 2
def baseEnd_8145885 : Nat := 4182754361249966921175263

theorem tailTrace_8145885 : CollatzResearch.WordTrace tailWord_8145885 prefixEnd_8145885 4182754361249966921175263 := by
  unfold tailWord_8145885
  simp only [CollatzResearch.WordTrace]
  refine ⟨297104834093857326243511109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198069889395904884162340739 297104834093857326243511109)
  ·
    refine ⟨55707156392598248670658333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297104834093857326243511109 55707156392598248670658333)
    ·
      refine ⟨20890183647224343251496875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55707156392598248670658333 20890183647224343251496875)
      ·
        refine ⟨31335275470836514877245313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20890183647224343251496875 31335275470836514877245313)
        ·
          refine ⟨23501456603127386157933985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31335275470836514877245313 23501456603127386157933985)
          ·
            refine ⟨17626092452345539618450489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23501456603127386157933985 17626092452345539618450489)
            ·
              refine ⟨13219569339259154713837867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17626092452345539618450489 13219569339259154713837867)
              ·
                refine ⟨19829354008888732070756801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13219569339259154713837867 19829354008888732070756801)
                ·
                  refine ⟨14872015506666549053067601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19829354008888732070756801 14872015506666549053067601)
                  ·
                    refine ⟨11154011629999911789800701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14872015506666549053067601 11154011629999911789800701)
                    ·
                      refine ⟨4182754361249966921175263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11154011629999911789800701 4182754361249966921175263)
                      ·
                        rfl

theorem cell23_8145885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_8145885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145885 prefixEnd_8145885 := by exact prefixLift 8145885
  have htrace : WordTrace (prefixWord ++ tailWord_8145885) baseStart_8145885 baseEnd_8145885 := by
    simpa [prefixWord, tailWord_8145885, baseEnd_8145885] using wordTrace_append hprefix tailTrace_8145885
  have hstable : (prefixWord ++ tailWord_8145885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145885).length < 2 ^ (prefixWord ++ tailWord_8145885).sum := by decide
  have hdescent : baseEnd_8145885 < baseStart_8145885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145909 : List Nat := [1, 3, 5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_8145909 : Nat := 118140960795 + 8145909 * 2 ^ 59
def prefixEnd_8145909 : Nat := 4983230072969 + 3 ^ 40 * 8145909 * 2
def baseEnd_8145909 : Nat := 1394255561595224942425051

theorem tailTrace_8145909 : CollatzResearch.WordTrace tailWord_8145909 prefixEnd_8145909 1394255561595224942425051 := by
  unfold tailWord_8145909
  simp only [CollatzResearch.WordTrace]
  refine ⟨297105709445770378342384781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198070472963846918894923187 297105709445770378342384781)
  ·
    refine ⟨111414641042163891878394293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297105709445770378342384781 111414641042163891878394293)
    ·
      refine ⟨10445122597702864863599465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111414641042163891878394293 10445122597702864863599465)
      ·
        refine ⟨7833841948277148647699599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10445122597702864863599465 7833841948277148647699599)
        ·
          refine ⟨11750762922415722971549399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833841948277148647699599 11750762922415722971549399)
          ·
            refine ⟨17626144383623584457324099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750762922415722971549399 17626144383623584457324099)
            ·
              refine ⟨26439216575435376685986149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17626144383623584457324099 26439216575435376685986149)
              ·
                refine ⟨4957353107894133128622403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26439216575435376685986149 4957353107894133128622403)
                ·
                  refine ⟨7436029661841199692933605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957353107894133128622403 7436029661841199692933605)
                  ·
                    refine ⟨1394255561595224942425051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7436029661841199692933605 1394255561595224942425051)
                    ·
                      rfl

theorem cell23_8145909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_8145909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145909 prefixEnd_8145909 := by exact prefixLift 8145909
  have htrace : WordTrace (prefixWord ++ tailWord_8145909) baseStart_8145909 baseEnd_8145909 := by
    simpa [prefixWord, tailWord_8145909, baseEnd_8145909] using wordTrace_append hprefix tailTrace_8145909
  have hstable : (prefixWord ++ tailWord_8145909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145909).length < 2 ^ (prefixWord ++ tailWord_8145909).sum := by decide
  have hdescent : baseEnd_8145909 < baseStart_8145909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145931 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 1, 6]
def baseStart_8145931 : Nat := 118140960795 + 8145931 * 2 ^ 59
def prefixEnd_8145931 : Nat := 4983230072969 + 3 ^ 40 * 8145931 * 2
def baseEnd_8145931 : Nat := 1394259327120024580400017

theorem tailTrace_8145931 : CollatzResearch.WordTrace tailWord_8145931 prefixEnd_8145931 1394259327120024580400017 := by
  unfold tailWord_8145931
  simp only [CollatzResearch.WordTrace]
  refine ⟨297106511851690676099685647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198071007901127117399790431 297106511851690676099685647)
  ·
    refine ⟨445659767777536014149528471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297106511851690676099685647 445659767777536014149528471)
    ·
      refine ⟨668489651666304021224292707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445659767777536014149528471 668489651666304021224292707)
      ·
        refine ⟨1002734477499456031836439061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668489651666304021224292707 1002734477499456031836439061)
        ·
          refine ⟨47003178632787001492333081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1002734477499456031836439061 47003178632787001492333081)
          ·
            refine ⟨35252383974590251119249811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47003178632787001492333081 35252383974590251119249811)
            ·
              refine ⟨52878575961885376678874717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35252383974590251119249811 52878575961885376678874717)
              ·
                refine ⟨19829465985707016254578019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52878575961885376678874717 19829465985707016254578019)
                ·
                  refine ⟨29744198978560524381867029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19829465985707016254578019 29744198978560524381867029)
                  ·
                    refine ⟨1394259327120024580400017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29744198978560524381867029 1394259327120024580400017)
                    ·
                      rfl

theorem cell23_8145931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 6].length) (baseStart_8145931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145931 prefixEnd_8145931 := by exact prefixLift 8145931
  have htrace : WordTrace (prefixWord ++ tailWord_8145931) baseStart_8145931 baseEnd_8145931 := by
    simpa [prefixWord, tailWord_8145931, baseEnd_8145931] using wordTrace_append hprefix tailTrace_8145931
  have hstable : (prefixWord ++ tailWord_8145931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145931).length < 2 ^ (prefixWord ++ tailWord_8145931).sum := by decide
  have hdescent : baseEnd_8145931 < baseStart_8145931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145949 : List Nat := [1, 4, 2, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_8145949 : Nat := 118140960795 + 8145949 * 2 ^ 59
def prefixEnd_8145949 : Nat := 4983230072969 + 3 ^ 40 * 8145949 * 2
def baseEnd_8145949 : Nat := 4182787224011854670774969

theorem tailTrace_8145949 : CollatzResearch.WordTrace tailWord_8145949 prefixEnd_8145949 4182787224011854670774969 := by
  unfold tailWord_8145949
  simp only [CollatzResearch.WordTrace]
  refine ⟨297107168365625465173840901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198071445577083643449227267 297107168365625465173840901)
  ·
    refine ⟨55707594068554774720095169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297107168365625465173840901 55707594068554774720095169)
    ·
      refine ⟨41780695551416081040071377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55707594068554774720095169 41780695551416081040071377)
      ·
        refine ⟨31335521663562060780053533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41780695551416081040071377 31335521663562060780053533)
        ·
          refine ⟨11750820623835772792520075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31335521663562060780053533 11750820623835772792520075)
          ·
            refine ⟨17626230935753659188780113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750820623835772792520075 17626230935753659188780113)
            ·
              refine ⟨13219673201815244391585085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17626230935753659188780113 13219673201815244391585085)
              ·
                refine ⟨4957377450680716646844407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13219673201815244391585085 4957377450680716646844407)
                ·
                  refine ⟨7436066176021074970266611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957377450680716646844407 7436066176021074970266611)
                  ·
                    refine ⟨11154099264031612455399917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7436066176021074970266611 11154099264031612455399917)
                    ·
                      refine ⟨4182787224011854670774969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11154099264031612455399917 4182787224011854670774969)
                      ·
                        rfl

theorem cell23_8145949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_8145949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145949 prefixEnd_8145949 := by exact prefixLift 8145949
  have htrace : WordTrace (prefixWord ++ tailWord_8145949) baseStart_8145949 baseEnd_8145949 := by
    simpa [prefixWord, tailWord_8145949, baseEnd_8145949] using wordTrace_append hprefix tailTrace_8145949
  have hstable : (prefixWord ++ tailWord_8145949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145949).length < 2 ^ (prefixWord ++ tailWord_8145949).sum := by decide
  have hdescent : baseEnd_8145949 < baseStart_8145949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8145955 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 1, 1, 4]
def baseStart_8145955 : Nat := 118140960795 + 8145955 * 2 ^ 59
def prefixEnd_8145955 : Nat := 4983230072969 + 3 ^ 40 * 8145955 * 2
def baseEnd_8145955 : Nat := 4182790304895781647299941

theorem tailTrace_8145955 : CollatzResearch.WordTrace tailWord_8145955 prefixEnd_8145955 4182790304895781647299941 := by
  unfold tailWord_8145955
  simp only [CollatzResearch.WordTrace]
  refine ⟨297107387203603728198559319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198071591469069152132372879 297107387203603728198559319)
  ·
    refine ⟨445661080805405592297838979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297107387203603728198559319 445661080805405592297838979)
    ·
      refine ⟨668491621208108388446758469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445661080805405592297838979 668491621208108388446758469)
      ·
        refine ⟨125342178976520322833767213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 668491621208108388446758469 125342178976520322833767213)
        ·
          refine ⟨47003317116195121062662705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125342178976520322833767213 47003317116195121062662705)
          ·
            refine ⟨35252487837146340796997029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47003317116195121062662705 35252487837146340796997029)
            ·
              refine ⟨6609841469464938899436943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35252487837146340796997029 6609841469464938899436943)
              ·
                refine ⟨9914762204197408349155415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6609841469464938899436943 9914762204197408349155415)
                ·
                  refine ⟨14872143306296112523733123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9914762204197408349155415 14872143306296112523733123)
                  ·
                    refine ⟨22308214959444168785599685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14872143306296112523733123 22308214959444168785599685)
                    ·
                      refine ⟨4182790304895781647299941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22308214959444168785599685 4182790304895781647299941)
                      ·
                        rfl

theorem cell23_8145955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_8145955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8145955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8145955 prefixEnd_8145955 := by exact prefixLift 8145955
  have htrace : WordTrace (prefixWord ++ tailWord_8145955) baseStart_8145955 baseEnd_8145955 := by
    simpa [prefixWord, tailWord_8145955, baseEnd_8145955] using wordTrace_append hprefix tailTrace_8145955
  have hstable : (prefixWord ++ tailWord_8145955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8145955).length < 2 ^ (prefixWord ++ tailWord_8145955).sum := by decide
  have hdescent : baseEnd_8145955 < baseStart_8145955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8145955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146001 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_8146001 : Nat := 118140960795 + 8146001 * 2 ^ 59
def prefixEnd_8146001 : Nat := 4983230072969 + 3 ^ 40 * 8146001 * 2
def baseEnd_8146001 : Nat := 4182813925005888467324729

theorem tailTrace_8146001 : CollatzResearch.WordTrace tailWord_8146001 prefixEnd_8146001 4182813925005888467324729 := by
  unfold tailWord_8146001
  simp only [CollatzResearch.WordTrace]
  refine ⟨297109064961437078054733857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198072709974291385369822571 297109064961437078054733857)
  ·
    refine ⟨222831798721077808541050393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297109064961437078054733857 222831798721077808541050393)
    ·
      refine ⟨167123849040808356405787795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222831798721077808541050393 167123849040808356405787795)
      ·
        refine ⟨250685773561212534608681693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167123849040808356405787795 250685773561212534608681693)
        ·
          refine ⟨94007165085454700478255635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250685773561212534608681693 94007165085454700478255635)
          ·
            refine ⟨141010747628182050717383453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94007165085454700478255635 141010747628182050717383453)
            ·
              refine ⟨52879030360568269019018795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141010747628182050717383453 52879030360568269019018795)
              ·
                refine ⟨79318545540852403528528193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52879030360568269019018795 79318545540852403528528193)
                ·
                  refine ⟨59488909155639302646396145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79318545540852403528528193 59488909155639302646396145)
                  ·
                    refine ⟨44616681866729476984797109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59488909155639302646396145 44616681866729476984797109)
                    ·
                      refine ⟨4182813925005888467324729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44616681866729476984797109 4182813925005888467324729)
                      ·
                        rfl

theorem cell23_8146001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_8146001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146001 prefixEnd_8146001 := by exact prefixLift 8146001
  have htrace : WordTrace (prefixWord ++ tailWord_8146001) baseStart_8146001 baseEnd_8146001 := by
    simpa [prefixWord, tailWord_8146001, baseEnd_8146001] using wordTrace_append hprefix tailTrace_8146001
  have hstable : (prefixWord ++ tailWord_8146001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146001).length < 2 ^ (prefixWord ++ tailWord_8146001).sum := by decide
  have hdescent : baseEnd_8146001 < baseStart_8146001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146015 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 1, 3, 2]
def baseStart_8146015 : Nat := 118140960795 + 8146015 * 2 ^ 59
def prefixEnd_8146015 : Nat := 4983230072969 + 3 ^ 40 * 8146015 * 2
def baseEnd_8146015 : Nat := 4182821113735051412549665

theorem tailTrace_8146015 : CollatzResearch.WordTrace tailWord_8146015 prefixEnd_8146015 4182821113735051412549665 := by
  unfold tailWord_8146015
  simp only [CollatzResearch.WordTrace]
  refine ⟨297109575583386358445743499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198073050388924238963828999 297109575583386358445743499)
  ·
    refine ⟨445664363375079537668615249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297109575583386358445743499 445664363375079537668615249)
    ·
      refine ⟨334248272531309653251461437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445664363375079537668615249 334248272531309653251461437)
      ·
        refine ⟨125343102199241119969298039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334248272531309653251461437 125343102199241119969298039)
        ·
          refine ⟨188014653298861679953947059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125343102199241119969298039 188014653298861679953947059)
          ·
            refine ⟨282021979948292519930920589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188014653298861679953947059 282021979948292519930920589)
            ·
              refine ⟨105758242480609694974095221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282021979948292519930920589 105758242480609694974095221)
              ·
                refine ⟨9914835232557158903821427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105758242480609694974095221 9914835232557158903821427)
                ·
                  refine ⟨14872252848835738355732141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9914835232557158903821427 14872252848835738355732141)
                  ·
                    refine ⟨5577094818313401883399553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14872252848835738355732141 5577094818313401883399553)
                    ·
                      refine ⟨4182821113735051412549665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577094818313401883399553 4182821113735051412549665)
                      ·
                        rfl

theorem cell23_8146015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_8146015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146015 prefixEnd_8146015 := by exact prefixLift 8146015
  have htrace : WordTrace (prefixWord ++ tailWord_8146015) baseStart_8146015 baseEnd_8146015 := by
    simpa [prefixWord, tailWord_8146015, baseEnd_8146015] using wordTrace_append hprefix tailTrace_8146015
  have hstable : (prefixWord ++ tailWord_8146015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146015).length < 2 ^ (prefixWord ++ tailWord_8146015).sum := by decide
  have hdescent : baseEnd_8146015 < baseStart_8146015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146031 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_8146031 : Nat := 118140960795 + 8146031 * 2 ^ 59
def prefixEnd_8146031 : Nat := 4983230072969 + 3 ^ 40 * 8146031 * 2
def baseEnd_8146031 : Nat := 4182829329425523349949591

theorem tailTrace_8146031 : CollatzResearch.WordTrace tailWord_8146031 prefixEnd_8146031 4182829329425523349949591 := by
  unfold tailWord_8146031
  simp only [CollatzResearch.WordTrace]
  refine ⟨297110159151328393178325947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198073439434218928785550631 297110159151328393178325947)
  ·
    refine ⟨445665238726992589767488921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297110159151328393178325947 445665238726992589767488921)
    ·
      refine ⟨334248929045244442325616691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445665238726992589767488921 334248929045244442325616691)
      ·
        refine ⟨501373393567866663488425037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334248929045244442325616691 501373393567866663488425037)
        ·
          refine ⟨188015022587949998808159389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501373393567866663488425037 188015022587949998808159389)
          ·
            refine ⟨70505633470481249553059771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188015022587949998808159389 70505633470481249553059771)
            ·
              refine ⟨105758450205721874329589657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70505633470481249553059771 105758450205721874329589657)
              ·
                refine ⟨79318837654291405747192243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105758450205721874329589657 79318837654291405747192243)
                ·
                  refine ⟨118978256481437108620788365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79318837654291405747192243 118978256481437108620788365)
                  ·
                    refine ⟨44616846180538915732795637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118978256481437108620788365 44616846180538915732795637)
                    ·
                      refine ⟨4182829329425523349949591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44616846180538915732795637 4182829329425523349949591)
                      ·
                        rfl

theorem cell23_8146031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_8146031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146031 prefixEnd_8146031 := by exact prefixLift 8146031
  have htrace : WordTrace (prefixWord ++ tailWord_8146031) baseStart_8146031 baseEnd_8146031 := by
    simpa [prefixWord, tailWord_8146031, baseEnd_8146031] using wordTrace_append hprefix tailTrace_8146031
  have hstable : (prefixWord ++ tailWord_8146031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146031).length < 2 ^ (prefixWord ++ tailWord_8146031).sum := by decide
  have hdescent : baseEnd_8146031 < baseStart_8146031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146038 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_8146038 : Nat := 118140960795 + 8146038 * 2 ^ 59
def prefixEnd_8146038 : Nat := 4983230072969 + 3 ^ 40 * 8146038 * 2
def baseEnd_8146038 : Nat := 1394277641263368274187353

theorem tailTrace_8146038 : CollatzResearch.WordTrace tailWord_8146038 prefixEnd_8146038 1394277641263368274187353 := by
  unfold tailWord_8146038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18569400903893939585864423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198073609641535355582553845 18569400903893939585864423)
  ·
    refine ⟨27854101355840909378796635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18569400903893939585864423 27854101355840909378796635)
    ·
      refine ⟨41781152033761364068194953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27854101355840909378796635 41781152033761364068194953)
      ·
        refine ⟨31335864025321023051146215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41781152033761364068194953 31335864025321023051146215)
        ·
          refine ⟨47003796037981534576719323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31335864025321023051146215 47003796037981534576719323)
          ·
            refine ⟨70505694056972301865078985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47003796037981534576719323 70505694056972301865078985)
            ·
              refine ⟨52879270542729226398809239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70505694056972301865078985 52879270542729226398809239)
              ·
                refine ⟨79318905814093839598213859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52879270542729226398809239 79318905814093839598213859)
                ·
                  refine ⟨118978358721140759397320789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79318905814093839598213859 118978358721140759397320789)
                  ·
                    refine ⟨1394277641263368274187353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118978358721140759397320789 1394277641263368274187353)
                    ·
                      rfl

theorem cell23_8146038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_8146038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146038 prefixEnd_8146038 := by exact prefixLift 8146038
  have htrace : WordTrace (prefixWord ++ tailWord_8146038) baseStart_8146038 baseEnd_8146038 := by
    simpa [prefixWord, tailWord_8146038, baseEnd_8146038] using wordTrace_append hprefix tailTrace_8146038
  have hstable : (prefixWord ++ tailWord_8146038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146038).length < 2 ^ (prefixWord ++ tailWord_8146038).sum := by decide
  have hdescent : baseEnd_8146038 < baseStart_8146038 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146045 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_8146045 : Nat := 118140960795 + 8146045 * 2 ^ 59
def prefixEnd_8146045 : Nat := 4983230072969 + 3 ^ 40 * 8146045 * 2
def baseEnd_8146045 : Nat := 4182836518154686295174527

theorem tailTrace_8146045 : CollatzResearch.WordTrace tailWord_8146045 prefixEnd_8146045 4182836518154686295174527 := by
  unfold tailWord_8146045
  simp only [CollatzResearch.WordTrace]
  refine ⟨297110669773277673569335589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198073779848851782379557059 297110669773277673569335589)
  ·
    refine ⟨55708250582489563794250423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297110669773277673569335589 55708250582489563794250423)
    ·
      refine ⟨83562375873734345691375635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55708250582489563794250423 83562375873734345691375635)
      ·
        refine ⟨125343563810601518537063453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83562375873734345691375635 125343563810601518537063453)
        ·
          refine ⟨47003836428975569451398795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125343563810601518537063453 47003836428975569451398795)
          ·
            refine ⟨70505754643463354177098193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47003836428975569451398795 70505754643463354177098193)
            ·
              refine ⟨52879315982597515632823645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70505754643463354177098193 52879315982597515632823645)
              ·
                refine ⟨19829743493474068362308867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52879315982597515632823645 19829743493474068362308867)
                ·
                  refine ⟨29744615240211102543463301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19829743493474068362308867 29744615240211102543463301)
                  ·
                    refine ⟨5577115357539581726899369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29744615240211102543463301 5577115357539581726899369)
                    ·
                      refine ⟨4182836518154686295174527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577115357539581726899369 4182836518154686295174527)
                      ·
                        rfl

theorem cell23_8146045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_8146045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146045 prefixEnd_8146045 := by exact prefixLift 8146045
  have htrace : WordTrace (prefixWord ++ tailWord_8146045) baseStart_8146045 baseEnd_8146045 := by
    simpa [prefixWord, tailWord_8146045, baseEnd_8146045] using wordTrace_append hprefix tailTrace_8146045
  have hstable : (prefixWord ++ tailWord_8146045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146045).length < 2 ^ (prefixWord ++ tailWord_8146045).sum := by decide
  have hdescent : baseEnd_8146045 < baseStart_8146045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146049 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_8146049 : Nat := 118140960795 + 8146049 * 2 ^ 59
def prefixEnd_8146049 : Nat := 4983230072969 + 3 ^ 40 * 8146049 * 2
def baseEnd_8146049 : Nat := 4182838572077304279524509

theorem tailTrace_8146049 : CollatzResearch.WordTrace tailWord_8146049 prefixEnd_8146049 4182838572077304279524509 := by
  unfold tailWord_8146049
  simp only [CollatzResearch.WordTrace]
  refine ⟨297110815665263182252481201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198073877110175454834987467 297110815665263182252481201)
  ·
    refine ⟨222833111748947386689360901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297110815665263182252481201 222833111748947386689360901)
    ·
      refine ⟨41781208452927635004255169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222833111748947386689360901 41781208452927635004255169)
      ·
        refine ⟨31335906339695726253191377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41781208452927635004255169 31335906339695726253191377)
        ·
          refine ⟨23501929754771794689893533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31335906339695726253191377 23501929754771794689893533)
          ·
            refine ⟨8813223658039423008710075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23501929754771794689893533 8813223658039423008710075)
            ·
              refine ⟨13219835487059134513065113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8813223658039423008710075 13219835487059134513065113)
              ·
                refine ⟨9914876615294350884798835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13219835487059134513065113 9914876615294350884798835)
                ·
                  refine ⟨14872314922941526327198253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9914876615294350884798835 14872314922941526327198253)
                  ·
                    refine ⟨5577118096103072372699345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14872314922941526327198253 5577118096103072372699345)
                    ·
                      refine ⟨4182838572077304279524509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577118096103072372699345 4182838572077304279524509)
                      ·
                        rfl

theorem cell23_8146049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_8146049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146049 prefixEnd_8146049 := by exact prefixLift 8146049
  have htrace : WordTrace (prefixWord ++ tailWord_8146049) baseStart_8146049 baseEnd_8146049 := by
    simpa [prefixWord, tailWord_8146049, baseEnd_8146049] using wordTrace_append hprefix tailTrace_8146049
  have hstable : (prefixWord ++ tailWord_8146049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146049).length < 2 ^ (prefixWord ++ tailWord_8146049).sum := by decide
  have hdescent : baseEnd_8146049 < baseStart_8146049 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146051 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 9]
def baseStart_8146051 : Nat := 118140960795 + 8146051 * 2 ^ 59
def prefixEnd_8146051 : Nat := 4983230072969 + 3 ^ 40 * 8146051 * 2
def baseEnd_8146051 : Nat := 464759955448734807966611

theorem tailTrace_8146051 : CollatzResearch.WordTrace tailWord_8146051 prefixEnd_8146051 464759955448734807966611 := by
  unfold tailWord_8146051
  simp only [CollatzResearch.WordTrace]
  refine ⟨297110888611255936594054007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198073925740837291062702671 297110888611255936594054007)
  ·
    refine ⟨445666332916883904891081011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297110888611255936594054007 445666332916883904891081011)
    ·
      refine ⟨668499499375325857336621517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445666332916883904891081011 668499499375325857336621517)
      ·
        refine ⟨250687312265747196501233069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668499499375325857336621517 250687312265747196501233069)
        ·
          refine ⟨94007742099655198687962401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250687312265747196501233069 94007742099655198687962401)
          ·
            refine ⟨70505806574741399015971801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94007742099655198687962401 70505806574741399015971801)
            ·
              refine ⟨52879354931056049261978851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70505806574741399015971801 52879354931056049261978851)
              ·
                refine ⟨79319032396584073892968277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52879354931056049261978851 79319032396584073892968277)
                ·
                  refine ⟨464759955448734807966611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79319032396584073892968277 464759955448734807966611)
                  ·
                    rfl

theorem cell23_8146051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 9].length) (baseStart_8146051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146051 prefixEnd_8146051 := by exact prefixLift 8146051
  have htrace : WordTrace (prefixWord ++ tailWord_8146051) baseStart_8146051 baseEnd_8146051 := by
    simpa [prefixWord, tailWord_8146051, baseEnd_8146051] using wordTrace_append hprefix tailTrace_8146051
  have hstable : (prefixWord ++ tailWord_8146051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146051).length < 2 ^ (prefixWord ++ tailWord_8146051).sum := by decide
  have hdescent : baseEnd_8146051 < baseStart_8146051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146062 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_8146062 : Nat := 118140960795 + 8146062 * 2 ^ 59
def prefixEnd_8146062 : Nat := 4983230072969 + 3 ^ 40 * 8146062 * 2
def baseEnd_8146062 : Nat := 4182845247325812728661949

theorem tailTrace_8146062 : CollatzResearch.WordTrace tailWord_8146062 prefixEnd_8146062 4182845247325812728661949 := by
  unfold tailWord_8146062
  simp only [CollatzResearch.WordTrace]
  refine ⟨37138911226777010684088055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198074193209477390315136293 37138911226777010684088055)
  ·
    refine ⟨55708366840165516026132083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37138911226777010684088055 55708366840165516026132083)
    ·
      refine ⟨83562550260248274039198125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55708366840165516026132083 83562550260248274039198125)
      ·
        refine ⟨31335956347593102764699297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83562550260248274039198125 31335956347593102764699297)
        ·
          refine ⟨23501967260694827073524473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31335956347593102764699297 23501967260694827073524473)
          ·
            refine ⟨17626475445521120305143355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23501967260694827073524473 17626475445521120305143355)
            ·
              refine ⟨26439713168281680457715033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17626475445521120305143355 26439713168281680457715033)
              ·
                refine ⟨19829784876211260343286275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26439713168281680457715033 19829784876211260343286275)
                ·
                  refine ⟨29744677314316890514929413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19829784876211260343286275 29744677314316890514929413)
                  ·
                    refine ⟨5577126996434416971549265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29744677314316890514929413 5577126996434416971549265)
                    ·
                      refine ⟨4182845247325812728661949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577126996434416971549265 4182845247325812728661949)
                      ·
                        rfl

theorem cell23_8146062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_8146062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146062 prefixEnd_8146062 := by exact prefixLift 8146062
  have htrace : WordTrace (prefixWord ++ tailWord_8146062) baseStart_8146062 baseEnd_8146062 := by
    simpa [prefixWord, tailWord_8146062, baseEnd_8146062] using wordTrace_append hprefix tailTrace_8146062
  have hstable : (prefixWord ++ tailWord_8146062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146062).length < 2 ^ (prefixWord ++ tailWord_8146062).sum := by decide
  have hdescent : baseEnd_8146062 < baseStart_8146062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146085 : List Nat := [1, 3, 1, 2, 1, 5, 1, 4, 5]
def baseStart_8146085 : Nat := 118140960795 + 8146085 * 2 ^ 59
def prefixEnd_8146085 : Nat := 4983230072969 + 3 ^ 40 * 8146085 * 2
def baseEnd_8146085 : Nat := 464761895264540682074927

theorem tailTrace_8146085 : CollatzResearch.WordTrace tailWord_8146085 prefixEnd_8146085 464761895264540682074927 := by
  unfold tailWord_8146085
  simp only [CollatzResearch.WordTrace]
  refine ⟨297112128693132760400791709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198074752462088506933861139 297112128693132760400791709)
  ·
    refine ⟨111417048259924785150296891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297112128693132760400791709 111417048259924785150296891)
    ·
      refine ⟨167125572389887177725445337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111417048259924785150296891 167125572389887177725445337)
      ·
        refine ⟨125344179292415383294084003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167125572389887177725445337 125344179292415383294084003)
        ·
          refine ⟨188016268938623074941126005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125344179292415383294084003 188016268938623074941126005)
          ·
            refine ⟨17626525212995913275730563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188016268938623074941126005 17626525212995913275730563)
            ·
              refine ⟨26439787819493869913595845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17626525212995913275730563 26439787819493869913595845)
              ·
                refine ⟨4957460216155100608799221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26439787819493869913595845 4957460216155100608799221)
                ·
                  refine ⟨464761895264540682074927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4957460216155100608799221 464761895264540682074927)
                  ·
                    rfl

theorem cell23_8146085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_8146085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146085 prefixEnd_8146085 := by exact prefixLift 8146085
  have htrace : WordTrace (prefixWord ++ tailWord_8146085) baseStart_8146085 baseEnd_8146085 := by
    simpa [prefixWord, tailWord_8146085, baseEnd_8146085] using wordTrace_append hprefix tailTrace_8146085
  have hstable : (prefixWord ++ tailWord_8146085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146085).length < 2 ^ (prefixWord ++ tailWord_8146085).sum := by decide
  have hdescent : baseEnd_8146085 < baseStart_8146085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146135 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 2, 4, 2]
def baseStart_8146135 : Nat := 118140960795 + 8146135 * 2 ^ 59
def prefixEnd_8146135 : Nat := 4983230072969 + 3 ^ 40 * 8146135 * 2
def baseEnd_8146135 : Nat := 4182882731413590943049113

theorem tailTrace_8146135 : CollatzResearch.WordTrace tailWord_8146135 prefixEnd_8146135 4182882731413590943049113 := by
  unfold tailWord_8146135
  simp only [CollatzResearch.WordTrace]
  refine ⟨297113952342951618940111859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198075968228634412626741239 297113952342951618940111859)
  ·
    refine ⟨445670928514427428410167789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297113952342951618940111859 445670928514427428410167789)
    ·
      refine ⟨167126598192910285653812921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445670928514427428410167789 167126598192910285653812921)
      ·
        refine ⟨125344948644682714240359691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167126598192910285653812921 125344948644682714240359691)
        ·
          refine ⟨188017422967024071360539537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125344948644682714240359691 188017422967024071360539537)
          ·
            refine ⟨141013067225268053520404653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188017422967024071360539537 141013067225268053520404653)
            ·
              refine ⟨52879900209475520070151745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141013067225268053520404653 52879900209475520070151745)
              ·
                refine ⟨39659925157106640052613809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52879900209475520070151745 39659925157106640052613809)
                ·
                  refine ⟨29744943867829980039460357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39659925157106640052613809 29744943867829980039460357)
                  ·
                    refine ⟨5577176975218121257398817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29744943867829980039460357 5577176975218121257398817)
                    ·
                      refine ⟨4182882731413590943049113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577176975218121257398817 4182882731413590943049113)
                      ·
                        rfl

theorem cell23_8146135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_8146135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146135 prefixEnd_8146135 := by exact prefixLift 8146135
  have htrace : WordTrace (prefixWord ++ tailWord_8146135) baseStart_8146135 baseEnd_8146135 := by
    simpa [prefixWord, tailWord_8146135, baseEnd_8146135] using wordTrace_append hprefix tailTrace_8146135
  have hstable : (prefixWord ++ tailWord_8146135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146135).length < 2 ^ (prefixWord ++ tailWord_8146135).sum := by decide
  have hdescent : baseEnd_8146135 < baseStart_8146135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146145 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 3, 4]
def baseStart_8146145 : Nat := 118140960795 + 8146145 * 2 ^ 59
def prefixEnd_8146145 : Nat := 4983230072969 + 3 ^ 40 * 8146145 * 2
def baseEnd_8146145 : Nat := 1394295955406711967974689

theorem tailTrace_8146145 : CollatzResearch.WordTrace tailWord_8146145 prefixEnd_8146145 1394295955406711967974689 := by
  unfold tailWord_8146145
  simp only [CollatzResearch.WordTrace]
  refine ⟨297114317072915390647975889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198076211381943593765317259 297114317072915390647975889)
  ·
    refine ⟨222835737804686542985981917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297114317072915390647975889 222835737804686542985981917)
    ·
      refine ⟨83563401676757453619743219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222835737804686542985981917 83563401676757453619743219)
      ·
        refine ⟨125345102515136180429614829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83563401676757453619743219 125345102515136180429614829)
        ·
          refine ⟨47004413443176067661105561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125345102515136180429614829 47004413443176067661105561)
          ·
            refine ⟨35253310082382050745829171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47004413443176067661105561 35253310082382050745829171)
            ·
              refine ⟨52879965123573076118743757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35253310082382050745829171 52879965123573076118743757)
              ·
                refine ⟨19829986921339903544528909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52879965123573076118743757 19829986921339903544528909)
                ·
                  refine ⟨7436245095502463829198341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19829986921339903544528909 7436245095502463829198341)
                  ·
                    refine ⟨1394295955406711967974689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7436245095502463829198341 1394295955406711967974689)
                    ·
                      rfl

theorem cell23_8146145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_8146145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146145 prefixEnd_8146145 := by exact prefixLift 8146145
  have htrace : WordTrace (prefixWord ++ tailWord_8146145) baseStart_8146145 baseEnd_8146145 := by
    simpa [prefixWord, tailWord_8146145, baseEnd_8146145] using wordTrace_append hprefix tailTrace_8146145
  have hstable : (prefixWord ++ tailWord_8146145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146145).length < 2 ^ (prefixWord ++ tailWord_8146145).sum := by decide
  have hdescent : baseEnd_8146145 < baseStart_8146145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146179 : List Nat := [1, 1, 1, 3, 2, 6, 1, 3, 1, 4]
def baseStart_8146179 : Nat := 118140960795 + 8146179 * 2 ^ 59
def prefixEnd_8146179 : Nat := 4983230072969 + 3 ^ 40 * 8146179 * 2
def baseEnd_8146179 : Nat := 1394301774854129590299637

theorem tailTrace_8146179 : CollatzResearch.WordTrace tailWord_8146179 prefixEnd_8146179 1394301774854129590299637 := by
  unfold tailWord_8146179
  simp only [CollatzResearch.WordTrace]
  refine ⟨297115557154792214454713591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198077038103194809636475727 297115557154792214454713591)
  ·
    refine ⟨445673335732188321682070387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297115557154792214454713591 445673335732188321682070387)
    ·
      refine ⟨668510003598282482523105581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445673335732188321682070387 668510003598282482523105581)
      ·
        refine ⟨250691251349355930946164593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668510003598282482523105581 250691251349355930946164593)
        ·
          refine ⟨188018438512016948209623445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250691251349355930946164593 188018438512016948209623445)
          ·
            refine ⟨8813364305250794447326099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188018438512016948209623445 8813364305250794447326099)
            ·
              refine ⟨13220046457876191670989149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8813364305250794447326099 13220046457876191670989149)
              ·
                refine ⟨4957517421703571876620931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13220046457876191670989149 4957517421703571876620931)
                ·
                  refine ⟨7436276132555357814931397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957517421703571876620931 7436276132555357814931397)
                  ·
                    refine ⟨1394301774854129590299637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7436276132555357814931397 1394301774854129590299637)
                    ·
                      rfl

theorem cell23_8146179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 4].length) (baseStart_8146179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146179 prefixEnd_8146179 := by exact prefixLift 8146179
  have htrace : WordTrace (prefixWord ++ tailWord_8146179) baseStart_8146179 baseEnd_8146179 := by
    simpa [prefixWord, tailWord_8146179, baseEnd_8146179] using wordTrace_append hprefix tailTrace_8146179
  have hstable : (prefixWord ++ tailWord_8146179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146179).length < 2 ^ (prefixWord ++ tailWord_8146179).sum := by decide
  have hdescent : baseEnd_8146179 < baseStart_8146179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146212 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_8146212 : Nat := 118140960795 + 8146212 * 2 ^ 59
def prefixEnd_8146212 : Nat := 4983230072969 + 3 ^ 40 * 8146212 * 2
def baseEnd_8146212 : Nat := 4182922269423987141786259

theorem tailTrace_8146212 : CollatzResearch.WordTrace tailWord_8146212 prefixEnd_8146212 4182922269423987141786259 := by
  unfold tailWord_8146212
  simp only [CollatzResearch.WordTrace]
  refine ⟨148558380381836330545332445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198077840509115107393776593 148558380381836330545332445)
  ·
    refine ⟨55709392643188623954499667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148558380381836330545332445 55709392643188623954499667)
    ·
      refine ⟨83564088964782935931749501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55709392643188623954499667 83564088964782935931749501)
      ·
        refine ⟨31336533361793600974406063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83564088964782935931749501 31336533361793600974406063)
        ·
          refine ⟨47004800042690401461609095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31336533361793600974406063 47004800042690401461609095)
          ·
            refine ⟨70507200064035602192413643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47004800042690401461609095 70507200064035602192413643)
            ·
              refine ⟨105760800096053403288620465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70507200064035602192413643 105760800096053403288620465)
              ·
                refine ⟨79320600072040052466465349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105760800096053403288620465 79320600072040052466465349)
                ·
                  refine ⟨14872612513507509837462253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79320600072040052466465349 14872612513507509837462253)
                  ·
                    refine ⟨5577229692565316189048345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14872612513507509837462253 5577229692565316189048345)
                    ·
                      refine ⟨4182922269423987141786259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577229692565316189048345 4182922269423987141786259)
                      ·
                        rfl

theorem cell23_8146212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_8146212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146212 prefixEnd_8146212 := by exact prefixLift 8146212
  have htrace : WordTrace (prefixWord ++ tailWord_8146212) baseStart_8146212 baseEnd_8146212 := by
    simpa [prefixWord, tailWord_8146212, baseEnd_8146212] using wordTrace_append hprefix tailTrace_8146212
  have hstable : (prefixWord ++ tailWord_8146212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146212).length < 2 ^ (prefixWord ++ tailWord_8146212).sum := by decide
  have hdescent : baseEnd_8146212 < baseStart_8146212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146229 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_8146229 : Nat := 118140960795 + 8146229 * 2 ^ 59
def prefixEnd_8146229 : Nat := 4983230072969 + 3 ^ 40 * 8146229 * 2
def baseEnd_8146229 : Nat := 4182930998595113575273681

theorem tailTrace_8146229 : CollatzResearch.WordTrace tailWord_8146229 prefixEnd_8146229 4182930998595113575273681 := by
  unfold tailWord_8146229
  simp only [CollatzResearch.WordTrace]
  refine ⟨297117380804611072994033741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198078253869740715329355827 297117380804611072994033741)
  ·
    refine ⟨111419017801729152372762653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297117380804611072994033741 111419017801729152372762653)
    ·
      refine ⟨41782131675648432139785995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111419017801729152372762653 41782131675648432139785995)
      ·
        refine ⟨62673197513472648209678993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41782131675648432139785995 62673197513472648209678993)
        ·
          refine ⟨47004898135104486157259245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62673197513472648209678993 47004898135104486157259245)
          ·
            refine ⟨17626836800664182308972217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47004898135104486157259245 17626836800664182308972217)
            ·
              refine ⟨13220127600498136731729163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17626836800664182308972217 13220127600498136731729163)
              ·
                refine ⟨19830191400747205097593745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13220127600498136731729163 19830191400747205097593745)
                ·
                  refine ⟨14872643550560403823195309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19830191400747205097593745 14872643550560403823195309)
                  ·
                    refine ⟨5577241331460151433698241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14872643550560403823195309 5577241331460151433698241)
                    ·
                      refine ⟨4182930998595113575273681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577241331460151433698241 4182930998595113575273681)
                      ·
                        rfl

theorem cell23_8146229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_8146229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146229 prefixEnd_8146229 := by exact prefixLift 8146229
  have htrace : WordTrace (prefixWord ++ tailWord_8146229) baseStart_8146229 baseEnd_8146229 := by
    simpa [prefixWord, tailWord_8146229, baseEnd_8146229] using wordTrace_append hprefix tailTrace_8146229
  have hstable : (prefixWord ++ tailWord_8146229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146229).length < 2 ^ (prefixWord ++ tailWord_8146229).sum := by decide
  have hdescent : baseEnd_8146229 < baseStart_8146229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146252 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_8146252 : Nat := 118140960795 + 8146252 * 2 ^ 59
def prefixEnd_8146252 : Nat := 4983230072969 + 3 ^ 40 * 8146252 * 2
def baseEnd_8146252 : Nat := 1394314269550055661762025

theorem tailTrace_8146252 : CollatzResearch.WordTrace tailWord_8146252 prefixEnd_8146252 1394314269550055661762025 := by
  unfold tailWord_8146252
  simp only [CollatzResearch.WordTrace]
  refine ⟨148559109841763873961060505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198078813122351831948080673 148559109841763873961060505)
  ·
    refine ⟨111419332381322905470795379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148559109841763873961060505 111419332381322905470795379)
    ·
      refine ⟨167128998571984358206193069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111419332381322905470795379 167128998571984358206193069)
      ·
        refine ⟨62673374464494134327322401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167128998571984358206193069 62673374464494134327322401)
        ·
          refine ⟨47005030848370600745491801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62673374464494134327322401 47005030848370600745491801)
          ·
            refine ⟨35253773136277950559118851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47005030848370600745491801 35253773136277950559118851)
            ·
              refine ⟨52880659704416925838678277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35253773136277950559118851 52880659704416925838678277)
              ·
                refine ⟨9915123694578173594752177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52880659704416925838678277 9915123694578173594752177)
                ·
                  refine ⟨7436342770933630196064133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9915123694578173594752177 7436342770933630196064133)
                  ·
                    refine ⟨1394314269550055661762025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7436342770933630196064133 1394314269550055661762025)
                    ·
                      rfl

theorem cell23_8146252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_8146252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146252 prefixEnd_8146252 := by exact prefixLift 8146252
  have htrace : WordTrace (prefixWord ++ tailWord_8146252) baseStart_8146252 baseEnd_8146252 := by
    simpa [prefixWord, tailWord_8146252, baseEnd_8146252] using wordTrace_append hprefix tailTrace_8146252
  have hstable : (prefixWord ++ tailWord_8146252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146252).length < 2 ^ (prefixWord ++ tailWord_8146252).sum := by decide
  have hdescent : baseEnd_8146252 < baseStart_8146252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146272 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 4]
def baseStart_8146272 : Nat := 118140960795 + 8146272 * 2 ^ 59
def prefixEnd_8146272 : Nat := 4983230072969 + 3 ^ 40 * 8146272 * 2
def baseEnd_8146272 : Nat := 4182953078263256907035983

theorem tailTrace_8146272 : CollatzResearch.WordTrace tailWord_8146272 prefixEnd_8146272 4182953078263256907035983 := by
  unfold tailWord_8146272
  simp only [CollatzResearch.WordTrace]
  refine ⟨148559474571727645668924535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198079299428970194225232713 148559474571727645668924535)
  ·
    refine ⟨222839211857591468503386803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148559474571727645668924535 222839211857591468503386803)
    ·
      refine ⟨334258817786387202755080205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222839211857591468503386803 334258817786387202755080205)
      ·
        refine ⟨125347056669895201033155077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334258817786387202755080205 125347056669895201033155077)
        ·
          refine ⟨23502573125605350193716577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125347056669895201033155077 23502573125605350193716577)
          ·
            refine ⟨17626929844204012645287433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23502573125605350193716577 17626929844204012645287433)
            ·
              refine ⟨13220197383153009483965575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17626929844204012645287433 13220197383153009483965575)
              ·
                refine ⟨19830296074729514225948363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13220197383153009483965575 19830296074729514225948363)
                ·
                  refine ⟨29745444112094271338922545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19830296074729514225948363 29745444112094271338922545)
                  ·
                    refine ⟨22309083084070703504191909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29745444112094271338922545 22309083084070703504191909)
                    ·
                      refine ⟨4182953078263256907035983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22309083084070703504191909 4182953078263256907035983)
                      ·
                        rfl

theorem cell23_8146272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_8146272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146272 prefixEnd_8146272 := by exact prefixLift 8146272
  have htrace : WordTrace (prefixWord ++ tailWord_8146272) baseStart_8146272 baseEnd_8146272 := by
    simpa [prefixWord, tailWord_8146272, baseEnd_8146272] using wordTrace_append hprefix tailTrace_8146272
  have hstable : (prefixWord ++ tailWord_8146272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146272).length < 2 ^ (prefixWord ++ tailWord_8146272).sum := by decide
  have hdescent : baseEnd_8146272 < baseStart_8146272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146293 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_8146293 : Nat := 118140960795 + 8146293 * 2 ^ 59
def prefixEnd_8146293 : Nat := 4983230072969 + 3 ^ 40 * 8146293 * 2
def baseEnd_8146293 : Nat := 4182963861357001324873387

theorem tailTrace_8146293 : CollatzResearch.WordTrace tailWord_8146293 prefixEnd_8146293 4182963861357001324873387 := by
  unfold tailWord_8146293
  simp only [CollatzResearch.WordTrace]
  refine ⟨297119715076379211924363533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198079810050919474616242355 297119715076379211924363533)
  ·
    refine ⟨111419893153642204471636325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297119715076379211924363533 111419893153642204471636325)
    ·
      refine ⟨20891229966307913338431811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111419893153642204471636325 20891229966307913338431811)
      ·
        refine ⟨31336844949461870007647717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20891229966307913338431811 31336844949461870007647717)
        ·
          refine ⟨5875658428024100626433947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31336844949461870007647717 5875658428024100626433947)
          ·
            refine ⟨8813487642036150939650921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875658428024100626433947 8813487642036150939650921)
            ·
              refine ⟨6610115731527113204738191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8813487642036150939650921 6610115731527113204738191)
              ·
                refine ⟨9915173597290669807107287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610115731527113204738191 9915173597290669807107287)
                ·
                  refine ⟨14872760395936004710660931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9915173597290669807107287 14872760395936004710660931)
                  ·
                    refine ⟨22309140593904007065991397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14872760395936004710660931 22309140593904007065991397)
                    ·
                      refine ⟨4182963861357001324873387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22309140593904007065991397 4182963861357001324873387)
                      ·
                        rfl

theorem cell23_8146293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_8146293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146293 prefixEnd_8146293 := by exact prefixLift 8146293
  have htrace : WordTrace (prefixWord ++ tailWord_8146293) baseStart_8146293 baseEnd_8146293 := by
    simpa [prefixWord, tailWord_8146293, baseEnd_8146293] using wordTrace_append hprefix tailTrace_8146293
  have hstable : (prefixWord ++ tailWord_8146293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146293).length < 2 ^ (prefixWord ++ tailWord_8146293).sum := by decide
  have hdescent : baseEnd_8146293 < baseStart_8146293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146309 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 3]
def baseStart_8146309 : Nat := 118140960795 + 8146309 * 2 ^ 59
def prefixEnd_8146309 : Nat := 4983230072969 + 3 ^ 40 * 8146309 * 2
def baseEnd_8146309 : Nat := 4182972077047473262273313

theorem tailTrace_8146309 : CollatzResearch.WordTrace tailWord_8146309 prefixEnd_8146309 4182972077047473262273313 := by
  unfold tailWord_8146309
  simp only [CollatzResearch.WordTrace]
  refine ⟨297120298644321246656945981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198080199096214164437963987 297120298644321246656945981)
  ·
    refine ⟨111420111991620467496354743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297120298644321246656945981 111420111991620467496354743)
    ·
      refine ⟨167130167987430701244532115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111420111991620467496354743 167130167987430701244532115)
      ·
        refine ⟨250695251981146051866798173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167130167987430701244532115 250695251981146051866798173)
        ·
          refine ⟨94010719492929769450049315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250695251981146051866798173 94010719492929769450049315)
          ·
            refine ⟨141016079239394654175073973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94010719492929769450049315 141016079239394654175073973)
            ·
              refine ⟨13220257428693248828913185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141016079239394654175073973 13220257428693248828913185)
              ·
                refine ⟨9915193071519936621684889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13220257428693248828913185 9915193071519936621684889)
                ·
                  refine ⟨7436394803639952466263667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9915193071519936621684889 7436394803639952466263667)
                  ·
                    refine ⟨11154592205459928699395501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7436394803639952466263667 11154592205459928699395501)
                    ·
                      refine ⟨4182972077047473262273313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11154592205459928699395501 4182972077047473262273313)
                      ·
                        rfl

theorem cell23_8146309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_8146309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146309 prefixEnd_8146309 := by exact prefixLift 8146309
  have htrace : WordTrace (prefixWord ++ tailWord_8146309) baseStart_8146309 baseEnd_8146309 := by
    simpa [prefixWord, tailWord_8146309, baseEnd_8146309] using wordTrace_append hprefix tailTrace_8146309
  have hstable : (prefixWord ++ tailWord_8146309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146309).length < 2 ^ (prefixWord ++ tailWord_8146309).sum := by decide
  have hdescent : baseEnd_8146309 < baseStart_8146309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146325 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_8146325 : Nat := 118140960795 + 8146325 * 2 ^ 59
def prefixEnd_8146325 : Nat := 4983230072969 + 3 ^ 40 * 8146325 * 2
def baseEnd_8146325 : Nat := 1394326764245981733224413

theorem tailTrace_8146325 : CollatzResearch.WordTrace tailWord_8146325 prefixEnd_8146325 1394326764245981733224413 := by
  unfold tailWord_8146325
  simp only [CollatzResearch.WordTrace]
  refine ⟨297120882212263281389528429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198080588141508854259685619 297120882212263281389528429)
  ·
    refine ⟨111420330829598730521073161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297120882212263281389528429 111420330829598730521073161)
    ·
      refine ⟨83565248122199047890804871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111420330829598730521073161 83565248122199047890804871)
      ·
        refine ⟨125347872183298571836207307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83565248122199047890804871 125347872183298571836207307)
        ·
          refine ⟨188021808274947857754310961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125347872183298571836207307 188021808274947857754310961)
          ·
            refine ⟨141016356206210893315733221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188021808274947857754310961 141016356206210893315733221)
            ·
              refine ⟨26440566788664542496699979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141016356206210893315733221 26440566788664542496699979)
              ·
                refine ⟨39660850182996813745049969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26440566788664542496699979 39660850182996813745049969)
                ·
                  refine ⟨29745637637247610308787477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39660850182996813745049969 29745637637247610308787477)
                  ·
                    refine ⟨1394326764245981733224413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29745637637247610308787477 1394326764245981733224413)
                    ·
                      rfl

theorem cell23_8146325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_8146325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146325 prefixEnd_8146325 := by exact prefixLift 8146325
  have htrace : WordTrace (prefixWord ++ tailWord_8146325) baseStart_8146325 baseEnd_8146325 := by
    simpa [prefixWord, tailWord_8146325, baseEnd_8146325] using wordTrace_append hprefix tailTrace_8146325
  have hstable : (prefixWord ++ tailWord_8146325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146325).length < 2 ^ (prefixWord ++ tailWord_8146325).sum := by decide
  have hdescent : baseEnd_8146325 < baseStart_8146325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146365 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_8146365 : Nat := 118140960795 + 8146365 * 2 ^ 59
def prefixEnd_8146365 : Nat := 4983230072969 + 3 ^ 40 * 8146365 * 2
def baseEnd_8146365 : Nat := 4183000831964125043173055

theorem tailTrace_8146365 : CollatzResearch.WordTrace tailWord_8146365 prefixEnd_8146365 4183000831964125043173055 := by
  unfold tailWord_8146365
  simp only [CollatzResearch.WordTrace]
  refine ⟨297122341132118368220984549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198081560754745578813989699 297122341132118368220984549)
  ·
    refine ⟨55710438962272194041434603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297122341132118368220984549 55710438962272194041434603)
    ·
      refine ⟨83565658443408291062151905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55710438962272194041434603 83565658443408291062151905)
      ·
        refine ⟨62674243832556218296613929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83565658443408291062151905 62674243832556218296613929)
        ·
          refine ⟨47005682874417163722460447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62674243832556218296613929 47005682874417163722460447)
          ·
            refine ⟨70508524311625745583690671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47005682874417163722460447 70508524311625745583690671)
            ·
              refine ⟨105762786467438618375536007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70508524311625745583690671 105762786467438618375536007)
              ·
                refine ⟨158644179701157927563304011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105762786467438618375536007 158644179701157927563304011)
                ·
                  refine ⟨237966269551736891344956017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158644179701157927563304011 237966269551736891344956017)
                  ·
                    refine ⟨178474702163802668508717013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237966269551736891344956017 178474702163802668508717013)
                    ·
                      refine ⟨4183000831964125043173055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178474702163802668508717013 4183000831964125043173055)
                      ·
                        rfl

theorem cell23_8146365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_8146365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146365 prefixEnd_8146365 := by exact prefixLift 8146365
  have htrace : WordTrace (prefixWord ++ tailWord_8146365) baseStart_8146365 baseEnd_8146365 := by
    simpa [prefixWord, tailWord_8146365, baseEnd_8146365] using wordTrace_append hprefix tailTrace_8146365
  have hstable : (prefixWord ++ tailWord_8146365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146365).length < 2 ^ (prefixWord ++ tailWord_8146365).sum := by decide
  have hdescent : baseEnd_8146365 < baseStart_8146365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146366 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_8146366 : Nat := 118140960795 + 8146366 * 2 ^ 59
def prefixEnd_8146366 : Nat := 4983230072969 + 3 ^ 40 * 8146366 * 2
def baseEnd_8146366 : Nat := 4183001345444779539260551

theorem tailTrace_8146366 : CollatzResearch.WordTrace tailWord_8146366 prefixEnd_8146366 4183001345444779539260551 := by
  unfold tailWord_8146366
  simp only [CollatzResearch.WordTrace]
  refine ⟨37140297200639343173971369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198081585070076496927847301 37140297200639343173971369)
  ·
    refine ⟨27855222900479507380478527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37140297200639343173971369 27855222900479507380478527)
    ·
      refine ⟨41782834350719261070717791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27855222900479507380478527 41782834350719261070717791)
      ·
        refine ⟨62674251526078891606076687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41782834350719261070717791 62674251526078891606076687)
        ·
          refine ⟨94011377289118337409115031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62674251526078891606076687 94011377289118337409115031)
          ·
            refine ⟨141017065933677506113672547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94011377289118337409115031 141017065933677506113672547)
            ·
              refine ⟨211525598900516259170508821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141017065933677506113672547 211525598900516259170508821)
              ·
                refine ⟨9915262448461699648617601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211525598900516259170508821 9915262448461699648617601)
                ·
                  refine ⟨7436446836346274736463201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9915262448461699648617601 7436446836346274736463201)
                  ·
                    refine ⟨5577335127259706052347401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7436446836346274736463201 5577335127259706052347401)
                    ·
                      refine ⟨4183001345444779539260551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577335127259706052347401 4183001345444779539260551)
                      ·
                        rfl

theorem cell23_8146366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_8146366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146366 prefixEnd_8146366 := by exact prefixLift 8146366
  have htrace : WordTrace (prefixWord ++ tailWord_8146366) baseStart_8146366 baseEnd_8146366 := by
    simpa [prefixWord, tailWord_8146366, baseEnd_8146366] using wordTrace_append hprefix tailTrace_8146366
  have hstable : (prefixWord ++ tailWord_8146366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146366).length < 2 ^ (prefixWord ++ tailWord_8146366).sum := by decide
  have hdescent : baseEnd_8146366 < baseStart_8146366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146382 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_8146382 : Nat := 118140960795 + 8146382 * 2 ^ 59
def prefixEnd_8146382 : Nat := 4983230072969 + 3 ^ 40 * 8146382 * 2
def baseEnd_8146382 : Nat := 4183009561135251476660477

theorem tailTrace_8146382 : CollatzResearch.WordTrace tailWord_8146382 prefixEnd_8146382 4183009561135251476660477 := by
  unfold tailWord_8146382
  simp only [CollatzResearch.WordTrace]
  refine ⟨37140370146632097515544175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198081974115371186749568933 37140370146632097515544175)
  ·
    refine ⟨55710555219948146273316263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37140370146632097515544175 55710555219948146273316263)
    ·
      refine ⟨83565832829922219409974395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55710555219948146273316263 83565832829922219409974395)
      ·
        refine ⟨125348749244883329114961593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83565832829922219409974395 125348749244883329114961593)
        ·
          refine ⟨94011561933662496836221195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125348749244883329114961593 94011561933662496836221195)
          ·
            refine ⟨141017342900493745254331793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94011561933662496836221195 141017342900493745254331793)
            ·
              refine ⟨105763007175370308940748845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141017342900493745254331793 105763007175370308940748845)
              ·
                refine ⟨39661127690763865852780817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105763007175370308940748845 39661127690763865852780817)
                ·
                  refine ⟨29745845768072899389585613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39661127690763865852780817 29745845768072899389585613)
                  ·
                    refine ⟨11154692163027337271094605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29745845768072899389585613 11154692163027337271094605)
                    ·
                      refine ⟨4183009561135251476660477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11154692163027337271094605 4183009561135251476660477)
                      ·
                        rfl

theorem cell23_8146382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_8146382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146382 prefixEnd_8146382 := by exact prefixLift 8146382
  have htrace : WordTrace (prefixWord ++ tailWord_8146382) baseStart_8146382 baseEnd_8146382 := by
    simpa [prefixWord, tailWord_8146382, baseEnd_8146382] using wordTrace_append hprefix tailTrace_8146382
  have hstable : (prefixWord ++ tailWord_8146382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146382).length < 2 ^ (prefixWord ++ tailWord_8146382).sum := by decide
  have hdescent : baseEnd_8146382 < baseStart_8146382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146425 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_8146425 : Nat := 118140960795 + 8146425 * 2 ^ 59
def prefixEnd_8146425 : Nat := 4983230072969 + 3 ^ 40 * 8146425 * 2
def baseEnd_8146425 : Nat := 4183031640803394808422779

theorem tailTrace_8146425 : CollatzResearch.WordTrace tailWord_8146425 prefixEnd_8146425 4183031640803394808422779 := by
  unfold tailWord_8146425
  simp only [CollatzResearch.WordTrace]
  refine ⟨297124529511900998468168729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198083019674600665645445819 297124529511900998468168729)
  ·
    refine ⟨222843397133925748851126547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297124529511900998468168729 222843397133925748851126547)
    ·
      refine ⟨334265095700888623276689821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222843397133925748851126547 334265095700888623276689821)
      ·
        refine ⟨125349410887833233728758683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334265095700888623276689821 125349410887833233728758683)
        ·
          refine ⟨188024116331749850593138025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125349410887833233728758683 188024116331749850593138025)
          ·
            refine ⟨141018087248812387944853519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188024116331749850593138025 141018087248812387944853519)
            ·
              refine ⟨211527130873218581917280279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141018087248812387944853519 211527130873218581917280279)
              ·
                refine ⟨317290696309827872875920419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211527130873218581917280279 317290696309827872875920419)
                ·
                  refine ⟨475936044464741809313880629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317290696309827872875920419 475936044464741809313880629)
                  ·
                    refine ⟨44619004168569544623176309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 475936044464741809313880629 44619004168569544623176309)
                    ·
                      refine ⟨4183031640803394808422779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44619004168569544623176309 4183031640803394808422779)
                      ·
                        rfl

theorem cell23_8146425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_8146425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146425 prefixEnd_8146425 := by exact prefixLift 8146425
  have htrace : WordTrace (prefixWord ++ tailWord_8146425) baseStart_8146425 baseEnd_8146425 := by
    simpa [prefixWord, tailWord_8146425, baseEnd_8146425] using wordTrace_append hprefix tailTrace_8146425
  have hstable : (prefixWord ++ tailWord_8146425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146425).length < 2 ^ (prefixWord ++ tailWord_8146425).sum := by decide
  have hdescent : baseEnd_8146425 < baseStart_8146425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146435 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 6]
def baseStart_8146435 : Nat := 118140960795 + 8146435 * 2 ^ 59
def prefixEnd_8146435 : Nat := 4983230072969 + 3 ^ 40 * 8146435 * 2
def baseEnd_8146435 : Nat := 4183036775609939769297733

theorem tailTrace_8146435 : CollatzResearch.WordTrace tailWord_8146435 prefixEnd_8146435 4183036775609939769297733 := by
  unfold tailWord_8146435
  simp only [CollatzResearch.WordTrace]
  refine ⟨297124894241864770176032759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198083262827909846784021839 297124894241864770176032759)
  ·
    refine ⟨445687341362797155264049139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297124894241864770176032759 445687341362797155264049139)
    ·
      refine ⟨668531012044195732896073709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445687341362797155264049139 668531012044195732896073709)
      ·
        refine ⟨250699129516573399836027641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668531012044195732896073709 250699129516573399836027641)
        ·
          refine ⟨188024347137430049877020731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250699129516573399836027641 188024347137430049877020731)
          ·
            refine ⟨282036520706145074815531097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188024347137430049877020731 282036520706145074815531097)
            ·
              refine ⟨211527390529608806111648323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282036520706145074815531097 211527390529608806111648323)
              ·
                refine ⟨317291085794413209167472485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211527390529608806111648323 317291085794413209167472485)
                ·
                  refine ⟨59492078586452476718901091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317291085794413209167472485 59492078586452476718901091)
                  ·
                    refine ⟨89238117879678715078351637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59492078586452476718901091 89238117879678715078351637)
                    ·
                      refine ⟨4183036775609939769297733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89238117879678715078351637 4183036775609939769297733)
                      ·
                        rfl

theorem cell23_8146435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_8146435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146435 prefixEnd_8146435 := by exact prefixLift 8146435
  have htrace : WordTrace (prefixWord ++ tailWord_8146435) baseStart_8146435 baseEnd_8146435 := by
    simpa [prefixWord, tailWord_8146435, baseEnd_8146435] using wordTrace_append hprefix tailTrace_8146435
  have hstable : (prefixWord ++ tailWord_8146435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146435).length < 2 ^ (prefixWord ++ tailWord_8146435).sum := by decide
  have hdescent : baseEnd_8146435 < baseStart_8146435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146439 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_8146439 : Nat := 118140960795 + 8146439 * 2 ^ 59
def prefixEnd_8146439 : Nat := 4983230072969 + 3 ^ 40 * 8146439 * 2
def baseEnd_8146439 : Nat := 4183038829532557753647715

theorem tailTrace_8146439 : CollatzResearch.WordTrace tailWord_8146439 prefixEnd_8146439 4183038829532557753647715 := by
  unfold tailWord_8146439
  simp only [CollatzResearch.WordTrace]
  refine ⟨297125040133850278859178371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198083360089233519239452247 297125040133850278859178371)
  ·
    refine ⟨445687560200775418288767557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297125040133850278859178371 445687560200775418288767557)
    ·
      refine ⟨83566417537645390929143917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 445687560200775418288767557 83566417537645390929143917)
      ·
        refine ⟨31337406576617021598428969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83566417537645390929143917 31337406576617021598428969)
        ·
          refine ⟨23503054932462766198821727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31337406576617021598428969 23503054932462766198821727)
          ·
            refine ⟨35254582398694149298232591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23503054932462766198821727 35254582398694149298232591)
            ·
              refine ⟨52881873598041223947348887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35254582398694149298232591 52881873598041223947348887)
              ·
                refine ⟨79322810397061835921023331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52881873598041223947348887 79322810397061835921023331)
                ·
                  refine ⟨118984215595592753881534997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79322810397061835921023331 118984215595592753881534997)
                  ·
                    refine ⟨5577385106043410338196953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118984215595592753881534997 5577385106043410338196953)
                    ·
                      refine ⟨4183038829532557753647715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577385106043410338196953 4183038829532557753647715)
                      ·
                        rfl

theorem cell23_8146439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_8146439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146439 prefixEnd_8146439 := by exact prefixLift 8146439
  have htrace : WordTrace (prefixWord ++ tailWord_8146439) baseStart_8146439 baseEnd_8146439 := by
    simpa [prefixWord, tailWord_8146439, baseEnd_8146439] using wordTrace_append hprefix tailTrace_8146439
  have hstable : (prefixWord ++ tailWord_8146439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146439).length < 2 ^ (prefixWord ++ tailWord_8146439).sum := by decide
  have hdescent : baseEnd_8146439 < baseStart_8146439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146456 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 2, 1, 4]
def baseStart_8146456 : Nat := 118140960795 + 8146456 * 2 ^ 59
def prefixEnd_8146456 : Nat := 4983230072969 + 3 ^ 40 * 8146456 * 2
def baseEnd_8146456 : Nat := 4183047558703684187135137

theorem tailTrace_8146456 : CollatzResearch.WordTrace tailWord_8146456 prefixEnd_8146456 4183047558703684187135137 := by
  unfold tailWord_8146456
  simp only [CollatzResearch.WordTrace]
  refine ⟨148562830087394345381273611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198083773449859127175031481 148562830087394345381273611)
  ·
    refine ⟨222844245131091518071910417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148562830087394345381273611 222844245131091518071910417)
    ·
      refine ⟨167133183848318638553932813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222844245131091518071910417 167133183848318638553932813)
      ·
        refine ⟨62674943943119489457724805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167133183848318638553932813 62674943943119489457724805)
        ·
          refine ⟨11751551989334904273323401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62674943943119489457724805 11751551989334904273323401)
          ·
            refine ⟨8813663992001178204992551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11751551989334904273323401 8813663992001178204992551)
            ·
              refine ⟨13220495988001767307488827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8813663992001178204992551 13220495988001767307488827)
              ·
                refine ⟨19830743982002650961233241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13220495988001767307488827 19830743982002650961233241)
                ·
                  refine ⟨14873057986501988220924931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19830743982002650961233241 14873057986501988220924931)
                  ·
                    refine ⟨22309586979752982331387397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14873057986501988220924931 22309586979752982331387397)
                    ·
                      refine ⟨4183047558703684187135137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22309586979752982331387397 4183047558703684187135137)
                      ·
                        rfl

theorem cell23_8146456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_8146456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146456 prefixEnd_8146456 := by exact prefixLift 8146456
  have htrace : WordTrace (prefixWord ++ tailWord_8146456) baseStart_8146456 baseEnd_8146456 := by
    simpa [prefixWord, tailWord_8146456, baseEnd_8146456] using wordTrace_append hprefix tailTrace_8146456
  have hstable : (prefixWord ++ tailWord_8146456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146456).length < 2 ^ (prefixWord ++ tailWord_8146456).sum := by decide
  have hdescent : baseEnd_8146456 < baseStart_8146456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146466 : List Nat := [3, 3, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_8146466 : Nat := 118140960795 + 8146466 * 2 ^ 59
def prefixEnd_8146466 : Nat := 4983230072969 + 3 ^ 40 * 8146466 * 2
def baseEnd_8146466 : Nat := 1394350897836743049336697

theorem tailTrace_8146466 : CollatzResearch.WordTrace tailWord_8146466 prefixEnd_8146466 1394350897836743049336697 := by
  unfold tailWord_8146466
  simp only [CollatzResearch.WordTrace]
  refine ⟨74281506226188115617602813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198084016603168308313607501 74281506226188115617602813)
  ·
    refine ⟨27855564834820543356601055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74281506226188115617602813 27855564834820543356601055)
    ·
      refine ⟨41783347252230815034901583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27855564834820543356601055 41783347252230815034901583)
      ·
        refine ⟨62675020878346222552352375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41783347252230815034901583 62675020878346222552352375)
        ·
          refine ⟨94012531317519333828528563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62675020878346222552352375 94012531317519333828528563)
          ·
            refine ⟨141018796976279000742792845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94012531317519333828528563 141018796976279000742792845)
            ·
              refine ⟨52882048866104625278547317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141018796976279000742792845 52882048866104625278547317)
              ·
                refine ⟨4957692081197308619863811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52882048866104625278547317 4957692081197308619863811)
                ·
                  refine ⟨7436538121795962929795717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957692081197308619863811 7436538121795962929795717)
                  ·
                    refine ⟨1394350897836743049336697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7436538121795962929795717 1394350897836743049336697)
                    ·
                      rfl

theorem cell23_8146466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_8146466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146466 prefixEnd_8146466 := by exact prefixLift 8146466
  have htrace : WordTrace (prefixWord ++ tailWord_8146466) baseStart_8146466 baseEnd_8146466 := by
    simpa [prefixWord, tailWord_8146466, baseEnd_8146466] using wordTrace_append hprefix tailTrace_8146466
  have hstable : (prefixWord ++ tailWord_8146466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146466).length < 2 ^ (prefixWord ++ tailWord_8146466).sum := by decide
  have hdescent : baseEnd_8146466 < baseStart_8146466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146516 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_8146516 : Nat := 118140960795 + 8146516 * 2 ^ 59
def prefixEnd_8146516 : Nat := 4983230072969 + 3 ^ 40 * 8146516 * 2
def baseEnd_8146516 : Nat := 4183078367542953952384861

theorem tailTrace_8146516 : CollatzResearch.WordTrace tailWord_8146516 prefixEnd_8146516 4183078367542953952384861 := by
  unfold tailWord_8146516
  simp only [CollatzResearch.WordTrace]
  refine ⟨148563924277285660504865701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198085232369714214006487601 148563924277285660504865701)
  ·
    refine ⟨27855735801991061344662319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148563924277285660504865701 27855735801991061344662319)
    ·
      refine ⟨41783603702986592016993479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27855735801991061344662319 41783603702986592016993479)
      ·
        refine ⟨62675405554479888025490219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41783603702986592016993479 62675405554479888025490219)
        ·
          refine ⟨94013108331719832038235329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62675405554479888025490219 94013108331719832038235329)
          ·
            refine ⟨70509831248789874028676497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94013108331719832038235329 70509831248789874028676497)
            ·
              refine ⟨52882373436592405521507373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70509831248789874028676497 52882373436592405521507373)
              ·
                refine ⟨19830890038722152070565265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52882373436592405521507373 19830890038722152070565265)
                ·
                  refine ⟨14873167529041614052923949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19830890038722152070565265 14873167529041614052923949)
                  ·
                    refine ⟨5577437823390605269846481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14873167529041614052923949 5577437823390605269846481)
                    ·
                      refine ⟨4183078367542953952384861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577437823390605269846481 4183078367542953952384861)
                      ·
                        rfl

theorem cell23_8146516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_8146516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146516 prefixEnd_8146516 := by exact prefixLift 8146516
  have htrace : WordTrace (prefixWord ++ tailWord_8146516) baseStart_8146516 baseEnd_8146516 := by
    simpa [prefixWord, tailWord_8146516, baseEnd_8146516] using wordTrace_append hprefix tailTrace_8146516
  have hstable : (prefixWord ++ tailWord_8146516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146516).length < 2 ^ (prefixWord ++ tailWord_8146516).sum := by decide
  have hdescent : baseEnd_8146516 < baseStart_8146516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146522 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_8146522 : Nat := 118140960795 + 8146522 * 2 ^ 59
def prefixEnd_8146522 : Nat := 4983230072969 + 3 ^ 40 * 8146522 * 2
def baseEnd_8146522 : Nat := 1394360482808960309636611

theorem tailTrace_8146522 : CollatzResearch.WordTrace tailWord_8146522 prefixEnd_8146522 1394360482808960309636611 := by
  unfold tailWord_8146522
  simp only [CollatzResearch.WordTrace]
  refine ⟨74282016848137396008612455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198085378261699722689633213 74282016848137396008612455)
  ·
    refine ⟨111423025272206094012918683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74282016848137396008612455 111423025272206094012918683)
    ·
      refine ⟨167134537908309141019378025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111423025272206094012918683 167134537908309141019378025)
      ·
        refine ⟨125350903431231855764533519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167134537908309141019378025 125350903431231855764533519)
        ·
          refine ⟨188026355146847783646800279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125350903431231855764533519 188026355146847783646800279)
          ·
            refine ⟨282039532720271675470200419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188026355146847783646800279 282039532720271675470200419)
            ·
              refine ⟨423059299080407513205300629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282039532720271675470200419 423059299080407513205300629)
              ·
                refine ⟨19830904644394102181498467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 423059299080407513205300629 19830904644394102181498467)
                ·
                  refine ⟨29746356966591153272247701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19830904644394102181498467 29746356966591153272247701)
                  ·
                    refine ⟨1394360482808960309636611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29746356966591153272247701 1394360482808960309636611)
                    ·
                      rfl

theorem cell23_8146522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_8146522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146522 prefixEnd_8146522 := by exact prefixLift 8146522
  have htrace : WordTrace (prefixWord ++ tailWord_8146522) baseStart_8146522 baseEnd_8146522 := by
    simpa [prefixWord, tailWord_8146522, baseEnd_8146522] using wordTrace_append hprefix tailTrace_8146522
  have hstable : (prefixWord ++ tailWord_8146522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146522).length < 2 ^ (prefixWord ++ tailWord_8146522).sum := by decide
  have hdescent : baseEnd_8146522 < baseStart_8146522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146529 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_8146529 : Nat := 118140960795 + 8146529 * 2 ^ 59
def prefixEnd_8146529 : Nat := 4983230072969 + 3 ^ 40 * 8146529 * 2
def baseEnd_8146529 : Nat := 4183085042791462401522301

theorem tailTrace_8146529 : CollatzResearch.WordTrace tailWord_8146529 prefixEnd_8146529 4183085042791462401522301 := by
  unfold tailWord_8146529
  simp only [CollatzResearch.WordTrace]
  refine ⟨297128322703524224229954641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198085548469016149486636427 297128322703524224229954641)
  ·
    refine ⟨222846242027643168172465981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297128322703524224229954641 222846242027643168172465981)
    ·
      refine ⟨83567340760366188064674743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222846242027643168172465981 83567340760366188064674743)
      ·
        refine ⟨125351011140549282097012115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83567340760366188064674743 125351011140549282097012115)
        ·
          refine ⟨188026516710823923145518173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125351011140549282097012115 188026516710823923145518173)
          ·
            refine ⟨70509943766558971179569315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188026516710823923145518173 70509943766558971179569315)
            ·
              refine ⟨105764915649838456769353973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70509943766558971179569315 105764915649838456769353973)
              ·
                refine ⟨9915460842172355322126935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105764915649838456769353973 9915460842172355322126935)
                ·
                  refine ⟨14873191263258532983190403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9915460842172355322126935 14873191263258532983190403)
                  ·
                    refine ⟨22309786894887799474785605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14873191263258532983190403 22309786894887799474785605)
                    ·
                      refine ⟨4183085042791462401522301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22309786894887799474785605 4183085042791462401522301)
                      ·
                        rfl

theorem cell23_8146529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_8146529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146529 prefixEnd_8146529 := by exact prefixLift 8146529
  have htrace : WordTrace (prefixWord ++ tailWord_8146529) baseStart_8146529 baseEnd_8146529 := by
    simpa [prefixWord, tailWord_8146529, baseEnd_8146529] using wordTrace_append hprefix tailTrace_8146529
  have hstable : (prefixWord ++ tailWord_8146529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146529).length < 2 ^ (prefixWord ++ tailWord_8146529).sum := by decide
  have hdescent : baseEnd_8146529 < baseStart_8146529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146580 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_8146580 : Nat := 118140960795 + 8146580 * 2 ^ 59
def prefixEnd_8146580 : Nat := 4983230072969 + 3 ^ 40 * 8146580 * 2
def baseEnd_8146580 : Nat := 4183111230304841701984567

theorem tailTrace_8146580 : CollatzResearch.WordTrace tailWord_8146580 prefixEnd_8146580 4183111230304841701984567 := by
  unfold tailWord_8146580
  simp only [CollatzResearch.WordTrace]
  refine ⟨148565091413169729970030597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198086788550892973293374129 148565091413169729970030597)
  ·
    refine ⟨27855954639969324369380737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148565091413169729970030597 27855954639969324369380737)
    ·
      refine ⟨20891965979976993277035553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27855954639969324369380737 20891965979976993277035553)
      ·
        refine ⟨15668974484982744957776665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20891965979976993277035553 15668974484982744957776665)
        ·
          refine ⟨11751730863737058718332499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15668974484982744957776665 11751730863737058718332499)
          ·
            refine ⟨17627596295605588077498749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11751730863737058718332499 17627596295605588077498749)
            ·
              refine ⟨6610348610852095529062031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17627596295605588077498749 6610348610852095529062031)
              ·
                refine ⟨9915522916278143293593047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610348610852095529062031 9915522916278143293593047)
                ·
                  refine ⟨14873284374417214940389571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9915522916278143293593047 14873284374417214940389571)
                  ·
                    refine ⟨22309926561625822410584357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14873284374417214940389571 22309926561625822410584357)
                    ·
                      refine ⟨4183111230304841701984567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22309926561625822410584357 4183111230304841701984567)
                      ·
                        rfl

theorem cell23_8146580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_8146580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146580 prefixEnd_8146580 := by exact prefixLift 8146580
  have htrace : WordTrace (prefixWord ++ tailWord_8146580) baseStart_8146580 baseEnd_8146580 := by
    simpa [prefixWord, tailWord_8146580, baseEnd_8146580] using wordTrace_append hprefix tailTrace_8146580
  have hstable : (prefixWord ++ tailWord_8146580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146580).length < 2 ^ (prefixWord ++ tailWord_8146580).sum := by decide
  have hdescent : baseEnd_8146580 < baseStart_8146580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146583 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 1, 2, 3]
def baseStart_8146583 : Nat := 118140960795 + 8146583 * 2 ^ 59
def prefixEnd_8146583 : Nat := 4983230072969 + 3 ^ 40 * 8146583 * 2
def baseEnd_8146583 : Nat := 4183112770746805190247053

theorem tailTrace_8146583 : CollatzResearch.WordTrace tailWord_8146583 prefixEnd_8146583 4183112770746805190247053 := by
  unfold tailWord_8146583
  simp only [CollatzResearch.WordTrace]
  refine ⟨297130292245328591452420403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198086861496885727634946935 297130292245328591452420403)
  ·
    refine ⟨445695438367992887178630605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297130292245328591452420403 445695438367992887178630605)
    ·
      refine ⟨167135789387997332691986477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445695438367992887178630605 167135789387997332691986477)
      ·
        refine ⟨62675921020498999759494929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167135789387997332691986477 62675921020498999759494929)
        ·
          refine ⟨47006940765374249819621197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62675921020498999759494929 47006940765374249819621197)
          ·
            refine ⟨17627602787015343682357949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47006940765374249819621197 17627602787015343682357949)
            ·
              refine ⟨6610351045130753880884231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17627602787015343682357949 6610351045130753880884231)
              ·
                refine ⟨9915526567696130821326347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610351045130753880884231 9915526567696130821326347)
                ·
                  refine ⟨14873289851544196231989521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9915526567696130821326347 14873289851544196231989521)
                  ·
                    refine ⟨11154967388658147173992141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14873289851544196231989521 11154967388658147173992141)
                    ·
                      refine ⟨4183112770746805190247053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11154967388658147173992141 4183112770746805190247053)
                      ·
                        rfl

theorem cell23_8146583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_8146583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146583 prefixEnd_8146583 := by exact prefixLift 8146583
  have htrace : WordTrace (prefixWord ++ tailWord_8146583) baseStart_8146583 baseEnd_8146583 := by
    simpa [prefixWord, tailWord_8146583, baseEnd_8146583] using wordTrace_append hprefix tailTrace_8146583
  have hstable : (prefixWord ++ tailWord_8146583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146583).length < 2 ^ (prefixWord ++ tailWord_8146583).sum := by decide
  have hdescent : baseEnd_8146583 < baseStart_8146583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146613 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_8146613 : Nat := 118140960795 + 8146613 * 2 ^ 59
def prefixEnd_8146613 : Nat := 4983230072969 + 3 ^ 40 * 8146613 * 2
def baseEnd_8146613 : Nat := 4183128175166440072871915

theorem tailTrace_8146613 : CollatzResearch.WordTrace tailWord_8146613 prefixEnd_8146613 4183128175166440072871915 := by
  unfold tailWord_8146613
  simp only [CollatzResearch.WordTrace]
  refine ⟨297131386435219906576012493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198087590956813271050674995 297131386435219906576012493)
  ·
    refine ⟨111424269913207464966004685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297131386435219906576012493 111424269913207464966004685)
    ·
      refine ⟨41784101217452799362251757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111424269913207464966004685 41784101217452799362251757)
      ·
        refine ⟨15669037956544799760844409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41784101217452799362251757 15669037956544799760844409)
        ·
          refine ⟨11751778467408599820633307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15669037956544799760844409 11751778467408599820633307)
          ·
            refine ⟨17627667701112899730949961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11751778467408599820633307 17627667701112899730949961)
            ·
              refine ⟨13220750775834674798212471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17627667701112899730949961 13220750775834674798212471)
              ·
                refine ⟨19831126163752012197318707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13220750775834674798212471 19831126163752012197318707)
                ·
                  refine ⟨29746689245628018295978061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19831126163752012197318707 29746689245628018295978061)
                  ·
                    refine ⟨11155008467110506860991773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29746689245628018295978061 11155008467110506860991773)
                    ·
                      refine ⟨4183128175166440072871915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11155008467110506860991773 4183128175166440072871915)
                      ·
                        rfl

theorem cell23_8146613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_8146613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146613 prefixEnd_8146613 := by exact prefixLift 8146613
  have htrace : WordTrace (prefixWord ++ tailWord_8146613) baseStart_8146613 baseEnd_8146613 := by
    simpa [prefixWord, tailWord_8146613, baseEnd_8146613] using wordTrace_append hprefix tailTrace_8146613
  have hstable : (prefixWord ++ tailWord_8146613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146613).length < 2 ^ (prefixWord ++ tailWord_8146613).sum := by decide
  have hdescent : baseEnd_8146613 < baseStart_8146613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146630 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_8146630 : Nat := 118140960795 + 8146630 * 2 ^ 59
def prefixEnd_8146630 : Nat := 4983230072969 + 3 ^ 40 * 8146630 * 2
def baseEnd_8146630 : Nat := 4183136904337566506359337

theorem tailTrace_8146630 : CollatzResearch.WordTrace tailWord_8146630 prefixEnd_8146630 4183136904337566506359337 := by
  unfold tailWord_8146630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9285375202379947452480667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198088004317438878986254229 9285375202379947452480667)
  ·
    refine ⟨13928062803569921178721001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9285375202379947452480667 13928062803569921178721001)
    ·
      refine ⟨10446047102677440884040751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13928062803569921178721001 10446047102677440884040751)
      ·
        refine ⟨15669070654016161326061127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10446047102677440884040751 15669070654016161326061127)
        ·
          refine ⟨23503605981024241989091691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15669070654016161326061127 23503605981024241989091691)
          ·
            refine ⟨35255408971536362983637537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23503605981024241989091691 35255408971536362983637537)
            ·
              refine ⟨26441556728652272237728153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35255408971536362983637537 26441556728652272237728153)
              ·
                refine ⟨19831167546489204178296115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26441556728652272237728153 19831167546489204178296115)
                ·
                  refine ⟨29746751319733806267444173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19831167546489204178296115 29746751319733806267444173)
                  ·
                    refine ⟨11155031744900177350291565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29746751319733806267444173 11155031744900177350291565)
                    ·
                      refine ⟨4183136904337566506359337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11155031744900177350291565 4183136904337566506359337)
                      ·
                        rfl

theorem cell23_8146630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_8146630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146630 prefixEnd_8146630 := by exact prefixLift 8146630
  have htrace : WordTrace (prefixWord ++ tailWord_8146630) baseStart_8146630 baseEnd_8146630 := by
    simpa [prefixWord, tailWord_8146630, baseEnd_8146630] using wordTrace_append hprefix tailTrace_8146630
  have hstable : (prefixWord ++ tailWord_8146630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146630).length < 2 ^ (prefixWord ++ tailWord_8146630).sum := by decide
  have hdescent : baseEnd_8146630 < baseStart_8146630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146649 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_8146649 : Nat := 118140960795 + 8146649 * 2 ^ 59
def prefixEnd_8146649 : Nat := 4983230072969 + 3 ^ 40 * 8146649 * 2
def baseEnd_8146649 : Nat := 4183146660470001932021749

theorem tailTrace_8146649 : CollatzResearch.WordTrace tailWord_8146649 prefixEnd_8146649 4183146660470001932021749 := by
  unfold tailWord_8146649
  simp only [CollatzResearch.WordTrace]
  refine ⟨297132699463089484724323001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198088466308726323149548667 297132699463089484724323001)
  ·
    refine ⟨222849524597317113543242251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297132699463089484724323001 222849524597317113543242251)
    ·
      refine ⟨334274286895975670314863377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222849524597317113543242251 334274286895975670314863377)
      ·
        refine ⟨250705715171981752736147533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334274286895975670314863377 250705715171981752736147533)
        ·
          refine ⟨94014643189493157276055325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250705715171981752736147533 94014643189493157276055325)
          ·
            refine ⟨35255491196059933978520747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94014643189493157276055325 35255491196059933978520747)
            ·
              refine ⟨52883236794089900967781121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35255491196059933978520747 52883236794089900967781121)
              ·
                refine ⟨39662427595567425725835841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52883236794089900967781121 39662427595567425725835841)
                ·
                  refine ⟨29746820696675569294376881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39662427595567425725835841 29746820696675569294376881)
                  ·
                    refine ⟨22310115522506676970782661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29746820696675569294376881 22310115522506676970782661)
                    ·
                      refine ⟨4183146660470001932021749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22310115522506676970782661 4183146660470001932021749)
                      ·
                        rfl

theorem cell23_8146649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_8146649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146649 prefixEnd_8146649 := by exact prefixLift 8146649
  have htrace : WordTrace (prefixWord ++ tailWord_8146649) baseStart_8146649 baseEnd_8146649 := by
    simpa [prefixWord, tailWord_8146649, baseEnd_8146649] using wordTrace_append hprefix tailTrace_8146649
  have hstable : (prefixWord ++ tailWord_8146649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146649).length < 2 ^ (prefixWord ++ tailWord_8146649).sum := by decide
  have hdescent : baseEnd_8146649 < baseStart_8146649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146689 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 1, 7]
def baseStart_8146689 : Nat := 118140960795 + 8146689 * 2 ^ 59
def prefixEnd_8146689 : Nat := 4983230072969 + 3 ^ 40 * 8146689 * 2
def baseEnd_8146689 : Nat := 1394389066565393925173855

theorem tailTrace_8146689 : CollatzResearch.WordTrace tailWord_8146689 prefixEnd_8146689 1394389066565393925173855 := by
  unfold tailWord_8146689
  simp only [CollatzResearch.WordTrace]
  refine ⟨297134158382944571555779121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198089438921963047703852747 297134158382944571555779121)
  ·
    refine ⟨222850618787208428666834341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297134158382944571555779121 222850618787208428666834341)
    ·
      refine ⟨41784491022601580375031439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222850618787208428666834341 41784491022601580375031439)
      ·
        refine ⟨62676736533902370562547159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41784491022601580375031439 62676736533902370562547159)
        ·
          refine ⟨94015104800853555843820739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62676736533902370562547159 94015104800853555843820739)
          ·
            refine ⟨141022657201280333765731109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94015104800853555843820739 141022657201280333765731109)
            ·
              refine ⟨26441748225240062581074583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141022657201280333765731109 26441748225240062581074583)
              ·
                refine ⟨39662622337860093871611875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26441748225240062581074583 39662622337860093871611875)
                ·
                  refine ⟨59493933506790140807417813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39662622337860093871611875 59493933506790140807417813)
                  ·
                    refine ⟨1394389066565393925173855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59493933506790140807417813 1394389066565393925173855)
                    ·
                      rfl

theorem cell23_8146689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_8146689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146689 prefixEnd_8146689 := by exact prefixLift 8146689
  have htrace : WordTrace (prefixWord ++ tailWord_8146689) baseStart_8146689 baseEnd_8146689 := by
    simpa [prefixWord, tailWord_8146689, baseEnd_8146689] using wordTrace_append hprefix tailTrace_8146689
  have hstable : (prefixWord ++ tailWord_8146689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146689).length < 2 ^ (prefixWord ++ tailWord_8146689).sum := by decide
  have hdescent : baseEnd_8146689 < baseStart_8146689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146770 : List Nat := [3, 2, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_8146770 : Nat := 118140960795 + 8146770 * 2 ^ 59
def prefixEnd_8146770 : Nat := 4983230072969 + 3 ^ 40 * 8146770 * 2
def baseEnd_8146770 : Nat := 1394402930543065319536231

theorem tailTrace_8146770 : CollatzResearch.WordTrace tailWord_8146770 prefixEnd_8146770 1394402930543065319536231 := by
  unfold tailWord_8146770
  simp only [CollatzResearch.WordTrace]
  refine ⟨74284278173912780597369441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198091408463767414926318509 74284278173912780597369441)
  ·
    refine ⟨55713208630434585448027081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74284278173912780597369441 55713208630434585448027081)
    ·
      refine ⟨41784906472825939086020311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55713208630434585448027081 41784906472825939086020311)
      ·
        refine ⟨62677359709238908629030467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41784906472825939086020311 62677359709238908629030467)
        ·
          refine ⟨94016039563858362943545701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62677359709238908629030467 94016039563858362943545701)
          ·
            refine ⟨17628007418223443051914819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94016039563858362943545701 17628007418223443051914819)
            ·
              refine ⟨26442011127335164577872229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17628007418223443051914819 26442011127335164577872229)
              ·
                refine ⟨4957877086375343358351043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26442011127335164577872229 4957877086375343358351043)
                ·
                  refine ⟨7436815629563015037526565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957877086375343358351043 7436815629563015037526565)
                  ·
                    refine ⟨1394402930543065319536231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7436815629563015037526565 1394402930543065319536231)
                    ·
                      rfl

theorem cell23_8146770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_8146770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146770 prefixEnd_8146770 := by exact prefixLift 8146770
  have htrace : WordTrace (prefixWord ++ tailWord_8146770) baseStart_8146770 baseEnd_8146770 := by
    simpa [prefixWord, tailWord_8146770, baseEnd_8146770] using wordTrace_append hprefix tailTrace_8146770
  have hstable : (prefixWord ++ tailWord_8146770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146770).length < 2 ^ (prefixWord ++ tailWord_8146770).sum := by decide
  have hdescent : baseEnd_8146770 < baseStart_8146770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146789 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_8146789 : Nat := 118140960795 + 8146789 * 2 ^ 59
def prefixEnd_8146789 : Nat := 4983230072969 + 3 ^ 40 * 8146789 * 2
def baseEnd_8146789 : Nat := 4183218547761631384271105

theorem tailTrace_8146789 : CollatzResearch.WordTrace tailWord_8146789 prefixEnd_8146789 4183218547761631384271105 := by
  unfold tailWord_8146789
  simp only [CollatzResearch.WordTrace]
  refine ⟨297137805682582288634419421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198091870455054859089612947 297137805682582288634419421)
  ·
    refine ⟨111426677130968358237907283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297137805682582288634419421 111426677130968358237907283)
    ·
      refine ⟨167140015696452537356860925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111426677130968358237907283 167140015696452537356860925)
      ·
        refine ⟨62677505886169701508822847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167140015696452537356860925 62677505886169701508822847)
        ·
          refine ⟨94016258829254552263234271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62677505886169701508822847 94016258829254552263234271)
          ·
            refine ⟨141024388243881828394851407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94016258829254552263234271 141024388243881828394851407)
            ·
              refine ⟨211536582365822742592277111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141024388243881828394851407 211536582365822742592277111)
              ·
                refine ⟨317304873548734113888415667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211536582365822742592277111 317304873548734113888415667)
                ·
                  refine ⟨475957310323101170832623501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317304873548734113888415667 475957310323101170832623501)
                  ·
                    refine ⟨178483991371162939062233813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475957310323101170832623501 178483991371162939062233813)
                    ·
                      refine ⟨4183218547761631384271105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178483991371162939062233813 4183218547761631384271105)
                      ·
                        rfl

theorem cell23_8146789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_8146789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146789 prefixEnd_8146789 := by exact prefixLift 8146789
  have htrace : WordTrace (prefixWord ++ tailWord_8146789) baseStart_8146789 baseEnd_8146789 := by
    simpa [prefixWord, tailWord_8146789, baseEnd_8146789] using wordTrace_append hprefix tailTrace_8146789
  have hstable : (prefixWord ++ tailWord_8146789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146789).length < 2 ^ (prefixWord ++ tailWord_8146789).sum := by decide
  have hdescent : baseEnd_8146789 < baseStart_8146789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146796 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_8146796 : Nat := 118140960795 + 8146796 * 2 ^ 59
def prefixEnd_8146796 : Nat := 4983230072969 + 3 ^ 40 * 8146796 * 2
def baseEnd_8146796 : Nat := 1394407380708737618961191

theorem tailTrace_8146796 : CollatzResearch.WordTrace tailWord_8146796 prefixEnd_8146796 1394407380708737618961191 := by
  unfold tailWord_8146796
  simp only [CollatzResearch.WordTrace]
  refine ⟨148569030496778464414962121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198092040662371285886616161 148569030496778464414962121)
  ·
    refine ⟨111426772872583848311221591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148569030496778464414962121 111426772872583848311221591)
    ·
      refine ⟨167140159308875772466832387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111426772872583848311221591 167140159308875772466832387)
      ·
        refine ⟨250710238963313658700248581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167140159308875772466832387 250710238963313658700248581)
        ·
          refine ⟨47008169805621311006296609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250710238963313658700248581 47008169805621311006296609)
          ·
            refine ⟨35256127354215983254722457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47008169805621311006296609 35256127354215983254722457)
            ·
              refine ⟨26442095515661987441041843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35256127354215983254722457 26442095515661987441041843)
              ·
                refine ⟨39663143273492981161562765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26442095515661987441041843 39663143273492981161562765)
                ·
                  refine ⟨14873678727559867935586037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39663143273492981161562765 14873678727559867935586037)
                  ·
                    refine ⟨1394407380708737618961191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14873678727559867935586037 1394407380708737618961191)
                    ·
                      rfl

theorem cell23_8146796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_8146796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146796 prefixEnd_8146796 := by exact prefixLift 8146796
  have htrace : WordTrace (prefixWord ++ tailWord_8146796) baseStart_8146796 baseEnd_8146796 := by
    simpa [prefixWord, tailWord_8146796, baseEnd_8146796] using wordTrace_append hprefix tailTrace_8146796
  have hstable : (prefixWord ++ tailWord_8146796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146796).length < 2 ^ (prefixWord ++ tailWord_8146796).sum := by decide
  have hdescent : baseEnd_8146796 < baseStart_8146796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146810 : List Nat := [3, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3]
def baseStart_8146810 : Nat := 118140960795 + 8146810 * 2 ^ 59
def prefixEnd_8146810 : Nat := 4983230072969 + 3 ^ 40 * 8146810 * 2
def baseEnd_8146810 : Nat := 4183229330855375802108509

theorem tailTrace_8146810 : CollatzResearch.WordTrace tailWord_8146810 prefixEnd_8146810 4183229330855375802108509 := by
  unfold tailWord_8146810
  simp only [CollatzResearch.WordTrace]
  refine ⟨74284642903876552305233471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198092381077004139480622589 74284642903876552305233471)
  ·
    refine ⟨111426964355814828457850207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74284642903876552305233471 111426964355814828457850207)
    ·
      refine ⟨167140446533722242686775311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111426964355814828457850207 167140446533722242686775311)
      ·
        refine ⟨250710669800583364030162967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167140446533722242686775311 250710669800583364030162967)
        ·
          refine ⟨376066004700875046045244451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250710669800583364030162967 376066004700875046045244451)
          ·
            refine ⟨564099007051312569067866677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376066004700875046045244451 564099007051312569067866677)
            ·
              refine ⟨52884281911060553350112501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 564099007051312569067866677 52884281911060553350112501)
              ·
                refine ⟨4957901429161926876573047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52884281911060553350112501 4957901429161926876573047)
                ·
                  refine ⟨7436852143742890314859571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957901429161926876573047 7436852143742890314859571)
                  ·
                    refine ⟨11155278215614335472289357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7436852143742890314859571 11155278215614335472289357)
                    ·
                      refine ⟨4183229330855375802108509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11155278215614335472289357 4183229330855375802108509)
                      ·
                        rfl

theorem cell23_8146810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3].length) (baseStart_8146810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146810 prefixEnd_8146810 := by exact prefixLift 8146810
  have htrace : WordTrace (prefixWord ++ tailWord_8146810) baseStart_8146810 baseEnd_8146810 := by
    simpa [prefixWord, tailWord_8146810, baseEnd_8146810] using wordTrace_append hprefix tailTrace_8146810
  have hstable : (prefixWord ++ tailWord_8146810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146810).length < 2 ^ (prefixWord ++ tailWord_8146810).sum := by decide
  have hdescent : baseEnd_8146810 < baseStart_8146810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146817 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 6]
def baseStart_8146817 : Nat := 118140960795 + 8146817 * 2 ^ 59
def prefixEnd_8146817 : Nat := 4983230072969 + 3 ^ 40 * 8146817 * 2
def baseEnd_8146817 : Nat := 464803658357773030524553

theorem tailTrace_8146817 : CollatzResearch.WordTrace tailWord_8146817 prefixEnd_8146817 464803658357773030524553 := by
  unfold tailWord_8146817
  simp only [CollatzResearch.WordTrace]
  refine ⟨297138826926480849416438705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198092551284320566277625803 297138826926480849416438705)
  ·
    refine ⟨222854120194860637062329029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297138826926480849416438705 222854120194860637062329029)
    ·
      refine ⟨41785147536536369449186693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222854120194860637062329029 41785147536536369449186693)
      ·
        refine ⟨7834715163100569271722505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41785147536536369449186693 7834715163100569271722505)
        ·
          refine ⟨5876036372325426953791879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7834715163100569271722505 5876036372325426953791879)
          ·
            refine ⟨8814054558488140430687819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876036372325426953791879 8814054558488140430687819)
            ·
              refine ⟨13221081837732210646031729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814054558488140430687819 13221081837732210646031729)
              ·
                refine ⟨9915811378299157984523797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13221081837732210646031729 9915811378299157984523797)
                ·
                  refine ⟨464803658357773030524553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9915811378299157984523797 464803658357773030524553)
                  ·
                    rfl

theorem cell23_8146817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 6].length) (baseStart_8146817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146817 prefixEnd_8146817 := by exact prefixLift 8146817
  have htrace : WordTrace (prefixWord ++ tailWord_8146817) baseStart_8146817 baseEnd_8146817 := by
    simpa [prefixWord, tailWord_8146817, baseEnd_8146817] using wordTrace_append hprefix tailTrace_8146817
  have hstable : (prefixWord ++ tailWord_8146817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146817).length < 2 ^ (prefixWord ++ tailWord_8146817).sum := by decide
  have hdescent : baseEnd_8146817 < baseStart_8146817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146927 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 1, 3, 2]
def baseStart_8146927 : Nat := 118140960795 + 8146927 * 2 ^ 59
def prefixEnd_8146927 : Nat := 4983230072969 + 3 ^ 40 * 8146927 * 2
def baseEnd_8146927 : Nat := 4183289408091951844345471

theorem tailTrace_8146927 : CollatzResearch.WordTrace tailWord_8146927 prefixEnd_8146927 4183289408091951844345471 := by
  unfold tailWord_8146927
  simp only [CollatzResearch.WordTrace]
  refine ⟨297142838956082338202943035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198095225970721558801962023 297142838956082338202943035)
  ·
    refine ⟨445714258434123507304414553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297142838956082338202943035 445714258434123507304414553)
    ·
      refine ⟨334285693825592630478310915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445714258434123507304414553 334285693825592630478310915)
      ·
        refine ⟨501428540738388945717466373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334285693825592630478310915 501428540738388945717466373)
        ·
          refine ⟨94017851388447927322024945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501428540738388945717466373 94017851388447927322024945)
          ·
            refine ⟨70513388541335945491518709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94017851388447927322024945 70513388541335945491518709)
            ·
              refine ⟨6610630175750244889829879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70513388541335945491518709 6610630175750244889829879)
              ·
                refine ⟨9915945263625367334744819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610630175750244889829879 9915945263625367334744819)
                ·
                  refine ⟨14873917895438051002117229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9915945263625367334744819 14873917895438051002117229)
                  ·
                    refine ⟨5577719210789269125793961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14873917895438051002117229 5577719210789269125793961)
                    ·
                      refine ⟨4183289408091951844345471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577719210789269125793961 4183289408091951844345471)
                      ·
                        rfl

theorem cell23_8146927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 3, 2].length) (baseStart_8146927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146927 prefixEnd_8146927 := by exact prefixLift 8146927
  have htrace : WordTrace (prefixWord ++ tailWord_8146927) baseStart_8146927 baseEnd_8146927 := by
    simpa [prefixWord, tailWord_8146927, baseEnd_8146927] using wordTrace_append hprefix tailTrace_8146927
  have hstable : (prefixWord ++ tailWord_8146927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146927).length < 2 ^ (prefixWord ++ tailWord_8146927).sum := by decide
  have hdescent : baseEnd_8146927 < baseStart_8146927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146934 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_8146934 : Nat := 118140960795 + 8146934 * 2 ^ 59
def prefixEnd_8146934 : Nat := 4983230072969 + 3 ^ 40 * 8146934 * 2
def baseEnd_8146934 : Nat := 4183293002456533316957939

theorem tailTrace_8146934 : CollatzResearch.WordTrace tailWord_8146934 prefixEnd_8146934 4183293002456533316957939 := by
  unfold tailWord_8146934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18571443391691061149902991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198095396178037985598965237 18571443391691061149902991)
  ·
    refine ⟨27857165087536591724854487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18571443391691061149902991 27857165087536591724854487)
    ·
      refine ⟨41785747631304887587281731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27857165087536591724854487 41785747631304887587281731)
      ·
        refine ⟨62678621446957331380922597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41785747631304887587281731 62678621446957331380922597)
        ·
          refine ⟨11752241521304499633922987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62678621446957331380922597 11752241521304499633922987)
          ·
            refine ⟨17628362281956749450884481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11752241521304499633922987 17628362281956749450884481)
            ·
              refine ⟨13221271711467562088163361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17628362281956749450884481 13221271711467562088163361)
              ·
                refine ⟨9915953783600671566122521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13221271711467562088163361 9915953783600671566122521)
                ·
                  refine ⟨7436965337700503674591891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9915953783600671566122521 7436965337700503674591891)
                  ·
                    refine ⟨11155448006550755511887837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7436965337700503674591891 11155448006550755511887837)
                    ·
                      refine ⟨4183293002456533316957939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11155448006550755511887837 4183293002456533316957939)
                      ·
                        rfl

theorem cell23_8146934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_8146934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146934 prefixEnd_8146934 := by exact prefixLift 8146934
  have htrace : WordTrace (prefixWord ++ tailWord_8146934) baseStart_8146934 baseEnd_8146934 := by
    simpa [prefixWord, tailWord_8146934, baseEnd_8146934] using wordTrace_append hprefix tailTrace_8146934
  have hstable : (prefixWord ++ tailWord_8146934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146934).length < 2 ^ (prefixWord ++ tailWord_8146934).sum := by decide
  have hdescent : baseEnd_8146934 < baseStart_8146934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8146990 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_8146990 : Nat := 118140960795 + 8146990 * 2 ^ 59
def prefixEnd_8146990 : Nat := 4983230072969 + 3 ^ 40 * 8146990 * 2
def baseEnd_8146990 : Nat := 4183321757373185097857681

theorem tailTrace_8146990 : CollatzResearch.WordTrace tailWord_8146990 prefixEnd_8146990 4183321757373185097857681 := by
  unfold tailWord_8146990
  simp only [CollatzResearch.WordTrace]
  refine ⟨37143142094356762495310803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198096757836569399974990949 37143142094356762495310803)
  ·
    refine ⟨55714713141535143742966205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37143142094356762495310803 55714713141535143742966205)
    ·
      refine ⟨20893017428075678903612327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55714713141535143742966205 20893017428075678903612327)
      ·
        refine ⟨31339526142113518355418491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20893017428075678903612327 31339526142113518355418491)
        ·
          refine ⟨47009289213170277533127737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31339526142113518355418491 47009289213170277533127737)
          ·
            refine ⟨35256966909877708149845803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47009289213170277533127737 35256966909877708149845803)
            ·
              refine ⟨52885450364816562224768705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35256966909877708149845803 52885450364816562224768705)
              ·
                refine ⟨39664087773612421668576529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52885450364816562224768705 39664087773612421668576529)
                ·
                  refine ⟨29748065830209316251432397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39664087773612421668576529 29748065830209316251432397)
                  ·
                    refine ⟨11155524686328493594287149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29748065830209316251432397 11155524686328493594287149)
                    ·
                      refine ⟨4183321757373185097857681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11155524686328493594287149 4183321757373185097857681)
                      ·
                        rfl

theorem cell23_8146990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_8146990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8146990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8146990 prefixEnd_8146990 := by exact prefixLift 8146990
  have htrace : WordTrace (prefixWord ++ tailWord_8146990) baseStart_8146990 baseEnd_8146990 := by
    simpa [prefixWord, tailWord_8146990, baseEnd_8146990] using wordTrace_append hprefix tailTrace_8146990
  have hstable : (prefixWord ++ tailWord_8146990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8146990).length < 2 ^ (prefixWord ++ tailWord_8146990).sum := by decide
  have hdescent : baseEnd_8146990 < baseStart_8146990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8146990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147033 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 3]
def baseStart_8147033 : Nat := 118140960795 + 8147033 * 2 ^ 59
def prefixEnd_8147033 : Nat := 4983230072969 + 3 ^ 40 * 8147033 * 2
def baseEnd_8147033 : Nat := 4183343837041328429619983

theorem tailTrace_8147033 : CollatzResearch.WordTrace tailWord_8147033 prefixEnd_8147033 4183343837041328429619983 := by
  unfold tailWord_8147033
  simp only [CollatzResearch.WordTrace]
  refine ⟨297146705093698318306301753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198097803395798878870867835 297146705093698318306301753)
  ·
    refine ⟨222860028820273738729726315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297146705093698318306301753 222860028820273738729726315)
    ·
      refine ⟨334290043230410608094589473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222860028820273738729726315 334290043230410608094589473)
      ·
        refine ⟨250717532422807956070942105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334290043230410608094589473 250717532422807956070942105)
        ·
          refine ⟨188038149317105967053206579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250717532422807956070942105 188038149317105967053206579)
          ·
            refine ⟨282057223975658950579809869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188038149317105967053206579 282057223975658950579809869)
            ·
              refine ⟨105771458990872106467428701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282057223975658950579809869 105771458990872106467428701)
              ·
                refine ⟨39664297121577039925285763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105771458990872106467428701 39664297121577039925285763)
                ·
                  refine ⟨59496445682365559887928645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39664297121577039925285763 59496445682365559887928645)
                  ·
                    refine ⟨11155583565443542478986621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59496445682365559887928645 11155583565443542478986621)
                    ·
                      refine ⟨4183343837041328429619983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11155583565443542478986621 4183343837041328429619983)
                      ·
                        rfl

theorem cell23_8147033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_8147033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147033 prefixEnd_8147033 := by exact prefixLift 8147033
  have htrace : WordTrace (prefixWord ++ tailWord_8147033) baseStart_8147033 baseEnd_8147033 := by
    simpa [prefixWord, tailWord_8147033, baseEnd_8147033] using wordTrace_append hprefix tailTrace_8147033
  have hstable : (prefixWord ++ tailWord_8147033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147033).length < 2 ^ (prefixWord ++ tailWord_8147033).sum := by decide
  have hdescent : baseEnd_8147033 < baseStart_8147033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147053 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 8]
def baseStart_8147053 : Nat := 118140960795 + 8147053 * 2 ^ 59
def prefixEnd_8147053 : Nat := 4983230072969 + 3 ^ 40 * 8147053 * 2
def baseEnd_8147053 : Nat := 464817122961602039041099

theorem tailTrace_8147053 : CollatzResearch.WordTrace tailWord_8147053 prefixEnd_8147053 464817122961602039041099 := by
  unfold tailWord_8147053
  simp only [CollatzResearch.WordTrace]
  refine ⟨297147434553625861722029813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198098289702417241148019875 297147434553625861722029813)
  ·
    refine ⟨27857571989402424536440295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297147434553625861722029813 27857571989402424536440295)
    ·
      refine ⟨41786357984103636804660443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27857571989402424536440295 41786357984103636804660443)
      ·
        refine ⟨62679536976155455206990665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41786357984103636804660443 62679536976155455206990665)
        ·
          refine ⟨47009652732116591405242999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62679536976155455206990665 47009652732116591405242999)
          ·
            refine ⟨70514479098174887107864499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47009652732116591405242999 70514479098174887107864499)
            ·
              refine ⟨105771718647262330661796749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70514479098174887107864499 105771718647262330661796749)
              ·
                refine ⟨39664394492723373998173781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105771718647262330661796749 39664394492723373998173781)
                ·
                  refine ⟨464817122961602039041099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39664394492723373998173781 464817122961602039041099)
                  ·
                    rfl

theorem cell23_8147053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_8147053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147053 prefixEnd_8147053 := by exact prefixLift 8147053
  have htrace : WordTrace (prefixWord ++ tailWord_8147053) baseStart_8147053 baseEnd_8147053 := by
    simpa [prefixWord, tailWord_8147053, baseEnd_8147053] using wordTrace_append hprefix tailTrace_8147053
  have hstable : (prefixWord ++ tailWord_8147053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147053).length < 2 ^ (prefixWord ++ tailWord_8147053).sum := by decide
  have hdescent : baseEnd_8147053 < baseStart_8147053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147108 : List Nat := [2, 3, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_8147108 : Nat := 118140960795 + 8147108 * 2 ^ 59
def prefixEnd_8147108 : Nat := 4983230072969 + 3 ^ 40 * 8147108 * 2
def baseEnd_8147108 : Nat := 1394460782696805212060713

theorem tailTrace_8147108 : CollatzResearch.WordTrace tailWord_8147108 prefixEnd_8147108 1394460782696805212060713 := by
  unfold tailWord_8147108
  simp only [CollatzResearch.WordTrace]
  refine ⟨148574720284213303057640989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198099627045617737410187985 148574720284213303057640989)
  ·
    refine ⟨55715520106579988646615371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148574720284213303057640989 55715520106579988646615371)
    ·
      refine ⟨83573280159869982969923057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55715520106579988646615371 83573280159869982969923057)
      ·
        refine ⟨62679960119902487227442293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83573280159869982969923057 62679960119902487227442293)
        ·
          refine ⟨5876246261240858177572715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62679960119902487227442293 5876246261240858177572715)
          ·
            refine ⟨8814369391861287266359073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876246261240858177572715 8814369391861287266359073)
            ·
              refine ⟨6610777043895965449769305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8814369391861287266359073 6610777043895965449769305)
              ·
                refine ⟨4958082782921974087326979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6610777043895965449769305 4958082782921974087326979)
                ·
                  refine ⟨7437124174382961130990469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958082782921974087326979 7437124174382961130990469)
                  ·
                    refine ⟨1394460782696805212060713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437124174382961130990469 1394460782696805212060713)
                    ·
                      rfl

theorem cell23_8147108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_8147108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147108 prefixEnd_8147108 := by exact prefixLift 8147108
  have htrace : WordTrace (prefixWord ++ tailWord_8147108) baseStart_8147108 baseEnd_8147108 := by
    simpa [prefixWord, tailWord_8147108, baseEnd_8147108] using wordTrace_append hprefix tailTrace_8147108
  have hstable : (prefixWord ++ tailWord_8147108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147108).length < 2 ^ (prefixWord ++ tailWord_8147108).sum := by decide
  have hdescent : baseEnd_8147108 < baseStart_8147108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147123 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 5]
def baseStart_8147123 : Nat := 118140960795 + 8147123 * 2 ^ 59
def prefixEnd_8147123 : Nat := 4983230072969 + 3 ^ 40 * 8147123 * 2
def baseEnd_8147123 : Nat := 4183390050300233077494569

theorem tailTrace_8147123 : CollatzResearch.WordTrace tailWord_8147123 prefixEnd_8147123 4183390050300233077494569 := by
  unfold tailWord_8147123
  simp only [CollatzResearch.WordTrace]
  refine ⟨297149987663372263677078023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198099991775581509118052015 297149987663372263677078023)
  ·
    refine ⟨445724981495058395515617035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297149987663372263677078023 445724981495058395515617035)
    ·
      refine ⟨668587472242587593273425553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445724981495058395515617035 668587472242587593273425553)
      ·
        refine ⟨501440604181940694955069165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668587472242587593273425553 501440604181940694955069165)
        ·
          refine ⟨188040226568227760608150937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501440604181940694955069165 188040226568227760608150937)
          ·
            refine ⟨141030169926170820456113203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188040226568227760608150937 141030169926170820456113203)
            ·
              refine ⟨211545254889256230684169805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141030169926170820456113203 211545254889256230684169805)
              ·
                refine ⟨79329470583471086506563677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211545254889256230684169805 79329470583471086506563677)
                ·
                  refine ⟨29748551468801657439961379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79329470583471086506563677 29748551468801657439961379)
                  ·
                    refine ⟨44622827203202486159942069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29748551468801657439961379 44622827203202486159942069)
                    ·
                      refine ⟨4183390050300233077494569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44622827203202486159942069 4183390050300233077494569)
                      ·
                        rfl

theorem cell23_8147123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_8147123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147123 prefixEnd_8147123 := by exact prefixLift 8147123
  have htrace : WordTrace (prefixWord ++ tailWord_8147123) baseStart_8147123 baseEnd_8147123 := by
    simpa [prefixWord, tailWord_8147123, baseEnd_8147123] using wordTrace_append hprefix tailTrace_8147123
  have hstable : (prefixWord ++ tailWord_8147123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147123).length < 2 ^ (prefixWord ++ tailWord_8147123).sum := by decide
  have hdescent : baseEnd_8147123 < baseStart_8147123 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147148 : List Nat := [2, 2, 1, 6, 1, 1, 2, 3, 1, 1, 3]
def baseStart_8147148 : Nat := 118140960795 + 8147148 * 2 ^ 59
def prefixEnd_8147148 : Nat := 4983230072969 + 3 ^ 40 * 8147148 * 2
def baseEnd_8147148 : Nat := 4183402887316595479681955

theorem tailTrace_8147148 : CollatzResearch.WordTrace tailWord_8147148 prefixEnd_8147148 4183402887316595479681955 := by
  unfold tailWord_8147148
  simp only [CollatzResearch.WordTrace]
  refine ⟨148575449744140846473369049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198100599658854461964492065 148575449744140846473369049)
  ·
    refine ⟨111431587308105634855026787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148575449744140846473369049 111431587308105634855026787)
    ·
      refine ⟨167147380962158452282540181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111431587308105634855026787 167147380962158452282540181)
      ·
        refine ⟨7835033482601177450744071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167147380962158452282540181 7835033482601177450744071)
        ·
          refine ⟨11752550223901766176116107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835033482601177450744071 11752550223901766176116107)
          ·
            refine ⟨17628825335852649264174161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11752550223901766176116107 17628825335852649264174161)
            ·
              refine ⟨13221619001889486948130621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17628825335852649264174161 13221619001889486948130621)
              ·
                refine ⟨4958107125708557605548983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13221619001889486948130621 4958107125708557605548983)
                ·
                  refine ⟨7437160688562836408323475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958107125708557605548983 7437160688562836408323475)
                  ·
                    refine ⟨11155741032844254612485213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7437160688562836408323475 11155741032844254612485213)
                    ·
                      refine ⟨4183402887316595479681955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11155741032844254612485213 4183402887316595479681955)
                      ·
                        rfl

theorem cell23_8147148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_8147148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147148 prefixEnd_8147148 := by exact prefixLift 8147148
  have htrace : WordTrace (prefixWord ++ tailWord_8147148) baseStart_8147148 baseEnd_8147148 := by
    simpa [prefixWord, tailWord_8147148, baseEnd_8147148] using wordTrace_append hprefix tailTrace_8147148
  have hstable : (prefixWord ++ tailWord_8147148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147148).length < 2 ^ (prefixWord ++ tailWord_8147148).sum := by decide
  have hdescent : baseEnd_8147148 < baseStart_8147148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147154 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_8147154 : Nat := 118140960795 + 8147154 * 2 ^ 59
def prefixEnd_8147154 : Nat := 4983230072969 + 3 ^ 40 * 8147154 * 2
def baseEnd_8147154 : Nat := 4183405968200522456206927

theorem tailTrace_8147154 : CollatzResearch.WordTrace tailWord_8147154 prefixEnd_8147154 4183405968200522456206927 := by
  unfold tailWord_8147154
  simp only [CollatzResearch.WordTrace]
  refine ⟨74287779581564988992864129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198100745550839970647637677 74287779581564988992864129)
  ·
    refine ⟨55715834686173741744648097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74287779581564988992864129 55715834686173741744648097)
    ·
      refine ⟨41786876014630306308486073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55715834686173741744648097 41786876014630306308486073)
      ·
        refine ⟨31340157010972729731364555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41786876014630306308486073 31340157010972729731364555)
        ·
          refine ⟨47010235516459094597046833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31340157010972729731364555 47010235516459094597046833)
          ·
            refine ⟨35257676637344320947785125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47010235516459094597046833 35257676637344320947785125)
            ·
              refine ⟨6610814369502060177709711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35257676637344320947785125 6610814369502060177709711)
              ·
                refine ⟨9916221554253090266564567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610814369502060177709711 9916221554253090266564567)
                ·
                  refine ⟨14874332331379635399846851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916221554253090266564567 14874332331379635399846851)
                  ·
                    refine ⟨22311498497069453099770277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14874332331379635399846851 22311498497069453099770277)
                    ·
                      refine ⟨4183405968200522456206927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22311498497069453099770277 4183405968200522456206927)
                      ·
                        rfl

theorem cell23_8147154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_8147154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147154 prefixEnd_8147154 := by exact prefixLift 8147154
  have htrace : WordTrace (prefixWord ++ tailWord_8147154) baseStart_8147154 baseEnd_8147154 := by
    simpa [prefixWord, tailWord_8147154, baseEnd_8147154] using wordTrace_append hprefix tailTrace_8147154
  have hstable : (prefixWord ++ tailWord_8147154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147154).length < 2 ^ (prefixWord ++ tailWord_8147154).sum := by decide
  have hdescent : baseEnd_8147154 < baseStart_8147154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147181 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_8147181 : Nat := 118140960795 + 8147181 * 2 ^ 59
def prefixEnd_8147181 : Nat := 4983230072969 + 3 ^ 40 * 8147181 * 2
def baseEnd_8147181 : Nat := 1394473277392731283523101

theorem tailTrace_8147181 : CollatzResearch.WordTrace tailWord_8147181 prefixEnd_8147181 1394473277392731283523101 := by
  unfold tailWord_8147181
  simp only [CollatzResearch.WordTrace]
  refine ⟨297152103097162139582689397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198101402064774759721792931 297152103097162139582689397)
  ·
    refine ⟨27858009665358950585877131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297152103097162139582689397 27858009665358950585877131)
    ·
      refine ⟨41787014498038425878815697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27858009665358950585877131 41787014498038425878815697)
      ·
        refine ⟨31340260873528819409111773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41787014498038425878815697 31340260873528819409111773)
        ·
          refine ⟨11752597827573307278416915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31340260873528819409111773 11752597827573307278416915)
          ·
            refine ⟨17628896741359960917625373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11752597827573307278416915 17628896741359960917625373)
            ·
              refine ⟨6610836278009985344109515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17628896741359960917625373 6610836278009985344109515)
              ·
                refine ⟨9916254417014978016164273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610836278009985344109515 9916254417014978016164273)
                ·
                  refine ⟨7437190812761233512123205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9916254417014978016164273 7437190812761233512123205)
                  ·
                    refine ⟨1394473277392731283523101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437190812761233512123205 1394473277392731283523101)
                    ·
                      rfl

theorem cell23_8147181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_8147181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147181 prefixEnd_8147181 := by exact prefixLift 8147181
  have htrace : WordTrace (prefixWord ++ tailWord_8147181) baseStart_8147181 baseEnd_8147181 := by
    simpa [prefixWord, tailWord_8147181, baseEnd_8147181] using wordTrace_append hprefix tailTrace_8147181
  have hstable : (prefixWord ++ tailWord_8147181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147181).length < 2 ^ (prefixWord ++ tailWord_8147181).sum := by decide
  have hdescent : baseEnd_8147181 < baseStart_8147181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147190 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_8147190 : Nat := 118140960795 + 8147190 * 2 ^ 59
def prefixEnd_8147190 : Nat := 4983230072969 + 3 ^ 40 * 8147190 * 2
def baseEnd_8147190 : Nat := 1394474817834694771785587

theorem tailTrace_8147190 : CollatzResearch.WordTrace tailWord_8147190 prefixEnd_8147190 1394474817834694771785587 := by
  unfold tailWord_8147190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18572026959633095882485439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198101620902753022746511349 18572026959633095882485439)
  ·
    refine ⟨27858040439449643823728159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18572026959633095882485439 27858040439449643823728159)
    ·
      refine ⟨41787060659174465735592239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27858040439449643823728159 41787060659174465735592239)
      ·
        refine ⟨62680590988761698603388359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41787060659174465735592239 62680590988761698603388359)
        ·
          refine ⟨94020886483142547905082539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62680590988761698603388359 94020886483142547905082539)
          ·
            refine ⟨141031329724713821857623809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94020886483142547905082539 141031329724713821857623809)
            ·
              refine ⟨105773497293535366393217857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141031329724713821857623809 105773497293535366393217857)
              ·
                refine ⟨79330122970151524794913393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105773497293535366393217857 79330122970151524794913393)
                ·
                  refine ⟨59497592227613643596185045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79330122970151524794913393 59497592227613643596185045)
                  ·
                    refine ⟨1394474817834694771785587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59497592227613643596185045 1394474817834694771785587)
                    ·
                      rfl

theorem cell23_8147190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_8147190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147190 prefixEnd_8147190 := by exact prefixLift 8147190
  have htrace : WordTrace (prefixWord ++ tailWord_8147190) baseStart_8147190 baseEnd_8147190 := by
    simpa [prefixWord, tailWord_8147190, baseEnd_8147190] using wordTrace_append hprefix tailTrace_8147190
  have hstable : (prefixWord ++ tailWord_8147190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147190).length < 2 ^ (prefixWord ++ tailWord_8147190).sum := by decide
  have hdescent : baseEnd_8147190 < baseStart_8147190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147193 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_8147193 : Nat := 118140960795 + 8147193 * 2 ^ 59
def prefixEnd_8147193 : Nat := 4983230072969 + 3 ^ 40 * 8147193 * 2
def baseEnd_8147193 : Nat := 4183425993946047803619247

theorem tailTrace_8147193 : CollatzResearch.WordTrace tailWord_8147193 prefixEnd_8147193 4183425993946047803619247 := by
  unfold tailWord_8147193
  simp only [CollatzResearch.WordTrace]
  refine ⟨297152540773118665632126233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198101693848745777088084155 297152540773118665632126233)
  ·
    refine ⟨222864405579838999224094675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297152540773118665632126233 222864405579838999224094675)
    ·
      refine ⟨334296608369758498836142013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222864405579838999224094675 334296608369758498836142013)
      ·
        refine ⟨125361228138659437063553255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334296608369758498836142013 125361228138659437063553255)
        ·
          refine ⟨188041842207989155595329883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125361228138659437063553255 188041842207989155595329883)
          ·
            refine ⟨282062763311983733392994825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188041842207989155595329883 282062763311983733392994825)
            ·
              refine ⟨211547072483987800044746119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282062763311983733392994825 211547072483987800044746119)
              ·
                refine ⟨317320608725981700067119179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211547072483987800044746119 317320608725981700067119179)
                ·
                  refine ⟨475980913088972550100678769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317320608725981700067119179 475980913088972550100678769)
                  ·
                    refine ⟨356985684816729412575509077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 475980913088972550100678769 356985684816729412575509077)
                    ·
                      refine ⟨4183425993946047803619247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 356985684816729412575509077 4183425993946047803619247)
                      ·
                        rfl

theorem cell23_8147193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_8147193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147193 prefixEnd_8147193 := by exact prefixLift 8147193
  have htrace : WordTrace (prefixWord ++ tailWord_8147193) baseStart_8147193 baseEnd_8147193 := by
    simpa [prefixWord, tailWord_8147193, baseEnd_8147193] using wordTrace_append hprefix tailTrace_8147193
  have hstable : (prefixWord ++ tailWord_8147193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147193).length < 2 ^ (prefixWord ++ tailWord_8147193).sum := by decide
  have hdescent : baseEnd_8147193 < baseStart_8147193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147197 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_8147197 : Nat := 118140960795 + 8147197 * 2 ^ 59
def prefixEnd_8147197 : Nat := 4983230072969 + 3 ^ 40 * 8147197 * 2
def baseEnd_8147197 : Nat := 4183428047868665787969229

theorem tailTrace_8147197 : CollatzResearch.WordTrace tailWord_8147197 prefixEnd_8147197 4183428047868665787969229 := by
  unfold tailWord_8147197
  simp only [CollatzResearch.WordTrace]
  refine ⟨297152686665104174315271845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198101791110069449543514563 297152686665104174315271845)
  ·
    refine ⟨55716128749707032684113471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297152686665104174315271845 55716128749707032684113471)
    ·
      refine ⟨83574193124560549026170207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55716128749707032684113471 83574193124560549026170207)
      ·
        refine ⟨125361289686840823539255311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83574193124560549026170207 125361289686840823539255311)
        ·
          refine ⟨188041934530261235308882967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125361289686840823539255311 188041934530261235308882967)
          ·
            refine ⟨282062901795391852963324451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188041934530261235308882967 282062901795391852963324451)
            ·
              refine ⟨423094352693087779444986677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282062901795391852963324451 423094352693087779444986677)
              ·
                refine ⟨39665095564976979322967501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 423094352693087779444986677 39665095564976979322967501)
                ·
                  refine ⟨14874410836866367246112813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39665095564976979322967501 14874410836866367246112813)
                  ·
                    refine ⟨5577904063824887717292305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14874410836866367246112813 5577904063824887717292305)
                    ·
                      refine ⟨4183428047868665787969229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577904063824887717292305 4183428047868665787969229)
                      ·
                        rfl

theorem cell23_8147197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_8147197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147197 prefixEnd_8147197 := by exact prefixLift 8147197
  have htrace : WordTrace (prefixWord ++ tailWord_8147197) baseStart_8147197 baseEnd_8147197 := by
    simpa [prefixWord, tailWord_8147197, baseEnd_8147197] using wordTrace_append hprefix tailTrace_8147197
  have hstable : (prefixWord ++ tailWord_8147197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147197).length < 2 ^ (prefixWord ++ tailWord_8147197).sum := by decide
  have hdescent : baseEnd_8147197 < baseStart_8147197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147214 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_8147214 : Nat := 118140960795 + 8147214 * 2 ^ 59
def prefixEnd_8147214 : Nat := 4983230072969 + 3 ^ 40 * 8147214 * 2
def baseEnd_8147214 : Nat := 4183436777039792221456651

theorem tailTrace_8147214 : CollatzResearch.WordTrace tailWord_8147214 prefixEnd_8147214 4183436777039792221456651 := by
  unfold tailWord_8147214
  simp only [CollatzResearch.WordTrace]
  refine ⟨37144163338255323277330087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198102204470695057479093797 37144163338255323277330087)
  ·
    refine ⟨55716245007382984915995131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37144163338255323277330087 55716245007382984915995131)
    ·
      refine ⟨83574367511074477373992697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55716245007382984915995131 83574367511074477373992697)
      ·
        refine ⟨62680775633305858030494523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83574367511074477373992697 62680775633305858030494523)
        ·
          refine ⟨94021163449958787045741785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62680775633305858030494523 94021163449958787045741785)
          ·
            refine ⟨70515872587469090284306339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94021163449958787045741785 70515872587469090284306339)
            ·
              refine ⟨105773808881203635426459509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70515872587469090284306339 105773808881203635426459509)
              ·
                refine ⟨9916294582612840821230579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105773808881203635426459509 9916294582612840821230579)
                ·
                  refine ⟨14874441873919261231845869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916294582612840821230579 14874441873919261231845869)
                  ·
                    refine ⟨5577915702719722961942201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14874441873919261231845869 5577915702719722961942201)
                    ·
                      refine ⟨4183436777039792221456651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577915702719722961942201 4183436777039792221456651)
                      ·
                        rfl

theorem cell23_8147214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_8147214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147214 prefixEnd_8147214 := by exact prefixLift 8147214
  have htrace : WordTrace (prefixWord ++ tailWord_8147214) baseStart_8147214 baseEnd_8147214 := by
    simpa [prefixWord, tailWord_8147214, baseEnd_8147214] using wordTrace_append hprefix tailTrace_8147214
  have hstable : (prefixWord ++ tailWord_8147214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147214).length < 2 ^ (prefixWord ++ tailWord_8147214).sum := by decide
  have hdescent : baseEnd_8147214 < baseStart_8147214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147284 : List Nat := [2, 4, 1, 1, 2, 3, 1, 4, 5]
def baseStart_8147284 : Nat := 118140960795 + 8147284 * 2 ^ 59
def prefixEnd_8147284 : Nat := 4983230072969 + 3 ^ 40 * 8147284 * 2
def baseEnd_8147284 : Nat := 464830302298400771953481

theorem tailTrace_8147284 : CollatzResearch.WordTrace tailWord_8147284 prefixEnd_8147284 464830302298400771953481 := by
  unfold tailWord_8147284
  simp only [CollatzResearch.WordTrace]
  refine ⟨148577929907894494086844453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198103906543859325449125937 148577929907894494086844453)
  ·
    refine ⟨27858361857730217641283335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148577929907894494086844453 27858361857730217641283335)
    ·
      refine ⟨41787542786595326461925003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27858361857730217641283335 41787542786595326461925003)
      ·
        refine ⟨62681314179892989692887505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41787542786595326461925003 62681314179892989692887505)
        ·
          refine ⟨47010985634919742269665629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62681314179892989692887505 47010985634919742269665629)
          ·
            refine ⟨17629119613094903351124611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47010985634919742269665629 17629119613094903351124611)
            ·
              refine ⟨26443679419642355026686917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17629119613094903351124611 26443679419642355026686917)
              ·
                refine ⟨4958189891182941567503797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26443679419642355026686917 4958189891182941567503797)
                ·
                  refine ⟨464830302298400771953481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4958189891182941567503797 464830302298400771953481)
                  ·
                    rfl

theorem cell23_8147284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_8147284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147284 prefixEnd_8147284 := by exact prefixLift 8147284
  have htrace : WordTrace (prefixWord ++ tailWord_8147284) baseStart_8147284 baseEnd_8147284 := by
    simpa [prefixWord, tailWord_8147284, baseEnd_8147284] using wordTrace_append hprefix tailTrace_8147284
  have hstable : (prefixWord ++ tailWord_8147284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147284).length < 2 ^ (prefixWord ++ tailWord_8147284).sum := by decide
  have hdescent : baseEnd_8147284 < baseStart_8147284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147287 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 1, 7, 2]
def baseStart_8147287 : Nat := 118140960795 + 8147287 * 2 ^ 59
def prefixEnd_8147287 : Nat := 4983230072969 + 3 ^ 40 * 8147287 * 2
def baseEnd_8147287 : Nat := 4183474261127570435843815

theorem tailTrace_8147287 : CollatzResearch.WordTrace tailWord_8147287 prefixEnd_8147287 4183474261127570435843815 := by
  unfold tailWord_8147287
  simp only [CollatzResearch.WordTrace]
  refine ⟨297155969234778119686048115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198103979489852079790698743 297155969234778119686048115)
  ·
    refine ⟨445733953852167179529072173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297155969234778119686048115 445733953852167179529072173)
    ·
      refine ⟨167150232694562692323402065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445733953852167179529072173 167150232694562692323402065)
      ·
        refine ⟨125362674520922019242551549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167150232694562692323402065 125362674520922019242551549)
        ·
          refine ⟨47011002945345757215956831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125362674520922019242551549 47011002945345757215956831)
          ·
            refine ⟨70516504418018635823935247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47011002945345757215956831 70516504418018635823935247)
            ·
              refine ⟨105774756627027953735902871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70516504418018635823935247 105774756627027953735902871)
              ·
                refine ⟨158662134940541930603854307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105774756627027953735902871 158662134940541930603854307)
                ·
                  refine ⟨237993202410812895905781461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158662134940541930603854307 237993202410812895905781461)
                  ·
                    refine ⟨5577965681503427247791753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 237993202410812895905781461 5577965681503427247791753)
                    ·
                      refine ⟨4183474261127570435843815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5577965681503427247791753 4183474261127570435843815)
                      ·
                        rfl

theorem cell23_8147287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_8147287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147287 prefixEnd_8147287 := by exact prefixLift 8147287
  have htrace : WordTrace (prefixWord ++ tailWord_8147287) baseStart_8147287 baseEnd_8147287 := by
    simpa [prefixWord, tailWord_8147287, baseEnd_8147287] using wordTrace_append hprefix tailTrace_8147287
  have hstable : (prefixWord ++ tailWord_8147287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147287).length < 2 ^ (prefixWord ++ tailWord_8147287).sum := by decide
  have hdescent : baseEnd_8147287 < baseStart_8147287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147314 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_8147314 : Nat := 118140960795 + 8147314 * 2 ^ 59
def prefixEnd_8147314 : Nat := 4983230072969 + 3 ^ 40 * 8147314 * 2
def baseEnd_8147314 : Nat := 1394496041701747276735397

theorem tailTrace_8147314 : CollatzResearch.WordTrace tailWord_8147314 prefixEnd_8147314 1394496041701747276735397 := by
  unfold tailWord_8147314
  simp only [CollatzResearch.WordTrace]
  refine ⟨74289238501420075824320249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198104636003786868864853997 74289238501420075824320249)
  ·
    refine ⟨55716928876065056868240187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74289238501420075824320249 55716928876065056868240187)
    ·
      refine ⟨83575393314097585302360281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55716928876065056868240187 83575393314097585302360281)
      ·
        refine ⟨62681544985573188976770211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83575393314097585302360281 62681544985573188976770211)
        ·
          refine ⟨94022317478359783465155317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62681544985573188976770211 94022317478359783465155317)
          ·
            refine ⟨8814592263596229699858311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94022317478359783465155317 8814592263596229699858311)
            ·
              refine ⟨13221888395394344549787467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814592263596229699858311 13221888395394344549787467)
              ·
                refine ⟨19832832593091516824681201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13221888395394344549787467 19832832593091516824681201)
                ·
                  refine ⟨14874624444818637618510901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19832832593091516824681201 14874624444818637618510901)
                  ·
                    refine ⟨1394496041701747276735397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14874624444818637618510901 1394496041701747276735397)
                    ·
                      rfl

theorem cell23_8147314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_8147314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147314 prefixEnd_8147314 := by exact prefixLift 8147314
  have htrace : WordTrace (prefixWord ++ tailWord_8147314) baseStart_8147314 baseEnd_8147314 := by
    simpa [prefixWord, tailWord_8147314, baseEnd_8147314] using wordTrace_append hprefix tailTrace_8147314
  have hstable : (prefixWord ++ tailWord_8147314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147314).length < 2 ^ (prefixWord ++ tailWord_8147314).sum := by decide
  have hdescent : baseEnd_8147314 < baseStart_8147314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147318 : List Nat := [5, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_8147318 : Nat := 118140960795 + 8147318 * 2 ^ 59
def prefixEnd_8147318 : Nat := 4983230072969 + 3 ^ 40 * 8147318 * 2
def baseEnd_8147318 : Nat := 464832242114206646061797

theorem tailTrace_8147318 : CollatzResearch.WordTrace tailWord_8147318 prefixEnd_8147318 464832242114206646061797 := by
  unfold tailWord_8147318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18572318743604113248776663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198104733265110541320284405 18572318743604113248776663)
  ·
    refine ⟨27858478115406169873164995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18572318743604113248776663 27858478115406169873164995)
    ·
      refine ⟨41787717173109254809747493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27858478115406169873164995 41787717173109254809747493)
      ·
        refine ⟨7835196969957985276827655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41787717173109254809747493 7835196969957985276827655)
        ·
          refine ⟨11752795454936977915241483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835196969957985276827655 11752795454936977915241483)
          ·
            refine ⟨17629193182405466872862225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11752795454936977915241483 17629193182405466872862225)
            ·
              refine ⟨13221894886804100154646669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17629193182405466872862225 13221894886804100154646669)
              ·
                refine ⟨4958210582551537557992501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13221894886804100154646669 4958210582551537557992501)
                ·
                  refine ⟨464832242114206646061797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4958210582551537557992501 464832242114206646061797)
                  ·
                    rfl

theorem cell23_8147318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_8147318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147318 prefixEnd_8147318 := by exact prefixLift 8147318
  have htrace : WordTrace (prefixWord ++ tailWord_8147318) baseStart_8147318 baseEnd_8147318 := by
    simpa [prefixWord, tailWord_8147318, baseEnd_8147318] using wordTrace_append hprefix tailTrace_8147318
  have hstable : (prefixWord ++ tailWord_8147318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147318).length < 2 ^ (prefixWord ++ tailWord_8147318).sum := by decide
  have hdescent : baseEnd_8147318 < baseStart_8147318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147401 : List Nat := [1, 2, 1, 1, 2, 1, 4, 6, 1, 1, 3]
def baseStart_8147401 : Nat := 118140960795 + 8147401 * 2 ^ 59
def prefixEnd_8147401 : Nat := 4983230072969 + 3 ^ 40 * 8147401 * 2
def baseEnd_8147401 : Nat := 4183532797922182989818291

theorem tailTrace_8147401 : CollatzResearch.WordTrace tailWord_8147401 prefixEnd_8147401 4183532797922182989818291 := by
  unfold tailWord_8147401
  simp only [CollatzResearch.WordTrace]
  refine ⟨297160127156365117155698057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198106751437576744770465371 297160127156365117155698057)
  ·
    refine ⟨222870095367273837866773543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297160127156365117155698057 222870095367273837866773543)
    ·
      refine ⟨334305143050910756800160315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222870095367273837866773543 334305143050910756800160315)
      ·
        refine ⟨501457714576366135200240473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334305143050910756800160315 501457714576366135200240473)
        ·
          refine ⟨376093285932274601400180355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501457714576366135200240473 376093285932274601400180355)
          ·
            refine ⟨564139928898411902100270533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376093285932274601400180355 564139928898411902100270533)
            ·
              refine ⟨105776236668452231643800725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 564139928898411902100270533 105776236668452231643800725)
              ·
                refine ⟨4958261093833698358303159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105776236668452231643800725 4958261093833698358303159)
                ·
                  refine ⟨7437391640750547537454739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958261093833698358303159 7437391640750547537454739)
                  ·
                    refine ⟨11156087461125821306182109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7437391640750547537454739 11156087461125821306182109)
                    ·
                      refine ⟨4183532797922182989818291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11156087461125821306182109 4183532797922182989818291)
                      ·
                        rfl

theorem cell23_8147401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 1, 3].length) (baseStart_8147401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147401 prefixEnd_8147401 := by exact prefixLift 8147401
  have htrace : WordTrace (prefixWord ++ tailWord_8147401) baseStart_8147401 baseEnd_8147401 := by
    simpa [prefixWord, tailWord_8147401, baseEnd_8147401] using wordTrace_append hprefix tailTrace_8147401
  have hstable : (prefixWord ++ tailWord_8147401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147401).length < 2 ^ (prefixWord ++ tailWord_8147401).sum := by decide
  have hdescent : baseEnd_8147401 < baseStart_8147401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147407 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_8147407 : Nat := 118140960795 + 8147407 * 2 ^ 59
def prefixEnd_8147407 : Nat := 4983230072969 + 3 ^ 40 * 8147407 * 2
def baseEnd_8147407 : Nat := 4183535878806109966343263

theorem tailTrace_8147407 : CollatzResearch.WordTrace tailWord_8147407 prefixEnd_8147407 4183535878806109966343263 := by
  unfold tailWord_8147407
  simp only [CollatzResearch.WordTrace]
  refine ⟨297160345994343380180416475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198106897329562253453610983 297160345994343380180416475)
  ·
    refine ⟨445740518991515070270624713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297160345994343380180416475 445740518991515070270624713)
    ·
      refine ⟨334305389243636302702968535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445740518991515070270624713 334305389243636302702968535)
      ·
        refine ⟨501458083865454454054452803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334305389243636302702968535 501458083865454454054452803)
        ·
          refine ⟨752187125798181681081679205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501458083865454454054452803 752187125798181681081679205)
          ·
            refine ⟨141035086087159065202814851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 752187125798181681081679205 141035086087159065202814851)
            ·
              refine ⟨211552629130738597804222277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141035086087159065202814851 211552629130738597804222277)
              ·
                refine ⟨39666117962013487088291677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211552629130738597804222277 39666117962013487088291677)
                ·
                  refine ⟨14874794235755057658109379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39666117962013487088291677 14874794235755057658109379)
                  ·
                    refine ⟨22312191353632586487164069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14874794235755057658109379 22312191353632586487164069)
                    ·
                      refine ⟨4183535878806109966343263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22312191353632586487164069 4183535878806109966343263)
                      ·
                        rfl

theorem cell23_8147407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_8147407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147407 prefixEnd_8147407 := by exact prefixLift 8147407
  have htrace : WordTrace (prefixWord ++ tailWord_8147407) baseStart_8147407 baseEnd_8147407 := by
    simpa [prefixWord, tailWord_8147407, baseEnd_8147407] using wordTrace_append hprefix tailTrace_8147407
  have hstable : (prefixWord ++ tailWord_8147407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147407).length < 2 ^ (prefixWord ++ tailWord_8147407).sum := by decide
  have hdescent : baseEnd_8147407 < baseStart_8147407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147417 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 1, 6]
def baseStart_8147417 : Nat := 118140960795 + 8147417 * 2 ^ 59
def prefixEnd_8147417 : Nat := 4983230072969 + 3 ^ 40 * 8147417 * 2
def baseEnd_8147417 : Nat := 1394513671204218309072739

theorem tailTrace_8147417 : CollatzResearch.WordTrace tailWord_8147417 prefixEnd_8147417 1394513671204218309072739 := by
  unfold tailWord_8147417
  simp only [CollatzResearch.WordTrace]
  refine ⟨297160710724307151888280505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198107140482871434592187003 297160710724307151888280505)
  ·
    refine ⟨222870533043230363916210379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297160710724307151888280505 222870533043230363916210379)
    ·
      refine ⟨334305799564845545874315569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222870533043230363916210379 334305799564845545874315569)
      ·
        refine ⟨250729349673634159405736677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334305799564845545874315569 250729349673634159405736677)
        ·
          refine ⟨47011753063806404888575627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250729349673634159405736677 47011753063806404888575627)
          ·
            refine ⟨70517629595709607332863441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47011753063806404888575627 70517629595709607332863441)
            ·
              refine ⟨52888222196782205499647581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70517629595709607332863441 52888222196782205499647581)
              ·
                refine ⟨19833083323793327062367843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52888222196782205499647581 19833083323793327062367843)
                ·
                  refine ⟨29749624985689990593551765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19833083323793327062367843 29749624985689990593551765)
                  ·
                    refine ⟨1394513671204218309072739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29749624985689990593551765 1394513671204218309072739)
                    ·
                      rfl

theorem cell23_8147417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_8147417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147417 prefixEnd_8147417 := by exact prefixLift 8147417
  have htrace : WordTrace (prefixWord ++ tailWord_8147417) baseStart_8147417 baseEnd_8147417 := by
    simpa [prefixWord, tailWord_8147417, baseEnd_8147417] using wordTrace_append hprefix tailTrace_8147417
  have hstable : (prefixWord ++ tailWord_8147417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147417).length < 2 ^ (prefixWord ++ tailWord_8147417).sum := by decide
  have hdescent : baseEnd_8147417 < baseStart_8147417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147434 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_8147434 : Nat := 118140960795 + 8147434 * 2 ^ 59
def prefixEnd_8147434 : Nat := 4983230072969 + 3 ^ 40 * 8147434 * 2
def baseEnd_8147434 : Nat := 1394516580927927120235213

theorem tailTrace_8147434 : CollatzResearch.WordTrace tailWord_8147434 prefixEnd_8147434 1394516580927927120235213 := by
  unfold tailWord_8147434
  simp only [CollatzResearch.WordTrace]
  refine ⟨74290332691311390947912339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198107553843497042527766237 74290332691311390947912339)
  ·
    refine ⟨111435499036967086421868509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74290332691311390947912339 111435499036967086421868509)
    ·
      refine ⟨41788312138862657408200691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111435499036967086421868509 41788312138862657408200691)
      ·
        refine ⟨62682468208293986112301037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41788312138862657408200691 62682468208293986112301037)
        ·
          refine ⟨23505925578110244792112889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62682468208293986112301037 23505925578110244792112889)
          ·
            refine ⟨17629444183582683594084667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23505925578110244792112889 17629444183582683594084667)
            ·
              refine ⟨26444166275374025391127001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17629444183582683594084667 26444166275374025391127001)
              ·
                refine ⟨19833124706530519043345251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26444166275374025391127001 19833124706530519043345251)
                ·
                  refine ⟨29749687059795778565017877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19833124706530519043345251 29749687059795778565017877)
                  ·
                    refine ⟨1394516580927927120235213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29749687059795778565017877 1394516580927927120235213)
                    ·
                      rfl

theorem cell23_8147434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_8147434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147434 prefixEnd_8147434 := by exact prefixLift 8147434
  have htrace : WordTrace (prefixWord ++ tailWord_8147434) baseStart_8147434 baseEnd_8147434 := by
    simpa [prefixWord, tailWord_8147434, baseEnd_8147434] using wordTrace_append hprefix tailTrace_8147434
  have hstable : (prefixWord ++ tailWord_8147434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147434).length < 2 ^ (prefixWord ++ tailWord_8147434).sum := by decide
  have hdescent : baseEnd_8147434 < baseStart_8147434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147441 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 1, 1, 4]
def baseStart_8147441 : Nat := 118140960795 + 8147441 * 2 ^ 59
def prefixEnd_8147441 : Nat := 4983230072969 + 3 ^ 40 * 8147441 * 2
def baseEnd_8147441 : Nat := 4183553337148362833318107

theorem tailTrace_8147441 : CollatzResearch.WordTrace tailWord_8147441 prefixEnd_8147441 4183553337148362833318107 := by
  unfold tailWord_8147441
  simp only [CollatzResearch.WordTrace]
  refine ⟨297161586076220203987154177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198107724050813469324769451 297161586076220203987154177)
  ·
    refine ⟨222871189557165152990365633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297161586076220203987154177 222871189557165152990365633)
    ·
      refine ⟨167153392167873864742774225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222871189557165152990365633 167153392167873864742774225)
      ·
        refine ⟨125365044125905398557080669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167153392167873864742774225 125365044125905398557080669)
        ·
          refine ⟨47011891547214524458905251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125365044125905398557080669 47011891547214524458905251)
          ·
            refine ⟨70517837320821786688357877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47011891547214524458905251 70517837320821786688357877)
            ·
              refine ⟨6611047248827042502033551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70517837320821786688357877 6611047248827042502033551)
              ·
                refine ⟨9916570873240563753050327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6611047248827042502033551 9916570873240563753050327)
                ·
                  refine ⟨14874856309860845629575491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916570873240563753050327 14874856309860845629575491)
                  ·
                    refine ⟨22312284464791268444363237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14874856309860845629575491 22312284464791268444363237)
                    ·
                      refine ⟨4183553337148362833318107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22312284464791268444363237 4183553337148362833318107)
                      ·
                        rfl

theorem cell23_8147441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_8147441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147441 prefixEnd_8147441 := by exact prefixLift 8147441
  have htrace : WordTrace (prefixWord ++ tailWord_8147441) baseStart_8147441 baseEnd_8147441 := by
    simpa [prefixWord, tailWord_8147441, baseEnd_8147441] using wordTrace_append hprefix tailTrace_8147441
  have hstable : (prefixWord ++ tailWord_8147441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147441).length < 2 ^ (prefixWord ++ tailWord_8147441).sum := by decide
  have hdescent : baseEnd_8147441 < baseStart_8147441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147477 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_8147477 : Nat := 118140960795 + 8147477 * 2 ^ 59
def prefixEnd_8147477 : Nat := 4983230072969 + 3 ^ 40 * 8147477 * 2
def baseEnd_8147477 : Nat := 1394523940817308230822647

theorem tailTrace_8147477 : CollatzResearch.WordTrace tailWord_8147477 prefixEnd_8147477 1394523940817308230822647 := by
  unfold tailWord_8147477
  simp only [CollatzResearch.WordTrace]
  refine ⟨297162899104089782135464685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198108599402726521423643123 297162899104089782135464685)
  ·
    refine ⟨111436087164033668300799257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297162899104089782135464685 111436087164033668300799257)
    ·
      refine ⟨83577065373025251225599443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111436087164033668300799257 83577065373025251225599443)
      ·
        refine ⟨125365598059537876838399165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83577065373025251225599443 125365598059537876838399165)
        ·
          refine ⟨47012099272326703814399687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125365598059537876838399165 47012099272326703814399687)
          ·
            refine ⟨70518148908490055721599531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47012099272326703814399687 70518148908490055721599531)
            ·
              refine ⟨105777223362735083582399297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70518148908490055721599531 105777223362735083582399297)
              ·
                refine ⟨79332917522051312686799473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105777223362735083582399297 79332917522051312686799473)
                ·
                  refine ⟨59499688141538484515099605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79332917522051312686799473 59499688141538484515099605)
                  ·
                    refine ⟨1394523940817308230822647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59499688141538484515099605 1394523940817308230822647)
                    ·
                      rfl

theorem cell23_8147477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_8147477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147477 prefixEnd_8147477 := by exact prefixLift 8147477
  have htrace : WordTrace (prefixWord ++ tailWord_8147477) baseStart_8147477 baseEnd_8147477 := by
    simpa [prefixWord, tailWord_8147477, baseEnd_8147477] using wordTrace_append hprefix tailTrace_8147477
  have hstable : (prefixWord ++ tailWord_8147477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147477).length < 2 ^ (prefixWord ++ tailWord_8147477).sum := by decide
  have hdescent : baseEnd_8147477 < baseStart_8147477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147487 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_8147487 : Nat := 118140960795 + 8147487 * 2 ^ 59
def prefixEnd_8147487 : Nat := 4983230072969 + 3 ^ 40 * 8147487 * 2
def baseEnd_8147487 : Nat := 4183576957258469653342895

theorem tailTrace_8147487 : CollatzResearch.WordTrace tailWord_8147487 prefixEnd_8147487 4183576957258469653342895 := by
  unfold tailWord_8147487
  simp only [CollatzResearch.WordTrace]
  refine ⟨297163263834053553843328715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198108842556035702562219143 297163263834053553843328715)
  ·
    refine ⟨445744895751080330764993073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297163263834053553843328715 445744895751080330764993073)
    ·
      refine ⟨334308671813310248073744805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445744895751080330764993073 334308671813310248073744805)
      ·
        refine ⟨62682875964995671513827151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334308671813310248073744805 62682875964995671513827151)
        ·
          refine ⟨94024313947493507270740727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62682875964995671513827151 94024313947493507270740727)
          ·
            refine ⟨141036470921240260906111091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94024313947493507270740727 141036470921240260906111091)
            ·
              refine ⟨211554706381860391359166637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141036470921240260906111091 211554706381860391359166637)
              ·
                refine ⟨79333014893197646759687489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211554706381860391359166637 79333014893197646759687489)
                ·
                  refine ⟨59499761169898235069765617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79333014893197646759687489 59499761169898235069765617)
                  ·
                    refine ⟨44624820877423676302324213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59499761169898235069765617 44624820877423676302324213)
                    ·
                      refine ⟨4183576957258469653342895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44624820877423676302324213 4183576957258469653342895)
                      ·
                        rfl

theorem cell23_8147487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_8147487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147487 prefixEnd_8147487 := by exact prefixLift 8147487
  have htrace : WordTrace (prefixWord ++ tailWord_8147487) baseStart_8147487 baseEnd_8147487 := by
    simpa [prefixWord, tailWord_8147487, baseEnd_8147487] using wordTrace_append hprefix tailTrace_8147487
  have hstable : (prefixWord ++ tailWord_8147487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147487).length < 2 ^ (prefixWord ++ tailWord_8147487).sum := by decide
  have hdescent : baseEnd_8147487 < baseStart_8147487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147492 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_8147492 : Nat := 118140960795 + 8147492 * 2 ^ 59
def prefixEnd_8147492 : Nat := 4983230072969 + 3 ^ 40 * 8147492 * 2
def baseEnd_8147492 : Nat := 4183579524661742133780373

theorem tailTrace_8147492 : CollatzResearch.WordTrace tailWord_8147492 prefixEnd_8147492 4183579524661742133780373 := by
  unfold tailWord_8147492
  simp only [CollatzResearch.WordTrace]
  refine ⟨148581723099517719848630365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198108964132690293131507153 148581723099517719848630365)
  ·
    refine ⟨55718146162319144943236387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148581723099517719848630365 55718146162319144943236387)
    ·
      refine ⟨83577219243478717414854581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55718146162319144943236387 83577219243478717414854581)
      ·
        refine ⟨7835364304076129757642617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83577219243478717414854581 7835364304076129757642617)
        ·
          refine ⟨5876523228057097318231963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7835364304076129757642617 5876523228057097318231963)
          ·
            refine ⟨8814784842085645977347945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876523228057097318231963 8814784842085645977347945)
            ·
              refine ⟨6611088631564234483010959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8814784842085645977347945 6611088631564234483010959)
              ·
                refine ⟨9916632947346351724516439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6611088631564234483010959 9916632947346351724516439)
                ·
                  refine ⟨14874949421019527586774659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916632947346351724516439 14874949421019527586774659)
                  ·
                    refine ⟨22312424131529291380161989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14874949421019527586774659 22312424131529291380161989)
                    ·
                      refine ⟨4183579524661742133780373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22312424131529291380161989 4183579524661742133780373)
                      ·
                        rfl

theorem cell23_8147492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_8147492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147492 prefixEnd_8147492 := by exact prefixLift 8147492
  have htrace : WordTrace (prefixWord ++ tailWord_8147492) baseStart_8147492 baseEnd_8147492 := by
    simpa [prefixWord, tailWord_8147492, baseEnd_8147492] using wordTrace_append hprefix tailTrace_8147492
  have hstable : (prefixWord ++ tailWord_8147492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147492).length < 2 ^ (prefixWord ++ tailWord_8147492).sum := by decide
  have hdescent : baseEnd_8147492 < baseStart_8147492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147495 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_8147495 : Nat := 118140960795 + 8147495 * 2 ^ 59
def prefixEnd_8147495 : Nat := 4983230072969 + 3 ^ 40 * 8147495 * 2
def baseEnd_8147495 : Nat := 4183581065103705622042859

theorem tailTrace_8147495 : CollatzResearch.WordTrace tailWord_8147495 prefixEnd_8147495 4183581065103705622042859 := by
  unfold tailWord_8147495
  simp only [CollatzResearch.WordTrace]
  refine ⟨297163555618024571209619939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198109037078683047473079959 297163555618024571209619939)
  ·
    refine ⟨445745333427036856814429909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297163555618024571209619939 445745333427036856814429909)
    ·
      refine ⟨10447156252196176331588201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 445745333427036856814429909 10447156252196176331588201)
      ·
        refine ⟨7835367189147132248691151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10447156252196176331588201 7835367189147132248691151)
        ·
          refine ⟨11753050783720698373036727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835367189147132248691151 11753050783720698373036727)
          ·
            refine ⟨17629576175581047559555091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11753050783720698373036727 17629576175581047559555091)
            ·
              refine ⟨26444364263371571339332637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17629576175581047559555091 26444364263371571339332637)
              ·
                refine ⟨9916636598764339252249739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26444364263371571339332637 9916636598764339252249739)
                ·
                  refine ⟨14874954898146508878374609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916636598764339252249739 14874954898146508878374609)
                  ·
                    refine ⟨11156216173609881658780957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14874954898146508878374609 11156216173609881658780957)
                    ·
                      refine ⟨4183581065103705622042859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11156216173609881658780957 4183581065103705622042859)
                      ·
                        rfl

theorem cell23_8147495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_8147495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147495 prefixEnd_8147495 := by exact prefixLift 8147495
  have htrace : WordTrace (prefixWord ++ tailWord_8147495) baseStart_8147495 baseEnd_8147495 := by
    simpa [prefixWord, tailWord_8147495, baseEnd_8147495] using wordTrace_append hprefix tailTrace_8147495
  have hstable : (prefixWord ++ tailWord_8147495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147495).length < 2 ^ (prefixWord ++ tailWord_8147495).sum := by decide
  have hdescent : baseEnd_8147495 < baseStart_8147495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147507 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 4, 6]
def baseStart_8147507 : Nat := 118140960795 + 8147507 * 2 ^ 59
def prefixEnd_8147507 : Nat := 4983230072969 + 3 ^ 40 * 8147507 * 2
def baseEnd_8147507 : Nat := 1394529075623853191697601

theorem tailTrace_8147507 : CollatzResearch.WordTrace tailWord_8147507 prefixEnd_8147507 1394529075623853191697601 := by
  unfold tailWord_8147507
  simp only [CollatzResearch.WordTrace]
  refine ⟨297163993293981097259056775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198109328862654064839371183 297163993293981097259056775)
  ·
    refine ⟨445745989940971645888585163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297163993293981097259056775 445745989940971645888585163)
    ·
      refine ⟨668618984911457468832877745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445745989940971645888585163 668618984911457468832877745)
      ·
        refine ⟨501464238683593101624658309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668618984911457468832877745 501464238683593101624658309)
        ·
          refine ⟨94024544753173706554623433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501464238683593101624658309 94024544753173706554623433)
          ·
            refine ⟨70518408564880279915967575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94024544753173706554623433 70518408564880279915967575)
            ·
              refine ⟨105777612847320419873951363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70518408564880279915967575 105777612847320419873951363)
              ·
                refine ⟨158666419270980629810927045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105777612847320419873951363 158666419270980629810927045)
                ·
                  refine ⟨29749953613308868089548821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158666419270980629810927045 29749953613308868089548821)
                  ·
                    refine ⟨1394529075623853191697601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29749953613308868089548821 1394529075623853191697601)
                    ·
                      rfl

theorem cell23_8147507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 6].length) (baseStart_8147507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147507 prefixEnd_8147507 := by exact prefixLift 8147507
  have htrace : WordTrace (prefixWord ++ tailWord_8147507) baseStart_8147507 baseEnd_8147507 := by
    simpa [prefixWord, tailWord_8147507, baseEnd_8147507] using wordTrace_append hprefix tailTrace_8147507
  have hstable : (prefixWord ++ tailWord_8147507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147507).length < 2 ^ (prefixWord ++ tailWord_8147507).sum := by decide
  have hdescent : baseEnd_8147507 < baseStart_8147507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147531 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 1, 4, 2]
def baseStart_8147531 : Nat := 118140960795 + 8147531 * 2 ^ 59
def prefixEnd_8147531 : Nat := 4983230072969 + 3 ^ 40 * 8147531 * 2
def baseEnd_8147531 : Nat := 4183599550407267481192693

theorem tailTrace_8147531 : CollatzResearch.WordTrace tailWord_8147531 prefixEnd_8147531 4183599550407267481192693 := by
  unfold tailWord_8147531
  simp only [CollatzResearch.WordTrace]
  refine ⟨297164868645894149357930447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198109912430596099571953631 297164868645894149357930447)
  ·
    refine ⟨445747302968841224036895671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297164868645894149357930447 445747302968841224036895671)
    ·
      refine ⟨668620954453261836055343507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445747302968841224036895671 668620954453261836055343507)
      ·
        refine ⟨1002931431679892754083015261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668620954453261836055343507 1002931431679892754083015261)
        ·
          refine ⟨376099286879959782781130723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1002931431679892754083015261 376099286879959782781130723)
          ·
            refine ⟨564148930319939674171696085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376099286879959782781130723 564148930319939674171696085)
            ·
              refine ⟨13222240554373586113399127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 564148930319939674171696085 13222240554373586113399127)
              ·
                refine ⟨19833360831560379170098691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13222240554373586113399127 19833360831560379170098691)
                ·
                  refine ⟨29750041247340568755148037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19833360831560379170098691 29750041247340568755148037)
                  ·
                    refine ⟨5578132733876356641590257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29750041247340568755148037 5578132733876356641590257)
                    ·
                      refine ⟨4183599550407267481192693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578132733876356641590257 4183599550407267481192693)
                      ·
                        rfl

theorem cell23_8147531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 4, 2].length) (baseStart_8147531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147531 prefixEnd_8147531 := by exact prefixLift 8147531
  have htrace : WordTrace (prefixWord ++ tailWord_8147531) baseStart_8147531 baseEnd_8147531 := by
    simpa [prefixWord, tailWord_8147531, baseEnd_8147531] using wordTrace_append hprefix tailTrace_8147531
  have hstable : (prefixWord ++ tailWord_8147531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147531).length < 2 ^ (prefixWord ++ tailWord_8147531).sum := by decide
  have hdescent : baseEnd_8147531 < baseStart_8147531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147534 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_8147534 : Nat := 118140960795 + 8147534 * 2 ^ 59
def prefixEnd_8147534 : Nat := 4983230072969 + 3 ^ 40 * 8147534 * 2
def baseEnd_8147534 : Nat := 4183601090849230969455179

theorem tailTrace_8147534 : CollatzResearch.WordTrace tailWord_8147534 prefixEnd_8147534 4183601090849230969455179 := by
  unfold tailWord_8147534
  simp only [CollatzResearch.WordTrace]
  refine ⟨37145622258110410108786207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198109985376588853913526437 37145622258110410108786207)
  ·
    refine ⟨55718433387165615163179311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37145622258110410108786207 55718433387165615163179311)
    ·
      refine ⟨83577650080748422744768967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55718433387165615163179311 83577650080748422744768967)
      ·
        refine ⟨125366475121122634117153451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83577650080748422744768967 125366475121122634117153451)
        ·
          refine ⟨188049712681683951175730177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125366475121122634117153451 188049712681683951175730177)
          ·
            refine ⟨141037284511262963381797633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188049712681683951175730177 141037284511262963381797633)
            ·
              refine ⟨105777963383447222536348225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141037284511262963381797633 105777963383447222536348225)
              ·
                refine ⟨79333472537585416902261169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105777963383447222536348225 79333472537585416902261169)
                ·
                  refine ⟨59500104403189062676695877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79333472537585416902261169 59500104403189062676695877)
                  ·
                    refine ⟨11156269575597949251880477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59500104403189062676695877 11156269575597949251880477)
                    ·
                      refine ⟨4183601090849230969455179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11156269575597949251880477 4183601090849230969455179)
                      ·
                        rfl

theorem cell23_8147534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_8147534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147534 prefixEnd_8147534 := by exact prefixLift 8147534
  have htrace : WordTrace (prefixWord ++ tailWord_8147534) baseStart_8147534 baseEnd_8147534 := by
    simpa [prefixWord, tailWord_8147534, baseEnd_8147534] using wordTrace_append hprefix tailTrace_8147534
  have hstable : (prefixWord ++ tailWord_8147534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147534).length < 2 ^ (prefixWord ++ tailWord_8147534).sum := by decide
  have hdescent : baseEnd_8147534 < baseStart_8147534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147564 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_8147564 : Nat := 118140960795 + 8147564 * 2 ^ 59
def prefixEnd_8147564 : Nat := 4983230072969 + 3 ^ 40 * 8147564 * 2
def baseEnd_8147564 : Nat := 4183616495268865852080041

theorem tailTrace_8147564 : CollatzResearch.WordTrace tailWord_8147564 prefixEnd_8147564 4183616495268865852080041 := by
  unfold tailWord_8147564
  simp only [CollatzResearch.WordTrace]
  refine ⟨148583036127387297996940873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198110714836516397329254497 148583036127387297996940873)
  ·
    refine ⟨111437277095540473497705655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148583036127387297996940873 111437277095540473497705655)
    ·
      refine ⟨167155915643310710246558483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111437277095540473497705655 167155915643310710246558483)
      ·
        refine ⟨250733873464966065369837725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167155915643310710246558483 250733873464966065369837725)
        ·
          refine ⟨94025202549362274513689147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250733873464966065369837725 94025202549362274513689147)
          ·
            refine ⟨141037803824043411770533721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94025202549362274513689147 141037803824043411770533721)
            ·
              refine ⟨105778352868032558827900291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141037803824043411770533721 105778352868032558827900291)
              ·
                refine ⟨158667529302048838241850437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105778352868032558827900291 158667529302048838241850437)
                ·
                  refine ⟨29750161744134157170346957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158667529302048838241850437 29750161744134157170346957)
                  ·
                    refine ⟨11156310654050308938880109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29750161744134157170346957 11156310654050308938880109)
                    ·
                      refine ⟨4183616495268865852080041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11156310654050308938880109 4183616495268865852080041)
                      ·
                        rfl

theorem cell23_8147564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_8147564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147564 prefixEnd_8147564 := by exact prefixLift 8147564
  have htrace : WordTrace (prefixWord ++ tailWord_8147564) baseStart_8147564 baseEnd_8147564 := by
    simpa [prefixWord, tailWord_8147564, baseEnd_8147564] using wordTrace_append hprefix tailTrace_8147564
  have hstable : (prefixWord ++ tailWord_8147564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147564).length < 2 ^ (prefixWord ++ tailWord_8147564).sum := by decide
  have hdescent : baseEnd_8147564 < baseStart_8147564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147586 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_8147586 : Nat := 118140960795 + 8147586 * 2 ^ 59
def prefixEnd_8147586 : Nat := 4983230072969 + 3 ^ 40 * 8147586 * 2
def baseEnd_8147586 : Nat := 4183627791843264766004941

theorem tailTrace_8147586 : CollatzResearch.WordTrace tailWord_8147586 prefixEnd_8147586 4183627791843264766004941 := by
  unfold tailWord_8147586
  simp only [CollatzResearch.WordTrace]
  refine ⟨74291718665173723437795653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198111249773796595834121741 74291718665173723437795653)
  ·
    refine ⟨13929697249720073144586685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74291718665173723437795653 13929697249720073144586685)
    ·
      refine ⟨5223636468645027429220007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13929697249720073144586685 5223636468645027429220007)
      ·
        refine ⟨7835454702967541143830011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5223636468645027429220007 7835454702967541143830011)
        ·
          refine ⟨11753182054451311715745017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835454702967541143830011 11753182054451311715745017)
          ·
            refine ⟨8814886540838483786808763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11753182054451311715745017 8814886540838483786808763)
            ·
              refine ⟨13222329811257725680213145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814886540838483786808763 13222329811257725680213145)
              ·
                refine ⟨9916747358443294260159859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13222329811257725680213145 9916747358443294260159859)
                ·
                  refine ⟨14875121037664941390239789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916747358443294260159859 14875121037664941390239789)
                  ·
                    refine ⟨5578170389124353021339921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14875121037664941390239789 5578170389124353021339921)
                    ·
                      refine ⟨4183627791843264766004941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578170389124353021339921 4183627791843264766004941)
                      ·
                        rfl

theorem cell23_8147586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_8147586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147586 prefixEnd_8147586 := by exact prefixLift 8147586
  have htrace : WordTrace (prefixWord ++ tailWord_8147586) baseStart_8147586 baseEnd_8147586 := by
    simpa [prefixWord, tailWord_8147586, baseEnd_8147586] using wordTrace_append hprefix tailTrace_8147586
  have hstable : (prefixWord ++ tailWord_8147586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147586).length < 2 ^ (prefixWord ++ tailWord_8147586).sum := by decide
  have hdescent : baseEnd_8147586 < baseStart_8147586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147621 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 2, 4, 2]
def baseStart_8147621 : Nat := 118140960795 + 8147621 * 2 ^ 59
def prefixEnd_8147621 : Nat := 4983230072969 + 3 ^ 40 * 8147621 * 2
def baseEnd_8147621 : Nat := 4183645763666172129067279

theorem tailTrace_8147621 : CollatzResearch.WordTrace tailWord_8147621 prefixEnd_8147621 4183645763666172129067279 := by
  unfold tailWord_8147621
  simp only [CollatzResearch.WordTrace]
  refine ⟨297168151215568094728706717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198112100810378729819137811 297168151215568094728706717)
  ·
    refine ⟨111438056705838035523265019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297168151215568094728706717 111438056705838035523265019)
    ·
      refine ⟨167157085058757053284897529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111438056705838035523265019 167157085058757053284897529)
      ·
        refine ⟨125367813794067789963673147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167157085058757053284897529 125367813794067789963673147)
        ·
          refine ⟨188051720691101684945509721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125367813794067789963673147 188051720691101684945509721)
          ·
            refine ⟨141038790518326263709132291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188051720691101684945509721 141038790518326263709132291)
            ·
              refine ⟨211558185777489395563698437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141038790518326263709132291 211558185777489395563698437)
              ·
                refine ⟨39667159833279261668193457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211558185777489395563698437 39667159833279261668193457)
                ·
                  refine ⟨29750369874959446251145093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39667159833279261668193457 29750369874959446251145093)
                  ·
                    refine ⟨5578194351554896172089705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29750369874959446251145093 5578194351554896172089705)
                    ·
                      refine ⟨4183645763666172129067279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578194351554896172089705 4183645763666172129067279)
                      ·
                        rfl

theorem cell23_8147621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_8147621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147621 prefixEnd_8147621 := by exact prefixLift 8147621
  have htrace : WordTrace (prefixWord ++ tailWord_8147621) baseStart_8147621 baseEnd_8147621 := by
    simpa [prefixWord, tailWord_8147621, baseEnd_8147621] using wordTrace_append hprefix tailTrace_8147621
  have hstable : (prefixWord ++ tailWord_8147621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147621).length < 2 ^ (prefixWord ++ tailWord_8147621).sum := by decide
  have hdescent : baseEnd_8147621 < baseStart_8147621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147634 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_8147634 : Nat := 118140960795 + 8147634 * 2 ^ 59
def prefixEnd_8147634 : Nat := 4983230072969 + 3 ^ 40 * 8147634 * 2
def baseEnd_8147634 : Nat := 4183652438914680578204719

theorem tailTrace_8147634 : CollatzResearch.WordTrace tailWord_8147634 prefixEnd_8147634 4183652438914680578204719 := by
  unfold tailWord_8147634
  simp only [CollatzResearch.WordTrace]
  refine ⟨74292156341130249487232489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198112416909680665299286637 74292156341130249487232489)
  ·
    refine ⟨55719117255847687115424367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74292156341130249487232489 55719117255847687115424367)
    ·
      refine ⟨83578675883771530673136551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55719117255847687115424367 83578675883771530673136551)
      ·
        refine ⟨125368013825657296009704827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83578675883771530673136551 125368013825657296009704827)
        ·
          refine ⟨188052020738485944014557241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125368013825657296009704827 188052020738485944014557241)
          ·
            refine ⟨141039015553864458010917931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188052020738485944014557241 141039015553864458010917931)
            ·
              refine ⟨211558523330796687016376897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141039015553864458010917931 211558523330796687016376897)
              ·
                refine ⟨158668892498097515262282673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211558523330796687016376897 158668892498097515262282673)
                ·
                  refine ⟨119001669373573136446712005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158668892498097515262282673 119001669373573136446712005)
                  ·
                    refine ⟨22312813007544963083758501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119001669373573136446712005 22312813007544963083758501)
                    ·
                      refine ⟨4183652438914680578204719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22312813007544963083758501 4183652438914680578204719)
                      ·
                        rfl

theorem cell23_8147634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_8147634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147634 prefixEnd_8147634 := by exact prefixLift 8147634
  have htrace : WordTrace (prefixWord ++ tailWord_8147634) baseStart_8147634 baseEnd_8147634 := by
    simpa [prefixWord, tailWord_8147634, baseEnd_8147634] using wordTrace_append hprefix tailTrace_8147634
  have hstable : (prefixWord ++ tailWord_8147634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147634).length < 2 ^ (prefixWord ++ tailWord_8147634).sum := by decide
  have hdescent : baseEnd_8147634 < baseStart_8147634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147658 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_8147658 : Nat := 118140960795 + 8147658 * 2 ^ 59
def prefixEnd_8147658 : Nat := 4983230072969 + 3 ^ 40 * 8147658 * 2
def baseEnd_8147658 : Nat := 4183664762450388484304609

theorem tailTrace_8147658 : CollatzResearch.WordTrace tailWord_8147658 prefixEnd_8147658 4183664762450388484304609 := by
  unfold tailWord_8147658
  simp only [CollatzResearch.WordTrace]
  refine ⟨74292375179108512511950907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198113000477622700031869085 74292375179108512511950907)
  ·
    refine ⟨111438562768662768767926361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74292375179108512511950907 111438562768662768767926361)
    ·
      refine ⟨83578922076497076575944771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111438562768662768767926361 83578922076497076575944771)
      ·
        refine ⟨125368383114745614863917157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83578922076497076575944771 125368383114745614863917157)
        ·
          refine ⟨23506571834014802786984467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125368383114745614863917157 23506571834014802786984467)
          ·
            refine ⟨35259857751022204180476701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23506571834014802786984467 35259857751022204180476701)
            ·
              refine ⟨13222446656633326567678763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35259857751022204180476701 13222446656633326567678763)
              ·
                refine ⟨19833669984949989851518145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13222446656633326567678763 19833669984949989851518145)
                ·
                  refine ⟨14875252488712492388638609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19833669984949989851518145 14875252488712492388638609)
                  ·
                    refine ⟨11156439366534369291478957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14875252488712492388638609 11156439366534369291478957)
                    ·
                      refine ⟨4183664762450388484304609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11156439366534369291478957 4183664762450388484304609)
                      ·
                        rfl

theorem cell23_8147658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_8147658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147658 prefixEnd_8147658 := by exact prefixLift 8147658
  have htrace : WordTrace (prefixWord ++ tailWord_8147658) baseStart_8147658 baseEnd_8147658 := by
    simpa [prefixWord, tailWord_8147658, baseEnd_8147658] using wordTrace_append hprefix tailTrace_8147658
  have hstable : (prefixWord ++ tailWord_8147658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147658).length < 2 ^ (prefixWord ++ tailWord_8147658).sum := by decide
  have hdescent : baseEnd_8147658 < baseStart_8147658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147698 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_8147698 : Nat := 118140960795 + 8147698 * 2 ^ 59
def prefixEnd_8147698 : Nat := 4983230072969 + 3 ^ 40 * 8147698 * 2
def baseEnd_8147698 : Nat := 4183685301676568327804425

theorem tailTrace_8147698 : CollatzResearch.WordTrace tailWord_8147698 prefixEnd_8147698 4183685301676568327804425 := by
  unfold tailWord_8147698
  simp only [CollatzResearch.WordTrace]
  refine ⟨74292739909072284219814937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198113973090859424586173165 74292739909072284219814937)
  ·
    refine ⟨55719554931804213164861203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74292739909072284219814937 55719554931804213164861203)
    ·
      refine ⟨83579332397706319747291805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55719554931804213164861203 83579332397706319747291805)
      ·
        refine ⟨31342249649139869905234427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83579332397706319747291805 31342249649139869905234427)
        ·
          refine ⟨47013374473709804857851641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31342249649139869905234427 47013374473709804857851641)
          ·
            refine ⟨35260030855282353643388731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47013374473709804857851641 35260030855282353643388731)
            ·
              refine ⟨52890046282923530465083097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35260030855282353643388731 52890046282923530465083097)
              ·
                refine ⟨39667534712192647848812323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52890046282923530465083097 39667534712192647848812323)
                ·
                  refine ⟨59501302068288971773218485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39667534712192647848812323 59501302068288971773218485)
                  ·
                    refine ⟨5578247068902091103739233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59501302068288971773218485 5578247068902091103739233)
                    ·
                      refine ⟨4183685301676568327804425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578247068902091103739233 4183685301676568327804425)
                      ·
                        rfl

theorem cell23_8147698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_8147698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147698 prefixEnd_8147698 := by exact prefixLift 8147698
  have htrace : WordTrace (prefixWord ++ tailWord_8147698) baseStart_8147698 baseEnd_8147698 := by
    simpa [prefixWord, tailWord_8147698, baseEnd_8147698] using wordTrace_append hprefix tailTrace_8147698
  have hstable : (prefixWord ++ tailWord_8147698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147698).length < 2 ^ (prefixWord ++ tailWord_8147698).sum := by decide
  have hdescent : baseEnd_8147698 < baseStart_8147698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147708 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_8147708 : Nat := 118140960795 + 8147708 * 2 ^ 59
def prefixEnd_8147708 : Nat := 4983230072969 + 3 ^ 40 * 8147708 * 2
def baseEnd_8147708 : Nat := 1394563478827704429559793

theorem tailTrace_8147708 : CollatzResearch.WordTrace tailWord_8147708 prefixEnd_8147708 1394563478827704429559793 := by
  unfold tailWord_8147708
  simp only [CollatzResearch.WordTrace]
  refine ⟨148585662183126454293561889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198114216244168605724749185 148585662183126454293561889)
  ·
    refine ⟨111439246637344840720171417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148585662183126454293561889 111439246637344840720171417)
    ·
      refine ⟨83579434978008630540128563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111439246637344840720171417 83579434978008630540128563)
      ·
        refine ⟨125369152467012945810192845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83579434978008630540128563 125369152467012945810192845)
        ·
          refine ⟨47013432175129854678822317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125369152467012945810192845 47013432175129854678822317)
          ·
            refine ⟨17630037065673695504558369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47013432175129854678822317 17630037065673695504558369)
            ·
              refine ⟨13222527799255271628418777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17630037065673695504558369 13222527799255271628418777)
              ·
                refine ⟨9916895849441453721314083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13222527799255271628418777 9916895849441453721314083)
                ·
                  refine ⟨14875343774162180581971125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916895849441453721314083 14875343774162180581971125)
                  ·
                    refine ⟨1394563478827704429559793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14875343774162180581971125 1394563478827704429559793)
                    ·
                      rfl

theorem cell23_8147708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_8147708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147708 prefixEnd_8147708 := by exact prefixLift 8147708
  have htrace : WordTrace (prefixWord ++ tailWord_8147708) baseStart_8147708 baseEnd_8147708 := by
    simpa [prefixWord, tailWord_8147708, baseEnd_8147708] using wordTrace_append hprefix tailTrace_8147708
  have hstable : (prefixWord ++ tailWord_8147708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147708).length < 2 ^ (prefixWord ++ tailWord_8147708).sum := by decide
  have hdescent : baseEnd_8147708 < baseStart_8147708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147711 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 1, 8, 2]
def baseStart_8147711 : Nat := 118140960795 + 8147711 * 2 ^ 59
def prefixEnd_8147711 : Nat := 4983230072969 + 3 ^ 40 * 8147711 * 2
def baseEnd_8147711 : Nat := 4183691976925076776941865

theorem tailTrace_8147711 : CollatzResearch.WordTrace tailWord_8147711 prefixEnd_8147711 4183691976925076776941865 := by
  unfold tailWord_8147711
  simp only [CollatzResearch.WordTrace]
  refine ⟨297171433785242040099482987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198114289190161360066321991 297171433785242040099482987)
  ·
    refine ⟨445757150677863060149224481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297171433785242040099482987 445757150677863060149224481)
    ·
      refine ⟨334317863008397295111918361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445757150677863060149224481 334317863008397295111918361)
      ·
        refine ⟨250738397256297971333938771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334317863008397295111918361 250738397256297971333938771)
        ·
          refine ⟨376107595884446957000908157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250738397256297971333938771 376107595884446957000908157)
          ·
            refine ⟨141040348456667608875340559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376107595884446957000908157 141040348456667608875340559)
            ·
              refine ⟨211560522685001413313010839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141040348456667608875340559 211560522685001413313010839)
              ·
                refine ⟨317340784027502119969516259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211560522685001413313010839 317340784027502119969516259)
                ·
                  refine ⟨476011176041253179954274389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317340784027502119969516259 476011176041253179954274389)
                  ·
                    refine ⟨5578255969233435702589153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 476011176041253179954274389 5578255969233435702589153)
                    ·
                      refine ⟨4183691976925076776941865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578255969233435702589153 4183691976925076776941865)
                      ·
                        rfl

theorem cell23_8147711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_8147711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147711 prefixEnd_8147711 := by exact prefixLift 8147711
  have htrace : WordTrace (prefixWord ++ tailWord_8147711) baseStart_8147711 baseEnd_8147711 := by
    simpa [prefixWord, tailWord_8147711, baseEnd_8147711] using wordTrace_append hprefix tailTrace_8147711
  have hstable : (prefixWord ++ tailWord_8147711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147711).length < 2 ^ (prefixWord ++ tailWord_8147711).sum := by decide
  have hdescent : baseEnd_8147711 < baseStart_8147711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147721 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 4, 4]
def baseStart_8147721 : Nat := 118140960795 + 8147721 * 2 ^ 59
def prefixEnd_8147721 : Nat := 4983230072969 + 3 ^ 40 * 8147721 * 2
def baseEnd_8147721 : Nat := 1394565703910540579272273

theorem tailTrace_8147721 : CollatzResearch.WordTrace tailWord_8147721 prefixEnd_8147721 1394565703910540579272273 := by
  unfold tailWord_8147721
  simp only [CollatzResearch.WordTrace]
  refine ⟨297171798515205811807347017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198114532343470541204898011 297171798515205811807347017)
  ·
    refine ⟨222878848886404358855510263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297171798515205811807347017 222878848886404358855510263)
    ·
      refine ⟨334318273329606538283265395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222878848886404358855510263 334318273329606538283265395)
      ·
        refine ⟨501477409994409807424898093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334318273329606538283265395 501477409994409807424898093)
        ·
          refine ⟨188054028747903677784336785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501477409994409807424898093 188054028747903677784336785)
          ·
            refine ⟨141040521560927758338252589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188054028747903677784336785 141040521560927758338252589)
            ·
              refine ⟨52890195585347909376844721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141040521560927758338252589 52890195585347909376844721)
              ·
                refine ⟨39667646689010932032633541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52890195585347909376844721 39667646689010932032633541)
                ·
                  refine ⟨7437683754189549756118789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39667646689010932032633541 7437683754189549756118789)
                  ·
                    refine ⟨1394565703910540579272273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437683754189549756118789 1394565703910540579272273)
                    ·
                      rfl

theorem cell23_8147721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 4].length) (baseStart_8147721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147721 prefixEnd_8147721 := by exact prefixLift 8147721
  have htrace : WordTrace (prefixWord ++ tailWord_8147721) baseStart_8147721 baseEnd_8147721 := by
    simpa [prefixWord, tailWord_8147721, baseEnd_8147721] using wordTrace_append hprefix tailTrace_8147721
  have hstable : (prefixWord ++ tailWord_8147721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147721).length < 2 ^ (prefixWord ++ tailWord_8147721).sum := by decide
  have hdescent : baseEnd_8147721 < baseStart_8147721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147731 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 5]
def baseStart_8147731 : Nat := 118140960795 + 8147731 * 2 ^ 59
def prefixEnd_8147731 : Nat := 4983230072969 + 3 ^ 40 * 8147731 * 2
def baseEnd_8147731 : Nat := 4183702246538166698691773

theorem tailTrace_8147731 : CollatzResearch.WordTrace tailWord_8147731 prefixEnd_8147731 4183702246538166698691773 := by
  unfold tailWord_8147731
  simp only [CollatzResearch.WordTrace]
  refine ⟨297172163245169583515211047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198114775496779722343474031 297172163245169583515211047)
  ·
    refine ⟨445758244867754375272816571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297172163245169583515211047 445758244867754375272816571)
    ·
      refine ⟨668637367301631562909224857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445758244867754375272816571 668637367301631562909224857)
      ·
        refine ⟨501478025476223672181918643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668637367301631562909224857 501478025476223672181918643)
        ·
          refine ⟨752217038214335508272877965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501478025476223672181918643 752217038214335508272877965)
          ·
            refine ⟨282081389330375815602329237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 752217038214335508272877965 282081389330375815602329237)
            ·
              refine ⟨13222565124861366356359183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282081389330375815602329237 13222565124861366356359183)
              ·
                refine ⟨19833847687292049534538775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13222565124861366356359183 19833847687292049534538775)
                ·
                  refine ⟨29750771530938074301808163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19833847687292049534538775 29750771530938074301808163)
                  ·
                    refine ⟨44626157296407111452712245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29750771530938074301808163 44626157296407111452712245)
                    ·
                      refine ⟨4183702246538166698691773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44626157296407111452712245 4183702246538166698691773)
                      ·
                        rfl

theorem cell23_8147731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_8147731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147731 prefixEnd_8147731 := by exact prefixLift 8147731
  have htrace : WordTrace (prefixWord ++ tailWord_8147731) baseStart_8147731 baseEnd_8147731 := by
    simpa [prefixWord, tailWord_8147731, baseEnd_8147731] using wordTrace_append hprefix tailTrace_8147731
  have hstable : (prefixWord ++ tailWord_8147731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147731).length < 2 ^ (prefixWord ++ tailWord_8147731).sum := by decide
  have hdescent : baseEnd_8147731 < baseStart_8147731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147738 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_8147738 : Nat := 118140960795 + 8147738 * 2 ^ 59
def prefixEnd_8147738 : Nat := 4983230072969 + 3 ^ 40 * 8147738 * 2
def baseEnd_8147738 : Nat := 1394568613634249390434747

theorem tailTrace_8147738 : CollatzResearch.WordTrace tailWord_8147738 prefixEnd_8147738 1394568613634249390434747 := by
  unfold tailWord_8147738
  simp only [CollatzResearch.WordTrace]
  refine ⟨74293104639036055927678967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198114945704096149140477245 74293104639036055927678967)
  ·
    refine ⟨111439656958554083891518451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74293104639036055927678967 111439656958554083891518451)
    ·
      refine ⟨167159485437831125837277677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111439656958554083891518451 167159485437831125837277677)
      ·
        refine ⟨62684807039186672188979129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167159485437831125837277677 62684807039186672188979129)
        ·
          refine ⟨47013605279390004141734347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62684807039186672188979129 47013605279390004141734347)
          ·
            refine ⟨70520407919085006212601521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47013605279390004141734347 70520407919085006212601521)
            ·
              refine ⟨52890305939313754659451141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70520407919085006212601521 52890305939313754659451141)
              ·
                refine ⟨9916932363621328998647089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52890305939313754659451141 9916932363621328998647089)
                ·
                  refine ⟨7437699272715996748985317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9916932363621328998647089 7437699272715996748985317)
                  ·
                    refine ⟨1394568613634249390434747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437699272715996748985317 1394568613634249390434747)
                    ·
                      rfl

theorem cell23_8147738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_8147738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147738 prefixEnd_8147738 := by exact prefixLift 8147738
  have htrace : WordTrace (prefixWord ++ tailWord_8147738) baseStart_8147738 baseEnd_8147738 := by
    simpa [prefixWord, tailWord_8147738, baseEnd_8147738] using wordTrace_append hprefix tailTrace_8147738
  have hstable : (prefixWord ++ tailWord_8147738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147738).length < 2 ^ (prefixWord ++ tailWord_8147738).sum := by decide
  have hdescent : baseEnd_8147738 < baseStart_8147738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147758 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_8147758 : Nat := 118140960795 + 8147758 * 2 ^ 59
def prefixEnd_8147758 : Nat := 4983230072969 + 3 ^ 40 * 8147758 * 2
def baseEnd_8147758 : Nat := 4183716110515838093054149

theorem tailTrace_8147758 : CollatzResearch.WordTrace tailWord_8147758 prefixEnd_8147758 4183716110515838093054149 := by
  unfold tailWord_8147758
  simp only [CollatzResearch.WordTrace]
  refine ⟨37146643502008970890805491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198115432010714511417629285 37146643502008970890805491)
  ·
    refine ⟨55719965253013456336208237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37146643502008970890805491 55719965253013456336208237)
    ·
      refine ⟨20894986969880046126078089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55719965253013456336208237 20894986969880046126078089)
      ·
        refine ⟨15671240227410034594558567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20894986969880046126078089 15671240227410034594558567)
        ·
          refine ⟨23506860341115051891837851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15671240227410034594558567 23506860341115051891837851)
          ·
            refine ⟨35260290511672577837756777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23506860341115051891837851 35260290511672577837756777)
            ·
              refine ⟨26445217883754433378317583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35260290511672577837756777 26445217883754433378317583)
              ·
                refine ⟨39667826825631650067476375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26445217883754433378317583 39667826825631650067476375)
                ·
                  refine ⟨59501740238447475101214563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39667826825631650067476375 59501740238447475101214563)
                  ·
                    refine ⟨89252610357671212651821845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59501740238447475101214563 89252610357671212651821845)
                    ·
                      refine ⟨4183716110515838093054149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89252610357671212651821845 4183716110515838093054149)
                      ·
                        rfl

theorem cell23_8147758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_8147758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147758 prefixEnd_8147758 := by exact prefixLift 8147758
  have htrace : WordTrace (prefixWord ++ tailWord_8147758) baseStart_8147758 baseEnd_8147758 := by
    simpa [prefixWord, tailWord_8147758, baseEnd_8147758] using wordTrace_append hprefix tailTrace_8147758
  have hstable : (prefixWord ++ tailWord_8147758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147758).length < 2 ^ (prefixWord ++ tailWord_8147758).sum := by decide
  have hdescent : baseEnd_8147758 < baseStart_8147758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147765 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_8147765 : Nat := 118140960795 + 8147765 * 2 ^ 59
def prefixEnd_8147765 : Nat := 4983230072969 + 3 ^ 40 * 8147765 * 2
def baseEnd_8147765 : Nat := 4183719704880419565666617

theorem tailTrace_8147765 : CollatzResearch.WordTrace tailWord_8147765 prefixEnd_8147765 4183719704880419565666617 := by
  unfold tailWord_8147765
  simp only [CollatzResearch.WordTrace]
  refine ⟨297173403327046407321948749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198115602218030938214632499 297173403327046407321948749)
  ·
    refine ⟨111440026247642402745730781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297173403327046407321948749 111440026247642402745730781)
    ·
      refine ⟨41790009842865901029649043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111440026247642402745730781 41790009842865901029649043)
      ·
        refine ⟨62685014764298851544473565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41790009842865901029649043 62685014764298851544473565)
        ·
          refine ⟨23506880536612069329177587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62685014764298851544473565 23506880536612069329177587)
          ·
            refine ⟨35260320804918103993766381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23506880536612069329177587 35260320804918103993766381)
            ·
              refine ⟨13222620301844288997662393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35260320804918103993766381 13222620301844288997662393)
              ·
                refine ⟨9916965226383216748246795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13222620301844288997662393 9916965226383216748246795)
                ·
                  refine ⟨14875447839574825122370193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916965226383216748246795 14875447839574825122370193)
                  ·
                    refine ⟨11156585879681118841777645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14875447839574825122370193 11156585879681118841777645)
                    ·
                      refine ⟨4183719704880419565666617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11156585879681118841777645 4183719704880419565666617)
                      ·
                        rfl

theorem cell23_8147765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_8147765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147765 prefixEnd_8147765 := by exact prefixLift 8147765
  have htrace : WordTrace (prefixWord ++ tailWord_8147765) baseStart_8147765 baseEnd_8147765 := by
    simpa [prefixWord, tailWord_8147765, baseEnd_8147765] using wordTrace_append hprefix tailTrace_8147765
  have hstable : (prefixWord ++ tailWord_8147765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147765).length < 2 ^ (prefixWord ++ tailWord_8147765).sum := by decide
  have hdescent : baseEnd_8147765 < baseStart_8147765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147801 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_8147801 : Nat := 118140960795 + 8147801 * 2 ^ 59
def prefixEnd_8147801 : Nat := 4983230072969 + 3 ^ 40 * 8147801 * 2
def baseEnd_8147801 : Nat := 4183738190183981424816451

theorem tailTrace_8147801 : CollatzResearch.WordTrace tailWord_8147801 prefixEnd_8147801 4183738190183981424816451 := by
  unfold tailWord_8147801
  simp only [CollatzResearch.WordTrace]
  refine ⟨297174716354915985470259257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198116477569943990313506171 297174716354915985470259257)
  ·
    refine ⟨222881037266186989102694443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297174716354915985470259257 222881037266186989102694443)
    ·
      refine ⟨334321555899280483654041665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222881037266186989102694443 334321555899280483654041665)
      ·
        refine ⟨250741166924460362740531249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334321555899280483654041665 250741166924460362740531249)
        ·
          refine ⟨188055875193345272055398437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250741166924460362740531249 188055875193345272055398437)
          ·
            refine ⟨35260476598752238510387207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188055875193345272055398437 35260476598752238510387207)
            ·
              refine ⟨52890714898128357765580811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35260476598752238510387207 52890714898128357765580811)
              ·
                refine ⟨79336072347192536648371217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52890714898128357765580811 79336072347192536648371217)
                ·
                  refine ⟨59502054260394402486278413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79336072347192536648371217 59502054260394402486278413)
                  ·
                    refine ⟨22313270347647900932354405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59502054260394402486278413 22313270347647900932354405)
                    ·
                      refine ⟨4183738190183981424816451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22313270347647900932354405 4183738190183981424816451)
                      ·
                        rfl

theorem cell23_8147801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_8147801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147801 prefixEnd_8147801 := by exact prefixLift 8147801
  have htrace : WordTrace (prefixWord ++ tailWord_8147801) baseStart_8147801 baseEnd_8147801 := by
    simpa [prefixWord, tailWord_8147801, baseEnd_8147801] using wordTrace_append hprefix tailTrace_8147801
  have hstable : (prefixWord ++ tailWord_8147801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147801).length < 2 ^ (prefixWord ++ tailWord_8147801).sum := by decide
  have hdescent : baseEnd_8147801 < baseStart_8147801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147811 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 1, 8]
def baseStart_8147811 : Nat := 118140960795 + 8147811 * 2 ^ 59
def prefixEnd_8147811 : Nat := 4983230072969 + 3 ^ 40 * 8147811 * 2
def baseEnd_8147811 : Nat := 1394581108330175461897135

theorem tailTrace_8147811 : CollatzResearch.WordTrace tailWord_8147811 prefixEnd_8147811 1394581108330175461897135 := by
  unfold tailWord_8147811
  simp only [CollatzResearch.WordTrace]
  refine ⟨297175081084879757178123287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198116720723253171452082191 297175081084879757178123287)
  ·
    refine ⟨445762621627319635767184931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297175081084879757178123287 445762621627319635767184931)
    ·
      refine ⟨668643932440979453650777397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445762621627319635767184931 668643932440979453650777397)
      ·
        refine ⟨62685368666341823779760381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 668643932440979453650777397 62685368666341823779760381)
        ·
          refine ⟨23507013249878183917410143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62685368666341823779760381 23507013249878183917410143)
          ·
            refine ⟨35260519874817275876115215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23507013249878183917410143 35260519874817275876115215)
            ·
              refine ⟨52890779812225913814172823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35260519874817275876115215 52890779812225913814172823)
              ·
                refine ⟨79336169718338870721259235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52890779812225913814172823 79336169718338870721259235)
                ·
                  refine ⟨119004254577508306081888853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79336169718338870721259235 119004254577508306081888853)
                  ·
                    refine ⟨1394581108330175461897135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119004254577508306081888853 1394581108330175461897135)
                    ·
                      rfl

theorem cell23_8147811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 8].length) (baseStart_8147811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147811 prefixEnd_8147811 := by exact prefixLift 8147811
  have htrace : WordTrace (prefixWord ++ tailWord_8147811) baseStart_8147811 baseEnd_8147811 := by
    simpa [prefixWord, tailWord_8147811, baseEnd_8147811] using wordTrace_append hprefix tailTrace_8147811
  have hstable : (prefixWord ++ tailWord_8147811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147811).length < 2 ^ (prefixWord ++ tailWord_8147811).sum := by decide
  have hdescent : baseEnd_8147811 < baseStart_8147811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147848 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_8147848 : Nat := 118140960795 + 8147848 * 2 ^ 59
def prefixEnd_8147848 : Nat := 4983230072969 + 3 ^ 40 * 8147848 * 2
def baseEnd_8147848 : Nat := 4183762323774742740928735

theorem tailTrace_8147848 : CollatzResearch.WordTrace tailWord_8147848 prefixEnd_8147848 4183762323774742740928735 := by
  unfold tailWord_8147848
  simp only [CollatzResearch.WordTrace]
  refine ⟨148588215292872856248610099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198117620390497141664813465 148588215292872856248610099)
  ·
    refine ⟨222882322939309284372915149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148588215292872856248610099 222882322939309284372915149)
    ·
      refine ⟨83580871102240981639843181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222882322939309284372915149 83580871102240981639843181)
      ·
        refine ⟨31342826663340368114941193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83580871102240981639843181 31342826663340368114941193)
        ·
          refine ⟨23507119997505276086205895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31342826663340368114941193 23507119997505276086205895)
          ·
            refine ⟨35260679996257914129308843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23507119997505276086205895 35260679996257914129308843)
            ·
              refine ⟨52891019994386871193963265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35260679996257914129308843 52891019994386871193963265)
              ·
                refine ⟨39668264995790153395472449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52891019994386871193963265 39668264995790153395472449)
                ·
                  refine ⟨29751198746842615046604337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39668264995790153395472449 29751198746842615046604337)
                  ·
                    refine ⟨22313399060131961284953253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29751198746842615046604337 22313399060131961284953253)
                    ·
                      refine ⟨4183762323774742740928735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22313399060131961284953253 4183762323774742740928735)
                      ·
                        rfl

theorem cell23_8147848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_8147848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147848 prefixEnd_8147848 := by exact prefixLift 8147848
  have htrace : WordTrace (prefixWord ++ tailWord_8147848) baseStart_8147848 baseEnd_8147848 := by
    simpa [prefixWord, tailWord_8147848, baseEnd_8147848] using wordTrace_append hprefix tailTrace_8147848
  have hstable : (prefixWord ++ tailWord_8147848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147848).length < 2 ^ (prefixWord ++ tailWord_8147848).sum := by decide
  have hdescent : baseEnd_8147848 < baseStart_8147848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147852 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 2, 2, 2]
def baseStart_8147852 : Nat := 118140960795 + 8147852 * 2 ^ 59
def prefixEnd_8147852 : Nat := 4983230072969 + 3 ^ 40 * 8147852 * 2
def baseEnd_8147852 : Nat := 4183764377697360725278717

theorem tailTrace_8147852 : CollatzResearch.WordTrace tailWord_8147852 prefixEnd_8147852 4183764377697360725278717 := by
  unfold tailWord_8147852
  simp only [CollatzResearch.WordTrace]
  refine ⟨148588288238865610590182905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198117717651820814120243873 148588288238865610590182905)
  ·
    refine ⟨111441216179149207942637179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148588288238865610590182905 111441216179149207942637179)
    ·
      refine ⟨167161824268723811913955769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111441216179149207942637179 167161824268723811913955769)
      ·
        refine ⟨125371368201542858935466827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167161824268723811913955769 125371368201542858935466827)
        ·
          refine ⟨188057052302314288403200241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125371368201542858935466827 188057052302314288403200241)
          ·
            refine ⟨141042789226735716302400181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188057052302314288403200241 141042789226735716302400181)
            ·
              refine ⟨13222761490006473403350017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141042789226735716302400181 13222761490006473403350017)
              ·
                refine ⟨9917071117504855052512513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13222761490006473403350017 9917071117504855052512513)
                ·
                  refine ⟨7437803338128641289384385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9917071117504855052512513 7437803338128641289384385)
                  ·
                    refine ⟨5578352503596480967038289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7437803338128641289384385 5578352503596480967038289)
                    ·
                      refine ⟨4183764377697360725278717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578352503596480967038289 4183764377697360725278717)
                      ·
                        rfl

theorem cell23_8147852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_8147852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147852 prefixEnd_8147852 := by exact prefixLift 8147852
  have htrace : WordTrace (prefixWord ++ tailWord_8147852) baseStart_8147852 baseEnd_8147852 := by
    simpa [prefixWord, tailWord_8147852, baseEnd_8147852] using wordTrace_append hprefix tailTrace_8147852
  have hstable : (prefixWord ++ tailWord_8147852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147852).length < 2 ^ (prefixWord ++ tailWord_8147852).sum := by decide
  have hdescent : baseEnd_8147852 < baseStart_8147852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147862 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_8147862 : Nat := 118140960795 + 8147862 * 2 ^ 59
def prefixEnd_8147862 : Nat := 4983230072969 + 3 ^ 40 * 8147862 * 2
def baseEnd_8147862 : Nat := 1394589837501301895384557

theorem tailTrace_8147862 : CollatzResearch.WordTrace tailWord_8147862 prefixEnd_8147862 1394589837501301895384557 := by
  unfold tailWord_8147862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18573558825480937055514365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198117960805129995258819893 18573558825480937055514365)
  ·
    refine ⟨6965084559555351395817887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18573558825480937055514365 6965084559555351395817887)
    ·
      refine ⟨10447626839333027093726831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6965084559555351395817887 10447626839333027093726831)
      ·
        refine ⟨15671440258999540640590247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10447626839333027093726831 15671440258999540640590247)
        ·
          refine ⟨23507160388499310960885371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15671440258999540640590247 23507160388499310960885371)
          ·
            refine ⟨35260740582748966441328057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23507160388499310960885371 35260740582748966441328057)
            ·
              refine ⟨26445555437061724830996043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35260740582748966441328057 26445555437061724830996043)
              ·
                refine ⟨39668333155592587246494065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26445555437061724830996043 39668333155592587246494065)
                ·
                  refine ⟨29751249866694440434870549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39668333155592587246494065 29751249866694440434870549)
                  ·
                    refine ⟨1394589837501301895384557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29751249866694440434870549 1394589837501301895384557)
                    ·
                      rfl

theorem cell23_8147862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_8147862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147862 prefixEnd_8147862 := by exact prefixLift 8147862
  have htrace : WordTrace (prefixWord ++ tailWord_8147862) baseStart_8147862 baseEnd_8147862 := by
    simpa [prefixWord, tailWord_8147862, baseEnd_8147862] using wordTrace_append hprefix tailTrace_8147862
  have hstable : (prefixWord ++ tailWord_8147862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147862).length < 2 ^ (prefixWord ++ tailWord_8147862).sum := by decide
  have hdescent : baseEnd_8147862 < baseStart_8147862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147869 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_8147869 : Nat := 118140960795 + 8147869 * 2 ^ 59
def prefixEnd_8147869 : Nat := 4983230072969 + 3 ^ 40 * 8147869 * 2
def baseEnd_8147869 : Nat := 4183773106868487158766139

theorem tailTrace_8147869 : CollatzResearch.WordTrace tailWord_8147869 prefixEnd_8147869 4183773106868487158766139 := by
  unfold tailWord_8147869
  simp only [CollatzResearch.WordTrace]
  refine ⟨297177196518669633083734661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198118131012446422055823107 297177196518669633083734661)
  ·
    refine ⟨55720724347250556203200249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297177196518669633083734661 55720724347250556203200249)
    ·
      refine ⟨41790543260437917152400187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55720724347250556203200249 41790543260437917152400187)
      ·
        refine ⟨62685814890656875728600281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41790543260437917152400187 62685814890656875728600281)
        ·
          refine ⟨47014361167992656796450211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62685814890656875728600281 47014361167992656796450211)
          ·
            refine ⟨70521541751988985194675317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47014361167992656796450211 70521541751988985194675317)
            ·
              refine ⟨6611394539248967362000811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70521541751988985194675317 6611394539248967362000811)
              ·
                refine ⟨9917091808873451043001217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6611394539248967362000811 9917091808873451043001217)
                ·
                  refine ⟨7437818856655088282250913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9917091808873451043001217 7437818856655088282250913)
                  ·
                    refine ⟨5578364142491316211688185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7437818856655088282250913 5578364142491316211688185)
                    ·
                      refine ⟨4183773106868487158766139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578364142491316211688185 4183773106868487158766139)
                      ·
                        rfl

theorem cell23_8147869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_8147869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147869 prefixEnd_8147869 := by exact prefixLift 8147869
  have htrace : WordTrace (prefixWord ++ tailWord_8147869) baseStart_8147869 baseEnd_8147869 := by
    simpa [prefixWord, tailWord_8147869, baseEnd_8147869] using wordTrace_append hprefix tailTrace_8147869
  have hstable : (prefixWord ++ tailWord_8147869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147869).length < 2 ^ (prefixWord ++ tailWord_8147869).sum := by decide
  have hdescent : baseEnd_8147869 < baseStart_8147869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147969 : List Nat := [1, 2, 4, 1, 2, 2, 4, 2, 1, 4]
def baseStart_8147969 : Nat := 118140960795 + 8147969 * 2 ^ 59
def prefixEnd_8147969 : Nat := 4983230072969 + 3 ^ 40 * 8147969 * 2
def baseEnd_8147969 : Nat := 1394608151644645589171893

theorem tailTrace_8147969 : CollatzResearch.WordTrace tailWord_8147969 prefixEnd_8147969 1394608151644645589171893 := by
  unfold tailWord_8147969
  simp only [CollatzResearch.WordTrace]
  refine ⟨297180843818307350162374961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198120562545538233441583307 297180843818307350162374961)
  ·
    refine ⟨222885632863730512621781221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297180843818307350162374961 222885632863730512621781221)
    ·
      refine ⟨41791056161949471116583979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222885632863730512621781221 41791056161949471116583979)
      ·
        refine ⟨62686584242924206674875969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41791056161949471116583979 62686584242924206674875969)
        ·
          refine ⟨47014938182193155006156977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62686584242924206674875969 47014938182193155006156977)
          ·
            refine ⟨35261203636644866254617733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47014938182193155006156977 35261203636644866254617733)
            ·
              refine ⟨6611475681870912422740825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35261203636644866254617733 6611475681870912422740825)
              ·
                refine ⟨4958606761403184317055619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6611475681870912422740825 4958606761403184317055619)
                ·
                  refine ⟨7437910142104776475583429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958606761403184317055619 7437910142104776475583429)
                  ·
                    refine ⟨1394608151644645589171893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437910142104776475583429 1394608151644645589171893)
                    ·
                      rfl

theorem cell23_8147969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_8147969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147969 prefixEnd_8147969 := by exact prefixLift 8147969
  have htrace : WordTrace (prefixWord ++ tailWord_8147969) baseStart_8147969 baseEnd_8147969 := by
    simpa [prefixWord, tailWord_8147969, baseEnd_8147969] using wordTrace_append hprefix tailTrace_8147969
  have hstable : (prefixWord ++ tailWord_8147969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147969).length < 2 ^ (prefixWord ++ tailWord_8147969).sum := by decide
  have hdescent : baseEnd_8147969 < baseStart_8147969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147985 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 4, 3, 2]
def baseStart_8147985 : Nat := 118140960795 + 8147985 * 2 ^ 59
def prefixEnd_8147985 : Nat := 4983230072969 + 3 ^ 40 * 8147985 * 2
def baseEnd_8147985 : Nat := 4183832670624408704915605

theorem tailTrace_8147985 : CollatzResearch.WordTrace tailWord_8147985 prefixEnd_8147985 4183832670624408704915605 := by
  unfold tailWord_8147985
  simp only [CollatzResearch.WordTrace]
  refine ⟨297181427386249384894957409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198120951590832923263304939 297181427386249384894957409)
  ·
    refine ⟨222886070539687038671218057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297181427386249384894957409 222886070539687038671218057)
    ·
      refine ⟨167164552904765279003413543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222886070539687038671218057 167164552904765279003413543)
      ·
        refine ⟨250746829357147918505120315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167164552904765279003413543 250746829357147918505120315)
        ·
          refine ⟨376120244035721877757680473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250746829357147918505120315 376120244035721877757680473)
          ·
            refine ⟨282090183026791408318260355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376120244035721877757680473 282090183026791408318260355)
            ·
              refine ⟨423135274540187112477390533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282090183026791408318260355 423135274540187112477390533)
              ·
                refine ⟨79337863976285083589510725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423135274540187112477390533 79337863976285083589510725)
                ·
                  refine ⟨14875849495553453173033261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79337863976285083589510725 14875849495553453173033261)
                  ·
                    refine ⟨5578443560832544939887473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14875849495553453173033261 5578443560832544939887473)
                    ·
                      refine ⟨4183832670624408704915605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578443560832544939887473 4183832670624408704915605)
                      ·
                        rfl

theorem cell23_8147985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_8147985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147985 prefixEnd_8147985 := by exact prefixLift 8147985
  have htrace : WordTrace (prefixWord ++ tailWord_8147985) baseStart_8147985 baseEnd_8147985 := by
    simpa [prefixWord, tailWord_8147985, baseEnd_8147985] using wordTrace_append hprefix tailTrace_8147985
  have hstable : (prefixWord ++ tailWord_8147985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147985).length < 2 ^ (prefixWord ++ tailWord_8147985).sum := by decide
  have hdescent : baseEnd_8147985 < baseStart_8147985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147986 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_8147986 : Nat := 118140960795 + 8147986 * 2 ^ 59
def prefixEnd_8147986 : Nat := 4983230072969 + 3 ^ 40 * 8147986 * 2
def baseEnd_8147986 : Nat := 1394611061368354400334367

theorem tailTrace_8147986 : CollatzResearch.WordTrace tailWord_8147986 prefixEnd_8147986 1394611061368354400334367 := by
  unfold tailWord_8147986
  simp only [CollatzResearch.WordTrace]
  refine ⟨74295365964811440516435953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198120975906163841377162541 74295365964811440516435953)
  ·
    refine ⟨55721524473608580387326965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74295365964811440516435953 55721524473608580387326965)
    ·
      refine ⟨5223892919400804411311903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55721524473608580387326965 5223892919400804411311903)
      ·
        refine ⟨7835839379101206616967855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5223892919400804411311903 7835839379101206616967855)
        ·
          refine ⟨11753759068651809925451783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835839379101206616967855 11753759068651809925451783)
          ·
            refine ⟨17630638602977714888177675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11753759068651809925451783 17630638602977714888177675)
            ·
              refine ⟨26445957904466572332266513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17630638602977714888177675 26445957904466572332266513)
              ·
                refine ⟨19834468428349929249199885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26445957904466572332266513 19834468428349929249199885)
                ·
                  refine ⟨7437925660631223468449957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19834468428349929249199885 7437925660631223468449957)
                  ·
                    refine ⟨1394611061368354400334367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437925660631223468449957 1394611061368354400334367)
                    ·
                      rfl

theorem cell23_8147986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_8147986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147986 prefixEnd_8147986 := by exact prefixLift 8147986
  have htrace : WordTrace (prefixWord ++ tailWord_8147986) baseStart_8147986 baseEnd_8147986 := by
    simpa [prefixWord, tailWord_8147986, baseEnd_8147986] using wordTrace_append hprefix tailTrace_8147986
  have hstable : (prefixWord ++ tailWord_8147986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147986).length < 2 ^ (prefixWord ++ tailWord_8147986).sum := by decide
  have hdescent : baseEnd_8147986 < baseStart_8147986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8147992 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 3, 1, 3]
def baseStart_8147992 : Nat := 118140960795 + 8147992 * 2 ^ 59
def prefixEnd_8147992 : Nat := 4983230072969 + 3 ^ 40 * 8147992 * 2
def baseEnd_8147992 : Nat := 4183836264988990177528073

theorem tailTrace_8147992 : CollatzResearch.WordTrace tailWord_8147992 prefixEnd_8147992 4183836264988990177528073 := by
  unfold tailWord_8147992
  simp only [CollatzResearch.WordTrace]
  refine ⟨148590841348612012545231115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198121121798149350060308153 148590841348612012545231115)
  ·
    refine ⟨222886262022918018817846673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148590841348612012545231115 222886262022918018817846673)
    ·
      refine ⟨167164696517188514113385005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222886262022918018817846673 167164696517188514113385005)
      ·
        refine ⟨62686761193945692792519377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167164696517188514113385005 62686761193945692792519377)
        ·
          refine ⟨47015070895459269594389533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62686761193945692792519377 47015070895459269594389533)
          ·
            refine ⟨17630651585797226097896075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47015070895459269594389533 17630651585797226097896075)
            ·
              refine ⟨26445977378695839146844113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17630651585797226097896075 26445977378695839146844113)
              ·
                refine ⟨19834483034021879360133085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26445977378695839146844113 19834483034021879360133085)
                ·
                  refine ⟨7437931137758204760049907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19834483034021879360133085 7437931137758204760049907)
                  ·
                    refine ⟨11156896706637307140074861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7437931137758204760049907 11156896706637307140074861)
                    ·
                      refine ⟨4183836264988990177528073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11156896706637307140074861 4183836264988990177528073)
                      ·
                        rfl

theorem cell23_8147992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_8147992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8147992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8147992 prefixEnd_8147992 := by exact prefixLift 8147992
  have htrace : WordTrace (prefixWord ++ tailWord_8147992) baseStart_8147992 baseEnd_8147992 := by
    simpa [prefixWord, tailWord_8147992, baseEnd_8147992] using wordTrace_append hprefix tailTrace_8147992
  have hstable : (prefixWord ++ tailWord_8147992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8147992).length < 2 ^ (prefixWord ++ tailWord_8147992).sum := by decide
  have hdescent : baseEnd_8147992 < baseStart_8147992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8147992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148002 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_8148002 : Nat := 118140960795 + 8148002 * 2 ^ 59
def prefixEnd_8148002 : Nat := 4983230072969 + 3 ^ 40 * 8148002 * 2
def baseEnd_8148002 : Nat := 4183841399795535138403027

theorem tailTrace_8148002 : CollatzResearch.WordTrace tailWord_8148002 prefixEnd_8148002 4183841399795535138403027 := by
  unfold tailWord_8148002
  simp only [CollatzResearch.WordTrace]
  refine ⟨74295511856796949199581565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198121364951458531198884173 74295511856796949199581565)
  ·
    refine ⟨27860816946298855949843087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74295511856796949199581565 27860816946298855949843087)
    ·
      refine ⟨41791225419448283924764631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27860816946298855949843087 41791225419448283924764631)
      ·
        refine ⟨62686838129172425887146947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41791225419448283924764631 62686838129172425887146947)
        ·
          refine ⟨94030257193758638830720421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62686838129172425887146947 94030257193758638830720421)
          ·
            refine ⟨17630673223829744780760079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94030257193758638830720421 17630673223829744780760079)
            ·
              refine ⟨26446009835744617171140119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17630673223829744780760079 26446009835744617171140119)
              ·
                refine ⟨39669014753616925756710179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26446009835744617171140119 39669014753616925756710179)
                ·
                  refine ⟨59503522130425388635065269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39669014753616925756710179 59503522130425388635065269)
                  ·
                    refine ⟨5578455199727380184537369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59503522130425388635065269 5578455199727380184537369)
                    ·
                      refine ⟨4183841399795535138403027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578455199727380184537369 4183841399795535138403027)
                      ·
                        rfl

theorem cell23_8148002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_8148002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148002 prefixEnd_8148002 := by exact prefixLift 8148002
  have htrace : WordTrace (prefixWord ++ tailWord_8148002) baseStart_8148002 baseEnd_8148002 := by
    simpa [prefixWord, tailWord_8148002, baseEnd_8148002] using wordTrace_append hprefix tailTrace_8148002
  have hstable : (prefixWord ++ tailWord_8148002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148002).length < 2 ^ (prefixWord ++ tailWord_8148002).sum := by decide
  have hdescent : baseEnd_8148002 < baseStart_8148002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148052 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_8148052 : Nat := 118140960795 + 8148052 * 2 ^ 59
def prefixEnd_8148052 : Nat := 4983230072969 + 3 ^ 40 * 8148052 * 2
def baseEnd_8148052 : Nat := 4183867073828259942777797

theorem tailTrace_8148052 : CollatzResearch.WordTrace tailWord_8148052 prefixEnd_8148052 4183867073828259942777797 := by
  unfold tailWord_8148052
  simp only [CollatzResearch.WordTrace]
  refine ⟨148591935538503327668823205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198122580718004436891764273 148591935538503327668823205)
  ·
    refine ⟨27860987913469373937904351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148591935538503327668823205 27860987913469373937904351)
    ·
      refine ⟨41791481870204060906856527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27860987913469373937904351 41791481870204060906856527)
      ·
        refine ⟨62687222805306091360284791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41791481870204060906856527 62687222805306091360284791)
        ·
          refine ⟨94030834207959137040427187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62687222805306091360284791 94030834207959137040427187)
          ·
            refine ⟨141046251311938705560640781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94030834207959137040427187 141046251311938705560640781)
            ·
              refine ⟨52892344241977014585240293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141046251311938705560640781 52892344241977014585240293)
              ·
                refine ⟨9917314545370690234732555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52892344241977014585240293 9917314545370690234732555)
                ·
                  refine ⟨14875971818056035352098833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9917314545370690234732555 14875971818056035352098833)
                  ·
                    refine ⟨11156978863542026514074125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14875971818056035352098833 11156978863542026514074125)
                    ·
                      refine ⟨4183867073828259942777797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11156978863542026514074125 4183867073828259942777797)
                      ·
                        rfl

theorem cell23_8148052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_8148052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148052 prefixEnd_8148052 := by exact prefixLift 8148052
  have htrace : WordTrace (prefixWord ++ tailWord_8148052) baseStart_8148052 baseEnd_8148052 := by
    simpa [prefixWord, tailWord_8148052, baseEnd_8148052] using wordTrace_append hprefix tailTrace_8148052
  have hstable : (prefixWord ++ tailWord_8148052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148052).length < 2 ^ (prefixWord ++ tailWord_8148052).sum := by decide
  have hdescent : baseEnd_8148052 < baseStart_8148052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148065 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_8148065 : Nat := 118140960795 + 8148065 * 2 ^ 59
def prefixEnd_8148065 : Nat := 4983230072969 + 3 ^ 40 * 8148065 * 2
def baseEnd_8148065 : Nat := 4183873749076768391915237

theorem tailTrace_8148065 : CollatzResearch.WordTrace tailWord_8148065 prefixEnd_8148065 4183873749076768391915237 := by
  unfold tailWord_8148065
  simp only [CollatzResearch.WordTrace]
  refine ⟨297184345225959558557869649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198122896817306372371913099 297184345225959558557869649)
  ·
    refine ⟨222888258919469668918402237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297184345225959558557869649 222888258919469668918402237)
    ·
      refine ⟨83583097094801125844400839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222888258919469668918402237 83583097094801125844400839)
      ·
        refine ⟨125374645642201688766601259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83583097094801125844400839 125374645642201688766601259)
        ·
          refine ⟨188061968463302533149901889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125374645642201688766601259 188061968463302533149901889)
          ·
            refine ⟨141046476347476899862426417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188061968463302533149901889 141046476347476899862426417)
            ·
              refine ⟨105784857260607674896819813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141046476347476899862426417 105784857260607674896819813)
              ·
                refine ⟨19834660736363939043153715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105784857260607674896819813 19834660736363939043153715)
                ·
                  refine ⟨29751991104545908564730573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19834660736363939043153715 29751991104545908564730573)
                  ·
                    refine ⟨11156996664204715711773965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29751991104545908564730573 11156996664204715711773965)
                    ·
                      refine ⟨4183873749076768391915237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11156996664204715711773965 4183873749076768391915237)
                      ·
                        rfl

theorem cell23_8148065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_8148065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148065 prefixEnd_8148065 := by exact prefixLift 8148065
  have htrace : WordTrace (prefixWord ++ tailWord_8148065) baseStart_8148065 baseEnd_8148065 := by
    simpa [prefixWord, tailWord_8148065, baseEnd_8148065] using wordTrace_append hprefix tailTrace_8148065
  have hstable : (prefixWord ++ tailWord_8148065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148065).length < 2 ^ (prefixWord ++ tailWord_8148065).sum := by decide
  have hdescent : baseEnd_8148065 < baseStart_8148065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148068 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_8148068 : Nat := 118140960795 + 8148068 * 2 ^ 59
def prefixEnd_8148068 : Nat := 4983230072969 + 3 ^ 40 * 8148068 * 2
def baseEnd_8148068 : Nat := 1394625096506243960059241

theorem tailTrace_8148068 : CollatzResearch.WordTrace tailWord_8148068 prefixEnd_8148068 1394625096506243960059241 := by
  unfold tailWord_8148068
  simp only [CollatzResearch.WordTrace]
  refine ⟨148592227322474345035114429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198122969763299126713485905 148592227322474345035114429)
  ·
    refine ⟨55722085245927879388167911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148592227322474345035114429 55722085245927879388167911)
    ·
      refine ⟨83583127868891819082251867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55722085245927879388167911 83583127868891819082251867)
      ·
        refine ⟨125374691803337728623377801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83583127868891819082251867 125374691803337728623377801)
        ·
          refine ⟨94031018852503296467533351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125374691803337728623377801 94031018852503296467533351)
          ·
            refine ⟨141046528278754944701300027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94031018852503296467533351 141046528278754944701300027)
            ·
              refine ⟨211569792418132417051950041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141046528278754944701300027 211569792418132417051950041)
              ·
                refine ⟨158677344313599312788962531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211569792418132417051950041 158677344313599312788962531)
                ·
                  refine ⟨238016016470398969183443797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158677344313599312788962531 238016016470398969183443797)
                  ·
                    refine ⟨1394625096506243960059241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 238016016470398969183443797 1394625096506243960059241)
                    ·
                      rfl

theorem cell23_8148068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_8148068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148068 prefixEnd_8148068 := by exact prefixLift 8148068
  have htrace : WordTrace (prefixWord ++ tailWord_8148068) baseStart_8148068 baseEnd_8148068 := by
    simpa [prefixWord, tailWord_8148068, baseEnd_8148068] using wordTrace_append hprefix tailTrace_8148068
  have hstable : (prefixWord ++ tailWord_8148068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148068).length < 2 ^ (prefixWord ++ tailWord_8148068).sum := by decide
  have hdescent : baseEnd_8148068 < baseStart_8148068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148072 : List Nat := [2, 1, 4, 4, 1, 2, 9]
def baseStart_8148072 : Nat := 118140960795 + 8148072 * 2 ^ 59
def prefixEnd_8148072 : Nat := 4983230072969 + 3 ^ 40 * 8148072 * 2
def baseEnd_8148072 : Nat := 51652806709152467463305

theorem tailTrace_8148072 : CollatzResearch.WordTrace tailWord_8148072 prefixEnd_8148072 51652806709152467463305 := by
  unfold tailWord_8148072
  simp only [CollatzResearch.WordTrace]
  refine ⟨148592300268467099376687235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198123067024622799168916313 148592300268467099376687235)
  ·
    refine ⟨222888450402700649065030853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148592300268467099376687235 222888450402700649065030853)
    ·
      refine ⟨41791584450506371699693285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222888450402700649065030853 41791584450506371699693285)
      ·
        refine ⟨7835922084469944693692491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41791584450506371699693285 7835922084469944693692491)
        ·
          refine ⟨11753883126704917040538737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835922084469944693692491 11753883126704917040538737)
          ·
            refine ⟨8815412345028687780404053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11753883126704917040538737 8815412345028687780404053)
            ·
              refine ⟨51652806709152467463305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8815412345028687780404053 51652806709152467463305)
              ·
                rfl

theorem cell23_8148072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 9].length) (baseStart_8148072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148072 prefixEnd_8148072 := by exact prefixLift 8148072
  have htrace : WordTrace (prefixWord ++ tailWord_8148072) baseStart_8148072 baseEnd_8148072 := by
    simpa [prefixWord, tailWord_8148072, baseEnd_8148072] using wordTrace_append hprefix tailTrace_8148072
  have hstable : (prefixWord ++ tailWord_8148072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148072).length < 2 ^ (prefixWord ++ tailWord_8148072).sum := by decide
  have hdescent : baseEnd_8148072 < baseStart_8148072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148082 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_8148082 : Nat := 118140960795 + 8148082 * 2 ^ 59
def prefixEnd_8148082 : Nat := 4983230072969 + 3 ^ 40 * 8148082 * 2
def baseEnd_8148082 : Nat := 4183882478247894825402659

theorem tailTrace_8148082 : CollatzResearch.WordTrace tailWord_8148082 prefixEnd_8148082 4183882478247894825402659 := by
  unfold tailWord_8148082
  simp only [CollatzResearch.WordTrace]
  refine ⟨74296241316724492615309625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198123310177931980307492333 74296241316724492615309625)
  ·
    refine ⟨55722180987543369461482219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74296241316724492615309625 55722180987543369461482219)
    ·
      refine ⟨83583271481315054192223329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55722180987543369461482219 83583271481315054192223329)
      ·
        refine ⟨62687453610986290644167497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83583271481315054192223329 62687453610986290644167497)
        ·
          refine ⟨47015590208239717983125623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62687453610986290644167497 47015590208239717983125623)
          ·
            refine ⟨70523385312359576974688435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47015590208239717983125623 70523385312359576974688435)
            ·
              refine ⟨105785077968539365462032653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70523385312359576974688435 105785077968539365462032653)
              ·
                refine ⟨39669404238202262048262245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105785077968539365462032653 39669404238202262048262245)
                ·
                  refine ⟨7438013294662924134049171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39669404238202262048262245 7438013294662924134049171)
                  ·
                    refine ⟨11157019941994386201073757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7438013294662924134049171 11157019941994386201073757)
                    ·
                      refine ⟨4183882478247894825402659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11157019941994386201073757 4183882478247894825402659)
                      ·
                        rfl

theorem cell23_8148082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_8148082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148082 prefixEnd_8148082 := by exact prefixLift 8148082
  have htrace : WordTrace (prefixWord ++ tailWord_8148082) baseStart_8148082 baseEnd_8148082 := by
    simpa [prefixWord, tailWord_8148082, baseEnd_8148082] using wordTrace_append hprefix tailTrace_8148082
  have hstable : (prefixWord ++ tailWord_8148082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148082).length < 2 ^ (prefixWord ++ tailWord_8148082).sum := by decide
  have hdescent : baseEnd_8148082 < baseStart_8148082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148092 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_8148092 : Nat := 118140960795 + 8148092 * 2 ^ 59
def prefixEnd_8148092 : Nat := 4983230072969 + 3 ^ 40 * 8148092 * 2
def baseEnd_8148092 : Nat := 4183887613054439786277613

theorem tailTrace_8148092 : CollatzResearch.WordTrace tailWord_8148092 prefixEnd_8148092 4183887613054439786277613 := by
  unfold tailWord_8148092
  simp only [CollatzResearch.WordTrace]
  refine ⟨148592664998430871084551265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198123553331241161446068353 148592664998430871084551265)
  ·
    refine ⟨111444498748823153313413449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148592664998430871084551265 111444498748823153313413449)
    ·
      refine ⟨83583374061617364985060087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111444498748823153313413449 83583374061617364985060087)
      ·
        refine ⟨125375061092426047477590131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83583374061617364985060087 125375061092426047477590131)
        ·
          refine ⟨188062591638639071216385197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125375061092426047477590131 188062591638639071216385197)
          ·
            refine ⟨70523471864489651706144449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188062591638639071216385197 70523471864489651706144449)
            ·
              refine ⟨52892603898367238779608337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70523471864489651706144449 52892603898367238779608337)
              ·
                refine ⟨39669452923775429084706253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52892603898367238779608337 39669452923775429084706253)
                ·
                  refine ⟨14876044846415785906764845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39669452923775429084706253 14876044846415785906764845)
                  ·
                    refine ⟨5578516817405919715036817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14876044846415785906764845 5578516817405919715036817)
                    ·
                      refine ⟨4183887613054439786277613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578516817405919715036817 4183887613054439786277613)
                      ·
                        rfl

theorem cell23_8148092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_8148092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148092 prefixEnd_8148092 := by exact prefixLift 8148092
  have htrace : WordTrace (prefixWord ++ tailWord_8148092) baseStart_8148092 baseEnd_8148092 := by
    simpa [prefixWord, tailWord_8148092, baseEnd_8148092] using wordTrace_append hprefix tailTrace_8148092
  have hstable : (prefixWord ++ tailWord_8148092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148092).length < 2 ^ (prefixWord ++ tailWord_8148092).sum := by decide
  have hdescent : baseEnd_8148092 < baseStart_8148092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148125 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_8148125 : Nat := 118140960795 + 8148125 * 2 ^ 59
def prefixEnd_8148125 : Nat := 4983230072969 + 3 ^ 40 * 8148125 * 2
def baseEnd_8148125 : Nat := 4183904557916038157164961

theorem tailTrace_8148125 : CollatzResearch.WordTrace tailWord_8148125 prefixEnd_8148125 4183904557916038157164961 := by
  unfold tailWord_8148125
  simp only [CollatzResearch.WordTrace]
  refine ⟨297186533605742188805053829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198124355737161459203369219 297186533605742188805053829)
  ·
    refine ⟨55722475051076660400947593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297186533605742188805053829 55722475051076660400947593)
    ·
      refine ⟨41791856288307495300710695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55722475051076660400947593 41791856288307495300710695)
      ·
        refine ⟨62687784432461242951066043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41791856288307495300710695 62687784432461242951066043)
        ·
          refine ⟨94031676648691864426599065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62687784432461242951066043 94031676648691864426599065)
          ·
            refine ⟨70523757486518898319949299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94031676648691864426599065 70523757486518898319949299)
            ·
              refine ⟨105785636229778347479923949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70523757486518898319949299 105785636229778347479923949)
              ·
                refine ⟨39669613586166880304971481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105785636229778347479923949 39669613586166880304971481)
                ·
                  refine ⟨29752210189625160228728611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39669613586166880304971481 29752210189625160228728611)
                  ·
                    refine ⟨44628315284437740343092917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29752210189625160228728611 44628315284437740343092917)
                    ·
                      refine ⟨4183904557916038157164961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44628315284437740343092917 4183904557916038157164961)
                      ·
                        rfl

theorem cell23_8148125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_8148125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148125 prefixEnd_8148125 := by exact prefixLift 8148125
  have htrace : WordTrace (prefixWord ++ tailWord_8148125) baseStart_8148125 baseEnd_8148125 := by
    simpa [prefixWord, tailWord_8148125, baseEnd_8148125] using wordTrace_append hprefix tailTrace_8148125
  have hstable : (prefixWord ++ tailWord_8148125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148125).length < 2 ^ (prefixWord ++ tailWord_8148125).sum := by decide
  have hdescent : baseEnd_8148125 < baseStart_8148125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148156 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_8148156 : Nat := 118140960795 + 8148156 * 2 ^ 59
def prefixEnd_8148156 : Nat := 4983230072969 + 3 ^ 40 * 8148156 * 2
def baseEnd_8148156 : Nat := 4183920475816327535877319

theorem tailTrace_8148156 : CollatzResearch.WordTrace tailWord_8148156 prefixEnd_8148156 4183920475816327535877319 := by
  unfold tailWord_8148156
  simp only [CollatzResearch.WordTrace]
  refine ⟨148593832134314940549716161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198125109512419920732954881 148593832134314940549716161)
  ·
    refine ⟨111445374100736205412287121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148593832134314940549716161 111445374100736205412287121)
    ·
      refine ⟨83584030575552154059215341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111445374100736205412287121 83584030575552154059215341)
      ·
        refine ⟨31344011465832057772205753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83584030575552154059215341 31344011465832057772205753)
        ·
          refine ⟨23508008599374043329154315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31344011465832057772205753 23508008599374043329154315)
          ·
            refine ⟨35262012899061064993731473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23508008599374043329154315 35262012899061064993731473)
            ·
              refine ⟨26446509674295798745298605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35262012899061064993731473 26446509674295798745298605)
              ·
                refine ⟨9917441127860924529486977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26446509674295798745298605 9917441127860924529486977)
                ·
                  refine ⟨7438080845895693397115233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9917441127860924529486977 7438080845895693397115233)
                  ·
                    refine ⟨5578560634421770047836425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7438080845895693397115233 5578560634421770047836425)
                    ·
                      refine ⟨4183920475816327535877319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578560634421770047836425 4183920475816327535877319)
                      ·
                        rfl

theorem cell23_8148156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_8148156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148156 prefixEnd_8148156 := by exact prefixLift 8148156
  have htrace : WordTrace (prefixWord ++ tailWord_8148156) baseStart_8148156 baseEnd_8148156 := by
    simpa [prefixWord, tailWord_8148156, baseEnd_8148156] using wordTrace_append hprefix tailTrace_8148156
  have hstable : (prefixWord ++ tailWord_8148156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148156).length < 2 ^ (prefixWord ++ tailWord_8148156).sum := by decide
  have hdescent : baseEnd_8148156 < baseStart_8148156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148175 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 2, 5]
def baseStart_8148175 : Nat := 118140960795 + 8148175 * 2 ^ 59
def prefixEnd_8148175 : Nat := 4983230072969 + 3 ^ 40 * 8148175 * 2
def baseEnd_8148175 : Nat := 1394643410649587653846577

theorem tailTrace_8148175 : CollatzResearch.WordTrace tailWord_8148175 prefixEnd_8148175 1394643410649587653846577 := by
  unfold tailWord_8148175
  simp only [CollatzResearch.WordTrace]
  refine ⟨297188357255561047344373979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198125571503707364896249319 297188357255561047344373979)
  ·
    refine ⟨445782535883341571016560969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297188357255561047344373979 445782535883341571016560969)
    ·
      refine ⟨334336901912506178262420727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445782535883341571016560969 334336901912506178262420727)
      ·
        refine ⟨501505352868759267393631091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334336901912506178262420727 501505352868759267393631091)
        ·
          refine ⟨752258029303138901090446637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501505352868759267393631091 752258029303138901090446637)
          ·
            refine ⟨282096760988677087908917489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 752258029303138901090446637 282096760988677087908917489)
            ·
              refine ⟨211572570741507815931688117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282096760988677087908917489 211572570741507815931688117)
              ·
                refine ⟨19834928507016357743595761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211572570741507815931688117 19834928507016357743595761)
                ·
                  refine ⟨14876196380262268307696821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19834928507016357743595761 14876196380262268307696821)
                  ·
                    refine ⟨1394643410649587653846577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14876196380262268307696821 1394643410649587653846577)
                    ·
                      rfl

theorem cell23_8148175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_8148175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148175 prefixEnd_8148175 := by exact prefixLift 8148175
  have htrace : WordTrace (prefixWord ++ tailWord_8148175) baseStart_8148175 baseEnd_8148175 := by
    simpa [prefixWord, tailWord_8148175, baseEnd_8148175] using wordTrace_append hprefix tailTrace_8148175
  have hstable : (prefixWord ++ tailWord_8148175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148175).length < 2 ^ (prefixWord ++ tailWord_8148175).sum := by decide
  have hdescent : baseEnd_8148175 < baseStart_8148175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148235 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 8]
def baseStart_8148235 : Nat := 118140960795 + 8148235 * 2 ^ 59
def prefixEnd_8148235 : Nat := 4983230072969 + 3 ^ 40 * 8148235 * 2
def baseEnd_8148235 : Nat := 464884560087559191865495

theorem tailTrace_8148235 : CollatzResearch.WordTrace tailWord_8148235 prefixEnd_8148235 464884560087559191865495 := by
  unfold tailWord_8148235
  simp only [CollatzResearch.WordTrace]
  refine ⟨297190545635343677591558159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198127030423562451727705439 297190545635343677591558159)
  ·
    refine ⟨445785818453015516387337239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297190545635343677591558159 445785818453015516387337239)
    ·
      refine ⟨668678727679523274581005859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445785818453015516387337239 668678727679523274581005859)
      ·
        refine ⟨1003018091519284911871508789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668678727679523274581005859 1003018091519284911871508789)
        ·
          refine ⟨94032946079932960487953949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1003018091519284911871508789 94032946079932960487953949)
          ·
            refine ⟨35262354779974860182982731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94032946079932960487953949 35262354779974860182982731)
            ·
              refine ⟨52893532169962290274474097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35262354779974860182982731 52893532169962290274474097)
              ·
                refine ⟨39670149127471717705855573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52893532169962290274474097 39670149127471717705855573)
                ·
                  refine ⟨464884560087559191865495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39670149127471717705855573 464884560087559191865495)
                  ·
                    rfl

theorem cell23_8148235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 8].length) (baseStart_8148235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148235 prefixEnd_8148235 := by exact prefixLift 8148235
  have htrace : WordTrace (prefixWord ++ tailWord_8148235) baseStart_8148235 baseEnd_8148235 := by
    simpa [prefixWord, tailWord_8148235, baseEnd_8148235] using wordTrace_append hprefix tailTrace_8148235
  have hstable : (prefixWord ++ tailWord_8148235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148235).length < 2 ^ (prefixWord ++ tailWord_8148235).sum := by decide
  have hdescent : baseEnd_8148235 < baseStart_8148235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148256 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 3, 4]
def baseStart_8148256 : Nat := 118140960795 + 8148256 * 2 ^ 59
def prefixEnd_8148256 : Nat := 4983230072969 + 3 ^ 40 * 8148256 * 2
def baseEnd_8148256 : Nat := 1394657274627259048208953

theorem tailTrace_8148256 : CollatzResearch.WordTrace tailWord_8148256 prefixEnd_8148256 1394657274627259048208953 := by
  unfold tailWord_8148256
  simp only [CollatzResearch.WordTrace]
  refine ⟨148595655784133799089036311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198127541045511732118715081 148595655784133799089036311)
  ·
    refine ⟨222893483676200698633554467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148595655784133799089036311 222893483676200698633554467)
    ·
      refine ⟨334340225514301047950331701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222893483676200698633554467 334340225514301047950331701)
      ·
        refine ⟨31344396141965723245343597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334340225514301047950331701 31344396141965723245343597)
        ·
          refine ⟨11754148553237146217003849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31344396141965723245343597 11754148553237146217003849)
          ·
            refine ⟨8815611414927859662752887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11754148553237146217003849 8815611414927859662752887)
            ·
              refine ⟨13223417122391789494129331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8815611414927859662752887 13223417122391789494129331)
              ·
                refine ⟨19835125683587684241193997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13223417122391789494129331 19835125683587684241193997)
                ·
                  refine ⟨7438172131345381590447749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19835125683587684241193997 7438172131345381590447749)
                  ·
                    refine ⟨1394657274627259048208953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7438172131345381590447749 1394657274627259048208953)
                    ·
                      rfl

theorem cell23_8148256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 4].length) (baseStart_8148256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148256 prefixEnd_8148256 := by exact prefixLift 8148256
  have htrace : WordTrace (prefixWord ++ tailWord_8148256) baseStart_8148256 baseEnd_8148256 := by
    simpa [prefixWord, tailWord_8148256, baseEnd_8148256] using wordTrace_append hprefix tailTrace_8148256
  have hstable : (prefixWord ++ tailWord_8148256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148256).length < 2 ^ (prefixWord ++ tailWord_8148256).sum := by decide
  have hdescent : baseEnd_8148256 < baseStart_8148256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148282 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_8148282 : Nat := 118140960795 + 8148282 * 2 ^ 59
def prefixEnd_8148282 : Nat := 4983230072969 + 3 ^ 40 * 8148282 * 2
def baseEnd_8148282 : Nat := 1394661724792931347633913

theorem tailTrace_8148282 : CollatzResearch.WordTrace tailWord_8148282 prefixEnd_8148282 1394661724792931347633913 := by
  unfold tailWord_8148282
  simp only [CollatzResearch.WordTrace]
  refine ⟨74298064966543351154629775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198128173244115603079012733 74298064966543351154629775)
  ·
    refine ⟨111447097449815026731944663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74298064966543351154629775 111447097449815026731944663)
    ·
      refine ⟨167170646174722540097916995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111447097449815026731944663 167170646174722540097916995)
      ·
        refine ⟨250755969262083810146875493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167170646174722540097916995 250755969262083810146875493)
        ·
          refine ⟨47016744236640714402539155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250755969262083810146875493 47016744236640714402539155)
          ·
            refine ⟨70525116354961071603808733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47016744236640714402539155 70525116354961071603808733)
            ·
              refine ⟨26446918633110401851428275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70525116354961071603808733 26446918633110401851428275)
              ·
                refine ⟨39670377949665602777142413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26446918633110401851428275 39670377949665602777142413)
                ·
                  refine ⟨14876391731124601041428405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39670377949665602777142413 14876391731124601041428405)
                  ·
                    refine ⟨1394661724792931347633913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14876391731124601041428405 1394661724792931347633913)
                    ·
                      rfl

theorem cell23_8148282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_8148282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148282 prefixEnd_8148282 := by exact prefixLift 8148282
  have htrace : WordTrace (prefixWord ++ tailWord_8148282) baseStart_8148282 baseEnd_8148282 := by
    simpa [prefixWord, tailWord_8148282, baseEnd_8148282] using wordTrace_append hprefix tailTrace_8148282
  have hstable : (prefixWord ++ tailWord_8148282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148282).length < 2 ^ (prefixWord ++ tailWord_8148282).sum := by decide
  have hdescent : baseEnd_8148282 < baseStart_8148282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148296 : List Nat := [2, 1, 3, 1, 1, 2, 1, 7, 1, 1, 3]
def baseStart_8148296 : Nat := 118140960795 + 8148296 * 2 ^ 59
def prefixEnd_8148296 : Nat := 4983230072969 + 3 ^ 40 * 8148296 * 2
def baseEnd_8148296 : Nat := 4183992363107956988126675

theorem tailTrace_8148296 : CollatzResearch.WordTrace tailWord_8148296 prefixEnd_8148296 4183992363107956988126675 := by
  unfold tailWord_8148296
  simp only [CollatzResearch.WordTrace]
  refine ⟨148596385244061342504764371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198128513658748456673019161 148596385244061342504764371)
  ·
    refine ⟨222894577866092013757146557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148596385244061342504764371 222894577866092013757146557)
    ·
      refine ⟨83585466699784505158929959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222894577866092013757146557 83585466699784505158929959)
      ·
        refine ⟨125378200049676757738394939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83585466699784505158929959 125378200049676757738394939)
        ·
          refine ⟨188067300074515136607592409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125378200049676757738394939 188067300074515136607592409)
          ·
            refine ⟨141050475055886352455694307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188067300074515136607592409 141050475055886352455694307)
            ·
              refine ⟨211575712583829528683541461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141050475055886352455694307 211575712583829528683541461)
              ·
                refine ⟨4958805763683504578520503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 211575712583829528683541461 4958805763683504578520503)
                ·
                  refine ⟨7438208645525256867780755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958805763683504578520503 7438208645525256867780755)
                  ·
                    refine ⟨11157312968287885301671133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7438208645525256867780755 11157312968287885301671133)
                    ·
                      refine ⟨4183992363107956988126675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11157312968287885301671133 4183992363107956988126675)
                      ·
                        rfl

theorem cell23_8148296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_8148296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148296 prefixEnd_8148296 := by exact prefixLift 8148296
  have htrace : WordTrace (prefixWord ++ tailWord_8148296) baseStart_8148296 baseEnd_8148296 := by
    simpa [prefixWord, tailWord_8148296, baseEnd_8148296] using wordTrace_append hprefix tailTrace_8148296
  have hstable : (prefixWord ++ tailWord_8148296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148296).length < 2 ^ (prefixWord ++ tailWord_8148296).sum := by decide
  have hdescent : baseEnd_8148296 < baseStart_8148296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148313 : List Nat := [1, 2, 1, 2, 2, 2, 6, 2, 1, 1, 3]
def baseStart_8148313 : Nat := 118140960795 + 8148313 * 2 ^ 59
def prefixEnd_8148313 : Nat := 4983230072969 + 3 ^ 40 * 8148313 * 2
def baseEnd_8148313 : Nat := 4184001092279083421614097

theorem tailTrace_8148313 : CollatzResearch.WordTrace tailWord_8148313 prefixEnd_8148313 4184001092279083421614097 := by
  unfold tailWord_8148313
  simp only [CollatzResearch.WordTrace]
  refine ⟨297193390529061096912897593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198128927019374064608598395 297193390529061096912897593)
  ·
    refine ⟨222895042896795822684673195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297193390529061096912897593 222895042896795822684673195)
    ·
      refine ⟨334342564345193734027009793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222895042896795822684673195 334342564345193734027009793)
      ·
        refine ⟨250756923258895300520257345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334342564345193734027009793 250756923258895300520257345)
        ·
          refine ⟨188067692444171475390193009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250756923258895300520257345 188067692444171475390193009)
          ·
            refine ⟨141050769333128606542644757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188067692444171475390193009 141050769333128606542644757)
            ·
              refine ⟨6611754812490403431686473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141050769333128606542644757 6611754812490403431686473)
              ·
                refine ⟨4958816109367802573764855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6611754812490403431686473 4958816109367802573764855)
                ·
                  refine ⟨7438224164051703860647283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958816109367802573764855 7438224164051703860647283)
                  ·
                    refine ⟨11157336246077555790970925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7438224164051703860647283 11157336246077555790970925)
                    ·
                      refine ⟨4184001092279083421614097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11157336246077555790970925 4184001092279083421614097)
                      ·
                        rfl

theorem cell23_8148313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 1, 3].length) (baseStart_8148313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148313 prefixEnd_8148313 := by exact prefixLift 8148313
  have htrace : WordTrace (prefixWord ++ tailWord_8148313) baseStart_8148313 baseEnd_8148313 := by
    simpa [prefixWord, tailWord_8148313, baseEnd_8148313] using wordTrace_append hprefix tailTrace_8148313
  have hstable : (prefixWord ++ tailWord_8148313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148313).length < 2 ^ (prefixWord ++ tailWord_8148313).sum := by decide
  have hdescent : baseEnd_8148313 < baseStart_8148313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148336 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 3, 2, 2]
def baseStart_8148336 : Nat := 118140960795 + 8148336 * 2 ^ 59
def prefixEnd_8148336 : Nat := 4983230072969 + 3 ^ 40 * 8148336 * 2
def baseEnd_8148336 : Nat := 4184012902334136831626491

theorem tailTrace_8148336 : CollatzResearch.WordTrace tailWord_8148336 prefixEnd_8148336 4184012902334136831626491 := by
  unfold tailWord_8148336
  simp only [CollatzResearch.WordTrace]
  refine ⟨148597114703988885920492431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198129486271985181227323241 148597114703988885920492431)
  ·
    refine ⟨222895672055983328880738647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148597114703988885920492431 222895672055983328880738647)
    ·
      refine ⟨334343508083974993321107971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222895672055983328880738647 334343508083974993321107971)
      ·
        refine ⟨501515262125962489981661957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334343508083974993321107971 501515262125962489981661957)
        ·
          refine ⟨94034111648617966871561617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501515262125962489981661957 94034111648617966871561617)
          ·
            refine ⟨70525583736463475153671213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94034111648617966871561617 70525583736463475153671213)
            ·
              refine ⟨26447093901173803182626705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70525583736463475153671213 26447093901173803182626705)
              ·
                refine ⟨19835320425880352386970029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26447093901173803182626705 19835320425880352386970029)
                ·
                  refine ⟨7438245159705132145113761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19835320425880352386970029 7438245159705132145113761)
                  ·
                    refine ⟨5578683869778849108835321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7438245159705132145113761 5578683869778849108835321)
                    ·
                      refine ⟨4184012902334136831626491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578683869778849108835321 4184012902334136831626491)
                      ·
                        rfl

theorem cell23_8148336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 2, 2].length) (baseStart_8148336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148336 prefixEnd_8148336 := by exact prefixLift 8148336
  have htrace : WordTrace (prefixWord ++ tailWord_8148336) baseStart_8148336 baseEnd_8148336 := by
    simpa [prefixWord, tailWord_8148336, baseEnd_8148336] using wordTrace_append hprefix tailTrace_8148336
  have hstable : (prefixWord ++ tailWord_8148336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148336).length < 2 ^ (prefixWord ++ tailWord_8148336).sum := by decide
  have hdescent : baseEnd_8148336 < baseStart_8148336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148356 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_8148356 : Nat := 118140960795 + 8148356 * 2 ^ 59
def prefixEnd_8148356 : Nat := 4983230072969 + 3 ^ 40 * 8148356 * 2
def baseEnd_8148356 : Nat := 4184023171947226753376399

theorem tailTrace_8148356 : CollatzResearch.WordTrace tailWord_8148356 prefixEnd_8148356 4184023171947226753376399 := by
  unfold tailWord_8148356
  simp only [CollatzResearch.WordTrace]
  refine ⟨148597479433952657628356461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198129972578603543504475281 148597479433952657628356461)
  ·
    refine ⟨55724054787732246610633673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148597479433952657628356461 55724054787732246610633673)
    ·
      refine ⟨41793041090799184957975255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55724054787732246610633673 41793041090799184957975255)
      ·
        refine ⟨62689561636198777436962883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41793041090799184957975255 62689561636198777436962883)
        ·
          refine ⟨94034342454298166155444325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62689561636198777436962883 94034342454298166155444325)
          ·
            refine ⟨17631439210180906154145811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94034342454298166155444325 17631439210180906154145811)
            ·
              refine ⟨26447158815271359231218717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17631439210180906154145811 26447158815271359231218717)
              ·
                refine ⟨9917684555726759711707019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26447158815271359231218717 9917684555726759711707019)
                ·
                  refine ⟨14876526833590139567560529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9917684555726759711707019 14876526833590139567560529)
                  ·
                    refine ⟨11157395125192604675670397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14876526833590139567560529 11157395125192604675670397)
                    ·
                      refine ⟨4184023171947226753376399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11157395125192604675670397 4184023171947226753376399)
                      ·
                        rfl

theorem cell23_8148356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_8148356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148356 prefixEnd_8148356 := by exact prefixLift 8148356
  have htrace : WordTrace (prefixWord ++ tailWord_8148356) baseStart_8148356 baseEnd_8148356 := by
    simpa [prefixWord, tailWord_8148356, baseEnd_8148356] using wordTrace_append hprefix tailTrace_8148356
  have hstable : (prefixWord ++ tailWord_8148356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148356).length < 2 ^ (prefixWord ++ tailWord_8148356).sum := by decide
  have hdescent : baseEnd_8148356 < baseStart_8148356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148369 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 3]
def baseStart_8148369 : Nat := 118140960795 + 8148369 * 2 ^ 59
def prefixEnd_8148369 : Nat := 4983230072969 + 3 ^ 40 * 8148369 * 2
def baseEnd_8148369 : Nat := 4184029847195735202513839

theorem tailTrace_8148369 : CollatzResearch.WordTrace tailWord_8148369 prefixEnd_8148369 4184029847195735202513839 := by
  unfold tailWord_8148369
  simp only [CollatzResearch.WordTrace]
  refine ⟨297195433016858218476936161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198130288677905478984624107 297195433016858218476936161)
  ·
    refine ⟨222896574762643663857702121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297195433016858218476936161 222896574762643663857702121)
    ·
      refine ⟨167172431071982747893276591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222896574762643663857702121 167172431071982747893276591)
      ·
        refine ⟨250758646607974121839914887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167172431071982747893276591 250758646607974121839914887)
        ·
          refine ⟨376137969911961182759872331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250758646607974121839914887 376137969911961182759872331)
          ·
            refine ⟨564206954867941774139808497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376137969911961182759872331 564206954867941774139808497)
            ·
              refine ⟨423155216150956330604856373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564206954867941774139808497 423155216150956330604856373)
              ·
                refine ⟨39670801514152155994205285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 423155216150956330604856373 39670801514152155994205285)
                ·
                  refine ⟨7438275283903529248913491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39670801514152155994205285 7438275283903529248913491)
                  ·
                    refine ⟨11157412925855293873370237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7438275283903529248913491 11157412925855293873370237)
                    ·
                      refine ⟨4184029847195735202513839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11157412925855293873370237 4184029847195735202513839)
                      ·
                        rfl

theorem cell23_8148369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_8148369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148369 prefixEnd_8148369 := by exact prefixLift 8148369
  have htrace : WordTrace (prefixWord ++ tailWord_8148369) baseStart_8148369 baseEnd_8148369 := by
    simpa [prefixWord, tailWord_8148369, baseEnd_8148369] using wordTrace_append hprefix tailTrace_8148369
  have hstable : (prefixWord ++ tailWord_8148369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148369).length < 2 ^ (prefixWord ++ tailWord_8148369).sum := by decide
  have hdescent : baseEnd_8148369 < baseStart_8148369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148380 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_8148380 : Nat := 118140960795 + 8148380 * 2 ^ 59
def prefixEnd_8148380 : Nat := 4983230072969 + 3 ^ 40 * 8148380 * 2
def baseEnd_8148380 : Nat := 1394678498494311553158763

theorem tailTrace_8148380 : CollatzResearch.WordTrace tailWord_8148380 prefixEnd_8148380 1394678498494311553158763 := by
  unfold tailWord_8148380
  simp only [CollatzResearch.WordTrace]
  refine ⟨148597917109909183677793297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198130556146545578237057729 148597917109909183677793297)
  ·
    refine ⟨111448437832431887758344973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148597917109909183677793297 111448437832431887758344973)
    ·
      refine ⟨41793164187161957909379365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111448437832431887758344973 41793164187161957909379365)
      ·
        refine ⟨7836218285092867108008631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41793164187161957909379365 7836218285092867108008631)
        ·
          refine ⟨11754327427639300662012947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7836218285092867108008631 11754327427639300662012947)
          ·
            refine ⟨17631491141458950993019421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11754327427639300662012947 17631491141458950993019421)
            ·
              refine ⟨6611809178047106622382283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17631491141458950993019421 6611809178047106622382283)
              ·
                refine ⟨9917713767070659933573425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6611809178047106622382283 9917713767070659933573425)
                ·
                  refine ⟨7438285325302994950180069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9917713767070659933573425 7438285325302994950180069)
                  ·
                    refine ⟨1394678498494311553158763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7438285325302994950180069 1394678498494311553158763)
                    ·
                      rfl

theorem cell23_8148380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_8148380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148380 prefixEnd_8148380 := by exact prefixLift 8148380
  have htrace : WordTrace (prefixWord ++ tailWord_8148380) baseStart_8148380 baseEnd_8148380 := by
    simpa [prefixWord, tailWord_8148380, baseEnd_8148380] using wordTrace_append hprefix tailTrace_8148380
  have hstable : (prefixWord ++ tailWord_8148380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148380).length < 2 ^ (prefixWord ++ tailWord_8148380).sum := by decide
  have hdescent : baseEnd_8148380 < baseStart_8148380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148386 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_8148386 : Nat := 118140960795 + 8148386 * 2 ^ 59
def prefixEnd_8148386 : Nat := 4983230072969 + 3 ^ 40 * 8148386 * 2
def baseEnd_8148386 : Nat := 4184038576366861636001261

theorem tailTrace_8148386 : CollatzResearch.WordTrace tailWord_8148386 prefixEnd_8148386 4184038576366861636001261 := by
  unfold tailWord_8148386
  simp only [CollatzResearch.WordTrace]
  refine ⟨74299013264449157595076253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198130702038531086920203341 74299013264449157595076253)
  ·
    refine ⟨27862129974168434098153595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74299013264449157595076253 27862129974168434098153595)
    ·
      refine ⟨41793194961252651147230393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27862129974168434098153595 41793194961252651147230393)
      ·
        refine ⟨31344896220939488360422795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41793194961252651147230393 31344896220939488360422795)
        ·
          refine ⟨47017344331409232540634193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31344896220939488360422795 47017344331409232540634193)
          ·
            refine ⟨35263008248556924405475645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47017344331409232540634193 35263008248556924405475645)
            ·
              refine ⟨13223628093208846652053367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35263008248556924405475645 13223628093208846652053367)
              ·
                refine ⟨19835442139813269978080051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13223628093208846652053367 19835442139813269978080051)
                ·
                  refine ⟨29753163209719904967120077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19835442139813269978080051 29753163209719904967120077)
                  ·
                    refine ⟨11157436203644964362670029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29753163209719904967120077 11157436203644964362670029)
                    ·
                      refine ⟨4184038576366861636001261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11157436203644964362670029 4184038576366861636001261)
                      ·
                        rfl

theorem cell23_8148386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_8148386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148386 prefixEnd_8148386 := by exact prefixLift 8148386
  have htrace : WordTrace (prefixWord ++ tailWord_8148386) baseStart_8148386 baseEnd_8148386 := by
    simpa [prefixWord, tailWord_8148386, baseEnd_8148386] using wordTrace_append hprefix tailTrace_8148386
  have hstable : (prefixWord ++ tailWord_8148386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148386).length < 2 ^ (prefixWord ++ tailWord_8148386).sum := by decide
  have hdescent : baseEnd_8148386 < baseStart_8148386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148396 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 1, 3, 2]
def baseStart_8148396 : Nat := 118140960795 + 8148396 * 2 ^ 59
def prefixEnd_8148396 : Nat := 4983230072969 + 3 ^ 40 * 8148396 * 2
def baseEnd_8148396 : Nat := 4184043711173406596876215

theorem tailTrace_8148396 : CollatzResearch.WordTrace tailWord_8148396 prefixEnd_8148396 4184043711173406596876215 := by
  unfold tailWord_8148396
  simp only [CollatzResearch.WordTrace]
  refine ⟨148598208893880201044084521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198130945191840268058779361 148598208893880201044084521)
  ·
    refine ⟨111448656670410150783063391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148598208893880201044084521 111448656670410150783063391)
    ·
      refine ⟨167172985005615226174595087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111448656670410150783063391 167172985005615226174595087)
      ·
        refine ⟨250759477508422839261892631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167172985005615226174595087 250759477508422839261892631)
        ·
          refine ⟨376139216262634258892838947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250759477508422839261892631 376139216262634258892838947)
          ·
            refine ⟨564208824393951388339258421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376139216262634258892838947 564208824393951388339258421)
            ·
              refine ⟨52894577286932942656805477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 564208824393951388339258421 52894577286932942656805477)
              ·
                refine ⟨9917733241299926748151027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52894577286932942656805477 9917733241299926748151027)
                ·
                  refine ⟨14876599861949890122226541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9917733241299926748151027 14876599861949890122226541)
                  ·
                    refine ⟨5578724948231208795834953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14876599861949890122226541 5578724948231208795834953)
                    ·
                      refine ⟨4184043711173406596876215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578724948231208795834953 4184043711173406596876215)
                      ·
                        rfl

theorem cell23_8148396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_8148396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148396 prefixEnd_8148396 := by exact prefixLift 8148396
  have htrace : WordTrace (prefixWord ++ tailWord_8148396) baseStart_8148396 baseEnd_8148396 := by
    simpa [prefixWord, tailWord_8148396, baseEnd_8148396] using wordTrace_append hprefix tailTrace_8148396
  have hstable : (prefixWord ++ tailWord_8148396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148396).length < 2 ^ (prefixWord ++ tailWord_8148396).sum := by decide
  have hdescent : baseEnd_8148396 < baseStart_8148396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148402 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_8148402 : Nat := 118140960795 + 8148402 * 2 ^ 59
def prefixEnd_8148402 : Nat := 4983230072969 + 3 ^ 40 * 8148402 * 2
def baseEnd_8148402 : Nat := 1394682264019111191133729

theorem tailTrace_8148402 : CollatzResearch.WordTrace tailWord_8148402 prefixEnd_8148402 1394682264019111191133729 := by
  unfold tailWord_8148402
  simp only [CollatzResearch.WordTrace]
  refine ⟨74299159156434666278221865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198131091083825776741924973 74299159156434666278221865)
  ·
    refine ⟨55724369367325999708666399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74299159156434666278221865 55724369367325999708666399)
    ·
      refine ⟨83586554050988999562999599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55724369367325999708666399 83586554050988999562999599)
      ·
        refine ⟨125379831076483499344499399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83586554050988999562999599 125379831076483499344499399)
        ·
          refine ⟨188069746614725249016749099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125379831076483499344499399 188069746614725249016749099)
          ·
            refine ⟨282104619922087873525123649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188069746614725249016749099 282104619922087873525123649)
            ·
              refine ⟨211578464941565905143842737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282104619922087873525123649 211578464941565905143842737)
              ·
                refine ⟨158683848706174428857882053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211578464941565905143842737 158683848706174428857882053)
                ·
                  refine ⟨29753221632407705410852885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158683848706174428857882053 29753221632407705410852885)
                  ·
                    refine ⟨1394682264019111191133729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29753221632407705410852885 1394682264019111191133729)
                    ·
                      rfl

theorem cell23_8148402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_8148402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148402 prefixEnd_8148402 := by exact prefixLift 8148402
  have htrace : WordTrace (prefixWord ++ tailWord_8148402) baseStart_8148402 baseEnd_8148402 := by
    simpa [prefixWord, tailWord_8148402, baseEnd_8148402] using wordTrace_append hprefix tailTrace_8148402
  have hstable : (prefixWord ++ tailWord_8148402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148402).length < 2 ^ (prefixWord ++ tailWord_8148402).sum := by decide
  have hdescent : baseEnd_8148402 < baseStart_8148402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148452 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_8148452 : Nat := 118140960795 + 8148452 * 2 ^ 59
def prefixEnd_8148452 : Nat := 4983230072969 + 3 ^ 40 * 8148452 * 2
def baseEnd_8148452 : Nat := 4184072466090058377775957

theorem tailTrace_8148452 : CollatzResearch.WordTrace tailWord_8148452 prefixEnd_8148452 4184072466090058377775957 := by
  unfold tailWord_8148452
  simp only [CollatzResearch.WordTrace]
  refine ⟨148599230137778761826103805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198132306850371682434805073 148599230137778761826103805)
  ·
    refine ⟨55724711301667035684788927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148599230137778761826103805 55724711301667035684788927)
    ·
      refine ⟨83587066952500553527183391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55724711301667035684788927 83587066952500553527183391)
      ·
        refine ⟨125380600428750830290775087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83587066952500553527183391 125380600428750830290775087)
        ·
          refine ⟨188070900643126245436162631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125380600428750830290775087 188070900643126245436162631)
          ·
            refine ⟨282106350964689368154243947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188070900643126245436162631 282106350964689368154243947)
            ·
              refine ⟨423159526447034052231365921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282106350964689368154243947 423159526447034052231365921)
              ·
                refine ⟨317369644835275539173524441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423159526447034052231365921 317369644835275539173524441)
                ·
                  refine ⟨238027233626456654380143331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317369644835275539173524441 238027233626456654380143331)
                  ·
                    refine ⟨357040850439684981570214997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238027233626456654380143331 357040850439684981570214997)
                    ·
                      refine ⟨4184072466090058377775957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 357040850439684981570214997 4184072466090058377775957)
                      ·
                        rfl

theorem cell23_8148452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_8148452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148452 prefixEnd_8148452 := by exact prefixLift 8148452
  have htrace : WordTrace (prefixWord ++ tailWord_8148452) baseStart_8148452 baseEnd_8148452 := by
    simpa [prefixWord, tailWord_8148452, baseEnd_8148452] using wordTrace_append hprefix tailTrace_8148452
  have hstable : (prefixWord ++ tailWord_8148452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148452).length < 2 ^ (prefixWord ++ tailWord_8148452).sum := by decide
  have hdescent : baseEnd_8148452 < baseStart_8148452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148543 : List Nat := [1, 1, 2, 2, 3, 3, 2, 4, 1, 4]
def baseStart_8148543 : Nat := 118140960795 + 8148543 * 2 ^ 59
def prefixEnd_8148543 : Nat := 4983230072969 + 3 ^ 40 * 8148543 * 2
def baseEnd_8148543 : Nat := 1394706397609872507246013

theorem tailTrace_8148543 : CollatzResearch.WordTrace tailWord_8148543 prefixEnd_8148543 1394706397609872507246013 := by
  unfold tailWord_8148543
  simp only [CollatzResearch.WordTrace]
  refine ⟨297201779318227846193770283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198134519545485230795846855 297201779318227846193770283)
  ·
    refine ⟨445802668977341769290655425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297201779318227846193770283 445802668977341769290655425)
    ·
      refine ⟨334352001733006326967991569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445802668977341769290655425 334352001733006326967991569)
      ·
        refine ⟨250764001299754745225993677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334352001733006326967991569 250764001299754745225993677)
        ·
          refine ⟨94036500487408029459747629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250764001299754745225993677 94036500487408029459747629)
          ·
            refine ⟨35263687682778011047405361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94036500487408029459747629 35263687682778011047405361)
            ·
              refine ⟨26447765762083508285554021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35263687682778011047405361 26447765762083508285554021)
              ·
                refine ⟨4958956080390657803541379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26447765762083508285554021 4958956080390657803541379)
                ·
                  refine ⟨7438434120585986705312069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958956080390657803541379 7438434120585986705312069)
                  ·
                    refine ⟨1394706397609872507246013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7438434120585986705312069 1394706397609872507246013)
                    ·
                      rfl

theorem cell23_8148543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 4].length) (baseStart_8148543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148543 prefixEnd_8148543 := by exact prefixLift 8148543
  have htrace : WordTrace (prefixWord ++ tailWord_8148543) baseStart_8148543 baseEnd_8148543 := by
    simpa [prefixWord, tailWord_8148543, baseEnd_8148543] using wordTrace_append hprefix tailTrace_8148543
  have hstable : (prefixWord ++ tailWord_8148543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148543).length < 2 ^ (prefixWord ++ tailWord_8148543).sum := by decide
  have hdescent : baseEnd_8148543 < baseStart_8148543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148569 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 3, 5]
def baseStart_8148569 : Nat := 118140960795 + 8148569 * 2 ^ 59
def prefixEnd_8148569 : Nat := 4983230072969 + 3 ^ 40 * 8148569 * 2
def baseEnd_8148569 : Nat := 1394710847775544806670973

theorem tailTrace_8148569 : CollatzResearch.WordTrace tailWord_8148569 prefixEnd_8148569 1394710847775544806670973 := by
  unfold tailWord_8148569
  simp only [CollatzResearch.WordTrace]
  refine ⟨297202727616133652634216761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198135151744089101756144507 297202727616133652634216761)
  ·
    refine ⟨222902045712100239475662571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297202727616133652634216761 222902045712100239475662571)
    ·
      refine ⟨334353068568150359213493857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222902045712100239475662571 334353068568150359213493857)
      ·
        refine ⟨250764801426112769410120393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334353068568150359213493857 250764801426112769410120393)
        ·
          refine ⟨188073601069584577057590295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250764801426112769410120393 188073601069584577057590295)
          ·
            refine ⟨282110401604376865586385443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188073601069584577057590295 282110401604376865586385443)
            ·
              refine ⟨423165602406565298379578165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282110401604376865586385443 423165602406565298379578165)
              ·
                refine ⟨39671775225615496723085453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 423165602406565298379578165 39671775225615496723085453)
                ·
                  refine ⟨14876915709605811271157045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39671775225615496723085453 14876915709605811271157045)
                  ·
                    refine ⟨1394710847775544806670973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14876915709605811271157045 1394710847775544806670973)
                    ·
                      rfl

theorem cell23_8148569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_8148569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148569 prefixEnd_8148569 := by exact prefixLift 8148569
  have htrace : WordTrace (prefixWord ++ tailWord_8148569) baseStart_8148569 baseEnd_8148569 := by
    simpa [prefixWord, tailWord_8148569, baseEnd_8148569] using wordTrace_append hprefix tailTrace_8148569
  have hstable : (prefixWord ++ tailWord_8148569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148569).length < 2 ^ (prefixWord ++ tailWord_8148569).sum := by decide
  have hdescent : baseEnd_8148569 < baseStart_8148569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148619 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 6]
def baseStart_8148619 : Nat := 118140960795 + 8148619 * 2 ^ 59
def prefixEnd_8148619 : Nat := 4983230072969 + 3 ^ 40 * 8148619 * 2
def baseEnd_8148619 : Nat := 4184158217359359224387689

theorem tailTrace_8148619 : CollatzResearch.WordTrace tailWord_8148619 prefixEnd_8148619 4184158217359359224387689 := by
  unfold tailWord_8148619
  simp only [CollatzResearch.WordTrace]
  refine ⟨297204551265952511173536911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198136367510635007449024607 297204551265952511173536911)
  ·
    refine ⟨445806826898928766760305367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297204551265952511173536911 445806826898928766760305367)
    ·
      refine ⟨668710240348393150140458051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445806826898928766760305367 668710240348393150140458051)
      ·
        refine ⟨1003065360522589725210687077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668710240348393150140458051 1003065360522589725210687077)
        ·
          refine ⟨188074755097985573477003827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1003065360522589725210687077 188074755097985573477003827)
          ·
            refine ⟨282112132646978360215505741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188074755097985573477003827 282112132646978360215505741)
            ·
              refine ⟨105792049742616885080814653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282112132646978360215505741 105792049742616885080814653)
              ·
                refine ⟨39672018653481331905305495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105792049742616885080814653 39672018653481331905305495)
                ·
                  refine ⟨59508027980221997857958243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39672018653481331905305495 59508027980221997857958243)
                  ·
                    refine ⟨89262041970332996786937365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59508027980221997857958243 89262041970332996786937365)
                    ·
                      refine ⟨4184158217359359224387689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89262041970332996786937365 4184158217359359224387689)
                      ·
                        rfl

theorem cell23_8148619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_8148619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148619 prefixEnd_8148619 := by exact prefixLift 8148619
  have htrace : WordTrace (prefixWord ++ tailWord_8148619) baseStart_8148619 baseEnd_8148619 := by
    simpa [prefixWord, tailWord_8148619, baseEnd_8148619] using wordTrace_append hprefix tailTrace_8148619
  have hstable : (prefixWord ++ tailWord_8148619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148619).length < 2 ^ (prefixWord ++ tailWord_8148619).sum := by decide
  have hdescent : baseEnd_8148619 < baseStart_8148619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148640 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 1, 1, 4]
def baseStart_8148640 : Nat := 118140960795 + 8148640 * 2 ^ 59
def prefixEnd_8148640 : Nat := 4983230072969 + 3 ^ 40 * 8148640 * 2
def baseEnd_8148640 : Nat := 4184169000453103642225093

theorem tailTrace_8148640 : CollatzResearch.WordTrace tailWord_8148640 prefixEnd_8148640 4184169000453103642225093 := by
  unfold tailWord_8148640
  simp only [CollatzResearch.WordTrace]
  refine ⟨148602658599438215880025687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198136878132584287840034249 148602658599438215880025687)
  ·
    refine ⟨222903987899157323820038531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148602658599438215880025687 222903987899157323820038531)
    ·
      refine ⟨334355981848735985730057797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222903987899157323820038531 334355981848735985730057797)
      ·
        refine ⟨62691746596637997324385837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334355981848735985730057797 62691746596637997324385837)
        ·
          refine ⟨23509404973739248996644689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62691746596637997324385837 23509404973739248996644689)
          ·
            refine ⟨17632053730304436747483517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23509404973739248996644689 17632053730304436747483517)
            ·
              refine ⟨6612020148864163780306319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17632053730304436747483517 6612020148864163780306319)
              ·
                refine ⟨9918030223296245670459479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6612020148864163780306319 9918030223296245670459479)
                ·
                  refine ⟨14877045334944368505689219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9918030223296245670459479 14877045334944368505689219)
                  ·
                    refine ⟨22315568002416552758533829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14877045334944368505689219 22315568002416552758533829)
                    ·
                      refine ⟨4184169000453103642225093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22315568002416552758533829 4184169000453103642225093)
                      ·
                        rfl

theorem cell23_8148640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_8148640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148640 prefixEnd_8148640 := by exact prefixLift 8148640
  have htrace : WordTrace (prefixWord ++ tailWord_8148640) baseStart_8148640 baseEnd_8148640 := by
    simpa [prefixWord, tailWord_8148640, baseEnd_8148640] using wordTrace_append hprefix tailTrace_8148640
  have hstable : (prefixWord ++ tailWord_8148640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148640).length < 2 ^ (prefixWord ++ tailWord_8148640).sum := by decide
  have hdescent : baseEnd_8148640 < baseStart_8148640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148659 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 1, 9]
def baseStart_8148659 : Nat := 118140960795 + 8148659 * 2 ^ 59
def prefixEnd_8148659 : Nat := 4983230072969 + 3 ^ 40 * 8148659 * 2
def baseEnd_8148659 : Nat := 1394726252195179689295835

theorem tailTrace_8148659 : CollatzResearch.WordTrace tailWord_8148659 prefixEnd_8148659 1394726252195179689295835 := by
  unfold tailWord_8148659
  simp only [CollatzResearch.WordTrace]
  refine ⟨297206010185807598004993031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198137340123871732003328687 297206010185807598004993031)
  ·
    refine ⟨445809015278711397007489547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297206010185807598004993031 445809015278711397007489547)
    ·
      refine ⟨668713522918067095511234321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445809015278711397007489547 668713522918067095511234321)
      ·
        refine ⟨501535142188550321633425741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668713522918067095511234321 501535142188550321633425741)
        ·
          refine ⟨188075678320706370612534653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501535142188550321633425741 188075678320706370612534653)
          ·
            refine ⟨70528379370264888979700495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188075678320706370612534653 70528379370264888979700495)
            ·
              refine ⟨105792569055397333469550743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70528379370264888979700495 105792569055397333469550743)
              ·
                refine ⟨158688853583096000204326115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105792569055397333469550743 158688853583096000204326115)
                ·
                  refine ⟨238033280374644000306489173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158688853583096000204326115 238033280374644000306489173)
                  ·
                    refine ⟨1394726252195179689295835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 238033280374644000306489173 1394726252195179689295835)
                    ·
                      rfl

theorem cell23_8148659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 9].length) (baseStart_8148659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148659 prefixEnd_8148659 := by exact prefixLift 8148659
  have htrace : WordTrace (prefixWord ++ tailWord_8148659) baseStart_8148659 baseEnd_8148659 := by
    simpa [prefixWord, tailWord_8148659, baseEnd_8148659] using wordTrace_append hprefix tailTrace_8148659
  have hstable : (prefixWord ++ tailWord_8148659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148659).length < 2 ^ (prefixWord ++ tailWord_8148659).sum := by decide
  have hdescent : baseEnd_8148659 < baseStart_8148659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148676 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_8148676 : Nat := 118140960795 + 8148676 * 2 ^ 59
def prefixEnd_8148676 : Nat := 4983230072969 + 3 ^ 40 * 8148676 * 2
def baseEnd_8148676 : Nat := 1394729161918888500458309

theorem tailTrace_8148676 : CollatzResearch.WordTrace tailWord_8148676 prefixEnd_8148676 1394729161918888500458309 := by
  unfold tailWord_8148676
  simp only [CollatzResearch.WordTrace]
  refine ⟨148603315113373004954180941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198137753484497339938907921 148603315113373004954180941)
  ·
    refine ⟨55726243167514876857817853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148603315113373004954180941 55726243167514876857817853)
    ·
      refine ⟨20897341187818078821681695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55726243167514876857817853 20897341187818078821681695)
      ·
        refine ⟨31346011781727118232522543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20897341187818078821681695 31346011781727118232522543)
        ·
          refine ⟨47019017672590677348783815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31346011781727118232522543 47019017672590677348783815)
          ·
            refine ⟨70528526508886016023175723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47019017672590677348783815 70528526508886016023175723)
            ·
              refine ⟨105792789763329024034763585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70528526508886016023175723 105792789763329024034763585)
              ·
                refine ⟨79344592322496768026072689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105792789763329024034763585 79344592322496768026072689)
                ·
                  refine ⟨59508444241872576019554517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79344592322496768026072689 59508444241872576019554517)
                  ·
                    refine ⟨1394729161918888500458309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59508444241872576019554517 1394729161918888500458309)
                    ·
                      rfl

theorem cell23_8148676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_8148676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148676 prefixEnd_8148676 := by exact prefixLift 8148676
  have htrace : WordTrace (prefixWord ++ tailWord_8148676) baseStart_8148676 baseEnd_8148676 := by
    simpa [prefixWord, tailWord_8148676, baseEnd_8148676] using wordTrace_append hprefix tailTrace_8148676
  have hstable : (prefixWord ++ tailWord_8148676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148676).length < 2 ^ (prefixWord ++ tailWord_8148676).sum := by decide
  have hdescent : baseEnd_8148676 < baseStart_8148676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148686 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_8148686 : Nat := 118140960795 + 8148686 * 2 ^ 59
def prefixEnd_8148686 : Nat := 4983230072969 + 3 ^ 40 * 8148686 * 2
def baseEnd_8148686 : Nat := 4184192620563210462249881

theorem tailTrace_8148686 : CollatzResearch.WordTrace tailWord_8148686 prefixEnd_8148686 4184192620563210462249881 := by
  unfold tailWord_8148686
  simp only [CollatzResearch.WordTrace]
  refine ⟨37150874369588722702028239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198137996637806521077483941 37150874369588722702028239)
  ·
    refine ⟨55726311554383084053042359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37150874369588722702028239 55726311554383084053042359)
    ·
      refine ⟨83589467331574626079563539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55726311554383084053042359 83589467331574626079563539)
      ·
        refine ⟨125384200997361939119345309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83589467331574626079563539 125384200997361939119345309)
        ·
          refine ⟨47019075374010727169754491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125384200997361939119345309 47019075374010727169754491)
          ·
            refine ⟨70528613061016090754631737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47019075374010727169754491 70528613061016090754631737)
            ·
              refine ⟨52896459795762068065973803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70528613061016090754631737 52896459795762068065973803)
              ·
                refine ⟨79344689693643102098960705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52896459795762068065973803 79344689693643102098960705)
                ·
                  refine ⟨59508517270232326574220529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79344689693643102098960705 59508517270232326574220529)
                  ·
                    refine ⟨44631387952674244930665397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59508517270232326574220529 44631387952674244930665397)
                    ·
                      refine ⟨4184192620563210462249881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44631387952674244930665397 4184192620563210462249881)
                      ·
                        rfl

theorem cell23_8148686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_8148686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148686 prefixEnd_8148686 := by exact prefixLift 8148686
  have htrace : WordTrace (prefixWord ++ tailWord_8148686) baseStart_8148686 baseEnd_8148686 := by
    simpa [prefixWord, tailWord_8148686, baseEnd_8148686] using wordTrace_append hprefix tailTrace_8148686
  have hstable : (prefixWord ++ tailWord_8148686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148686).length < 2 ^ (prefixWord ++ tailWord_8148686).sum := by decide
  have hdescent : baseEnd_8148686 < baseStart_8148686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148694 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_8148694 : Nat := 118140960795 + 8148694 * 2 ^ 59
def prefixEnd_8148694 : Nat := 4983230072969 + 3 ^ 40 * 8148694 * 2
def baseEnd_8148694 : Nat := 4184196728408446430949845

theorem tailTrace_8148694 : CollatzResearch.WordTrace tailWord_8148694 prefixEnd_8148694 4184196728408446430949845 := by
  unfold tailWord_8148694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18575455421292549936407321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198138191160453865988344757 18575455421292549936407321)
  ·
    refine ⟨13931591565969412452305491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18575455421292549936407321 13931591565969412452305491)
    ·
      refine ⟨20897387348954118678458237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13931591565969412452305491 20897387348954118678458237)
      ·
        refine ⟨7836520255857794504421839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20897387348954118678458237 7836520255857794504421839)
        ·
          refine ⟨11754780383786691756632759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7836520255857794504421839 11754780383786691756632759)
          ·
            refine ⟨17632170575680037634949139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11754780383786691756632759 17632170575680037634949139)
            ·
              refine ⟨26448255863520056452423709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17632170575680037634949139 26448255863520056452423709)
              ·
                refine ⟨9918095948820021169658891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26448255863520056452423709 9918095948820021169658891)
                ·
                  refine ⟨14877143923230031754488337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9918095948820021169658891 14877143923230031754488337)
                  ·
                    refine ⟨11157857942422523815866253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14877143923230031754488337 11157857942422523815866253)
                    ·
                      refine ⟨4184196728408446430949845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11157857942422523815866253 4184196728408446430949845)
                      ·
                        rfl

theorem cell23_8148694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_8148694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148694 prefixEnd_8148694 := by exact prefixLift 8148694
  have htrace : WordTrace (prefixWord ++ tailWord_8148694) baseStart_8148694 baseEnd_8148694 := by
    simpa [prefixWord, tailWord_8148694, baseEnd_8148694] using wordTrace_append hprefix tailTrace_8148694
  have hstable : (prefixWord ++ tailWord_8148694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148694).length < 2 ^ (prefixWord ++ tailWord_8148694).sum := by decide
  have hdescent : baseEnd_8148694 < baseStart_8148694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148716 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_8148716 : Nat := 118140960795 + 8148716 * 2 ^ 59
def prefixEnd_8148716 : Nat := 4983230072969 + 3 ^ 40 * 8148716 * 2
def baseEnd_8148716 : Nat := 4184208024982845344874743

theorem tailTrace_8148716 : CollatzResearch.WordTrace tailWord_8148716 prefixEnd_8148716 4184208024982845344874743 := by
  unfold tailWord_8148716
  simp only [CollatzResearch.WordTrace]
  refine ⟨148604044573300548369909001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198138726097734064493212001 148604044573300548369909001)
  ·
    refine ⟨111453033429975411277431751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148604044573300548369909001 111453033429975411277431751)
    ·
      refine ⟨167179550144963116916147627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111453033429975411277431751 167179550144963116916147627)
      ·
        refine ⟨250769325217444675374221441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167179550144963116916147627 250769325217444675374221441)
        ·
          refine ⟨188076993913083506530666081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250769325217444675374221441 188076993913083506530666081)
          ·
            refine ⟨141057745434812629897999561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188076993913083506530666081 141057745434812629897999561)
            ·
              refine ⟨105793309076109472423499671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141057745434812629897999561 105793309076109472423499671)
              ·
                refine ⟨158689963614164208635249507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105793309076109472423499671 158689963614164208635249507)
                ·
                  refine ⟨238034945421246312952874261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158689963614164208635249507 238034945421246312952874261)
                  ·
                    refine ⟨11157888066620920919665981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 238034945421246312952874261 11157888066620920919665981)
                    ·
                      refine ⟨4184208024982845344874743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11157888066620920919665981 4184208024982845344874743)
                      ·
                        rfl

theorem cell23_8148716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_8148716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148716 prefixEnd_8148716 := by exact prefixLift 8148716
  have htrace : WordTrace (prefixWord ++ tailWord_8148716) baseStart_8148716 baseEnd_8148716 := by
    simpa [prefixWord, tailWord_8148716, baseEnd_8148716] using wordTrace_append hprefix tailTrace_8148716
  have hstable : (prefixWord ++ tailWord_8148716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148716).length < 2 ^ (prefixWord ++ tailWord_8148716).sum := by decide
  have hdescent : baseEnd_8148716 < baseStart_8148716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148724 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_8148724 : Nat := 118140960795 + 8148724 * 2 ^ 59
def prefixEnd_8148724 : Nat := 4983230072969 + 3 ^ 40 * 8148724 * 2
def baseEnd_8148724 : Nat := 4184212132828081313574707

theorem tailTrace_8148724 : CollatzResearch.WordTrace tailWord_8148724 prefixEnd_8148724 4184212132828081313574707 := by
  unfold tailWord_8148724
  simp only [CollatzResearch.WordTrace]
  refine ⟨148604190465286057053054613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198138920620381409404072817 148604190465286057053054613)
  ·
    refine ⟨6965821428060283924361935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148604190465286057053054613 6965821428060283924361935)
    ·
      refine ⟨10448732142090425886542903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6965821428060283924361935 10448732142090425886542903)
      ·
        refine ⟨15673098213135638829814355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10448732142090425886542903 15673098213135638829814355)
        ·
          refine ⟨23509647319703458244721533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15673098213135638829814355 23509647319703458244721533)
          ·
            refine ⟨8816117744888796841770575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23509647319703458244721533 8816117744888796841770575)
            ·
              refine ⟨13224176617333195262655863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8816117744888796841770575 13224176617333195262655863)
              ·
                refine ⟨19836264925999792893983795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13224176617333195262655863 19836264925999792893983795)
                ·
                  refine ⟨29754397388999689340975693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19836264925999792893983795 29754397388999689340975693)
                  ·
                    refine ⟨11157899020874883502865885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29754397388999689340975693 11157899020874883502865885)
                    ·
                      refine ⟨4184212132828081313574707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11157899020874883502865885 4184212132828081313574707)
                      ·
                        rfl

theorem cell23_8148724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_8148724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148724 prefixEnd_8148724 := by exact prefixLift 8148724
  have htrace : WordTrace (prefixWord ++ tailWord_8148724) baseStart_8148724 baseEnd_8148724 := by
    simpa [prefixWord, tailWord_8148724, baseEnd_8148724] using wordTrace_append hprefix tailTrace_8148724
  have hstable : (prefixWord ++ tailWord_8148724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148724).length < 2 ^ (prefixWord ++ tailWord_8148724).sum := by decide
  have hdescent : baseEnd_8148724 < baseStart_8148724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148734 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_8148734 : Nat := 118140960795 + 8148734 * 2 ^ 59
def prefixEnd_8148734 : Nat := 4983230072969 + 3 ^ 40 * 8148734 * 2
def baseEnd_8148734 : Nat := 4184217267634626274449661

theorem tailTrace_8148734 : CollatzResearch.WordTrace tailWord_8148734 prefixEnd_8148734 4184217267634626274449661 := by
  unfold tailWord_8148734
  simp only [CollatzResearch.WordTrace]
  refine ⟨37151093207566985726746657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198139163773690590542648837 37151093207566985726746657)
  ·
    refine ⟨27863319905675239295059993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37151093207566985726746657 27863319905675239295059993)
    ·
      refine ⟨20897489929256429471294995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27863319905675239295059993 20897489929256429471294995)
      ·
        refine ⟨31346234893884644206942493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20897489929256429471294995 31346234893884644206942493)
        ·
          refine ⟨11754838085206741577603435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31346234893884644206942493 11754838085206741577603435)
          ·
            refine ⟨17632257127810112366405153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11754838085206741577603435 17632257127810112366405153)
            ·
              refine ⟨13224192845857584274803865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17632257127810112366405153 13224192845857584274803865)
              ·
                refine ⟨9918144634393188206102899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13224192845857584274803865 9918144634393188206102899)
                ·
                  refine ⟨14877216951589782309154349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9918144634393188206102899 14877216951589782309154349)
                  ·
                    refine ⟨5578956356846168365932881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14877216951589782309154349 5578956356846168365932881)
                    ·
                      refine ⟨4184217267634626274449661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5578956356846168365932881 4184217267634626274449661)
                      ·
                        rfl

theorem cell23_8148734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_8148734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148734 prefixEnd_8148734 := by exact prefixLift 8148734
  have htrace : WordTrace (prefixWord ++ tailWord_8148734) baseStart_8148734 baseEnd_8148734 := by
    simpa [prefixWord, tailWord_8148734, baseEnd_8148734] using wordTrace_append hprefix tailTrace_8148734
  have hstable : (prefixWord ++ tailWord_8148734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148734).length < 2 ^ (prefixWord ++ tailWord_8148734).sum := by decide
  have hdescent : baseEnd_8148734 < baseStart_8148734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148796 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_8148796 : Nat := 118140960795 + 8148796 * 2 ^ 59
def prefixEnd_8148796 : Nat := 4983230072969 + 3 ^ 40 * 8148796 * 2
def baseEnd_8148796 : Nat := 1394749701145068343958125

theorem tailTrace_8148796 : CollatzResearch.WordTrace tailWord_8148796 prefixEnd_8148796 1394749701145068343958125 := by
  unfold tailWord_8148796
  simp only [CollatzResearch.WordTrace]
  refine ⟨148605503493155635201365121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198140671324207513601820161 148605503493155635201365121)
  ·
    refine ⟨111454127619866726401023841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148605503493155635201365121 111454127619866726401023841)
    ·
      refine ⟨83590595714900044800767881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111454127619866726401023841 83590595714900044800767881)
      ·
        refine ⟨62692946786175033600575911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83590595714900044800767881 62692946786175033600575911)
        ·
          refine ⟨94039420179262550400863867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62692946786175033600575911 94039420179262550400863867)
          ·
            refine ⟨141059130268893825601295801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94039420179262550400863867 141059130268893825601295801)
            ·
              refine ⟨105794347701670369200971851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141059130268893825601295801 105794347701670369200971851)
              ·
                refine ⟨158691521552505553801457777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105794347701670369200971851 158691521552505553801457777)
                ·
                  refine ⟨119018641164379165351093333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158691521552505553801457777 119018641164379165351093333)
                  ·
                    refine ⟨1394749701145068343958125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119018641164379165351093333 1394749701145068343958125)
                    ·
                      rfl

theorem cell23_8148796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_8148796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148796 prefixEnd_8148796 := by exact prefixLift 8148796
  have htrace : WordTrace (prefixWord ++ tailWord_8148796) baseStart_8148796 baseEnd_8148796 := by
    simpa [prefixWord, tailWord_8148796, baseEnd_8148796] using wordTrace_append hprefix tailTrace_8148796
  have hstable : (prefixWord ++ tailWord_8148796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148796).length < 2 ^ (prefixWord ++ tailWord_8148796).sum := by decide
  have hdescent : baseEnd_8148796 < baseStart_8148796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148803 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 4]
def baseStart_8148803 : Nat := 118140960795 + 8148803 * 2 ^ 59
def prefixEnd_8148803 : Nat := 4983230072969 + 3 ^ 40 * 8148803 * 2
def baseEnd_8148803 : Nat := 4184252697799786504486843

theorem tailTrace_8148803 : CollatzResearch.WordTrace tailWord_8148803 prefixEnd_8148803 4184252697799786504486843 := by
  unfold tailWord_8148803
  simp only [CollatzResearch.WordTrace]
  refine ⟨297211262297285910598235063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198140841531523940398823375 297211262297285910598235063)
  ·
    refine ⟨445816893445928865897352595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297211262297285910598235063 445816893445928865897352595)
    ·
      refine ⟨668725340168893298846028893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445816893445928865897352595 668725340168893298846028893)
      ·
        refine ⟨250772002563334987067260835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668725340168893298846028893 250772002563334987067260835)
        ·
          refine ⟨376158003845002480600891253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250772002563334987067260835 376158003845002480600891253)
          ·
            refine ⟨35264812860468982556333555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 376158003845002480600891253 35264812860468982556333555)
            ·
              refine ⟨52897219290703473834500333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35264812860468982556333555 52897219290703473834500333)
              ·
                refine ⟨19836457234013802687937625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52897219290703473834500333 19836457234013802687937625)
                ·
                  refine ⟨14877342925510352015953219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19836457234013802687937625 14877342925510352015953219)
                  ·
                    refine ⟨22316014388265528023929829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14877342925510352015953219 22316014388265528023929829)
                    ·
                      refine ⟨4184252697799786504486843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22316014388265528023929829 4184252697799786504486843)
                      ·
                        rfl

theorem cell23_8148803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_8148803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148803 prefixEnd_8148803 := by exact prefixLift 8148803
  have htrace : WordTrace (prefixWord ++ tailWord_8148803) baseStart_8148803 baseEnd_8148803 := by
    simpa [prefixWord, tailWord_8148803, baseEnd_8148803] using wordTrace_append hprefix tailTrace_8148803
  have hstable : (prefixWord ++ tailWord_8148803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148803).length < 2 ^ (prefixWord ++ tailWord_8148803).sum := by decide
  have hdescent : baseEnd_8148803 < baseStart_8148803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148816 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_8148816 : Nat := 118140960795 + 8148816 * 2 ^ 59
def prefixEnd_8148816 : Nat := 4983230072969 + 3 ^ 40 * 8148816 * 2
def baseEnd_8148816 : Nat := 4184259373048294953624283

theorem tailTrace_8148816 : CollatzResearch.WordTrace tailWord_8148816 prefixEnd_8148816 4184259373048294953624283 := by
  unfold tailWord_8148816
  simp only [CollatzResearch.WordTrace]
  refine ⟨148605868223119406909229151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198141157630825875878972201 148605868223119406909229151)
  ·
    refine ⟨222908802334679110363843727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148605868223119406909229151 222908802334679110363843727)
    ·
      refine ⟨334363203502018665545765591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222908802334679110363843727 334363203502018665545765591)
      ·
        refine ⟨501544805253027998318648387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334363203502018665545765591 501544805253027998318648387)
        ·
          refine ⟨752317207879541997477972581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501544805253027998318648387 752317207879541997477972581)
          ·
            refine ⟨141059476477414124527119859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 752317207879541997477972581 141059476477414124527119859)
            ·
              refine ⟨211589214716121186790679789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141059476477414124527119859 211589214716121186790679789)
              ·
                refine ⟨79345955518545445046504921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211589214716121186790679789 79345955518545445046504921)
                ·
                  refine ⟨59509466638909083784878691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79345955518545445046504921 59509466638909083784878691)
                  ·
                    refine ⟨89264199958363625677318037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59509466638909083784878691 89264199958363625677318037)
                    ·
                      refine ⟨4184259373048294953624283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89264199958363625677318037 4184259373048294953624283)
                      ·
                        rfl

theorem cell23_8148816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_8148816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148816 prefixEnd_8148816 := by exact prefixLift 8148816
  have htrace : WordTrace (prefixWord ++ tailWord_8148816) baseStart_8148816 baseEnd_8148816 := by
    simpa [prefixWord, tailWord_8148816, baseEnd_8148816] using wordTrace_append hprefix tailTrace_8148816
  have hstable : (prefixWord ++ tailWord_8148816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148816).length < 2 ^ (prefixWord ++ tailWord_8148816).sum := by decide
  have hdescent : baseEnd_8148816 < baseStart_8148816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148820 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_8148820 : Nat := 118140960795 + 8148820 * 2 ^ 59
def prefixEnd_8148820 : Nat := 4983230072969 + 3 ^ 40 * 8148820 * 2
def baseEnd_8148820 : Nat := 4184261426970912937974265

theorem tailTrace_8148820 : CollatzResearch.WordTrace tailWord_8148820 prefixEnd_8148820 4184261426970912937974265 := by
  unfold tailWord_8148820
  simp only [CollatzResearch.WordTrace]
  refine ⟨148605941169112161250801957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198141254892149548334402609 148605941169112161250801957)
  ·
    refine ⟨27863613969208530234525367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148605941169112161250801957 27863613969208530234525367)
    ·
      refine ⟨41795420953812795351788051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27863613969208530234525367 41795420953812795351788051)
      ·
        refine ⟨62693131430719193027682077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41795420953812795351788051 62693131430719193027682077)
        ·
          refine ⟨23509924286519697385380779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62693131430719193027682077 23509924286519697385380779)
          ·
            refine ⟨35264886429779546078071169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23509924286519697385380779 35264886429779546078071169)
            ·
              refine ⟨26448664822334659558553377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35264886429779546078071169 26448664822334659558553377)
              ·
                refine ⟨19836498616750994668915033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26448664822334659558553377 19836498616750994668915033)
                ·
                  refine ⟨14877373962563246001686275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19836498616750994668915033 14877373962563246001686275)
                  ·
                    refine ⟨22316060943844869002529413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14877373962563246001686275 22316060943844869002529413)
                    ·
                      refine ⟨4184261426970912937974265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22316060943844869002529413 4184261426970912937974265)
                      ·
                        rfl

theorem cell23_8148820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_8148820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148820 prefixEnd_8148820 := by exact prefixLift 8148820
  have htrace : WordTrace (prefixWord ++ tailWord_8148820) baseStart_8148820 baseEnd_8148820 := by
    simpa [prefixWord, tailWord_8148820, baseEnd_8148820] using wordTrace_append hprefix tailTrace_8148820
  have hstable : (prefixWord ++ tailWord_8148820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148820).length < 2 ^ (prefixWord ++ tailWord_8148820).sum := by decide
  have hdescent : baseEnd_8148820 < baseStart_8148820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148854 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_8148854 : Nat := 118140960795 + 8148854 * 2 ^ 59
def prefixEnd_8148854 : Nat := 4983230072969 + 3 ^ 40 * 8148854 * 2
def baseEnd_8148854 : Nat := 4184278885313165804949109

theorem tailTrace_8148854 : CollatzResearch.WordTrace tailWord_8148854 prefixEnd_8148854 4184278885313165804949109 := by
  unfold tailWord_8148854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18575820151256321644271351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198142081613400764205561077 18575820151256321644271351)
  ·
    refine ⟨27863730226884482466407027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18575820151256321644271351 27863730226884482466407027)
    ·
      refine ⟨41795595340326723699610541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27863730226884482466407027 41795595340326723699610541)
      ·
        refine ⟨15673348252622521387353953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41795595340326723699610541 15673348252622521387353953)
        ·
          refine ⟨11755011189466891040515465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15673348252622521387353953 11755011189466891040515465)
          ·
            refine ⟨8816258392100168280386599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11755011189466891040515465 8816258392100168280386599)
            ·
              refine ⟨13224387588150252420579899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8816258392100168280386599 13224387588150252420579899)
              ·
                refine ⟨19836581382225378630869849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13224387588150252420579899 19836581382225378630869849)
                ·
                  refine ⟨14877436036669033973152387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19836581382225378630869849 14877436036669033973152387)
                  ·
                    refine ⟨22316154055003550959728581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14877436036669033973152387 22316154055003550959728581)
                    ·
                      refine ⟨4184278885313165804949109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22316154055003550959728581 4184278885313165804949109)
                      ·
                        rfl

theorem cell23_8148854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_8148854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148854 prefixEnd_8148854 := by exact prefixLift 8148854
  have htrace : WordTrace (prefixWord ++ tailWord_8148854) baseStart_8148854 baseEnd_8148854 := by
    simpa [prefixWord, tailWord_8148854, baseEnd_8148854] using wordTrace_append hprefix tailTrace_8148854
  have hstable : (prefixWord ++ tailWord_8148854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148854).length < 2 ^ (prefixWord ++ tailWord_8148854).sum := by decide
  have hdescent : baseEnd_8148854 < baseStart_8148854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148887 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 3]
def baseStart_8148887 : Nat := 118140960795 + 8148887 * 2 ^ 59
def prefixEnd_8148887 : Nat := 4983230072969 + 3 ^ 40 * 8148887 * 2
def baseEnd_8148887 : Nat := 4184295830174764175836457

theorem tailTrace_8148887 : CollatzResearch.WordTrace tailWord_8148887 prefixEnd_8148887 4184295830174764175836457 := by
  unfold tailWord_8148887
  simp only [CollatzResearch.WordTrace]
  refine ⟨297214326028981592944292915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198142884019321061962861943 297214326028981592944292915)
  ·
    refine ⟨445821489043472389416439373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297214326028981592944292915 445821489043472389416439373)
    ·
      refine ⟨167183058391302146031164765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445821489043472389416439373 167183058391302146031164765)
      ·
        refine ⟨62693646896738304761686787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167183058391302146031164765 62693646896738304761686787)
        ·
          refine ⟨94040470345107457142530181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62693646896738304761686787 94040470345107457142530181)
          ·
            refine ⟨17632588189707648214224409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94040470345107457142530181 17632588189707648214224409)
            ·
              refine ⟨13224441142280736160668307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17632588189707648214224409 13224441142280736160668307)
              ·
                refine ⟨19836661713421104241002461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13224441142280736160668307 19836661713421104241002461)
                ·
                  refine ⟨7438748142532914090375923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19836661713421104241002461 7438748142532914090375923)
                  ·
                    refine ⟨11158122213799371135563885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7438748142532914090375923 11158122213799371135563885)
                    ·
                      refine ⟨4184295830174764175836457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11158122213799371135563885 4184295830174764175836457)
                      ·
                        rfl

theorem cell23_8148887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_8148887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148887 prefixEnd_8148887 := by exact prefixLift 8148887
  have htrace : WordTrace (prefixWord ++ tailWord_8148887) baseStart_8148887 baseEnd_8148887 := by
    simpa [prefixWord, tailWord_8148887, baseEnd_8148887] using wordTrace_append hprefix tailTrace_8148887
  have hstable : (prefixWord ++ tailWord_8148887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148887).length < 2 ^ (prefixWord ++ tailWord_8148887).sum := by decide
  have hdescent : baseEnd_8148887 < baseStart_8148887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148944 : List Nat := [2, 1, 1, 1, 1, 2, 4, 6, 1, 2, 2]
def baseStart_8148944 : Nat := 118140960795 + 8148944 * 2 ^ 59
def prefixEnd_8148944 : Nat := 4983230072969 + 3 ^ 40 * 8148944 * 2
def baseEnd_8148944 : Nat := 4184325098572070452823695

theorem tailTrace_8148944 : CollatzResearch.WordTrace tailWord_8148944 prefixEnd_8148944 4184325098572070452823695 := by
  unfold tailWord_8148944
  simp only [CollatzResearch.WordTrace]
  refine ⟨148608202494887545839558943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198144269993183394452745257 148608202494887545839558943)
  ·
    refine ⟨222912303742331318759338415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148608202494887545839558943 222912303742331318759338415)
    ·
      refine ⟨334368455613496978139007623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222912303742331318759338415 334368455613496978139007623)
      ·
        refine ⟨501552683420245467208511435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334368455613496978139007623 501552683420245467208511435)
        ·
          refine ⟨752329025130368200812767153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501552683420245467208511435 752329025130368200812767153)
          ·
            refine ⟨564246768847776150609575365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752329025130368200812767153 564246768847776150609575365)
            ·
              refine ⟨105796269158958028239295381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 564246768847776150609575365 105796269158958028239295381)
              ·
                refine ⟨4959200116826157573716971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105796269158958028239295381 4959200116826157573716971)
                ·
                  refine ⟨7438800175239236360575457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959200116826157573716971 7438800175239236360575457)
                  ·
                    refine ⟨5579100131429427270431593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7438800175239236360575457 5579100131429427270431593)
                    ·
                      refine ⟨4184325098572070452823695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579100131429427270431593 4184325098572070452823695)
                      ·
                        rfl

theorem cell23_8148944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 2, 2].length) (baseStart_8148944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148944 prefixEnd_8148944 := by exact prefixLift 8148944
  have htrace : WordTrace (prefixWord ++ tailWord_8148944) baseStart_8148944 baseEnd_8148944 := by
    simpa [prefixWord, tailWord_8148944, baseEnd_8148944] using wordTrace_append hprefix tailTrace_8148944
  have hstable : (prefixWord ++ tailWord_8148944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148944).length < 2 ^ (prefixWord ++ tailWord_8148944).sum := by decide
  have hdescent : baseEnd_8148944 < baseStart_8148944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148977 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_8148977 : Nat := 118140960795 + 8148977 * 2 ^ 59
def prefixEnd_8148977 : Nat := 4983230072969 + 3 ^ 40 * 8148977 * 2
def baseEnd_8148977 : Nat := 4184342043433668823711043

theorem tailTrace_8148977 : CollatzResearch.WordTrace tailWord_8148977 prefixEnd_8148977 4184342043433668823711043 := by
  unfold tailWord_8148977
  simp only [CollatzResearch.WordTrace]
  refine ⟨297217608598655538315069185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198145072399103692210046123 297217608598655538315069185)
  ·
    refine ⟨222913206448991653736301889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297217608598655538315069185 222913206448991653736301889)
    ·
      refine ⟨167184904836743740302226417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222913206448991653736301889 167184904836743740302226417)
      ·
        refine ⟨125388678627557805226669813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167184904836743740302226417 125388678627557805226669813)
        ·
          refine ⟨11755188621333544240000295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125388678627557805226669813 11755188621333544240000295)
          ·
            refine ⟨17632782932000316360000443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11755188621333544240000295 17632782932000316360000443)
            ·
              refine ⟨26449174398000474540000665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17632782932000316360000443 26449174398000474540000665)
              ·
                refine ⟨19836880798500355905000499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26449174398000474540000665 19836880798500355905000499)
                ·
                  refine ⟨29755321197750533857500749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19836880798500355905000499 29755321197750533857500749)
                  ·
                    refine ⟨11158245449156450196562781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29755321197750533857500749 11158245449156450196562781)
                    ·
                      refine ⟨4184342043433668823711043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11158245449156450196562781 4184342043433668823711043)
                      ·
                        rfl

theorem cell23_8148977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_8148977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148977 prefixEnd_8148977 := by exact prefixLift 8148977
  have htrace : WordTrace (prefixWord ++ tailWord_8148977) baseStart_8148977 baseEnd_8148977 := by
    simpa [prefixWord, tailWord_8148977, baseEnd_8148977] using wordTrace_append hprefix tailTrace_8148977
  have hstable : (prefixWord ++ tailWord_8148977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148977).length < 2 ^ (prefixWord ++ tailWord_8148977).sum := by decide
  have hdescent : baseEnd_8148977 < baseStart_8148977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148983 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_8148983 : Nat := 118140960795 + 8148983 * 2 ^ 59
def prefixEnd_8148983 : Nat := 4983230072969 + 3 ^ 40 * 8148983 * 2
def baseEnd_8148983 : Nat := 4184345124317595800236015

theorem tailTrace_8148983 : CollatzResearch.WordTrace tailWord_8148983 prefixEnd_8148983 4184345124317595800236015 := by
  unfold tailWord_8148983
  simp only [CollatzResearch.WordTrace]
  refine ⟨297217827436633801339787603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198145218291089200893191735 297217827436633801339787603)
  ·
    refine ⟨445826741154950702009681405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297217827436633801339787603 445826741154950702009681405)
    ·
      refine ⟨167185027933106513253630527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445826741154950702009681405 167185027933106513253630527)
      ·
        refine ⟨250777541899659769880445791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167185027933106513253630527 250777541899659769880445791)
        ·
          refine ⟨376166312849489654820668687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250777541899659769880445791 376166312849489654820668687)
          ·
            refine ⟨564249469274234482231003031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376166312849489654820668687 564249469274234482231003031)
            ·
              refine ⟨846374203911351723346504547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564249469274234482231003031 846374203911351723346504547)
              ·
                refine ⟨1269561305867027585019756821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846374203911351723346504547 1269561305867027585019756821)
                ·
                  refine ⟨59510686212516918047801101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1269561305867027585019756821 59510686212516918047801101)
                  ·
                    refine ⟨22316507329693844267925413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59510686212516918047801101 22316507329693844267925413)
                    ·
                      refine ⟨4184345124317595800236015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22316507329693844267925413 4184345124317595800236015)
                      ·
                        rfl

theorem cell23_8148983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_8148983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148983 prefixEnd_8148983 := by exact prefixLift 8148983
  have htrace : WordTrace (prefixWord ++ tailWord_8148983) baseStart_8148983 baseEnd_8148983 := by
    simpa [prefixWord, tailWord_8148983, baseEnd_8148983] using wordTrace_append hprefix tailTrace_8148983
  have hstable : (prefixWord ++ tailWord_8148983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148983).length < 2 ^ (prefixWord ++ tailWord_8148983).sum := by decide
  have hdescent : baseEnd_8148983 < baseStart_8148983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8148987 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 1, 3, 2]
def baseStart_8148987 : Nat := 118140960795 + 8148987 * 2 ^ 59
def prefixEnd_8148987 : Nat := 4983230072969 + 3 ^ 40 * 8148987 * 2
def baseEnd_8148987 : Nat := 4184347178240213784585997

theorem tailTrace_8148987 : CollatzResearch.WordTrace tailWord_8148987 prefixEnd_8148987 4184347178240213784585997 := by
  unfold tailWord_8148987
  simp only [CollatzResearch.WordTrace]
  refine ⟨297217973328619310022933215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198145315552412873348622143 297217973328619310022933215)
  ·
    refine ⟨445826959992928965034399823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297217973328619310022933215 445826959992928965034399823)
    ·
      refine ⟨668740439989393447551599735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445826959992928965034399823 668740439989393447551599735)
      ·
        refine ⟨1003110659984090171327399603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668740439989393447551599735 1003110659984090171327399603)
        ·
          refine ⟨1504665989976135256991099405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003110659984090171327399603 1504665989976135256991099405)
          ·
            refine ⟨564249746241050721371662277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1504665989976135256991099405 564249746241050721371662277)
            ·
              refine ⟨105796827420197010257186677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 564249746241050721371662277 105796827420197010257186677)
              ·
                refine ⟨9918452570643469711611251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105796827420197010257186677 9918452570643469711611251)
                ·
                  refine ⟨14877678855965204567416877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9918452570643469711611251 14877678855965204567416877)
                  ·
                    refine ⟨5579129570986951712781329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14877678855965204567416877 5579129570986951712781329)
                    ·
                      refine ⟨4184347178240213784585997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579129570986951712781329 4184347178240213784585997)
                      ·
                        rfl

theorem cell23_8148987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 3, 2].length) (baseStart_8148987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8148987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8148987 prefixEnd_8148987 := by exact prefixLift 8148987
  have htrace : WordTrace (prefixWord ++ tailWord_8148987) baseStart_8148987 baseEnd_8148987 := by
    simpa [prefixWord, tailWord_8148987, baseEnd_8148987] using wordTrace_append hprefix tailTrace_8148987
  have hstable : (prefixWord ++ tailWord_8148987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8148987).length < 2 ^ (prefixWord ++ tailWord_8148987).sum := by decide
  have hdescent : baseEnd_8148987 < baseStart_8148987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8148987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149017 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 6, 2, 2]
def baseStart_8149017 : Nat := 118140960795 + 8149017 * 2 ^ 59
def prefixEnd_8149017 : Nat := 4983230072969 + 3 ^ 40 * 8149017 * 2
def baseEnd_8149017 : Nat := 4184362582659848667210859

theorem tailTrace_8149017 : CollatzResearch.WordTrace tailWord_8149017 prefixEnd_8149017 4184362582659848667210859 := by
  unfold tailWord_8149017
  simp only [CollatzResearch.WordTrace]
  refine ⟨297219067518510625146525305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198146045012340416764350203 297219067518510625146525305)
  ·
    refine ⟨222914300638882968859893979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297219067518510625146525305 222914300638882968859893979)
    ·
      refine ⟨334371450958324453289840969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222914300638882968859893979 334371450958324453289840969)
      ·
        refine ⟨250778588218743339967380727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334371450958324453289840969 250778588218743339967380727)
        ·
          refine ⟨376167882328115009951071091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250778588218743339967380727 376167882328115009951071091)
          ·
            refine ⟨564251823492172514926606637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376167882328115009951071091 564251823492172514926606637)
            ·
              refine ⟨211594433809564693097477489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 564251823492172514926606637 211594433809564693097477489)
              ·
                refine ⟨158695825357173519823108117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211594433809564693097477489 158695825357173519823108117)
                ·
                  refine ⟨7438866813617508741708193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158695825357173519823108117 7438866813617508741708193)
                  ·
                    refine ⟨5579150110213131556281145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7438866813617508741708193 5579150110213131556281145)
                    ·
                      refine ⟨4184362582659848667210859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579150110213131556281145 4184362582659848667210859)
                      ·
                        rfl

theorem cell23_8149017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_8149017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149017 prefixEnd_8149017 := by exact prefixLift 8149017
  have htrace : WordTrace (prefixWord ++ tailWord_8149017) baseStart_8149017 baseEnd_8149017 := by
    simpa [prefixWord, tailWord_8149017, baseEnd_8149017] using wordTrace_append hprefix tailTrace_8149017
  have hstable : (prefixWord ++ tailWord_8149017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149017).length < 2 ^ (prefixWord ++ tailWord_8149017).sum := by decide
  have hdescent : baseEnd_8149017 < baseStart_8149017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149034 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_8149034 : Nat := 118140960795 + 8149034 * 2 ^ 59
def prefixEnd_8149034 : Nat := 4983230072969 + 3 ^ 40 * 8149034 * 2
def baseEnd_8149034 : Nat := 4184371311830975100698281

theorem tailTrace_8149034 : CollatzResearch.WordTrace tailWord_8149034 prefixEnd_8149034 4184371311830975100698281 := by
  unfold tailWord_8149034
  simp only [CollatzResearch.WordTrace]
  refine ⟨74304921889862259262473539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198146458372966024699929437 74304921889862259262473539)
  ·
    refine ⟨111457382834793388893710309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74304921889862259262473539 111457382834793388893710309)
    ·
      refine ⟨20898259281523760417570683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111457382834793388893710309 20898259281523760417570683)
      ·
        refine ⟨31347388922285640626356025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20898259281523760417570683 31347388922285640626356025)
        ·
          refine ⟨23510541691714230469767019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31347388922285640626356025 23510541691714230469767019)
          ·
            refine ⟨35265812537571345704650529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23510541691714230469767019 35265812537571345704650529)
            ·
              refine ⟨26449359403178509278487897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35265812537571345704650529 26449359403178509278487897)
              ·
                refine ⟨19837019552383881958865923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26449359403178509278487897 19837019552383881958865923)
                ·
                  refine ⟨29755529328575822938298885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19837019552383881958865923 29755529328575822938298885)
                  ·
                    refine ⟨5579161749107966800931041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29755529328575822938298885 5579161749107966800931041)
                    ·
                      refine ⟨4184371311830975100698281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579161749107966800931041 4184371311830975100698281)
                      ·
                        rfl

theorem cell23_8149034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_8149034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149034 prefixEnd_8149034 := by exact prefixLift 8149034
  have htrace : WordTrace (prefixWord ++ tailWord_8149034) baseStart_8149034 baseEnd_8149034 := by
    simpa [prefixWord, tailWord_8149034, baseEnd_8149034] using wordTrace_append hprefix tailTrace_8149034
  have hstable : (prefixWord ++ tailWord_8149034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149034).length < 2 ^ (prefixWord ++ tailWord_8149034).sum := by decide
  have hdescent : baseEnd_8149034 < baseStart_8149034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149038 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_8149038 : Nat := 118140960795 + 8149038 * 2 ^ 59
def prefixEnd_8149038 : Nat := 4983230072969 + 3 ^ 40 * 8149038 * 2
def baseEnd_8149038 : Nat := 4184373365753593085048263

theorem tailTrace_8149038 : CollatzResearch.WordTrace tailWord_8149038 prefixEnd_8149038 4184373365753593085048263 := by
  unfold tailWord_8149038
  simp only [CollatzResearch.WordTrace]
  refine ⟨37152479181429318216629971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198146555634289697155359845 37152479181429318216629971)
  ·
    refine ⟨55728718772143977324944957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37152479181429318216629971 55728718772143977324944957)
    ·
      refine ⟨20898269539553991496854359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55728718772143977324944957 20898269539553991496854359)
      ·
        refine ⟨31347404309330987245281539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20898269539553991496854359 31347404309330987245281539)
        ·
          refine ⟨47021106463996480867922309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31347404309330987245281539 47021106463996480867922309)
          ·
            refine ⟨8816457461999340162735433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47021106463996480867922309 8816457461999340162735433)
            ·
              refine ⟨6612343096499505122051575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8816457461999340162735433 6612343096499505122051575)
              ·
                refine ⟨9918514644749257683077363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6612343096499505122051575 9918514644749257683077363)
                ·
                  refine ⟨14877771967123886524616045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9918514644749257683077363 14877771967123886524616045)
                  ·
                    refine ⟨5579164487671457446731017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14877771967123886524616045 5579164487671457446731017)
                    ·
                      refine ⟨4184373365753593085048263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579164487671457446731017 4184373365753593085048263)
                      ·
                        rfl

theorem cell23_8149038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_8149038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149038 prefixEnd_8149038 := by exact prefixLift 8149038
  have htrace : WordTrace (prefixWord ++ tailWord_8149038) baseStart_8149038 baseEnd_8149038 := by
    simpa [prefixWord, tailWord_8149038, baseEnd_8149038] using wordTrace_append hprefix tailTrace_8149038
  have hstable : (prefixWord ++ tailWord_8149038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149038).length < 2 ^ (prefixWord ++ tailWord_8149038).sum := by decide
  have hdescent : baseEnd_8149038 < baseStart_8149038 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149057 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 7]
def baseStart_8149057 : Nat := 118140960795 + 8149057 * 2 ^ 59
def prefixEnd_8149057 : Nat := 4983230072969 + 3 ^ 40 * 8149057 * 2
def baseEnd_8149057 : Nat := 464931457987336501190075

theorem tailTrace_8149057 : CollatzResearch.WordTrace tailWord_8149057 prefixEnd_8149057 464931457987336501190075 := by
  unfold tailWord_8149057
  simp only [CollatzResearch.WordTrace]
  refine ⟨297220526438365711977981425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198147017625577141318654283 297220526438365711977981425)
  ·
    refine ⟨222915394828774283983486069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297220526438365711977981425 222915394828774283983486069)
    ·
      refine ⟨20898318265197589123451819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222915394828774283983486069 20898318265197589123451819)
      ·
        refine ⟨31347477397796383685177729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20898318265197589123451819 31347477397796383685177729)
        ·
          refine ⟨23510608048347287763883297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31347477397796383685177729 23510608048347287763883297)
          ·
            refine ⟨17632956036260465822912473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23510608048347287763883297 17632956036260465822912473)
            ·
              refine ⟨13224717027195349367184355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17632956036260465822912473 13224717027195349367184355)
              ·
                refine ⟨19837075540793024050776533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13224717027195349367184355 19837075540793024050776533)
                ·
                  refine ⟨464931457987336501190075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19837075540793024050776533 464931457987336501190075)
                  ·
                    rfl

theorem cell23_8149057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 7].length) (baseStart_8149057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149057 prefixEnd_8149057 := by exact prefixLift 8149057
  have htrace : WordTrace (prefixWord ++ tailWord_8149057) baseStart_8149057 baseEnd_8149057 := by
    simpa [prefixWord, tailWord_8149057, baseEnd_8149057] using wordTrace_append hprefix tailTrace_8149057
  have hstable : (prefixWord ++ tailWord_8149057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149057).length < 2 ^ (prefixWord ++ tailWord_8149057).sum := by decide
  have hdescent : baseEnd_8149057 < baseStart_8149057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149070 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_8149070 : Nat := 118140960795 + 8149070 * 2 ^ 59
def prefixEnd_8149070 : Nat := 4983230072969 + 3 ^ 40 * 8149070 * 2
def baseEnd_8149070 : Nat := 1394796599044845653282705

theorem tailTrace_8149070 : CollatzResearch.WordTrace tailWord_8149070 prefixEnd_8149070 1394796599044845653282705 := by
  unfold tailWord_8149070
  simp only [CollatzResearch.WordTrace]
  refine ⟨37152625073414826899775583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198147333724879076798803109 37152625073414826899775583)
  ·
    refine ⟨55728937610122240349663375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37152625073414826899775583 55728937610122240349663375)
    ·
      refine ⟨83593406415183360524495063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55728937610122240349663375 83593406415183360524495063)
      ·
        refine ⟨125390109622775040786742595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83593406415183360524495063 125390109622775040786742595)
        ·
          refine ⟨188085164434162561180113893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125390109622775040786742595 188085164434162561180113893)
          ·
            refine ⟨35265968331405480221271355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188085164434162561180113893 35265968331405480221271355)
            ·
              refine ⟨52898952497108220331907033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35265968331405480221271355 52898952497108220331907033)
              ·
                refine ⟨39674214372831165248930275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52898952497108220331907033 39674214372831165248930275)
                ·
                  refine ⟨59511321559246747873395413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39674214372831165248930275 59511321559246747873395413)
                  ·
                    refine ⟨1394796599044845653282705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59511321559246747873395413 1394796599044845653282705)
                    ·
                      rfl

theorem cell23_8149070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_8149070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149070 prefixEnd_8149070 := by exact prefixLift 8149070
  have htrace : WordTrace (prefixWord ++ tailWord_8149070) baseStart_8149070 baseEnd_8149070 := by
    simpa [prefixWord, tailWord_8149070, baseEnd_8149070] using wordTrace_append hprefix tailTrace_8149070
  have hstable : (prefixWord ++ tailWord_8149070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149070).length < 2 ^ (prefixWord ++ tailWord_8149070).sum := by decide
  have hdescent : baseEnd_8149070 < baseStart_8149070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149167 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 3, 5, 2]
def baseStart_8149167 : Nat := 118140960795 + 8149167 * 2 ^ 59
def prefixEnd_8149167 : Nat := 4983230072969 + 3 ^ 40 * 8149167 * 2
def baseEnd_8149167 : Nat := 4184439604758023080335169

theorem tailTrace_8149167 : CollatzResearch.WordTrace tailWord_8149167 prefixEnd_8149167 4184439604758023080335169 := by
  unfold tailWord_8149167
  simp only [CollatzResearch.WordTrace]
  refine ⟨297224538467967200764485755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198149692311978133842990503 297224538467967200764485755)
  ·
    refine ⟨445836807701950801146728633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297224538467967200764485755 445836807701950801146728633)
    ·
      refine ⟨334377605776463100860046475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445836807701950801146728633 334377605776463100860046475)
      ·
        refine ⟨501566408664694651290069713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334377605776463100860046475 501566408664694651290069713)
        ·
          refine ⟨376174806498520988467552285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501566408664694651290069713 376174806498520988467552285)
          ·
            refine ⟨141065552436945370675332107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376174806498520988467552285 141065552436945370675332107)
            ·
              refine ⟨211598328655418056012998161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141065552436945370675332107 211598328655418056012998161)
              ·
                refine ⟨158698746491563542009748621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211598328655418056012998161 158698746491563542009748621)
                ·
                  refine ⟨59512029934336328253655733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158698746491563542009748621 59512029934336328253655733)
                  ·
                    refine ⟨5579252806344030773780225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59512029934336328253655733 5579252806344030773780225)
                    ·
                      refine ⟨4184439604758023080335169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579252806344030773780225 4184439604758023080335169)
                      ·
                        rfl

theorem cell23_8149167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 5, 2].length) (baseStart_8149167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149167 prefixEnd_8149167 := by exact prefixLift 8149167
  have htrace : WordTrace (prefixWord ++ tailWord_8149167) baseStart_8149167 baseEnd_8149167 := by
    simpa [prefixWord, tailWord_8149167, baseEnd_8149167] using wordTrace_append hprefix tailTrace_8149167
  have hstable : (prefixWord ++ tailWord_8149167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149167).length < 2 ^ (prefixWord ++ tailWord_8149167).sum := by decide
  have hdescent : baseEnd_8149167 < baseStart_8149167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149207 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 4, 4]
def baseStart_8149207 : Nat := 118140960795 + 8149207 * 2 ^ 59
def prefixEnd_8149207 : Nat := 4983230072969 + 3 ^ 40 * 8149207 * 2
def baseEnd_8149207 : Nat := 1394820047994734307944995

theorem tailTrace_8149207 : CollatzResearch.WordTrace tailWord_8149207 prefixEnd_8149207 1394820047994734307944995 := by
  unfold tailWord_8149207
  simp only [CollatzResearch.WordTrace]
  refine ⟨297225997387822287595941875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198150664925214858397294583 297225997387822287595941875)
  ·
    refine ⟨445838996081733431393912813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297225997387822287595941875 445838996081733431393912813)
    ·
      refine ⟨167189623530650036772717305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445838996081733431393912813 167189623530650036772717305)
      ·
        refine ⟨125392217647987527579537979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167189623530650036772717305 125392217647987527579537979)
        ·
          refine ⟨188088326471981291369306969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125392217647987527579537979 188088326471981291369306969)
          ·
            refine ⟨141066244853985968526980227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188088326471981291369306969 141066244853985968526980227)
            ·
              refine ⟨211599367280978952790470341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141066244853985968526980227 211599367280978952790470341)
              ·
                refine ⟨39674881365183553648213189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211599367280978952790470341 39674881365183553648213189)
                ·
                  refine ⟨7439040255971916309039973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39674881365183553648213189 7439040255971916309039973)
                  ·
                    refine ⟨1394820047994734307944995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7439040255971916309039973 1394820047994734307944995)
                    ·
                      rfl

theorem cell23_8149207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_8149207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149207 prefixEnd_8149207 := by exact prefixLift 8149207
  have htrace : WordTrace (prefixWord ++ tailWord_8149207) baseStart_8149207 baseEnd_8149207 := by
    simpa [prefixWord, tailWord_8149207, baseEnd_8149207] using wordTrace_append hprefix tailTrace_8149207
  have hstable : (prefixWord ++ tailWord_8149207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149207).length < 2 ^ (prefixWord ++ tailWord_8149207).sum := by decide
  have hdescent : baseEnd_8149207 < baseStart_8149207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149208 : List Nat := [2, 1, 2, 2, 4, 2, 2, 3, 1, 1, 3]
def baseStart_8149208 : Nat := 118140960795 + 8149208 * 2 ^ 59
def prefixEnd_8149208 : Nat := 4983230072969 + 3 ^ 40 * 8149208 * 2
def baseEnd_8149208 : Nat := 4184460657464857419922481

theorem tailTrace_8149208 : CollatzResearch.WordTrace tailWord_8149208 prefixEnd_8149208 4184460657464857419922481 := by
  unfold tailWord_8149208
  simp only [CollatzResearch.WordTrace]
  refine ⟨148613016930409332383364139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198150689240545776511152185 148613016930409332383364139)
  ·
    refine ⟨222919525395613998575046209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148613016930409332383364139 222919525395613998575046209)
    ·
      refine ⟨167189644046710498931284657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222919525395613998575046209 167189644046710498931284657)
      ·
        refine ⟨125392233035032874198463493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167189644046710498931284657 125392233035032874198463493)
        ·
          refine ⟨23511043694068663912211905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125392233035032874198463493 23511043694068663912211905)
          ·
            refine ⟨17633282770551497934158929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23511043694068663912211905 17633282770551497934158929)
            ·
              refine ⟨13224962077913623450619197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17633282770551497934158929 13224962077913623450619197)
              ·
                refine ⟨4959360779217608793982199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13224962077913623450619197 4959360779217608793982199)
                ·
                  refine ⟨7439041168826413190973299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959360779217608793982199 7439041168826413190973299)
                  ·
                    refine ⟨11158561753239619786459949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7439041168826413190973299 11158561753239619786459949)
                    ·
                      refine ⟨4184460657464857419922481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11158561753239619786459949 4184460657464857419922481)
                      ·
                        rfl

theorem cell23_8149208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_8149208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149208 prefixEnd_8149208 := by exact prefixLift 8149208
  have htrace : WordTrace (prefixWord ++ tailWord_8149208) baseStart_8149208 baseEnd_8149208 := by
    simpa [prefixWord, tailWord_8149208, baseEnd_8149208] using wordTrace_append hprefix tailTrace_8149208
  have hstable : (prefixWord ++ tailWord_8149208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149208).length < 2 ^ (prefixWord ++ tailWord_8149208).sum := by decide
  have hdescent : baseEnd_8149208 < baseStart_8149208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149217 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_8149217 : Nat := 118140960795 + 8149217 * 2 ^ 59
def prefixEnd_8149217 : Nat := 4983230072969 + 3 ^ 40 * 8149217 * 2
def baseEnd_8149217 : Nat := 4184465278790747884709939

theorem tailTrace_8149217 : CollatzResearch.WordTrace tailWord_8149217 prefixEnd_8149217 4184465278790747884709939 := by
  unfold tailWord_8149217
  simp only [CollatzResearch.WordTrace]
  refine ⟨297226362117786059303805905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198150908078524039535870603 297226362117786059303805905)
  ·
    refine ⟨222919771588339544477854429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297226362117786059303805905 222919771588339544477854429)
    ·
      refine ⟨83594914345627329179195411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222919771588339544477854429 83594914345627329179195411)
      ·
        refine ⟨125392371518440993768793117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83594914345627329179195411 125392371518440993768793117)
        ·
          refine ⟨47022139319415372663297419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125392371518440993768793117 47022139319415372663297419)
          ·
            refine ⟨70533208979123058994946129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47022139319415372663297419 70533208979123058994946129)
            ·
              refine ⟨52899906734342294246209597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70533208979123058994946129 52899906734342294246209597)
              ·
                refine ⟨19837465025378360342328599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52899906734342294246209597 19837465025378360342328599)
                ·
                  refine ⟨29756197538067540513492899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19837465025378360342328599 29756197538067540513492899)
                  ·
                    refine ⟨44634296307101310770239349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29756197538067540513492899 44634296307101310770239349)
                    ·
                      refine ⟨4184465278790747884709939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44634296307101310770239349 4184465278790747884709939)
                      ·
                        rfl

theorem cell23_8149217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_8149217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149217 prefixEnd_8149217 := by exact prefixLift 8149217
  have htrace : WordTrace (prefixWord ++ tailWord_8149217) baseStart_8149217 baseEnd_8149217 := by
    simpa [prefixWord, tailWord_8149217, baseEnd_8149217] using wordTrace_append hprefix tailTrace_8149217
  have hstable : (prefixWord ++ tailWord_8149217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149217).length < 2 ^ (prefixWord ++ tailWord_8149217).sum := by decide
  have hdescent : baseEnd_8149217 < baseStart_8149217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149224 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 4, 4]
def baseStart_8149224 : Nat := 118140960795 + 8149224 * 2 ^ 59
def prefixEnd_8149224 : Nat := 4983230072969 + 3 ^ 40 * 8149224 * 2
def baseEnd_8149224 : Nat := 1394822957718443119107469

theorem tailTrace_8149224 : CollatzResearch.WordTrace tailWord_8149224 prefixEnd_8149224 1394822957718443119107469 := by
  unfold tailWord_8149224
  simp only [CollatzResearch.WordTrace]
  refine ⟨148613308714380349749655363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198151078285840466332873817 148613308714380349749655363)
  ·
    refine ⟨222919963071570524624483045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148613308714380349749655363 222919963071570524624483045)
    ·
      refine ⟨41797493075919473367090571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222919963071570524624483045 41797493075919473367090571)
      ·
        refine ⟨62696239613879210050635857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41797493075919473367090571 62696239613879210050635857)
        ·
          refine ⟨47022179710409407537976893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62696239613879210050635857 47022179710409407537976893)
          ·
            refine ⟨17633317391403527826741335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47022179710409407537976893 17633317391403527826741335)
            ·
              refine ⟨26449976087105291740112003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17633317391403527826741335 26449976087105291740112003)
              ·
                refine ⟨39674964130657937610168005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26449976087105291740112003 39674964130657937610168005)
                ·
                  refine ⟨7439055774498363301906501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39674964130657937610168005 7439055774498363301906501)
                  ·
                    refine ⟨1394822957718443119107469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7439055774498363301906501 1394822957718443119107469)
                    ·
                      rfl

theorem cell23_8149224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_8149224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149224 prefixEnd_8149224 := by exact prefixLift 8149224
  have htrace : WordTrace (prefixWord ++ tailWord_8149224) baseStart_8149224 baseEnd_8149224 := by
    simpa [prefixWord, tailWord_8149224, baseEnd_8149224] using wordTrace_append hprefix tailTrace_8149224
  have hstable : (prefixWord ++ tailWord_8149224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149224).length < 2 ^ (prefixWord ++ tailWord_8149224).sum := by decide
  have hdescent : baseEnd_8149224 < baseStart_8149224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149231 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 3, 2, 2]
def baseStart_8149231 : Nat := 118140960795 + 8149231 * 2 ^ 59
def prefixEnd_8149231 : Nat := 4983230072969 + 3 ^ 40 * 8149231 * 2
def baseEnd_8149231 : Nat := 4184472467519910829934875

theorem tailTrace_8149231 : CollatzResearch.WordTrace tailWord_8149231 prefixEnd_8149231 4184472467519910829934875 := by
  unfold tailWord_8149231
  simp only [CollatzResearch.WordTrace]
  refine ⟨297226872739735339694815547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198151248493156893129877031 297226872739735339694815547)
  ·
    refine ⟨445840309109603009542223321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297226872739735339694815547 445840309109603009542223321)
    ·
      refine ⟨334380231832202257156667491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445840309109603009542223321 334380231832202257156667491)
      ·
        refine ⟨501570347748303385735001237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334380231832202257156667491 501570347748303385735001237)
        ·
          refine ⟨23511110050701721206328183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 501570347748303385735001237 23511110050701721206328183)
          ·
            refine ⟨35266665076052581809492275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23511110050701721206328183 35266665076052581809492275)
            ·
              refine ⟨52899997614078872714238413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35266665076052581809492275 52899997614078872714238413)
              ·
                refine ⟨19837499105279577267839405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52899997614078872714238413 19837499105279577267839405)
                ·
                  refine ⟨7439062164479841475439777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19837499105279577267839405 7439062164479841475439777)
                  ·
                    refine ⟨5579296623359881106579833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7439062164479841475439777 5579296623359881106579833)
                    ·
                      refine ⟨4184472467519910829934875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579296623359881106579833 4184472467519910829934875)
                      ·
                        rfl

theorem cell23_8149231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 2, 2].length) (baseStart_8149231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149231 prefixEnd_8149231 := by exact prefixLift 8149231
  have htrace : WordTrace (prefixWord ++ tailWord_8149231) baseStart_8149231 baseEnd_8149231 := by
    simpa [prefixWord, tailWord_8149231, baseEnd_8149231] using wordTrace_append hprefix tailTrace_8149231
  have hstable : (prefixWord ++ tailWord_8149231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149231).length < 2 ^ (prefixWord ++ tailWord_8149231).sum := by decide
  have hdescent : baseEnd_8149231 < baseStart_8149231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149234 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_8149234 : Nat := 118140960795 + 8149234 * 2 ^ 59
def prefixEnd_8149234 : Nat := 4983230072969 + 3 ^ 40 * 8149234 * 2
def baseEnd_8149234 : Nat := 4184474007961874318197361

theorem tailTrace_8149234 : CollatzResearch.WordTrace tailWord_8149234 prefixEnd_8149234 4184474007961874318197361 := by
  unfold tailWord_8149234
  simp only [CollatzResearch.WordTrace]
  refine ⟨74306745539681117801793689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198151321439149647471449837 74306745539681117801793689)
  ·
    refine ⟨55730059154760838351345267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74306745539681117801793689 55730059154760838351345267)
    ·
      refine ⟨83595088732141257527017901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55730059154760838351345267 83595088732141257527017901)
      ·
        refine ⟨31348158274552971572631713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83595088732141257527017901 31348158274552971572631713)
        ·
          refine ⟨23511118705914728679473785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31348158274552971572631713 23511118705914728679473785)
          ·
            refine ⟨17633339029436046509605339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23511118705914728679473785 17633339029436046509605339)
            ·
              refine ⟨26450008544154069764408009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17633339029436046509605339 26450008544154069764408009)
              ·
                refine ⟨19837506408115552323306007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26450008544154069764408009 19837506408115552323306007)
                ·
                  refine ⟨29756259612173328484959011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19837506408115552323306007 29756259612173328484959011)
                  ·
                    refine ⟨44634389418259992727438517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29756259612173328484959011 44634389418259992727438517)
                    ·
                      refine ⟨4184474007961874318197361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44634389418259992727438517 4184474007961874318197361)
                      ·
                        rfl

theorem cell23_8149234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_8149234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149234 prefixEnd_8149234 := by exact prefixLift 8149234
  have htrace : WordTrace (prefixWord ++ tailWord_8149234) baseStart_8149234 baseEnd_8149234 := by
    simpa [prefixWord, tailWord_8149234, baseEnd_8149234] using wordTrace_append hprefix tailTrace_8149234
  have hstable : (prefixWord ++ tailWord_8149234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149234).length < 2 ^ (prefixWord ++ tailWord_8149234).sum := by decide
  have hdescent : baseEnd_8149234 < baseStart_8149234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149244 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_8149244 : Nat := 118140960795 + 8149244 * 2 ^ 59
def prefixEnd_8149244 : Nat := 4983230072969 + 3 ^ 40 * 8149244 * 2
def baseEnd_8149244 : Nat := 4184479142768419279072315

theorem tailTrace_8149244 : CollatzResearch.WordTrace tailWord_8149244 prefixEnd_8149244 4184479142768419279072315 := by
  unfold tailWord_8149244
  simp only [CollatzResearch.WordTrace]
  refine ⟨148613673444344121457519393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198151564592458828610025857 148613673444344121457519393)
  ·
    refine ⟨111460255083258091093139545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148613673444344121457519393 111460255083258091093139545)
    ·
      refine ⟨83595191312443568319854659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111460255083258091093139545 83595191312443568319854659)
      ·
        refine ⟨125392786968665352479781989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83595191312443568319854659 125392786968665352479781989)
        ·
          refine ⟨23511147556624753589959123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125392786968665352479781989 23511147556624753589959123)
          ·
            refine ⟨35266721334937130384938685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23511147556624753589959123 35266721334937130384938685)
            ·
              refine ⟨13225020500601423894352007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35266721334937130384938685 13225020500601423894352007)
              ·
                refine ⟨19837530750902135841528011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13225020500601423894352007 19837530750902135841528011)
                ·
                  refine ⟨29756296126353203762292017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19837530750902135841528011 29756296126353203762292017)
                  ·
                    refine ⟨22317222094764902821719013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29756296126353203762292017 22317222094764902821719013)
                    ·
                      refine ⟨4184479142768419279072315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22317222094764902821719013 4184479142768419279072315)
                      ·
                        rfl

theorem cell23_8149244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_8149244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149244 prefixEnd_8149244 := by exact prefixLift 8149244
  have htrace : WordTrace (prefixWord ++ tailWord_8149244) baseStart_8149244 baseEnd_8149244 := by
    simpa [prefixWord, tailWord_8149244, baseEnd_8149244] using wordTrace_append hprefix tailTrace_8149244
  have hstable : (prefixWord ++ tailWord_8149244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149244).length < 2 ^ (prefixWord ++ tailWord_8149244).sum := by decide
  have hdescent : baseEnd_8149244 < baseStart_8149244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149265 : List Nat := [1, 2, 2, 1, 1, 7, 1, 3, 1, 2, 2]
def baseStart_8149265 : Nat := 118140960795 + 8149265 * 2 ^ 59
def prefixEnd_8149265 : Nat := 4983230072969 + 3 ^ 40 * 8149265 * 2
def baseEnd_8149265 : Nat := 4184489925862163696909719

theorem tailTrace_8149265 : CollatzResearch.WordTrace tailWord_8149265 prefixEnd_8149265 4184489925862163696909719 := by
  unfold tailWord_8149265
  simp only [CollatzResearch.WordTrace]
  refine ⟨297228112821612163501553249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198152075214408109001035499 297228112821612163501553249)
  ·
    refine ⟨222921084616209122626164937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297228112821612163501553249 222921084616209122626164937)
    ·
      refine ⟨167190813462156841969623703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222921084616209122626164937 167190813462156841969623703)
      ·
        refine ⟨250786220193235262954435555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167190813462156841969623703 250786220193235262954435555)
        ·
          refine ⟨376179330289852894431653333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250786220193235262954435555 376179330289852894431653333)
          ·
            refine ⟨8816703053668427213241875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 376179330289852894431653333 8816703053668427213241875)
            ·
              refine ⟨13225054580502640819862813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8816703053668427213241875 13225054580502640819862813)
              ·
                refine ⟨4959395467688490307448555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13225054580502640819862813 4959395467688490307448555)
                ·
                  refine ⟨7439093201532735461172833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959395467688490307448555 7439093201532735461172833)
                  ·
                    refine ⟨5579319901149551595879625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7439093201532735461172833 5579319901149551595879625)
                    ·
                      refine ⟨4184489925862163696909719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579319901149551595879625 4184489925862163696909719)
                      ·
                        rfl

theorem cell23_8149265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 2, 2].length) (baseStart_8149265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149265 prefixEnd_8149265 := by exact prefixLift 8149265
  have htrace : WordTrace (prefixWord ++ tailWord_8149265) baseStart_8149265 baseEnd_8149265 := by
    simpa [prefixWord, tailWord_8149265, baseEnd_8149265] using wordTrace_append hprefix tailTrace_8149265
  have hstable : (prefixWord ++ tailWord_8149265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149265).length < 2 ^ (prefixWord ++ tailWord_8149265).sum := by decide
  have hdescent : baseEnd_8149265 < baseStart_8149265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149282 : List Nat := [3, 3, 1, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_8149282 : Nat := 118140960795 + 8149282 * 2 ^ 59
def prefixEnd_8149282 : Nat := 4983230072969 + 3 ^ 40 * 8149282 * 2
def baseEnd_8149282 : Nat := 4184498655033290130397141

theorem tailTrace_8149282 : CollatzResearch.WordTrace tailWord_8149282 prefixEnd_8149282 4184498655033290130397141 := by
  unfold tailWord_8149282
  simp only [CollatzResearch.WordTrace]
  refine ⟨74307183215637643851230525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198152488575033716936614733 74307183215637643851230525)
  ·
    refine ⟨27865193705864116444211447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74307183215637643851230525 27865193705864116444211447)
    ·
      refine ⟨41797790558796174666317171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27865193705864116444211447 41797790558796174666317171)
      ·
        refine ⟨62696685838194261999475757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41797790558796174666317171 62696685838194261999475757)
        ·
          refine ⟨23511257189322848249803409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62696685838194261999475757 23511257189322848249803409)
          ·
            refine ⟨17633442891992136187352557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23511257189322848249803409 17633442891992136187352557)
            ·
              refine ⟨6612541084497051070257209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17633442891992136187352557 6612541084497051070257209)
              ·
                refine ⟨4959405813372788302692907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6612541084497051070257209 4959405813372788302692907)
                ·
                  refine ⟨7439108720059182454039361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959405813372788302692907 7439108720059182454039361)
                  ·
                    refine ⟨5579331540044386840529521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7439108720059182454039361 5579331540044386840529521)
                    ·
                      refine ⟨4184498655033290130397141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579331540044386840529521 4184498655033290130397141)
                      ·
                        rfl

theorem cell23_8149282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_8149282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149282 prefixEnd_8149282 := by exact prefixLift 8149282
  have htrace : WordTrace (prefixWord ++ tailWord_8149282) baseStart_8149282 baseEnd_8149282 := by
    simpa [prefixWord, tailWord_8149282, baseEnd_8149282] using wordTrace_append hprefix tailTrace_8149282
  have hstable : (prefixWord ++ tailWord_8149282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149282).length < 2 ^ (prefixWord ++ tailWord_8149282).sum := by decide
  have hdescent : baseEnd_8149282 < baseStart_8149282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149298 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_8149298 : Nat := 118140960795 + 8149298 * 2 ^ 59
def prefixEnd_8149298 : Nat := 4983230072969 + 3 ^ 40 * 8149298 * 2
def baseEnd_8149298 : Nat := 4184506870723762067797067

theorem tailTrace_8149298 : CollatzResearch.WordTrace tailWord_8149298 prefixEnd_8149298 4184506870723762067797067 := by
  unfold tailWord_8149298
  simp only [CollatzResearch.WordTrace]
  refine ⟨74307329107623152534376137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198152877620328406758336365 74307329107623152534376137)
  ·
    refine ⟨55730496830717364400782103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74307329107623152534376137 55730496830717364400782103)
    ·
      refine ⟨83595745246076046601173155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55730496830717364400782103 83595745246076046601173155)
      ·
        refine ⟨125393617869114069901759733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83595745246076046601173155 125393617869114069901759733)
        ·
          refine ⟨11755651675229444053289975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125393617869114069901759733 11755651675229444053289975)
          ·
            refine ⟨17633477512844166079934963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11755651675229444053289975 17633477512844166079934963)
            ·
              refine ⟨26450216269266249119902445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17633477512844166079934963 26450216269266249119902445)
              ·
                refine ⟨9918831100974843419963417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26450216269266249119902445 9918831100974843419963417)
                ·
                  refine ⟨7439123325731132564972563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9918831100974843419963417 7439123325731132564972563)
                  ·
                    refine ⟨11158684988596698847458845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7439123325731132564972563 11158684988596698847458845)
                    ·
                      refine ⟨4184506870723762067797067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11158684988596698847458845 4184506870723762067797067)
                      ·
                        rfl

theorem cell23_8149298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_8149298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149298 prefixEnd_8149298 := by exact prefixLift 8149298
  have htrace : WordTrace (prefixWord ++ tailWord_8149298) baseStart_8149298 baseEnd_8149298 := by
    simpa [prefixWord, tailWord_8149298, baseEnd_8149298] using wordTrace_append hprefix tailTrace_8149298
  have hstable : (prefixWord ++ tailWord_8149298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149298).length < 2 ^ (prefixWord ++ tailWord_8149298).sum := by decide
  have hdescent : baseEnd_8149298 < baseStart_8149298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149317 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_8149317 : Nat := 118140960795 + 8149317 * 2 ^ 59
def prefixEnd_8149317 : Nat := 4983230072969 + 3 ^ 40 * 8149317 * 2
def baseEnd_8149317 : Nat := 4184516626856197493459479

theorem tailTrace_8149317 : CollatzResearch.WordTrace tailWord_8149317 prefixEnd_8149317 4184516626856197493459479 := by
  unfold tailWord_8149317
  simp only [CollatzResearch.WordTrace]
  refine ⟨297230009417423776382446205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198153339611615850921630803 297230009417423776382446205)
  ·
    refine ⟨111461253531533916143417327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297230009417423776382446205 111461253531533916143417327)
    ·
      refine ⟨167191880297300874215125991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111461253531533916143417327 167191880297300874215125991)
      ·
        refine ⟨250787820445951311322688987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167191880297300874215125991 250787820445951311322688987)
        ·
          refine ⟨376181730668926966984033481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250787820445951311322688987 376181730668926966984033481)
          ·
            refine ⟨282136298001695225238025111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376181730668926966984033481 282136298001695225238025111)
            ·
              refine ⟨423204447002542837857037667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282136298001695225238025111 423204447002542837857037667)
              ·
                refine ⟨634806670503814256785556501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423204447002542837857037667 634806670503814256785556501)
                ·
                  refine ⟨29756562679866293286822961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 634806670503814256785556501 29756562679866293286822961)
                  ·
                    refine ⟨22317422009899719965117221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29756562679866293286822961 22317422009899719965117221)
                    ·
                      refine ⟨4184516626856197493459479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22317422009899719965117221 4184516626856197493459479)
                      ·
                        rfl

theorem cell23_8149317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_8149317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149317 prefixEnd_8149317 := by exact prefixLift 8149317
  have htrace : WordTrace (prefixWord ++ tailWord_8149317) baseStart_8149317 baseEnd_8149317 := by
    simpa [prefixWord, tailWord_8149317, baseEnd_8149317] using wordTrace_append hprefix tailTrace_8149317
  have hstable : (prefixWord ++ tailWord_8149317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149317).length < 2 ^ (prefixWord ++ tailWord_8149317).sum := by decide
  have hdescent : baseEnd_8149317 < baseStart_8149317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149367 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_8149367 : Nat := 118140960795 + 8149367 * 2 ^ 59
def prefixEnd_8149367 : Nat := 4983230072969 + 3 ^ 40 * 8149367 * 2
def baseEnd_8149367 : Nat := 4184542300888922297834249

theorem tailTrace_8149367 : CollatzResearch.WordTrace tailWord_8149367 prefixEnd_8149367 4184542300888922297834249 := by
  unfold tailWord_8149367
  simp only [CollatzResearch.WordTrace]
  refine ⟨297231833067242634921766355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198154555378161756614510903 297231833067242634921766355)
  ·
    refine ⟨445847749600863952382649533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297231833067242634921766355 445847749600863952382649533)
    ·
      refine ⟨167192906100323982143493575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445847749600863952382649533 167192906100323982143493575)
      ·
        refine ⟨250789359150485973215240363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167192906100323982143493575 250789359150485973215240363)
        ·
          refine ⟨376184038725728959822860545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250789359150485973215240363 376184038725728959822860545)
          ·
            refine ⟨282138029044296719867145409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376184038725728959822860545 282138029044296719867145409)
            ·
              refine ⟨211603521783222539900359057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282138029044296719867145409 211603521783222539900359057)
              ·
                refine ⟨158702641337416904925269293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211603521783222539900359057 158702641337416904925269293)
                ·
                  refine ⟨59513490501531339346975985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158702641337416904925269293 59513490501531339346975985)
                  ·
                    refine ⟨44635117876148504510231989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59513490501531339346975985 44635117876148504510231989)
                    ·
                      refine ⟨4184542300888922297834249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44635117876148504510231989 4184542300888922297834249)
                      ·
                        rfl

theorem cell23_8149367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_8149367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149367 prefixEnd_8149367 := by exact prefixLift 8149367
  have htrace : WordTrace (prefixWord ++ tailWord_8149367) baseStart_8149367 baseEnd_8149367 := by
    simpa [prefixWord, tailWord_8149367, baseEnd_8149367] using wordTrace_append hprefix tailTrace_8149367
  have hstable : (prefixWord ++ tailWord_8149367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149367).length < 2 ^ (prefixWord ++ tailWord_8149367).sum := by decide
  have hdescent : baseEnd_8149367 < baseStart_8149367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149411 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 2, 4, 2]
def baseStart_8149411 : Nat := 118140960795 + 8149411 * 2 ^ 59
def prefixEnd_8149411 : Nat := 4983230072969 + 3 ^ 40 * 8149411 * 2
def baseEnd_8149411 : Nat := 4184564894037720125684047

theorem tailTrace_8149411 : CollatzResearch.WordTrace tailWord_8149411 prefixEnd_8149411 4184564894037720125684047 := by
  unfold tailWord_8149411
  simp only [CollatzResearch.WordTrace]
  refine ⟨297233437879083230436368087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198155625252722153624245391 297233437879083230436368087)
  ·
    refine ⟨445850156818624845654552131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297233437879083230436368087 445850156818624845654552131)
    ·
      refine ⟨668775235227937268481828197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445850156818624845654552131 668775235227937268481828197)
      ·
        refine ⟨125395356605238237840342787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 668775235227937268481828197 125395356605238237840342787)
        ·
          refine ⟨188093034907857356760514181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125395356605238237840342787 188093034907857356760514181)
          ·
            refine ⟨35267444045223254392596409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188093034907857356760514181 35267444045223254392596409)
            ·
              refine ⟨26450583033917440794447307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35267444045223254392596409 26450583033917440794447307)
              ·
                refine ⟨39675874550876161191670961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26450583033917440794447307 39675874550876161191670961)
                ·
                  refine ⟨29756905913157120893753221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39675874550876161191670961 29756905913157120893753221)
                  ·
                    refine ⟨5579419858716960167578729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29756905913157120893753221 5579419858716960167578729)
                    ·
                      refine ⟨4184564894037720125684047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579419858716960167578729 4184564894037720125684047)
                      ·
                        rfl

theorem cell23_8149411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_8149411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149411 prefixEnd_8149411 := by exact prefixLift 8149411
  have htrace : WordTrace (prefixWord ++ tailWord_8149411) baseStart_8149411 baseEnd_8149411 := by
    simpa [prefixWord, tailWord_8149411, baseEnd_8149411] using wordTrace_append hprefix tailTrace_8149411
  have hstable : (prefixWord ++ tailWord_8149411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149411).length < 2 ^ (prefixWord ++ tailWord_8149411).sum := by decide
  have hdescent : baseEnd_8149411 < baseStart_8149411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149427 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 9]
def baseStart_8149427 : Nat := 118140960795 + 8149427 * 2 ^ 59
def prefixEnd_8149427 : Nat := 4983230072969 + 3 ^ 40 * 8149427 * 2
def baseEnd_8149427 : Nat := 4184573109728192063083973

theorem tailTrace_8149427 : CollatzResearch.WordTrace tailWord_8149427 prefixEnd_8149427 4184573109728192063083973 := by
  unfold tailWord_8149427
  simp only [CollatzResearch.WordTrace]
  refine ⟨297234021447025265168950535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198156014298016843445967023 297234021447025265168950535)
  ·
    refine ⟨445851032170537897753425803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297234021447025265168950535 445851032170537897753425803)
    ·
      refine ⟨668776548255806846630138705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445851032170537897753425803 668776548255806846630138705)
      ·
        refine ⟨501582411191855134972604029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668776548255806846630138705 501582411191855134972604029)
        ·
          refine ⟨188093404196945675614726511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501582411191855134972604029 188093404196945675614726511)
          ·
            refine ⟨282140106295418513422089767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188093404196945675614726511 282140106295418513422089767)
            ·
              refine ⟨423210159443127770133134651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282140106295418513422089767 423210159443127770133134651)
              ·
                refine ⟨634815239164691655199701977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423210159443127770133134651 634815239164691655199701977)
                ·
                  refine ⟨476111429373518741399776483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634815239164691655199701977 476111429373518741399776483)
                  ·
                    refine ⟨714167144060278112099664725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 476111429373518741399776483 714167144060278112099664725)
                    ·
                      refine ⟨4184573109728192063083973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 714167144060278112099664725 4184573109728192063083973)
                      ·
                        rfl

theorem cell23_8149427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_8149427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149427 prefixEnd_8149427 := by exact prefixLift 8149427
  have htrace : WordTrace (prefixWord ++ tailWord_8149427) baseStart_8149427 baseEnd_8149427 := by
    simpa [prefixWord, tailWord_8149427, baseEnd_8149427] using wordTrace_append hprefix tailTrace_8149427
  have hstable : (prefixWord ++ tailWord_8149427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149427).length < 2 ^ (prefixWord ++ tailWord_8149427).sum := by decide
  have hdescent : baseEnd_8149427 < baseStart_8149427 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149464 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 3, 5]
def baseStart_8149464 : Nat := 118140960795 + 8149464 * 2 ^ 59
def prefixEnd_8149464 : Nat := 4983230072969 + 3 ^ 40 * 8149464 * 2
def baseEnd_8149464 : Nat := 1394864036170802806107101

theorem tailTrace_8149464 : CollatzResearch.WordTrace tailWord_8149464 prefixEnd_8149464 1394864036170802806107101 := by
  unfold tailWord_8149464
  simp only [CollatzResearch.WordTrace]
  refine ⟨148617685473945610244023723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198156913965260813658698297 148617685473945610244023723)
  ·
    refine ⟨222926528210918415366035585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148617685473945610244023723 222926528210918415366035585)
    ·
      refine ⟨167194896158188811524526689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222926528210918415366035585 167194896158188811524526689)
      ·
        refine ⟨125396172118641608643395017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167194896158188811524526689 125396172118641608643395017)
        ·
          refine ⟨94047129088981206482546263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125396172118641608643395017 94047129088981206482546263)
          ·
            refine ⟨141070693633471809723819395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94047129088981206482546263 141070693633471809723819395)
            ·
              refine ⟨211606040450207714585729093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141070693633471809723819395 211606040450207714585729093)
              ·
                refine ⟨39676132584413946484824205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211606040450207714585729093 39676132584413946484824205)
                ·
                  refine ⟨14878549719155229931809077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39676132584413946484824205 14878549719155229931809077)
                  ·
                    refine ⟨1394864036170802806107101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14878549719155229931809077 1394864036170802806107101)
                    ·
                      rfl

theorem cell23_8149464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_8149464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149464 prefixEnd_8149464 := by exact prefixLift 8149464
  have htrace : WordTrace (prefixWord ++ tailWord_8149464) baseStart_8149464 baseEnd_8149464 := by
    simpa [prefixWord, tailWord_8149464, baseEnd_8149464] using wordTrace_append hprefix tailTrace_8149464
  have hstable : (prefixWord ++ tailWord_8149464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149464).length < 2 ^ (prefixWord ++ tailWord_8149464).sum := by decide
  have hdescent : baseEnd_8149464 < baseStart_8149464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149488 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 2, 3, 2]
def baseStart_8149488 : Nat := 118140960795 + 8149488 * 2 ^ 59
def prefixEnd_8149488 : Nat := 4983230072969 + 3 ^ 40 * 8149488 * 2
def baseEnd_8149488 : Nat := 4184604432048116324421193

theorem tailTrace_8149488 : CollatzResearch.WordTrace tailWord_8149488 prefixEnd_8149488 4184604432048116324421193 := by
  unfold tailWord_8149488
  simp only [CollatzResearch.WordTrace]
  refine ⟨148618123149902136293460559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198157497533202848391280745 148618123149902136293460559)
  ·
    refine ⟨222927184724853204440190839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148618123149902136293460559 222927184724853204440190839)
    ·
      refine ⟨334390777087279806660286259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222927184724853204440190839 334390777087279806660286259)
      ·
        refine ⟨501586165630919709990429389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334390777087279806660286259 501586165630919709990429389)
        ·
          refine ⟨188094812111594891246411021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501586165630919709990429389 188094812111594891246411021)
          ·
            refine ⟨70535554541848084217404133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188094812111594891246411021 70535554541848084217404133)
            ·
              refine ⟨13225416476596515790763275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70535554541848084217404133 13225416476596515790763275)
              ·
                refine ⟨19838124714894773686144913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13225416476596515790763275 19838124714894773686144913)
                ·
                  refine ⟨14878593536171080264608685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19838124714894773686144913 14878593536171080264608685)
                  ·
                    refine ⟨5579472576064155099228257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14878593536171080264608685 5579472576064155099228257)
                    ·
                      refine ⟨4184604432048116324421193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579472576064155099228257 4184604432048116324421193)
                      ·
                        rfl

theorem cell23_8149488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 3, 2].length) (baseStart_8149488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149488 prefixEnd_8149488 := by exact prefixLift 8149488
  have htrace : WordTrace (prefixWord ++ tailWord_8149488) baseStart_8149488 baseEnd_8149488 := by
    simpa [prefixWord, tailWord_8149488, baseEnd_8149488] using wordTrace_append hprefix tailTrace_8149488
  have hstable : (prefixWord ++ tailWord_8149488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149488).length < 2 ^ (prefixWord ++ tailWord_8149488).sum := by decide
  have hdescent : baseEnd_8149488 < baseStart_8149488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149506 : List Nat := [3, 4, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_8149506 : Nat := 118140960795 + 8149506 * 2 ^ 59
def prefixEnd_8149506 : Nat := 4983230072969 + 3 ^ 40 * 8149506 * 2
def baseEnd_8149506 : Nat := 1394871224899965751332037

theorem tailTrace_8149506 : CollatzResearch.WordTrace tailWord_8149506 prefixEnd_8149506 1394871224899965751332037 := by
  unfold tailWord_8149506
  simp only [CollatzResearch.WordTrace]
  refine ⟨74309225703434765415269093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198157935209159374440717581 74309225703434765415269093)
  ·
    refine ⟨13932979819394018515362955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74309225703434765415269093 13932979819394018515362955)
    ·
      refine ⟨20899469729091027773044433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13932979819394018515362955 20899469729091027773044433)
      ·
        refine ⟨15674602296818270829783325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20899469729091027773044433 15674602296818270829783325)
        ·
          refine ⟨5877975861306851561168747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15674602296818270829783325 5877975861306851561168747)
          ·
            refine ⟨8816963791960277341753121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877975861306851561168747 8816963791960277341753121)
            ·
              refine ⟨6612722843970208006314841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8816963791960277341753121 6612722843970208006314841)
              ·
                refine ⟨4959542132977656004736131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6612722843970208006314841 4959542132977656004736131)
                ·
                  refine ⟨7439313199466484007104197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959542132977656004736131 7439313199466484007104197)
                  ·
                    refine ⟨1394871224899965751332037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7439313199466484007104197 1394871224899965751332037)
                    ·
                      rfl

theorem cell23_8149506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_8149506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149506 prefixEnd_8149506 := by exact prefixLift 8149506
  have htrace : WordTrace (prefixWord ++ tailWord_8149506) baseStart_8149506 baseEnd_8149506 := by
    simpa [prefixWord, tailWord_8149506, baseEnd_8149506] using wordTrace_append hprefix tailTrace_8149506
  have hstable : (prefixWord ++ tailWord_8149506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149506).length < 2 ^ (prefixWord ++ tailWord_8149506).sum := by decide
  have hdescent : baseEnd_8149506 < baseStart_8149506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149528 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 2, 4]
def baseStart_8149528 : Nat := 118140960795 + 8149528 * 2 ^ 59
def prefixEnd_8149528 : Nat := 4983230072969 + 3 ^ 40 * 8149528 * 2
def baseEnd_8149528 : Nat := 1394874990424765389307003

theorem tailTrace_8149528 : CollatzResearch.WordTrace tailWord_8149528 prefixEnd_8149528 1394874990424765389307003 := by
  unfold tailWord_8149528
  simp only [CollatzResearch.WordTrace]
  refine ⟨148618852609829679709188619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198158470146439572945584825 148618852609829679709188619)
  ·
    refine ⟨222928278914744519563782929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148618852609829679709188619 222928278914744519563782929)
    ·
      refine ⟨167196209186058389672837197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222928278914744519563782929 167196209186058389672837197)
      ·
        refine ⟨62698578444771896127313949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167196209186058389672837197 62698578444771896127313949)
        ·
          refine ⟨23511966916789461047742731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62698578444771896127313949 23511966916789461047742731)
          ·
            refine ⟨35267950375184191571614097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23511966916789461047742731 35267950375184191571614097)
            ·
              refine ⟨26450962781388143678710573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35267950375184191571614097 26450962781388143678710573)
              ·
                refine ⟨9919111043020553879516465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26450962781388143678710573 9919111043020553879516465)
                ·
                  refine ⟨7439333282265415409637349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9919111043020553879516465 7439333282265415409637349)
                  ·
                    refine ⟨1394874990424765389307003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7439333282265415409637349 1394874990424765389307003)
                    ·
                      rfl

theorem cell23_8149528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_8149528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149528 prefixEnd_8149528 := by exact prefixLift 8149528
  have htrace : WordTrace (prefixWord ++ tailWord_8149528) baseStart_8149528 baseEnd_8149528 := by
    simpa [prefixWord, tailWord_8149528, baseEnd_8149528] using wordTrace_append hprefix tailTrace_8149528
  have hstable : (prefixWord ++ tailWord_8149528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149528).length < 2 ^ (prefixWord ++ tailWord_8149528).sum := by decide
  have hdescent : baseEnd_8149528 < baseStart_8149528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149538 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_8149538 : Nat := 118140960795 + 8149538 * 2 ^ 59
def prefixEnd_8149538 : Nat := 4983230072969 + 3 ^ 40 * 8149538 * 2
def baseEnd_8149538 : Nat := 4184630106080841128795963

theorem tailTrace_8149538 : CollatzResearch.WordTrace tailWord_8149538 prefixEnd_8149538 4184630106080841128795963 := by
  unfold tailWord_8149538
  simp only [CollatzResearch.WordTrace]
  refine ⟨74309517487405782781560317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198158713299748754084160845 74309517487405782781560317)
  ·
    refine ⟨27866069057777168543085119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74309517487405782781560317 27866069057777168543085119)
    ·
      refine ⟨41799103586665752814627679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27866069057777168543085119 41799103586665752814627679)
      ·
        refine ⟨62698655379998629221941519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41799103586665752814627679 62698655379998629221941519)
        ·
          refine ⟨94047983069997943832912279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62698655379998629221941519 94047983069997943832912279)
          ·
            refine ⟨141071974604996915749368419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94047983069997943832912279 141071974604996915749368419)
            ·
              refine ⟨211607961907495373624052629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141071974604996915749368419 211607961907495373624052629)
              ·
                refine ⟨9919123214413845638627467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211607961907495373624052629 9919123214413845638627467)
                ·
                  refine ⟨14878684821620768457941201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9919123214413845638627467 14878684821620768457941201)
                  ·
                    refine ⟨11159013616215576343455901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14878684821620768457941201 11159013616215576343455901)
                    ·
                      refine ⟨4184630106080841128795963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11159013616215576343455901 4184630106080841128795963)
                      ·
                        rfl

theorem cell23_8149538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_8149538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149538 prefixEnd_8149538 := by exact prefixLift 8149538
  have htrace : WordTrace (prefixWord ++ tailWord_8149538) baseStart_8149538 baseEnd_8149538 := by
    simpa [prefixWord, tailWord_8149538, baseEnd_8149538] using wordTrace_append hprefix tailTrace_8149538
  have hstable : (prefixWord ++ tailWord_8149538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149538).length < 2 ^ (prefixWord ++ tailWord_8149538).sum := by decide
  have hdescent : baseEnd_8149538 < baseStart_8149538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149572 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_8149572 : Nat := 118140960795 + 8149572 * 2 ^ 59
def prefixEnd_8149572 : Nat := 4983230072969 + 3 ^ 40 * 8149572 * 2
def baseEnd_8149572 : Nat := 4184647564423093995770807

theorem tailTrace_8149572 : CollatzResearch.WordTrace tailWord_8149572 prefixEnd_8149572 4184647564423093995770807 := by
  unfold tailWord_8149572
  simp only [CollatzResearch.WordTrace]
  refine ⟨148619655015749977466489485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198159540020999969955319313 148619655015749977466489485)
  ·
    refine ⟨55732370630906241549933557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148619655015749977466489485 55732370630906241549933557)
    ·
      refine ⟨5224909746647460145306271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55732370630906241549933557 5224909746647460145306271)
      ·
        refine ⟨7837364619971190217959407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5224909746647460145306271 7837364619971190217959407)
        ·
          refine ⟨11756046929956785326939111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837364619971190217959407 11756046929956785326939111)
          ·
            refine ⟨17634070394935177990408667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11756046929956785326939111 17634070394935177990408667)
            ·
              refine ⟨26451105592402766985613001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17634070394935177990408667 26451105592402766985613001)
              ·
                refine ⟨19838329194302075239209751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26451105592402766985613001 19838329194302075239209751)
                ·
                  refine ⟨29757493791453112858814627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19838329194302075239209751 29757493791453112858814627)
                  ·
                    refine ⟨44636240687179669288221941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29757493791453112858814627 44636240687179669288221941)
                    ·
                      refine ⟨4184647564423093995770807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44636240687179669288221941 4184647564423093995770807)
                      ·
                        rfl

theorem cell23_8149572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_8149572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149572 prefixEnd_8149572 := by exact prefixLift 8149572
  have htrace : WordTrace (prefixWord ++ tailWord_8149572) baseStart_8149572 baseEnd_8149572 := by
    simpa [prefixWord, tailWord_8149572, baseEnd_8149572] using wordTrace_append hprefix tailTrace_8149572
  have hstable : (prefixWord ++ tailWord_8149572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149572).length < 2 ^ (prefixWord ++ tailWord_8149572).sum := by decide
  have hdescent : baseEnd_8149572 < baseStart_8149572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149584 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 1, 8]
def baseStart_8149584 : Nat := 118140960795 + 8149584 * 2 ^ 59
def prefixEnd_8149584 : Nat := 4983230072969 + 3 ^ 40 * 8149584 * 2
def baseEnd_8149584 : Nat := 1394884575396982649606917

theorem tailTrace_8149584 : CollatzResearch.WordTrace tailWord_8149584 prefixEnd_8149584 1394884575396982649606917 := by
  unfold tailWord_8149584
  simp only [CollatzResearch.WordTrace]
  refine ⟨148619873853728240491207903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198159831804970987321610537 148619873853728240491207903)
  ·
    refine ⟨222929810780592360736811855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148619873853728240491207903 222929810780592360736811855)
    ·
      refine ⟨334394716170888541105217783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222929810780592360736811855 334394716170888541105217783)
      ·
        refine ⟨501592074256332811657826675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334394716170888541105217783 501592074256332811657826675)
        ·
          refine ⟨752388111384499217486740013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501592074256332811657826675 752388111384499217486740013)
          ·
            refine ⟨282145541769187206557527505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 752388111384499217486740013 282145541769187206557527505)
            ·
              refine ⟨211609156326890404918145629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282145541769187206557527505 211609156326890404918145629)
              ·
                refine ⟨79353433622583901844304611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211609156326890404918145629 79353433622583901844304611)
                ·
                  refine ⟨119030150433875852766456917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79353433622583901844304611 119030150433875852766456917)
                  ·
                    refine ⟨1394884575396982649606917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119030150433875852766456917 1394884575396982649606917)
                    ·
                      rfl

theorem cell23_8149584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_8149584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149584 prefixEnd_8149584 := by exact prefixLift 8149584
  have htrace : WordTrace (prefixWord ++ tailWord_8149584) baseStart_8149584 baseEnd_8149584 := by
    simpa [prefixWord, tailWord_8149584, baseEnd_8149584] using wordTrace_append hprefix tailTrace_8149584
  have hstable : (prefixWord ++ tailWord_8149584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149584).length < 2 ^ (prefixWord ++ tailWord_8149584).sum := by decide
  have hdescent : baseEnd_8149584 < baseStart_8149584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149625 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 4, 2, 2]
def baseStart_8149625 : Nat := 118140960795 + 8149625 * 2 ^ 59
def prefixEnd_8149625 : Nat := 4983230072969 + 3 ^ 40 * 8149625 * 2
def baseEnd_8149625 : Nat := 4184674778897782288408063

theorem tailTrace_8149625 : CollatzResearch.WordTrace tailWord_8149625 prefixEnd_8149625 4184674778897782288408063 := by
  unfold tailWord_8149625
  simp only [CollatzResearch.WordTrace]
  refine ⟨297241243100307944984658329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198160828733538629989772219 297241243100307944984658329)
  ·
    refine ⟨222930932325230958738493747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297241243100307944984658329 222930932325230958738493747)
    ·
      refine ⟨334396398487846438107740621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222930932325230958738493747 334396398487846438107740621)
      ·
        refine ⟨125398649432942414290402733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334396398487846438107740621 125398649432942414290402733)
        ·
          refine ⟨47024493537353405358901025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125398649432942414290402733 47024493537353405358901025)
          ·
            refine ⟨35268370153015054019175769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47024493537353405358901025 35268370153015054019175769)
            ·
              refine ⟨26451277614761290514381827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35268370153015054019175769 26451277614761290514381827)
              ·
                refine ⟨39676916422141935771572741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26451277614761290514381827 39676916422141935771572741)
                ·
                  refine ⟨7439421829151612957169889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39676916422141935771572741 7439421829151612957169889)
                  ·
                    refine ⟨5579566371863709717877417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7439421829151612957169889 5579566371863709717877417)
                    ·
                      refine ⟨4184674778897782288408063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579566371863709717877417 4184674778897782288408063)
                      ·
                        rfl

theorem cell23_8149625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_8149625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149625 prefixEnd_8149625 := by exact prefixLift 8149625
  have htrace : WordTrace (prefixWord ++ tailWord_8149625) baseStart_8149625 baseEnd_8149625 := by
    simpa [prefixWord, tailWord_8149625, baseEnd_8149625] using wordTrace_append hprefix tailTrace_8149625
  have hstable : (prefixWord ++ tailWord_8149625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149625).length < 2 ^ (prefixWord ++ tailWord_8149625).sum := by decide
  have hdescent : baseEnd_8149625 < baseStart_8149625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149641 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 3]
def baseStart_8149641 : Nat := 118140960795 + 8149641 * 2 ^ 59
def prefixEnd_8149641 : Nat := 4983230072969 + 3 ^ 40 * 8149641 * 2
def baseEnd_8149641 : Nat := 4184682994588254225807989

theorem tailTrace_8149641 : CollatzResearch.WordTrace tailWord_8149641 prefixEnd_8149641 4184682994588254225807989 := by
  unfold tailWord_8149641
  simp only [CollatzResearch.WordTrace]
  refine ⟨297241826668249979717240777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198161217778833319811493851 297241826668249979717240777)
  ·
    refine ⟨222931370001187484787930583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297241826668249979717240777 222931370001187484787930583)
    ·
      refine ⟨334397055001781227181895875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222931370001187484787930583 334397055001781227181895875)
      ·
        refine ⟨501595582502671840772843813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334397055001781227181895875 501595582502671840772843813)
        ·
          refine ⟨94049171719250970144908215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501595582502671840772843813 94049171719250970144908215)
          ·
            refine ⟨141073757578876455217362323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94049171719250970144908215 141073757578876455217362323)
            ·
              refine ⟨211610636368314682826043485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141073757578876455217362323 211610636368314682826043485)
              ·
                refine ⟨79353988638118006059766307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211610636368314682826043485 79353988638118006059766307)
                ·
                  refine ⟨119030982957177009089649461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79353988638118006059766307 119030982957177009089649461)
                  ·
                    refine ⟨11159154652235344602154637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119030982957177009089649461 11159154652235344602154637)
                    ·
                      refine ⟨4184682994588254225807989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11159154652235344602154637 4184682994588254225807989)
                      ·
                        rfl

theorem cell23_8149641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_8149641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149641 prefixEnd_8149641 := by exact prefixLift 8149641
  have htrace : WordTrace (prefixWord ++ tailWord_8149641) baseStart_8149641 baseEnd_8149641 := by
    simpa [prefixWord, tailWord_8149641, baseEnd_8149641] using wordTrace_append hprefix tailTrace_8149641
  have hstable : (prefixWord ++ tailWord_8149641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149641).length < 2 ^ (prefixWord ++ tailWord_8149641).sum := by decide
  have hdescent : baseEnd_8149641 < baseStart_8149641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149661 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_8149661 : Nat := 118140960795 + 8149661 * 2 ^ 59
def prefixEnd_8149661 : Nat := 4983230072969 + 3 ^ 40 * 8149661 * 2
def baseEnd_8149661 : Nat := 1394897754733781382519299

theorem tailTrace_8149661 : CollatzResearch.WordTrace tailWord_8149661 prefixEnd_8149661 1394897754733781382519299 := by
  unfold tailWord_8149661
  simp only [CollatzResearch.WordTrace]
  refine ⟨297242556128177523132968837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198161704085451682088645891 297242556128177523132968837)
  ·
    refine ⟨55732979274033285587431657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297242556128177523132968837 55732979274033285587431657)
    ·
      refine ⟨41799734455524964190573743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55732979274033285587431657 41799734455524964190573743)
      ·
        refine ⟨62699601683287446285860615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41799734455524964190573743 62699601683287446285860615)
        ·
          refine ⟨94049402524931169428790923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62699601683287446285860615 94049402524931169428790923)
          ·
            refine ⟨141074103787396754143186385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94049402524931169428790923 141074103787396754143186385)
            ·
              refine ⟨105805577840547565607389789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141074103787396754143186385 105805577840547565607389789)
              ·
                refine ⟨39677091690205337102771171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105805577840547565607389789 39677091690205337102771171)
                ·
                  refine ⟨59515637535308005654156757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39677091690205337102771171 59515637535308005654156757)
                  ·
                    refine ⟨1394897754733781382519299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59515637535308005654156757 1394897754733781382519299)
                    ·
                      rfl

theorem cell23_8149661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_8149661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149661 prefixEnd_8149661 := by exact prefixLift 8149661
  have htrace : WordTrace (prefixWord ++ tailWord_8149661) baseStart_8149661 baseEnd_8149661 := by
    simpa [prefixWord, tailWord_8149661, baseEnd_8149661] using wordTrace_append hprefix tailTrace_8149661
  have hstable : (prefixWord ++ tailWord_8149661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149661).length < 2 ^ (prefixWord ++ tailWord_8149661).sum := by decide
  have hdescent : baseEnd_8149661 < baseStart_8149661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149685 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_8149685 : Nat := 118140960795 + 8149685 * 2 ^ 59
def prefixEnd_8149685 : Nat := 4983230072969 + 3 ^ 40 * 8149685 * 2
def baseEnd_8149685 : Nat := 4184705587737052053657787

theorem tailTrace_8149685 : CollatzResearch.WordTrace tailWord_8149685 prefixEnd_8149685 4184705587737052053657787 := by
  unfold tailWord_8149685
  simp only [CollatzResearch.WordTrace]
  refine ⟨297243431480090575231842509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198162287653393716821228339 297243431480090575231842509)
  ·
    refine ⟨111466286805033965711940941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297243431480090575231842509 111466286805033965711940941)
    ·
      refine ⟨41799857551887737141977853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111466286805033965711940941 41799857551887737141977853)
      ·
        refine ⟨15674946581957901428241695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41799857551887737141977853 15674946581957901428241695)
        ·
          refine ⟨23512419872936852142362543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15674946581957901428241695 23512419872936852142362543)
          ·
            refine ⟨35268629809405278213543815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23512419872936852142362543 35268629809405278213543815)
            ·
              refine ⟨52902944714107917320315723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35268629809405278213543815 52902944714107917320315723)
              ·
                refine ⟨79354417071161875980473585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52902944714107917320315723 79354417071161875980473585)
                ·
                  refine ⟨59515812803371406985355189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79354417071161875980473585 59515812803371406985355189)
                  ·
                    refine ⟨5579607450316069404877049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59515812803371406985355189 5579607450316069404877049)
                    ·
                      refine ⟨4184705587737052053657787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579607450316069404877049 4184705587737052053657787)
                      ·
                        rfl

theorem cell23_8149685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_8149685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149685 prefixEnd_8149685 := by exact prefixLift 8149685
  have htrace : WordTrace (prefixWord ++ tailWord_8149685) baseStart_8149685 baseEnd_8149685 := by
    simpa [prefixWord, tailWord_8149685, baseEnd_8149685] using wordTrace_append hprefix tailTrace_8149685
  have hstable : (prefixWord ++ tailWord_8149685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149685).length < 2 ^ (prefixWord ++ tailWord_8149685).sum := by decide
  have hdescent : baseEnd_8149685 < baseStart_8149685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149721 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 8]
def baseStart_8149721 : Nat := 118140960795 + 8149721 * 2 ^ 59
def prefixEnd_8149721 : Nat := 4983230072969 + 3 ^ 40 * 8149721 * 2
def baseEnd_8149721 : Nat := 464969341448957101423069

theorem tailTrace_8149721 : CollatzResearch.WordTrace tailWord_8149721 prefixEnd_8149721 464969341448957101423069 := by
  unfold tailWord_8149721
  simp only [CollatzResearch.WordTrace]
  refine ⟨297244744507960153380153017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198163163005306768920102011 297244744507960153380153017)
  ·
    refine ⟨222933558380970115035114763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297244744507960153380153017 222933558380970115035114763)
    ·
      refine ⟨334400337571455172552672145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222933558380970115035114763 334400337571455172552672145)
      ·
        refine ⟨250800253178591379414504109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334400337571455172552672145 250800253178591379414504109)
        ·
          refine ⟨94050094941971767280439041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250800253178591379414504109 94050094941971767280439041)
          ·
            refine ⟨70537571206478825460329281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94050094941971767280439041 70537571206478825460329281)
            ·
              refine ⟨52903178404859119095246961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70537571206478825460329281 52903178404859119095246961)
              ·
                refine ⟨39677383803644339321435221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52903178404859119095246961 39677383803644339321435221)
                ·
                  refine ⟨464969341448957101423069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39677383803644339321435221 464969341448957101423069)
                  ·
                    rfl

theorem cell23_8149721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 8].length) (baseStart_8149721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149721 prefixEnd_8149721 := by exact prefixLift 8149721
  have htrace : WordTrace (prefixWord ++ tailWord_8149721) baseStart_8149721 baseEnd_8149721 := by
    simpa [prefixWord, tailWord_8149721, baseEnd_8149721] using wordTrace_append hprefix tailTrace_8149721
  have hstable : (prefixWord ++ tailWord_8149721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149721).length < 2 ^ (prefixWord ++ tailWord_8149721).sum := by decide
  have hdescent : baseEnd_8149721 < baseStart_8149721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149742 : List Nat := [4, 1, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_8149742 : Nat := 118140960795 + 8149742 * 2 ^ 59
def prefixEnd_8149742 : Nat := 4983230072969 + 3 ^ 40 * 8149742 * 2
def baseEnd_8149742 : Nat := 1394911618711452776881675

theorem tailTrace_8149742 : CollatzResearch.WordTrace tailWord_8149742 prefixEnd_8149742 1394911618711452776881675 := by
  unfold tailWord_8149742
  simp only [CollatzResearch.WordTrace]
  refine ⟨37155688805110509245833435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198163673627256049311111653 37155688805110509245833435)
  ·
    refine ⟨55733533207665763868750153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37155688805110509245833435 55733533207665763868750153)
    ·
      refine ⟨41800149905749322901562615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55733533207665763868750153 41800149905749322901562615)
      ·
        refine ⟨62700224858623984352343923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41800149905749322901562615 62700224858623984352343923)
        ·
          refine ⟨94050337287935976528515885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62700224858623984352343923 94050337287935976528515885)
          ·
            refine ⟨35268876482975991198193457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94050337287935976528515885 35268876482975991198193457)
            ·
              refine ⟨26451657362231993398645093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35268876482975991198193457 26451657362231993398645093)
              ·
                refine ⟨4959685755418498762245955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26451657362231993398645093 4959685755418498762245955)
                ·
                  refine ⟨7439528633127748143368933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959685755418498762245955 7439528633127748143368933)
                  ·
                    refine ⟨1394911618711452776881675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7439528633127748143368933 1394911618711452776881675)
                    ·
                      rfl

theorem cell23_8149742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_8149742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149742 prefixEnd_8149742 := by exact prefixLift 8149742
  have htrace : WordTrace (prefixWord ++ tailWord_8149742) baseStart_8149742 baseEnd_8149742 := by
    simpa [prefixWord, tailWord_8149742, baseEnd_8149742] using wordTrace_append hprefix tailTrace_8149742
  have hstable : (prefixWord ++ tailWord_8149742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149742).length < 2 ^ (prefixWord ++ tailWord_8149742).sum := by decide
  have hdescent : baseEnd_8149742 < baseStart_8149742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149775 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 2, 3, 2]
def baseStart_8149775 : Nat := 118140960795 + 8149775 * 2 ^ 59
def prefixEnd_8149775 : Nat := 4983230072969 + 3 ^ 40 * 8149775 * 2
def baseEnd_8149775 : Nat := 4184751800995956701532373

theorem tailTrace_8149775 : CollatzResearch.WordTrace tailWord_8149775 prefixEnd_8149775 4184751800995956701532373 := by
  unfold tailWord_8149775
  simp only [CollatzResearch.WordTrace]
  refine ⟨297246714049764520602618779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198164476033176347068412519 297246714049764520602618779)
  ·
    refine ⟨445870071074646780903928169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297246714049764520602618779 445870071074646780903928169)
    ·
      refine ⟨334402553305985085677946127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445870071074646780903928169 334402553305985085677946127)
      ·
        refine ⟨501603829958977628516919191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334402553305985085677946127 501603829958977628516919191)
        ·
          refine ⟨752405744938466442775378787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501603829958977628516919191 752405744938466442775378787)
          ·
            refine ⟨1128608617407699664163068181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752405744938466442775378787 1128608617407699664163068181)
            ·
              refine ⟨52903528940985921757643821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1128608617407699664163068181 52903528940985921757643821)
              ·
                refine ⟨19838823352869720659116433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52903528940985921757643821 19838823352869720659116433)
                ·
                  refine ⟨14879117514652290494337325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19838823352869720659116433 14879117514652290494337325)
                  ·
                    refine ⟨5579669067994608935376497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14879117514652290494337325 5579669067994608935376497)
                    ·
                      refine ⟨4184751800995956701532373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579669067994608935376497 4184751800995956701532373)
                      ·
                        rfl

theorem cell23_8149775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 3, 2].length) (baseStart_8149775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149775 prefixEnd_8149775 := by exact prefixLift 8149775
  have htrace : WordTrace (prefixWord ++ tailWord_8149775) baseStart_8149775 baseEnd_8149775 := by
    simpa [prefixWord, tailWord_8149775, baseEnd_8149775] using wordTrace_append hprefix tailTrace_8149775
  have hstable : (prefixWord ++ tailWord_8149775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149775).length < 2 ^ (prefixWord ++ tailWord_8149775).sum := by decide
  have hdescent : baseEnd_8149775 < baseStart_8149775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149792 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 2, 3, 2]
def baseStart_8149792 : Nat := 118140960795 + 8149792 * 2 ^ 59
def prefixEnd_8149792 : Nat := 4983230072969 + 3 ^ 40 * 8149792 * 2
def baseEnd_8149792 : Nat := 4184760530167083135019795

theorem tailTrace_8149792 : CollatzResearch.WordTrace tailWord_8149792 prefixEnd_8149792 4184760530167083135019795 := by
  unfold tailWord_8149792
  simp only [CollatzResearch.WordTrace]
  refine ⟨148623667045351466252993815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198164889393801955003991753 148623667045351466252993815)
  ·
    refine ⟨222935500568027199379490723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148623667045351466252993815 222935500568027199379490723)
    ·
      refine ⟨334403250852040799069236085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222935500568027199379490723 334403250852040799069236085)
      ·
        refine ⟨31350304767378824912740883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334403250852040799069236085 31350304767378824912740883)
        ·
          refine ⟨47025457151068237369111325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31350304767378824912740883 47025457151068237369111325)
          ·
            refine ⟨17634546431650589013416747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47025457151068237369111325 17634546431650589013416747)
            ·
              refine ⟨26451819647475883520125121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17634546431650589013416747 26451819647475883520125121)
              ·
                refine ⟨19838864735606912640093841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26451819647475883520125121 19838864735606912640093841)
                ·
                  refine ⟨14879148551705184480070381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19838864735606912640093841 14879148551705184480070381)
                  ·
                    refine ⟨5579680706889444180026393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14879148551705184480070381 5579680706889444180026393)
                    ·
                      refine ⟨4184760530167083135019795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579680706889444180026393 4184760530167083135019795)
                      ·
                        rfl

theorem cell23_8149792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_8149792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149792 prefixEnd_8149792 := by exact prefixLift 8149792
  have htrace : WordTrace (prefixWord ++ tailWord_8149792) baseStart_8149792 baseEnd_8149792 := by
    simpa [prefixWord, tailWord_8149792, baseEnd_8149792] using wordTrace_append hprefix tailTrace_8149792
  have hstable : (prefixWord ++ tailWord_8149792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149792).length < 2 ^ (prefixWord ++ tailWord_8149792).sum := by decide
  have hdescent : baseEnd_8149792 < baseStart_8149792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149815 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 2, 4]
def baseStart_8149815 : Nat := 118140960795 + 8149815 * 2 ^ 59
def prefixEnd_8149815 : Nat := 4983230072969 + 3 ^ 40 * 8149815 * 2
def baseEnd_8149815 : Nat := 1394924113407378848344063

theorem tailTrace_8149815 : CollatzResearch.WordTrace tailWord_8149815 prefixEnd_8149815 1394924113407378848344063 := by
  unfold tailWord_8149815
  simp only [CollatzResearch.WordTrace]
  refine ⟨297248172969619607434074899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198165448646413071622716599 297248172969619607434074899)
  ·
    refine ⟨445872259454429411151112349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297248172969619607434074899 445872259454429411151112349)
    ·
      refine ⟨167202097295411029181667131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445872259454429411151112349 167202097295411029181667131)
      ·
        refine ⟨250803145943116543772500697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167202097295411029181667131 250803145943116543772500697)
        ·
          refine ⟨188102359457337407829375523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250803145943116543772500697 188102359457337407829375523)
          ·
            refine ⟨282153539186006111744063285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188102359457337407829375523 282153539186006111744063285)
            ·
              refine ⟨26451894298688072976005933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282153539186006111744063285 26451894298688072976005933)
              ·
                refine ⟨9919460362008027366002225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26451894298688072976005933 9919460362008027366002225)
                ·
                  refine ⟨7439595271506020524501669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9919460362008027366002225 7439595271506020524501669)
                  ·
                    refine ⟨1394924113407378848344063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7439595271506020524501669 1394924113407378848344063)
                    ·
                      rfl

theorem cell23_8149815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_8149815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149815 prefixEnd_8149815 := by exact prefixLift 8149815
  have htrace : WordTrace (prefixWord ++ tailWord_8149815) baseStart_8149815 baseEnd_8149815 := by
    simpa [prefixWord, tailWord_8149815, baseEnd_8149815] using wordTrace_append hprefix tailTrace_8149815
  have hstable : (prefixWord ++ tailWord_8149815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149815).length < 2 ^ (prefixWord ++ tailWord_8149815).sum := by decide
  have hdescent : baseEnd_8149815 < baseStart_8149815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149822 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_8149822 : Nat := 118140960795 + 8149822 * 2 ^ 59
def prefixEnd_8149822 : Nat := 4983230072969 + 3 ^ 40 * 8149822 * 2
def baseEnd_8149822 : Nat := 4184775934586718017644657

theorem tailTrace_8149822 : CollatzResearch.WordTrace tailWord_8149822 prefixEnd_8149822 4184775934586718017644657 := by
  unfold tailWord_8149822
  simp only [CollatzResearch.WordTrace]
  refine ⟨37156053535074280953697465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198165618853729498419719813 37156053535074280953697465)
  ·
    refine ⟨27867040151305710715273099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37156053535074280953697465 27867040151305710715273099)
    ·
      refine ⟨41800560226958566072909649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27867040151305710715273099 41800560226958566072909649)
      ·
        refine ⟨31350420170218924554682237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41800560226958566072909649 31350420170218924554682237)
        ·
          refine ⟨11756407563832096708005839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31350420170218924554682237 11756407563832096708005839)
          ·
            refine ⟨17634611345748145062008759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11756407563832096708005839 17634611345748145062008759)
            ·
              refine ⟨26451917018622217593013139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17634611345748145062008759 26451917018622217593013139)
              ·
                refine ⟨39677875527933326389519709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26451917018622217593013139 39677875527933326389519709)
                ·
                  refine ⟨14879203322974997396069891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39677875527933326389519709 14879203322974997396069891)
                  ·
                    refine ⟨22318804984462496094104837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14879203322974997396069891 22318804984462496094104837)
                    ·
                      refine ⟨4184775934586718017644657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22318804984462496094104837 4184775934586718017644657)
                      ·
                        rfl

theorem cell23_8149822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_8149822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149822 prefixEnd_8149822 := by exact prefixLift 8149822
  have htrace : WordTrace (prefixWord ++ tailWord_8149822) baseStart_8149822 baseEnd_8149822 := by
    simpa [prefixWord, tailWord_8149822, baseEnd_8149822] using wordTrace_append hprefix tailTrace_8149822
  have hstable : (prefixWord ++ tailWord_8149822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149822).length < 2 ^ (prefixWord ++ tailWord_8149822).sum := by decide
  have hdescent : baseEnd_8149822 < baseStart_8149822 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149872 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 2, 1, 3]
def baseStart_8149872 : Nat := 118140960795 + 8149872 * 2 ^ 59
def prefixEnd_8149872 : Nat := 4983230072969 + 3 ^ 40 * 8149872 * 2
def baseEnd_8149872 : Nat := 4184801608619442822019427

theorem tailTrace_8149872 : CollatzResearch.WordTrace tailWord_8149872 prefixEnd_8149872 4184801608619442822019427 := by
  unfold tailWord_8149872
  simp only [CollatzResearch.WordTrace]
  refine ⟨148625125965206553084449935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198166834620275404112599913 148625125965206553084449935)
  ·
    refine ⟨222937688947809829626674903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148625125965206553084449935 222937688947809829626674903)
    ·
      refine ⟨334406533421714744440012355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222937688947809829626674903 334406533421714744440012355)
      ·
        refine ⟨501609800132572116660018533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334406533421714744440012355 501609800132572116660018533)
        ·
          refine ⟨94051837524857271873753475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501609800132572116660018533 94051837524857271873753475)
          ·
            refine ⟨141077756287285907810630213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94051837524857271873753475 141077756287285907810630213)
            ·
              refine ⟨26452079303866107714493165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141077756287285907810630213 26452079303866107714493165)
              ·
                refine ⟨9919529738949790392934937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26452079303866107714493165 9919529738949790392934937)
                ·
                  refine ⟨7439647304212342794701203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9919529738949790392934937 7439647304212342794701203)
                  ·
                    refine ⟨11159470956318514192051805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7439647304212342794701203 11159470956318514192051805)
                    ·
                      refine ⟨4184801608619442822019427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11159470956318514192051805 4184801608619442822019427)
                      ·
                        rfl

theorem cell23_8149872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 1, 3].length) (baseStart_8149872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149872 prefixEnd_8149872 := by exact prefixLift 8149872
  have htrace : WordTrace (prefixWord ++ tailWord_8149872) baseStart_8149872 baseEnd_8149872 := by
    simpa [prefixWord, tailWord_8149872, baseEnd_8149872] using wordTrace_append hprefix tailTrace_8149872
  have hstable : (prefixWord ++ tailWord_8149872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149872).length < 2 ^ (prefixWord ++ tailWord_8149872).sum := by decide
  have hdescent : baseEnd_8149872 < baseStart_8149872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149882 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2]
def baseStart_8149882 : Nat := 118140960795 + 8149882 * 2 ^ 59
def prefixEnd_8149882 : Nat := 4983230072969 + 3 ^ 40 * 8149882 * 2
def baseEnd_8149882 : Nat := 4184806743425987782894381

theorem tailTrace_8149882 : CollatzResearch.WordTrace tailWord_8149882 prefixEnd_8149882 4184806743425987782894381 := by
  unfold tailWord_8149882
  simp only [CollatzResearch.WordTrace]
  refine ⟨74312654165094219469190975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198167077773584585251175933 74312654165094219469190975)
  ·
    refine ⟨111468981247641329203786463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74312654165094219469190975 111468981247641329203786463)
    ·
      refine ⟨167203471871461993805679695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111468981247641329203786463 167203471871461993805679695)
      ·
        refine ⟨250805207807192990708519543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167203471871461993805679695 250805207807192990708519543)
        ·
          refine ⟨376207811710789486062779315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250805207807192990708519543 376207811710789486062779315)
          ·
            refine ⟨564311717566184229094168973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376207811710789486062779315 564311717566184229094168973)
            ·
              refine ⟨211616894087319085910313365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 564311717566184229094168973 211616894087319085910313365)
              ·
                refine ⟨9919541910343082152045939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211616894087319085910313365 9919541910343082152045939)
                ·
                  refine ⟨14879312865514623228068909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9919541910343082152045939 14879312865514623228068909)
                  ·
                    refine ⟨5579742324567983710525841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14879312865514623228068909 5579742324567983710525841)
                    ·
                      refine ⟨4184806743425987782894381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579742324567983710525841 4184806743425987782894381)
                      ·
                        rfl

theorem cell23_8149882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_8149882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149882 prefixEnd_8149882 := by exact prefixLift 8149882
  have htrace : WordTrace (prefixWord ++ tailWord_8149882) baseStart_8149882 baseEnd_8149882 := by
    simpa [prefixWord, tailWord_8149882, baseEnd_8149882] using wordTrace_append hprefix tailTrace_8149882
  have hstable : (prefixWord ++ tailWord_8149882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149882).length < 2 ^ (prefixWord ++ tailWord_8149882).sum := by decide
  have hdescent : baseEnd_8149882 < baseStart_8149882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149890 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_8149890 : Nat := 118140960795 + 8149890 * 2 ^ 59
def prefixEnd_8149890 : Nat := 4983230072969 + 3 ^ 40 * 8149890 * 2
def baseEnd_8149890 : Nat := 4184810851271223751594345

theorem tailTrace_8149890 : CollatzResearch.WordTrace tailWord_8149890 prefixEnd_8149890 4184810851271223751594345 := by
  unfold tailWord_8149890
  simp only [CollatzResearch.WordTrace]
  refine ⟨74312727111086973810763781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198167272296231930162036749 74312727111086973810763781)
  ·
    refine ⟨13933636333328807589518209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74312727111086973810763781 13933636333328807589518209)
    ·
      refine ⟨10450227249996605692138657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13933636333328807589518209 10450227249996605692138657)
      ·
        refine ⟨7837670437497454269103993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10450227249996605692138657 7837670437497454269103993)
        ·
          refine ⟨5878252828123090701827995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7837670437497454269103993 5878252828123090701827995)
          ·
            refine ⟨8817379242184636052741993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5878252828123090701827995 8817379242184636052741993)
            ·
              refine ⟨6613034431638477039556495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8817379242184636052741993 6613034431638477039556495)
              ·
                refine ⟨9919551647457715559334743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613034431638477039556495 9919551647457715559334743)
                ·
                  refine ⟨14879327471186573339002115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9919551647457715559334743 14879327471186573339002115)
                  ·
                    refine ⟨22318991206779860008503173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14879327471186573339002115 22318991206779860008503173)
                    ·
                      refine ⟨4184810851271223751594345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22318991206779860008503173 4184810851271223751594345)
                      ·
                        rfl

theorem cell23_8149890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_8149890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149890 prefixEnd_8149890 := by exact prefixLift 8149890
  have htrace : WordTrace (prefixWord ++ tailWord_8149890) baseStart_8149890 baseEnd_8149890 := by
    simpa [prefixWord, tailWord_8149890, baseEnd_8149890] using wordTrace_append hprefix tailTrace_8149890
  have hstable : (prefixWord ++ tailWord_8149890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149890).length < 2 ^ (prefixWord ++ tailWord_8149890).sum := by decide
  have hdescent : baseEnd_8149890 < baseStart_8149890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149899 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 1, 3, 2]
def baseStart_8149899 : Nat := 118140960795 + 8149899 * 2 ^ 59
def prefixEnd_8149899 : Nat := 4983230072969 + 3 ^ 40 * 8149899 * 2
def baseEnd_8149899 : Nat := 4184815472597114216381803

theorem tailTrace_8149899 : CollatzResearch.WordTrace tailWord_8149899 prefixEnd_8149899 4184815472597114216381803 := by
  unfold tailWord_8149899
  simp only [CollatzResearch.WordTrace]
  refine ⟨297251236701315289780132751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198167491134210193186755167 297251236701315289780132751)
  ·
    refine ⟨445876855051972934670199127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297251236701315289780132751 445876855051972934670199127)
    ·
      refine ⟨668815282577959402005298691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445876855051972934670199127 668815282577959402005298691)
      ·
        refine ⟨1003222923866939103007948037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668815282577959402005298691 1003222923866939103007948037)
        ·
          refine ⟨188104298225051081813990257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1003222923866939103007948037 188104298225051081813990257)
          ·
            refine ⟨141078223668788311360492693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188104298225051081813990257 141078223668788311360492693)
            ·
              refine ⟨6613041734474452095023095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141078223668788311360492693 6613041734474452095023095)
              ·
                refine ⟨9919562601711678142534643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613041734474452095023095 9919562601711678142534643)
                ·
                  refine ⟨14879343902567517213801965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9919562601711678142534643 14879343902567517213801965)
                  ·
                    refine ⟨5579753963462818955175737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14879343902567517213801965 5579753963462818955175737)
                    ·
                      refine ⟨4184815472597114216381803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579753963462818955175737 4184815472597114216381803)
                      ·
                        rfl

theorem cell23_8149899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 3, 2].length) (baseStart_8149899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149899 prefixEnd_8149899 := by exact prefixLift 8149899
  have htrace : WordTrace (prefixWord ++ tailWord_8149899) baseStart_8149899 baseEnd_8149899 := by
    simpa [prefixWord, tailWord_8149899, baseEnd_8149899] using wordTrace_append hprefix tailTrace_8149899
  have hstable : (prefixWord ++ tailWord_8149899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149899).length < 2 ^ (prefixWord ++ tailWord_8149899).sum := by decide
  have hdescent : baseEnd_8149899 < baseStart_8149899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
