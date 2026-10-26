import V185TrunkScan23Chunk0402

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2383269 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_2383269 : Nat := 118140960795 + 2383269 * 2 ^ 59
def prefixEnd_2383269 : Nat := 4983230072969 + 3 ^ 40 * 2383269 * 2
def baseEnd_2383269 : Nat := 407920841986780394259017

theorem tailTrace_2383269 : CollatzResearch.WordTrace tailWord_2383269 prefixEnd_2383269 407920841986780394259017 := by
  unfold tailWord_2383269
  simp only [CollatzResearch.WordTrace]
  refine ⟨86924961602830917785000861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57949974401887278523333907 86924961602830917785000861)
  ·
    refine ⟨32596860601061594169375323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86924961602830917785000861 32596860601061594169375323)
    ·
      refine ⟨48895290901592391254062985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32596860601061594169375323 48895290901592391254062985)
      ·
        refine ⟨36671468176194293440547239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48895290901592391254062985 36671468176194293440547239)
        ·
          refine ⟨55007202264291440160820859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36671468176194293440547239 55007202264291440160820859)
          ·
            refine ⟨82510803396437160241231289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55007202264291440160820859 82510803396437160241231289)
            ·
              refine ⟨61883102547327870180923467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82510803396437160241231289 61883102547327870180923467)
              ·
                refine ⟨92824653820991805271385201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61883102547327870180923467 92824653820991805271385201)
                ·
                  refine ⟨69618490365743853953538901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92824653820991805271385201 69618490365743853953538901)
                  ·
                    refine ⟨407920841986780394259017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 69618490365743853953538901 407920841986780394259017)
                    ·
                      rfl

theorem cell23_2383269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_2383269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383269 prefixEnd_2383269 := by exact prefixLift 2383269
  have htrace : WordTrace (prefixWord ++ tailWord_2383269) baseStart_2383269 baseEnd_2383269 := by
    simpa [prefixWord, tailWord_2383269, baseEnd_2383269] using wordTrace_append hprefix tailTrace_2383269
  have hstable : (prefixWord ++ tailWord_2383269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383269).length < 2 ^ (prefixWord ++ tailWord_2383269).sum := by decide
  have hdescent : baseEnd_2383269 < baseStart_2383269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383279 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_2383279 : Nat := 118140960795 + 2383279 * 2 ^ 59
def prefixEnd_2383279 : Nat := 4983230072969 + 3 ^ 40 * 2383279 * 2
def baseEnd_2383279 : Nat := 1223767660766886143652005

theorem tailTrace_2383279 : CollatzResearch.WordTrace tailWord_2383279 prefixEnd_2383279 1223767660766886143652005 := by
  unfold tailWord_2383279
  simp only [CollatzResearch.WordTrace]
  refine ⟨86925326332794689492864891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57950217555196459661909927 86925326332794689492864891)
  ·
    refine ⟨130387989499192034239297337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86925326332794689492864891 130387989499192034239297337)
    ·
      refine ⟨97790992124394025679473003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130387989499192034239297337 97790992124394025679473003)
      ·
        refine ⟨146686488186591038519209505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97790992124394025679473003 146686488186591038519209505)
        ·
          refine ⟨110014866139943278889407129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146686488186591038519209505 110014866139943278889407129)
          ·
            refine ⟨82511149604957459167055347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110014866139943278889407129 82511149604957459167055347)
            ·
              refine ⟨123766724407436188750583021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82511149604957459167055347 123766724407436188750583021)
              ·
                refine ⟨46412521652788570781468633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123766724407436188750583021 46412521652788570781468633)
                ·
                  refine ⟨34809391239591428086101475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46412521652788570781468633 34809391239591428086101475)
                  ·
                    refine ⟨52214086859387142129152213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34809391239591428086101475 52214086859387142129152213)
                    ·
                      refine ⟨1223767660766886143652005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52214086859387142129152213 1223767660766886143652005)
                      ·
                        rfl

theorem cell23_2383279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_2383279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383279 prefixEnd_2383279 := by exact prefixLift 2383279
  have htrace : WordTrace (prefixWord ++ tailWord_2383279) baseStart_2383279 baseEnd_2383279 := by
    simpa [prefixWord, tailWord_2383279, baseEnd_2383279] using wordTrace_append hprefix tailTrace_2383279
  have hstable : (prefixWord ++ tailWord_2383279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383279).length < 2 ^ (prefixWord ++ tailWord_2383279).sum := by decide
  have hdescent : baseEnd_2383279 < baseStart_2383279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383293 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_2383293 : Nat := 118140960795 + 2383293 * 2 ^ 59
def prefixEnd_2383293 : Nat := 4983230072969 + 3 ^ 40 * 2383293 * 2
def baseEnd_2383293 : Nat := 1223774849496049088876941

theorem tailTrace_2383293 : CollatzResearch.WordTrace tailWord_2383293 prefixEnd_2383293 1223774849496049088876941 := by
  unfold tailWord_2383293
  simp only [CollatzResearch.WordTrace]
  refine ⟨86925836954743969883874533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57950557969829313255916355 86925836954743969883874533)
  ·
    refine ⟨16298594429014494353226475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86925836954743969883874533 16298594429014494353226475)
    ·
      refine ⟨24447891643521741529839713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16298594429014494353226475 24447891643521741529839713)
      ·
        refine ⟨18335918732641306147379785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24447891643521741529839713 18335918732641306147379785)
        ·
          refine ⟨13751939049480979610534839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18335918732641306147379785 13751939049480979610534839)
          ·
            refine ⟨20627908574221469415802259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13751939049480979610534839 20627908574221469415802259)
            ·
              refine ⟨30941862861332204123703389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20627908574221469415802259 30941862861332204123703389)
              ·
                refine ⟨11603198572999576546388771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30941862861332204123703389 11603198572999576546388771)
                ·
                  refine ⟨17404797859499364819583157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11603198572999576546388771 17404797859499364819583157)
                  ·
                    refine ⟨1631699799328065451835921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17404797859499364819583157 1631699799328065451835921)
                    ·
                      refine ⟨1223774849496049088876941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1631699799328065451835921 1223774849496049088876941)
                      ·
                        rfl

theorem cell23_2383293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_2383293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383293 prefixEnd_2383293 := by exact prefixLift 2383293
  have htrace : WordTrace (prefixWord ++ tailWord_2383293) baseStart_2383293 baseEnd_2383293 := by
    simpa [prefixWord, tailWord_2383293, baseEnd_2383293] using wordTrace_append hprefix tailTrace_2383293
  have hstable : (prefixWord ++ tailWord_2383293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383293).length < 2 ^ (prefixWord ++ tailWord_2383293).sum := by decide
  have hdescent : baseEnd_2383293 < baseStart_2383293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383336 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2383336 : Nat := 118140960795 + 2383336 * 2 ^ 59
def prefixEnd_2383336 : Nat := 4983230072969 + 3 ^ 40 * 2383336 * 2
def baseEnd_2383336 : Nat := 1223796929164192420639243

theorem tailTrace_2383336 : CollatzResearch.WordTrace tailWord_2383336 prefixEnd_2383336 1223796929164192420639243 := by
  unfold tailWord_2383336
  simp only [CollatzResearch.WordTrace]
  refine ⟨43463702646794094113844931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57951603529058792151793241 43463702646794094113844931)
  ·
    refine ⟨65195553970191141170767397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43463702646794094113844931 65195553970191141170767397)
    ·
      refine ⟨12224166369410838969518887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65195553970191141170767397 12224166369410838969518887)
      ·
        refine ⟨18336249554116258454278331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12224166369410838969518887 18336249554116258454278331)
        ·
          refine ⟨27504374331174387681417497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18336249554116258454278331 27504374331174387681417497)
          ·
            refine ⟨20628280748380790761063123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27504374331174387681417497 20628280748380790761063123)
            ·
              refine ⟨30942421122571186141594685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20628280748380790761063123 30942421122571186141594685)
              ·
                refine ⟨11603407920964194803098007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30942421122571186141594685 11603407920964194803098007)
                ·
                  refine ⟨17405111881446292204647011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11603407920964194803098007 17405111881446292204647011)
                  ·
                    refine ⟨26107667822169438306970517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17405111881446292204647011 26107667822169438306970517)
                    ·
                      refine ⟨1223796929164192420639243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26107667822169438306970517 1223796929164192420639243)
                      ·
                        rfl

theorem cell23_2383336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2383336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383336 prefixEnd_2383336 := by exact prefixLift 2383336
  have htrace : WordTrace (prefixWord ++ tailWord_2383336) baseStart_2383336 baseEnd_2383336 := by
    simpa [prefixWord, tailWord_2383336, baseEnd_2383336] using wordTrace_append hprefix tailTrace_2383336
  have hstable : (prefixWord ++ tailWord_2383336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383336).length < 2 ^ (prefixWord ++ tailWord_2383336).sum := by decide
  have hdescent : baseEnd_2383336 < baseStart_2383336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383386 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_2383386 : Nat := 118140960795 + 2383386 * 2 ^ 59
def prefixEnd_2383386 : Nat := 4983230072969 + 3 ^ 40 * 2383386 * 2
def baseEnd_2383386 : Nat := 1223822603196917225014013

theorem tailTrace_2383386 : CollatzResearch.WordTrace tailWord_2383386 prefixEnd_2383386 1223822603196917225014013 := by
  unfold tailWord_2383386
  simp only [CollatzResearch.WordTrace]
  refine ⟨21732307235851761691752503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57952819295604697844673341 21732307235851761691752503)
  ·
    refine ⟨32598460853777642537628755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21732307235851761691752503 32598460853777642537628755)
    ·
      refine ⟨48897691280666463806443133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32598460853777642537628755 48897691280666463806443133)
      ·
        refine ⟨18336634230249923927416175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48897691280666463806443133 18336634230249923927416175)
        ·
          refine ⟨27504951345374885891124263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18336634230249923927416175 27504951345374885891124263)
          ·
            refine ⟨41257427018062328836686395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27504951345374885891124263 41257427018062328836686395)
            ·
              refine ⟨61886140527093493255029593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41257427018062328836686395 61886140527093493255029593)
              ·
                refine ⟨46414605395320119941272195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61886140527093493255029593 46414605395320119941272195)
                ·
                  refine ⟨69621908092980179911908293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46414605395320119941272195 69621908092980179911908293)
                  ·
                    refine ⟨13054107767433783733482805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69621908092980179911908293 13054107767433783733482805)
                    ·
                      refine ⟨1223822603196917225014013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13054107767433783733482805 1223822603196917225014013)
                      ·
                        rfl

theorem cell23_2383386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_2383386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383386 prefixEnd_2383386 := by exact prefixLift 2383386
  have htrace : WordTrace (prefixWord ++ tailWord_2383386) baseStart_2383386 baseEnd_2383386 := by
    simpa [prefixWord, tailWord_2383386, baseEnd_2383386] using wordTrace_append hprefix tailTrace_2383386
  have hstable : (prefixWord ++ tailWord_2383386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383386).length < 2 ^ (prefixWord ++ tailWord_2383386).sum := by decide
  have hdescent : baseEnd_2383386 < baseStart_2383386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383417 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 1, 3, 2]
def baseStart_2383417 : Nat := 118140960795 + 2383417 * 2 ^ 59
def prefixEnd_2383417 : Nat := 4983230072969 + 3 ^ 40 * 2383417 * 2
def baseEnd_2383417 : Nat := 1223838521097206603726371

theorem tailTrace_2383417 : CollatzResearch.WordTrace tailWord_2383417 prefixEnd_2383417 1223838521097206603726371 := by
  unfold tailWord_2383417
  simp only [CollatzResearch.WordTrace]
  refine ⟨86930359606294739061388505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57953573070863159374259003 86930359606294739061388505)
  ·
    refine ⟨65197769704721054296041379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86930359606294739061388505 65197769704721054296041379)
    ·
      refine ⟨97796654557081581444062069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65197769704721054296041379 97796654557081581444062069)
      ·
        refine ⟨9168436364726398260380819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97796654557081581444062069 9168436364726398260380819)
        ·
          refine ⟨13752654547089597390571229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9168436364726398260380819 13752654547089597390571229)
          ·
            refine ⟨5157245455158599021464211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13752654547089597390571229 5157245455158599021464211)
            ·
              refine ⟨7735868182737898532196317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5157245455158599021464211 7735868182737898532196317)
              ·
                refine ⟨2900950568526711949573619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7735868182737898532196317 2900950568526711949573619)
                ·
                  refine ⟨4351425852790067924360429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900950568526711949573619 4351425852790067924360429)
                  ·
                    refine ⟨1631784694796275471635161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4351425852790067924360429 1631784694796275471635161)
                    ·
                      refine ⟨1223838521097206603726371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1631784694796275471635161 1223838521097206603726371)
                      ·
                        rfl

theorem cell23_2383417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_2383417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383417 prefixEnd_2383417 := by exact prefixLift 2383417
  have htrace : WordTrace (prefixWord ++ tailWord_2383417) baseStart_2383417 baseEnd_2383417 := by
    simpa [prefixWord, tailWord_2383417, baseEnd_2383417] using wordTrace_append hprefix tailTrace_2383417
  have hstable : (prefixWord ++ tailWord_2383417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383417).length < 2 ^ (prefixWord ++ tailWord_2383417).sum := by decide
  have hdescent : baseEnd_2383417 < baseStart_2383417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383447 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 1, 4, 2]
def baseStart_2383447 : Nat := 118140960795 + 2383447 * 2 ^ 59
def prefixEnd_2383447 : Nat := 4983230072969 + 3 ^ 40 * 2383447 * 2
def baseEnd_2383447 : Nat := 1223853925516841486351233

theorem tailTrace_2383447 : CollatzResearch.WordTrace tailWord_2383447 prefixEnd_2383447 1223853925516841486351233 := by
  unfold tailWord_2383447
  simp only [CollatzResearch.WordTrace]
  refine ⟨86931453796186054184980595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57954302530790702789987063 86931453796186054184980595)
  ·
    refine ⟨130397180694279081277470893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86931453796186054184980595 130397180694279081277470893)
    ·
      refine ⟨48898942760354655479051585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130397180694279081277470893 48898942760354655479051585)
      ·
        refine ⟨36674207070265991609288689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48898942760354655479051585 36674207070265991609288689)
        ·
          refine ⟨27505655302699493706966517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36674207070265991609288689 27505655302699493706966517)
          ·
            refine ⟨2578655184628077535028111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27505655302699493706966517 2578655184628077535028111)
            ·
              refine ⟨3867982776942116302542167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2578655184628077535028111 3867982776942116302542167)
              ·
                refine ⟨5801974165413174453813251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867982776942116302542167 5801974165413174453813251)
                ·
                  refine ⟨8702961248119761680719877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5801974165413174453813251 8702961248119761680719877)
                  ·
                    refine ⟨1631805234022455315134977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8702961248119761680719877 1631805234022455315134977)
                    ·
                      refine ⟨1223853925516841486351233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1631805234022455315134977 1223853925516841486351233)
                      ·
                        rfl

theorem cell23_2383447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_2383447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383447 prefixEnd_2383447 := by exact prefixLift 2383447
  have htrace : WordTrace (prefixWord ++ tailWord_2383447) baseStart_2383447 baseEnd_2383447 := by
    simpa [prefixWord, tailWord_2383447, baseEnd_2383447] using wordTrace_append hprefix tailTrace_2383447
  have hstable : (prefixWord ++ tailWord_2383447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383447).length < 2 ^ (prefixWord ++ tailWord_2383447).sum := by decide
  have hdescent : baseEnd_2383447 < baseStart_2383447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383463 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2383463 : Nat := 118140960795 + 2383463 * 2 ^ 59
def prefixEnd_2383463 : Nat := 4983230072969 + 3 ^ 40 * 2383463 * 2
def baseEnd_2383463 : Nat := 1223862141207313423751159

theorem tailTrace_2383463 : CollatzResearch.WordTrace tailWord_2383463 prefixEnd_2383463 1223862141207313423751159 := by
  unfold tailWord_2383463
  simp only [CollatzResearch.WordTrace]
  refine ⟨86932037364128088917563043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57954691576085392611708695 86932037364128088917563043)
  ·
    refine ⟨130398056046192133376344565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86932037364128088917563043 130398056046192133376344565)
    ·
      refine ⟨12224817754330512504032303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130398056046192133376344565 12224817754330512504032303)
      ·
        refine ⟨18337226631495768756048455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12224817754330512504032303 18337226631495768756048455)
        ·
          refine ⟨27505839947243653134072683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18337226631495768756048455 27505839947243653134072683)
          ·
            refine ⟨41258759920865479701109025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27505839947243653134072683 41258759920865479701109025)
            ·
              refine ⟨30944069940649109775831769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41258759920865479701109025 30944069940649109775831769)
              ·
                refine ⟨23208052455486832331873827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30944069940649109775831769 23208052455486832331873827)
                ·
                  refine ⟨34812078683230248497810741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23208052455486832331873827 34812078683230248497810741)
                  ·
                    refine ⟨3263632376552835796669757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34812078683230248497810741 3263632376552835796669757)
                    ·
                      refine ⟨1223862141207313423751159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3263632376552835796669757 1223862141207313423751159)
                      ·
                        rfl

theorem cell23_2383463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2383463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383463 prefixEnd_2383463 := by exact prefixLift 2383463
  have htrace : WordTrace (prefixWord ++ tailWord_2383463) baseStart_2383463 baseEnd_2383463 := by
    simpa [prefixWord, tailWord_2383463, baseEnd_2383463] using wordTrace_append hprefix tailTrace_2383463
  have hstable : (prefixWord ++ tailWord_2383463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383463).length < 2 ^ (prefixWord ++ tailWord_2383463).sum := by decide
  have hdescent : baseEnd_2383463 < baseStart_2383463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383483 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 2, 5]
def baseStart_2383483 : Nat := 118140960795 + 2383483 * 2 ^ 59
def prefixEnd_2383483 : Nat := 4983230072969 + 3 ^ 40 * 2383483 * 2
def baseEnd_2383483 : Nat := 407957470273467781833689

theorem tailTrace_2383483 : CollatzResearch.WordTrace tailWord_2383483 prefixEnd_2383483 407957470273467781833689 := by
  unfold tailWord_2383483
  simp only [CollatzResearch.WordTrace]
  refine ⟨86932766824055632333291103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57955177882703754888860735 86932766824055632333291103)
  ·
    refine ⟨130399150236083448499936655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86932766824055632333291103 130399150236083448499936655)
    ·
      refine ⟨195598725354125172749904983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130399150236083448499936655 195598725354125172749904983)
      ·
        refine ⟨293398088031187759124857475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195598725354125172749904983 293398088031187759124857475)
        ·
          refine ⟨440097132046781638687286213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293398088031187759124857475 440097132046781638687286213)
          ·
            refine ⟨82518212258771557253866165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 440097132046781638687286213 82518212258771557253866165)
            ·
              refine ⟨7736082399259833492549953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82518212258771557253866165 7736082399259833492549953)
              ·
                refine ⟨5802061799444875119412465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7736082399259833492549953 5802061799444875119412465)
                ·
                  refine ⟨4351546349583656339559349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5802061799444875119412465 4351546349583656339559349)
                  ·
                    refine ⟨407957470273467781833689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4351546349583656339559349 407957470273467781833689)
                    ·
                      rfl

theorem cell23_2383483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 5].length) (baseStart_2383483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383483 prefixEnd_2383483 := by exact prefixLift 2383483
  have htrace : WordTrace (prefixWord ++ tailWord_2383483) baseStart_2383483 baseEnd_2383483 := by
    simpa [prefixWord, tailWord_2383483, baseEnd_2383483] using wordTrace_append hprefix tailTrace_2383483
  have hstable : (prefixWord ++ tailWord_2383483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383483).length < 2 ^ (prefixWord ++ tailWord_2383483).sum := by decide
  have hdescent : baseEnd_2383483 < baseStart_2383483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383493 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_2383493 : Nat := 118140960795 + 2383493 * 2 ^ 59
def prefixEnd_2383493 : Nat := 4983230072969 + 3 ^ 40 * 2383493 * 2
def baseEnd_2383493 : Nat := 1223877545626948306376021

theorem tailTrace_2383493 : CollatzResearch.WordTrace tailWord_2383493 prefixEnd_2383493 1223877545626948306376021 := by
  unfold tailWord_2383493
  simp only [CollatzResearch.WordTrace]
  refine ⟨86933131554019404041155133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57955421036012936027436755 86933131554019404041155133)
  ·
    refine ⟨32599924332757276515433175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86933131554019404041155133 32599924332757276515433175)
    ·
      refine ⟨48899886499135914773149763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32599924332757276515433175 48899886499135914773149763)
      ·
        refine ⟨73349829748703872159724645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48899886499135914773149763 73349829748703872159724645)
        ·
          refine ⟨13753093077881976029948371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73349829748703872159724645 13753093077881976029948371)
          ·
            refine ⟨20629639616822964044922557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13753093077881976029948371 20629639616822964044922557)
            ·
              refine ⟨7736114856308611516845959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20629639616822964044922557 7736114856308611516845959)
              ·
                refine ⟨11604172284462917275268939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7736114856308611516845959 11604172284462917275268939)
                ·
                  refine ⟨17406258426694375912903409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11604172284462917275268939 17406258426694375912903409)
                  ·
                    refine ⟨13054693820020781934677557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17406258426694375912903409 13054693820020781934677557)
                    ·
                      refine ⟨1223877545626948306376021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13054693820020781934677557 1223877545626948306376021)
                      ·
                        rfl

theorem cell23_2383493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_2383493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383493 prefixEnd_2383493 := by exact prefixLift 2383493
  have htrace : WordTrace (prefixWord ++ tailWord_2383493) baseStart_2383493 baseEnd_2383493 := by
    simpa [prefixWord, tailWord_2383493, baseEnd_2383493] using wordTrace_append hprefix tailTrace_2383493
  have hstable : (prefixWord ++ tailWord_2383493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383493).length < 2 ^ (prefixWord ++ tailWord_2383493).sum := by decide
  have hdescent : baseEnd_2383493 < baseStart_2383493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383520 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2383520 : Nat := 118140960795 + 2383520 * 2 ^ 59
def prefixEnd_2383520 : Nat := 4983230072969 + 3 ^ 40 * 2383520 * 2
def baseEnd_2383520 : Nat := 1223891409604619700738397

theorem tailTrace_2383520 : CollatzResearch.WordTrace tailWord_2383520 prefixEnd_2383520 1223891409604619700738397 := by
  unfold tailWord_2383520
  simp only [CollatzResearch.WordTrace]
  refine ⟨43467058162460793826194007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57956077549947725101592009 43467058162460793826194007)
  ·
    refine ⟨65200587243691190739291011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43467058162460793826194007 65200587243691190739291011)
    ·
      refine ⟨97800880865536786108936517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65200587243691190739291011 97800880865536786108936517)
      ·
        refine ⟨18337665162288147395425597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97800880865536786108936517 18337665162288147395425597)
        ·
          refine ⟨6876624435858055273284599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18337665162288147395425597 6876624435858055273284599)
          ·
            refine ⟨10314936653787082909926899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6876624435858055273284599 10314936653787082909926899)
            ·
              refine ⟨15472404980680624364890349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10314936653787082909926899 15472404980680624364890349)
              ·
                refine ⟨5802151867755234136833881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15472404980680624364890349 5802151867755234136833881)
                ·
                  refine ⟨4351613900816425602625411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5802151867755234136833881 4351613900816425602625411)
                  ·
                    refine ⟨6527420851224638403938117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4351613900816425602625411 6527420851224638403938117)
                    ·
                      refine ⟨1223891409604619700738397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6527420851224638403938117 1223891409604619700738397)
                      ·
                        rfl

theorem cell23_2383520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2383520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383520 prefixEnd_2383520 := by exact prefixLift 2383520
  have htrace : WordTrace (prefixWord ++ tailWord_2383520) baseStart_2383520 baseEnd_2383520 := by
    simpa [prefixWord, tailWord_2383520, baseEnd_2383520] using wordTrace_append hprefix tailTrace_2383520
  have hstable : (prefixWord ++ tailWord_2383520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383520).length < 2 ^ (prefixWord ++ tailWord_2383520).sum := by decide
  have hdescent : baseEnd_2383520 < baseStart_2383520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383603 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 3, 6]
def baseStart_2383603 : Nat := 118140960795 + 2383603 * 2 ^ 59
def prefixEnd_2383603 : Nat := 4983230072969 + 3 ^ 40 * 2383603 * 2
def baseEnd_2383603 : Nat := 407978009499647625333505

theorem tailTrace_2383603 : CollatzResearch.WordTrace tailWord_2383603 prefixEnd_2383603 407978009499647625333505 := by
  unfold tailWord_2383603
  simp only [CollatzResearch.WordTrace]
  refine ⟨86937143583620892827659463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57958095722413928551772975 86937143583620892827659463)
  ·
    refine ⟨130405715375431339241489195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86937143583620892827659463 130405715375431339241489195)
    ·
      refine ⟨195608573063147008862233793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130405715375431339241489195 195608573063147008862233793)
      ·
        refine ⟨146706429797360256646675345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195608573063147008862233793 146706429797360256646675345)
        ·
          refine ⟨110029822348020192485006509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146706429797360256646675345 110029822348020192485006509)
          ·
            refine ⟨41261183380507572181877441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110029822348020192485006509 41261183380507572181877441)
            ·
              refine ⟨30945887535380679136408081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41261183380507572181877441 30945887535380679136408081)
              ·
                refine ⟨23209415651535509352306061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30945887535380679136408081 23209415651535509352306061)
                ·
                  refine ⟨8703530869325816007114773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23209415651535509352306061 8703530869325816007114773)
                  ·
                    refine ⟨407978009499647625333505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8703530869325816007114773 407978009499647625333505)
                    ·
                      rfl

theorem cell23_2383603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 6].length) (baseStart_2383603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383603 prefixEnd_2383603 := by exact prefixLift 2383603
  have htrace : WordTrace (prefixWord ++ tailWord_2383603) baseStart_2383603 baseEnd_2383603 := by
    simpa [prefixWord, tailWord_2383603, baseEnd_2383603] using wordTrace_append hprefix tailTrace_2383603
  have hstable : (prefixWord ++ tailWord_2383603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383603).length < 2 ^ (prefixWord ++ tailWord_2383603).sum := by decide
  have hdescent : baseEnd_2383603 < baseStart_2383603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383640 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2383640 : Nat := 118140960795 + 2383640 * 2 ^ 59
def prefixEnd_2383640 : Nat := 4983230072969 + 3 ^ 40 * 2383640 * 2
def baseEnd_2383640 : Nat := 1223953027283159231237845

theorem tailTrace_2383640 : CollatzResearch.WordTrace tailWord_2383640 prefixEnd_2383640 1223953027283159231237845 := by
  unfold tailWord_2383640
  simp only [CollatzResearch.WordTrace]
  refine ⟨43469246542243424073378187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57958995389657898764504249 43469246542243424073378187)
  ·
    refine ⟨65203869813365136110067281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43469246542243424073378187 65203869813365136110067281)
    ·
      refine ⟨48902902360023852082550461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65203869813365136110067281 48902902360023852082550461)
      ·
        refine ⟨18338588385008944530956423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48902902360023852082550461 18338588385008944530956423)
        ·
          refine ⟨27507882577513416796434635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18338588385008944530956423 27507882577513416796434635)
          ·
            refine ⟨41261823866270125194651953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27507882577513416796434635 41261823866270125194651953)
            ·
              refine ⟨30946367899702593895988965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41261823866270125194651953 30946367899702593895988965)
              ·
                refine ⟨5802443981194236355497931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30946367899702593895988965 5802443981194236355497931)
                ·
                  refine ⟨8703665971791354533246897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5802443981194236355497931 8703665971791354533246897)
                  ·
                    refine ⟨6527749478843515899935173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8703665971791354533246897 6527749478843515899935173)
                    ·
                      refine ⟨1223953027283159231237845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6527749478843515899935173 1223953027283159231237845)
                      ·
                        rfl

theorem cell23_2383640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2383640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383640 prefixEnd_2383640 := by exact prefixLift 2383640
  have htrace : WordTrace (prefixWord ++ tailWord_2383640) baseStart_2383640 baseEnd_2383640 := by
    simpa [prefixWord, tailWord_2383640, baseEnd_2383640] using wordTrace_append hprefix tailTrace_2383640
  have hstable : (prefixWord ++ tailWord_2383640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383640).length < 2 ^ (prefixWord ++ tailWord_2383640).sum := by decide
  have hdescent : baseEnd_2383640 < baseStart_2383640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383647 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 3]
def baseStart_2383647 : Nat := 118140960795 + 2383647 * 2 ^ 59
def prefixEnd_2383647 : Nat := 4983230072969 + 3 ^ 40 * 2383647 * 2
def baseEnd_2383647 : Nat := 1223956621647740703850313

theorem tailTrace_2383647 : CollatzResearch.WordTrace tailWord_2383647 prefixEnd_2383647 1223956621647740703850313 := by
  unfold tailWord_2383647
  simp only [CollatzResearch.WordTrace]
  refine ⟨86938748395461488342261195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57959165596974325561507463 86938748395461488342261195)
  ·
    refine ⟨130408122593192232513391793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86938748395461488342261195 130408122593192232513391793)
    ·
      refine ⟨97806091944894174385043845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130408122593192232513391793 97806091944894174385043845)
      ·
        refine ⟨18338642239667657697195721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97806091944894174385043845 18338642239667657697195721)
        ·
          refine ⟨13753981679750743272896791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18338642239667657697195721 13753981679750743272896791)
          ·
            refine ⟨20630972519626114909345187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13753981679750743272896791 20630972519626114909345187)
            ·
              refine ⟨30946458779439172364017781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20630972519626114909345187 30946458779439172364017781)
              ·
                refine ⟨2901230510572422409126667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30946458779439172364017781 2901230510572422409126667)
                ·
                  refine ⟨4351845765858633613690001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901230510572422409126667 4351845765858633613690001)
                  ·
                    refine ⟨3263884324393975210267501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4351845765858633613690001 3263884324393975210267501)
                    ·
                      refine ⟨1223956621647740703850313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3263884324393975210267501 1223956621647740703850313)
                      ·
                        rfl

theorem cell23_2383647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_2383647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383647 prefixEnd_2383647 := by exact prefixLift 2383647
  have htrace : WordTrace (prefixWord ++ tailWord_2383647) baseStart_2383647 baseEnd_2383647 := by
    simpa [prefixWord, tailWord_2383647, baseEnd_2383647] using wordTrace_append hprefix tailTrace_2383647
  have hstable : (prefixWord ++ tailWord_2383647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383647).length < 2 ^ (prefixWord ++ tailWord_2383647).sum := by decide
  have hdescent : baseEnd_2383647 < baseStart_2383647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383663 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 1, 9]
def baseStart_2383663 : Nat := 118140960795 + 2383663 * 2 ^ 59
def prefixEnd_2383663 : Nat := 4983230072969 + 3 ^ 40 * 2383663 * 2
def baseEnd_2383663 : Nat := 407988279112737547083413

theorem tailTrace_2383663 : CollatzResearch.WordTrace tailWord_2383663 prefixEnd_2383663 407988279112737547083413 := by
  unfold tailWord_2383663
  simp only [CollatzResearch.WordTrace]
  refine ⟨86939331963403523074843643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57959554642269015383229095 86939331963403523074843643)
  ·
    refine ⟨130408997945105284612265465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86939331963403523074843643 130408997945105284612265465)
    ·
      refine ⟨97806748458828963459199099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130408997945105284612265465 97806748458828963459199099)
      ·
        refine ⟨146710122688243445188798649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97806748458828963459199099 146710122688243445188798649)
        ·
          refine ⟨110032592016182583891598987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146710122688243445188798649 110032592016182583891598987)
          ·
            refine ⟨165048888024273875837398481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110032592016182583891598987 165048888024273875837398481)
            ·
              refine ⟨123786666018205406878048861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165048888024273875837398481 123786666018205406878048861)
              ·
                refine ⟨46419999756827027579268323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123786666018205406878048861 46419999756827027579268323)
                ·
                  refine ⟨69629999635240541368902485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46419999756827027579268323 69629999635240541368902485)
                  ·
                    refine ⟨407988279112737547083413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 69629999635240541368902485 407988279112737547083413)
                    ·
                      rfl

theorem cell23_2383663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_2383663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383663 prefixEnd_2383663 := by exact prefixLift 2383663
  have htrace : WordTrace (prefixWord ++ tailWord_2383663) baseStart_2383663 baseEnd_2383663 := by
    simpa [prefixWord, tailWord_2383663, baseEnd_2383663] using wordTrace_append hprefix tailTrace_2383663
  have hstable : (prefixWord ++ tailWord_2383663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383663).length < 2 ^ (prefixWord ++ tailWord_2383663).sum := by decide
  have hdescent : baseEnd_2383663 < baseStart_2383663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383717 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 5, 4, 2]
def baseStart_2383717 : Nat := 118140960795 + 2383717 * 2 ^ 59
def prefixEnd_2383717 : Nat := 4983230072969 + 3 ^ 40 * 2383717 * 2
def baseEnd_2383717 : Nat := 1223992565293555429974991

theorem tailTrace_2383717 : CollatzResearch.WordTrace tailWord_2383717 prefixEnd_2383717 1223992565293555429974991 := by
  unfold tailWord_2383717
  simp only [CollatzResearch.WordTrace]
  refine ⟨86941301505207890297309405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57960867670138593531539603 86941301505207890297309405)
  ·
    refine ⟨32602988064452958861491027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86941301505207890297309405 32602988064452958861491027)
    ·
      refine ⟨48904482096679438292236541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32602988064452958861491027 48904482096679438292236541)
      ·
        refine ⟨18339180786254789359588703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48904482096679438292236541 18339180786254789359588703)
        ·
          refine ⟨27508771179382184039383055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18339180786254789359588703 27508771179382184039383055)
          ·
            refine ⟨41263156769073276059074583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27508771179382184039383055 41263156769073276059074583)
            ·
              refine ⟨61894735153609914088611875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41263156769073276059074583 61894735153609914088611875)
              ·
                refine ⟨92842102730414871132917813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61894735153609914088611875 92842102730414871132917813)
                ·
                  refine ⟨8703947130976394168711045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92842102730414871132917813 8703947130976394168711045)
                  ·
                    refine ⟨1631990087058073906633321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8703947130976394168711045 1631990087058073906633321)
                    ·
                      refine ⟨1223992565293555429974991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1631990087058073906633321 1223992565293555429974991)
                      ·
                        rfl

theorem cell23_2383717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_2383717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383717 prefixEnd_2383717 := by exact prefixLift 2383717
  have htrace : WordTrace (prefixWord ++ tailWord_2383717) baseStart_2383717 baseEnd_2383717 := by
    simpa [prefixWord, tailWord_2383717, baseEnd_2383717] using wordTrace_append hprefix tailTrace_2383717
  have hstable : (prefixWord ++ tailWord_2383717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383717).length < 2 ^ (prefixWord ++ tailWord_2383717).sum := by decide
  have hdescent : baseEnd_2383717 < baseStart_2383717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383767 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_2383767 : Nat := 118140960795 + 2383767 * 2 ^ 59
def prefixEnd_2383767 : Nat := 4983230072969 + 3 ^ 40 * 2383767 * 2
def baseEnd_2383767 : Nat := 1224018239326280234349761

theorem tailTrace_2383767 : CollatzResearch.WordTrace tailWord_2383767 prefixEnd_2383767 1224018239326280234349761 := by
  unfold tailWord_2383767
  simp only [CollatzResearch.WordTrace]
  refine ⟨86943125155026748836629555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57962083436684499224419703 86943125155026748836629555)
  ·
    refine ⟨130414687732540123254944333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86943125155026748836629555 130414687732540123254944333)
    ·
      refine ⟨48905507899702546220604125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130414687732540123254944333 48905507899702546220604125)
      ·
        refine ⟨18339565462388454832726547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48905507899702546220604125 18339565462388454832726547)
        ·
          refine ⟨27509348193582682249089821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18339565462388454832726547 27509348193582682249089821)
          ·
            refine ⟨10316005572593505843408683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27509348193582682249089821 10316005572593505843408683)
            ·
              refine ⟨15474008358890258765113025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10316005572593505843408683 15474008358890258765113025)
              ·
                refine ⟨11605506269167694073834769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15474008358890258765113025 11605506269167694073834769)
                ·
                  refine ⟨8704129701875770555376077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11605506269167694073834769 8704129701875770555376077)
                  ·
                    refine ⟨3264048638203413958266029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8704129701875770555376077 3264048638203413958266029)
                    ·
                      refine ⟨1224018239326280234349761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3264048638203413958266029 1224018239326280234349761)
                      ·
                        rfl

theorem cell23_2383767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_2383767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383767 prefixEnd_2383767 := by exact prefixLift 2383767
  have htrace : WordTrace (prefixWord ++ tailWord_2383767) baseStart_2383767 baseEnd_2383767 := by
    simpa [prefixWord, tailWord_2383767, baseEnd_2383767] using wordTrace_append hprefix tailTrace_2383767
  have hstable : (prefixWord ++ tailWord_2383767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383767).length < 2 ^ (prefixWord ++ tailWord_2383767).sum := by decide
  have hdescent : baseEnd_2383767 < baseStart_2383767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383768 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2383768 : Nat := 118140960795 + 2383768 * 2 ^ 59
def prefixEnd_2383768 : Nat := 4983230072969 + 3 ^ 40 * 2383768 * 2
def baseEnd_2383768 : Nat := 1224018752806934730437257

theorem tailTrace_2383768 : CollatzResearch.WordTrace tailWord_2383768 prefixEnd_2383768 1224018752806934730437257 := by
  unfold tailWord_2383768
  simp only [CollatzResearch.WordTrace]
  refine ⟨43471580814011563003707979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57962107752015417338277305 43471580814011563003707979)
  ·
    refine ⟨65207371221017344505561969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43471580814011563003707979 65207371221017344505561969)
    ·
      refine ⟨48905528415763008379171477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65207371221017344505561969 48905528415763008379171477)
      ·
        refine ⟨2292446644488891017773663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48905528415763008379171477 2292446644488891017773663)
        ·
          refine ⟨3438669966733336526660495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292446644488891017773663 3438669966733336526660495)
          ·
            refine ⟨5158004950100004789990743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438669966733336526660495 5158004950100004789990743)
            ·
              refine ⟨7737007425150007184986115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5158004950100004789990743 7737007425150007184986115)
              ·
                refine ⟨11605511137725010777479173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7737007425150007184986115 11605511137725010777479173)
                ·
                  refine ⟨2176033338323439520777345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11605511137725010777479173 2176033338323439520777345)
                  ·
                    refine ⟨1632025003742579640583009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2176033338323439520777345 1632025003742579640583009)
                    ·
                      refine ⟨1224018752806934730437257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632025003742579640583009 1224018752806934730437257)
                      ·
                        rfl

theorem cell23_2383768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2383768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383768 prefixEnd_2383768 := by exact prefixLift 2383768
  have htrace : WordTrace (prefixWord ++ tailWord_2383768) baseStart_2383768 baseEnd_2383768 := by
    simpa [prefixWord, tailWord_2383768, baseEnd_2383768] using wordTrace_append hprefix tailTrace_2383768
  have hstable : (prefixWord ++ tailWord_2383768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383768).length < 2 ^ (prefixWord ++ tailWord_2383768).sum := by decide
  have hdescent : baseEnd_2383768 < baseStart_2383768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383800 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 2, 8]
def baseStart_2383800 : Nat := 118140960795 + 2383800 * 2 ^ 59
def prefixEnd_2383800 : Nat := 4983230072969 + 3 ^ 40 * 2383800 * 2
def baseEnd_2383800 : Nat := 408011728062626201745703

theorem tailTrace_2383800 : CollatzResearch.WordTrace tailWord_2383800 prefixEnd_2383800 408011728062626201745703 := by
  unfold tailWord_2383800
  simp only [CollatzResearch.WordTrace]
  refine ⟨43472164381953597736290427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57962885842604796981720569 43472164381953597736290427)
  ·
    refine ⟨65208246572930396604435641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43472164381953597736290427 65208246572930396604435641)
    ·
      refine ⟨48906184929697797453326731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65208246572930396604435641 48906184929697797453326731)
      ·
        refine ⟨73359277394546696179990097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48906184929697797453326731 73359277394546696179990097)
        ·
          refine ⟨55019458045910022134992573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73359277394546696179990097 55019458045910022134992573)
          ·
            refine ⟨20632296767216258300622215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55019458045910022134992573 20632296767216258300622215)
            ·
              refine ⟨30948445150824387450933323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20632296767216258300622215 30948445150824387450933323)
              ·
                refine ⟨46422667726236581176399985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30948445150824387450933323 46422667726236581176399985)
                ·
                  refine ⟨34817000794677435882299989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46422667726236581176399985 34817000794677435882299989)
                  ·
                    refine ⟨408011728062626201745703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34817000794677435882299989 408011728062626201745703)
                    ·
                      rfl

theorem cell23_2383800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_2383800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383800 prefixEnd_2383800 := by exact prefixLift 2383800
  have htrace : WordTrace (prefixWord ++ tailWord_2383800) baseStart_2383800 baseEnd_2383800 := by
    simpa [prefixWord, tailWord_2383800, baseEnd_2383800] using wordTrace_append hprefix tailTrace_2383800
  have hstable : (prefixWord ++ tailWord_2383800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383800).length < 2 ^ (prefixWord ++ tailWord_2383800).sum := by decide
  have hdescent : baseEnd_2383800 < baseStart_2383800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383807 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_2383807 : Nat := 118140960795 + 2383807 * 2 ^ 59
def prefixEnd_2383807 : Nat := 4983230072969 + 3 ^ 40 * 2383807 * 2
def baseEnd_2383807 : Nat := 1224038778552460077849577

theorem tailTrace_2383807 : CollatzResearch.WordTrace tailWord_2383807 prefixEnd_2383807 1224038778552460077849577 := by
  unfold tailWord_2383807
  simp only [CollatzResearch.WordTrace]
  refine ⟨86944584074881835668085675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57963056049921223778723783 86944584074881835668085675)
  ·
    refine ⟨130416876112322753502128513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86944584074881835668085675 130416876112322753502128513)
    ·
      refine ⟨97812657084242065126596385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130416876112322753502128513 97812657084242065126596385)
      ·
        refine ⟨73359492813181548844947289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97812657084242065126596385 73359492813181548844947289)
        ·
          refine ⟨55019619609886161633710467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73359492813181548844947289 55019619609886161633710467)
          ·
            refine ⟨82529429414829242450565701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55019619609886161633710467 82529429414829242450565701)
            ·
              refine ⟨15474268015280482959481069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82529429414829242450565701 15474268015280482959481069)
              ·
                refine ⟨5802850505730181109805401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15474268015280482959481069 5802850505730181109805401)
                ·
                  refine ⟨4352137879297635832354051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5802850505730181109805401 4352137879297635832354051)
                  ·
                    refine ⟨6528206818946453748531077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4352137879297635832354051 6528206818946453748531077)
                    ·
                      refine ⟨1224038778552460077849577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6528206818946453748531077 1224038778552460077849577)
                      ·
                        rfl

theorem cell23_2383807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_2383807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383807 prefixEnd_2383807 := by exact prefixLift 2383807
  have htrace : WordTrace (prefixWord ++ tailWord_2383807) baseStart_2383807 baseEnd_2383807 := by
    simpa [prefixWord, tailWord_2383807, baseEnd_2383807] using wordTrace_append hprefix tailTrace_2383807
  have hstable : (prefixWord ++ tailWord_2383807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383807).length < 2 ^ (prefixWord ++ tailWord_2383807).sum := by decide
  have hdescent : baseEnd_2383807 < baseStart_2383807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383836 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2383836 : Nat := 118140960795 + 2383836 * 2 ^ 59
def prefixEnd_2383836 : Nat := 4983230072969 + 3 ^ 40 * 2383836 * 2
def baseEnd_2383836 : Nat := 1224053669491440464386945

theorem tailTrace_2383836 : CollatzResearch.WordTrace tailWord_2383836 prefixEnd_2383836 1224053669491440464386945 := by
  unfold tailWord_2383836
  simp only [CollatzResearch.WordTrace]
  refine ⟨43472820895888386810445681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57963761194517849080594241 43472820895888386810445681)
  ·
    refine ⟨32604615671916290107834261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43472820895888386810445681 32604615671916290107834261)
    ·
      refine ⟨1528341359621076098804731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32604615671916290107834261 1528341359621076098804731)
      ·
        refine ⟨2292512039431614148207097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1528341359621076098804731 2292512039431614148207097)
        ·
          refine ⟨1719384029573710611155323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2292512039431614148207097 1719384029573710611155323)
          ·
            refine ⟨2579076044360565916732985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719384029573710611155323 2579076044360565916732985)
            ·
              refine ⟨1934307033270424437549739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579076044360565916732985 1934307033270424437549739)
              ·
                refine ⟨2901460549905636656324609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934307033270424437549739 2901460549905636656324609)
                ·
                  refine ⟨2176095412429227492243457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2901460549905636656324609 2176095412429227492243457)
                  ·
                    refine ⟨1632071559321920619182593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2176095412429227492243457 1632071559321920619182593)
                    ·
                      refine ⟨1224053669491440464386945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632071559321920619182593 1224053669491440464386945)
                      ·
                        rfl

theorem cell23_2383836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2383836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383836 prefixEnd_2383836 := by exact prefixLift 2383836
  have htrace : WordTrace (prefixWord ++ tailWord_2383836) baseStart_2383836 baseEnd_2383836 := by
    simpa [prefixWord, tailWord_2383836, baseEnd_2383836] using wordTrace_append hprefix tailTrace_2383836
  have hstable : (prefixWord ++ tailWord_2383836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383836).length < 2 ^ (prefixWord ++ tailWord_2383836).sum := by decide
  have hdescent : baseEnd_2383836 < baseStart_2383836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383908 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2383908 : Nat := 118140960795 + 2383908 * 2 ^ 59
def prefixEnd_2383908 : Nat := 4983230072969 + 3 ^ 40 * 2383908 * 2
def baseEnd_2383908 : Nat := 1224090640098564182686613

theorem tailTrace_2383908 : CollatzResearch.WordTrace tailWord_2383908 prefixEnd_2383908 1224090640098564182686613 := by
  unfold tailWord_2383908
  simp only [CollatzResearch.WordTrace]
  refine ⟨43474133923757964958756189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57965511898343953278341585 43474133923757964958756189)
  ·
    refine ⟨16302800221409236859533571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43474133923757964958756189 16302800221409236859533571)
    ·
      refine ⟨24454200332113855289300357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16302800221409236859533571 24454200332113855289300357)
      ·
        refine ⟨4585162562271347866743817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24454200332113855289300357 4585162562271347866743817)
        ·
          refine ⟨3438871921703510900057863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4585162562271347866743817 3438871921703510900057863)
          ·
            refine ⟨5158307882555266350086795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438871921703510900057863 5158307882555266350086795)
            ·
              refine ⟨7737461823832899525130193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5158307882555266350086795 7737461823832899525130193)
              ·
                refine ⟨5803096367874674643847645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7737461823832899525130193 5803096367874674643847645)
                ·
                  refine ⟨2176161137953002991442867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5803096367874674643847645 2176161137953002991442867)
                  ·
                    refine ⟨3264241706929504487164301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2176161137953002991442867 3264241706929504487164301)
                    ·
                      refine ⟨1224090640098564182686613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3264241706929504487164301 1224090640098564182686613)
                      ·
                        rfl

theorem cell23_2383908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2383908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383908 prefixEnd_2383908 := by exact prefixLift 2383908
  have htrace : WordTrace (prefixWord ++ tailWord_2383908) baseStart_2383908 baseEnd_2383908 := by
    simpa [prefixWord, tailWord_2383908, baseEnd_2383908] using wordTrace_append hprefix tailTrace_2383908
  have hstable : (prefixWord ++ tailWord_2383908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383908).length < 2 ^ (prefixWord ++ tailWord_2383908).sum := by decide
  have hdescent : baseEnd_2383908 < baseStart_2383908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383918 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_2383918 : Nat := 118140960795 + 2383918 * 2 ^ 59
def prefixEnd_2383918 : Nat := 4983230072969 + 3 ^ 40 * 2383918 * 2
def baseEnd_2383918 : Nat := 1224095774905109143561567

theorem tailTrace_2383918 : CollatzResearch.WordTrace tailWord_2383918 prefixEnd_2383918 1224095774905109143561567 := by
  unfold tailWord_2383918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10868579072184962703172051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57965755051653134416917605 10868579072184962703172051)
  ·
    refine ⟨16302868608277444054758077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10868579072184962703172051 16302868608277444054758077)
    ·
      refine ⟨6113575728104041520534279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16302868608277444054758077 6113575728104041520534279)
      ·
        refine ⟨9170363592156062280801419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6113575728104041520534279 9170363592156062280801419)
        ·
          refine ⟨13755545388234093421202129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9170363592156062280801419 13755545388234093421202129)
          ·
            refine ⟨10316659041175570065901597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13755545388234093421202129 10316659041175570065901597)
            ·
              refine ⟨3868747140440838774713099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10316659041175570065901597 3868747140440838774713099)
              ·
                refine ⟨5803120710661258162069649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3868747140440838774713099 5803120710661258162069649)
                ·
                  refine ⟨4352340532995943621552237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5803120710661258162069649 4352340532995943621552237)
                  ·
                    refine ⟨1632127699873478858082089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4352340532995943621552237 1632127699873478858082089)
                    ·
                      refine ⟨1224095774905109143561567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632127699873478858082089 1224095774905109143561567)
                      ·
                        rfl

theorem cell23_2383918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_2383918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383918 prefixEnd_2383918 := by exact prefixLift 2383918
  have htrace : WordTrace (prefixWord ++ tailWord_2383918) baseStart_2383918 baseEnd_2383918 := by
    simpa [prefixWord, tailWord_2383918, baseEnd_2383918] using wordTrace_append hprefix tailTrace_2383918
  have hstable : (prefixWord ++ tailWord_2383918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383918).length < 2 ^ (prefixWord ++ tailWord_2383918).sum := by decide
  have hdescent : baseEnd_2383918 < baseStart_2383918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383928 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 1, 5]
def baseStart_2383928 : Nat := 118140960795 + 2383928 * 2 ^ 59
def prefixEnd_2383928 : Nat := 4983230072969 + 3 ^ 40 * 2383928 * 2
def baseEnd_2383928 : Nat := 408033636570551368145507

theorem tailTrace_2383928 : CollatzResearch.WordTrace tailWord_2383928 prefixEnd_2383928 408033636570551368145507 := by
  unfold tailWord_2383928
  simp only [CollatzResearch.WordTrace]
  refine ⟨43474498653721736666620219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57965998204962315555493625 43474498653721736666620219)
  ·
    refine ⟨65211747980582604999930329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43474498653721736666620219 65211747980582604999930329)
    ·
      refine ⟨48908810985436953749947747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65211747980582604999930329 48908810985436953749947747)
      ·
        refine ⟨73363216478155430624921621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48908810985436953749947747 73363216478155430624921621)
        ·
          refine ⟨3438900772413535810543201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73363216478155430624921621 3438900772413535810543201)
          ·
            refine ⟨2579175579310151857907401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3438900772413535810543201 2579175579310151857907401)
            ·
              refine ⟨1934381684482613893430551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579175579310151857907401 1934381684482613893430551)
              ·
                refine ⟨2901572526723920840145827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934381684482613893430551 2901572526723920840145827)
                ·
                  refine ⟨4352358790085881260218741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901572526723920840145827 4352358790085881260218741)
                  ·
                    refine ⟨408033636570551368145507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4352358790085881260218741 408033636570551368145507)
                    ·
                      rfl

theorem cell23_2383928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_2383928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383928 prefixEnd_2383928 := by exact prefixLift 2383928
  have htrace : WordTrace (prefixWord ++ tailWord_2383928) baseStart_2383928 baseEnd_2383928 := by
    simpa [prefixWord, tailWord_2383928, baseEnd_2383928] using wordTrace_append hprefix tailTrace_2383928
  have hstable : (prefixWord ++ tailWord_2383928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383928).length < 2 ^ (prefixWord ++ tailWord_2383928).sum := by decide
  have hdescent : baseEnd_2383928 < baseStart_2383928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383958 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2383958 : Nat := 118140960795 + 2383958 * 2 ^ 59
def prefixEnd_2383958 : Nat := 4983230072969 + 3 ^ 40 * 2383958 * 2
def baseEnd_2383958 : Nat := 408038771377096329020461

theorem tailTrace_2383958 : CollatzResearch.WordTrace tailWord_2383958 prefixEnd_2383958 408038771377096329020461 := by
  unfold tailWord_2383958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5434380718583424278552033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57966727664889858971221685 5434380718583424278552033)
  ·
    refine ⟨4075785538937568208914025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5434380718583424278552033 4075785538937568208914025)
    ·
      refine ⟨3056839154203176156685519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4075785538937568208914025 3056839154203176156685519)
      ·
        refine ⟨4585258731304764235028279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056839154203176156685519 4585258731304764235028279)
        ·
          refine ⟨6877888096957146352542419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4585258731304764235028279 6877888096957146352542419)
          ·
            refine ⟨10316832145435719528813629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6877888096957146352542419 10316832145435719528813629)
            ·
              refine ⟨3868812054538394823305111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10316832145435719528813629 3868812054538394823305111)
              ·
                refine ⟨5803218081807592234957667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3868812054538394823305111 5803218081807592234957667)
                ·
                  refine ⟨8704827122711388352436501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5803218081807592234957667 8704827122711388352436501)
                  ·
                    refine ⟨408038771377096329020461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8704827122711388352436501 408038771377096329020461)
                    ·
                      rfl

theorem cell23_2383958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2383958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383958 prefixEnd_2383958 := by exact prefixLift 2383958
  have htrace : WordTrace (prefixWord ++ tailWord_2383958) baseStart_2383958 baseEnd_2383958 := by
    simpa [prefixWord, tailWord_2383958, baseEnd_2383958] using wordTrace_append hprefix tailTrace_2383958
  have hstable : (prefixWord ++ tailWord_2383958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383958).length < 2 ^ (prefixWord ++ tailWord_2383958).sum := by decide
  have hdescent : baseEnd_2383958 < baseStart_2383958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383965 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2383965 : Nat := 118140960795 + 2383965 * 2 ^ 59
def prefixEnd_2383965 : Nat := 4983230072969 + 3 ^ 40 * 2383965 * 2
def baseEnd_2383965 : Nat := 1224119908495870459673851

theorem tailTrace_2383965 : CollatzResearch.WordTrace tailWord_2383965 prefixEnd_2383965 1224119908495870459673851 := by
  unfold tailWord_2383965
  simp only [CollatzResearch.WordTrace]
  refine ⟨86950346808309428652337349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57966897872206285768224899 86950346808309428652337349)
  ·
    refine ⟨16303190026558017872313253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86950346808309428652337349 16303190026558017872313253)
    ·
      refine ⟨3056848129979628351058735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16303190026558017872313253 3056848129979628351058735)
      ·
        refine ⟨4585272194969442526588103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056848129979628351058735 4585272194969442526588103)
        ·
          refine ⟨6877908292454163789882155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4585272194969442526588103 6877908292454163789882155)
          ·
            refine ⟨10316862438681245684823233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6877908292454163789882155 10316862438681245684823233)
            ·
              refine ⟨7737646829010934263617425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10316862438681245684823233 7737646829010934263617425)
              ·
                refine ⟨5803235121758200697713069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7737646829010934263617425 5803235121758200697713069)
                ·
                  refine ⟨2176213170659325261642401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5803235121758200697713069 2176213170659325261642401)
                  ·
                    refine ⟨1632159877994493946231801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2176213170659325261642401 1632159877994493946231801)
                    ·
                      refine ⟨1224119908495870459673851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632159877994493946231801 1224119908495870459673851)
                      ·
                        rfl

theorem cell23_2383965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2383965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383965 prefixEnd_2383965 := by exact prefixLift 2383965
  have htrace : WordTrace (prefixWord ++ tailWord_2383965) baseStart_2383965 baseEnd_2383965 := by
    simpa [prefixWord, tailWord_2383965, baseEnd_2383965] using wordTrace_append hprefix tailTrace_2383965
  have hstable : (prefixWord ++ tailWord_2383965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383965).length < 2 ^ (prefixWord ++ tailWord_2383965).sum := by decide
  have hdescent : baseEnd_2383965 < baseStart_2383965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383977 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_2383977 : Nat := 118140960795 + 2383977 * 2 ^ 59
def prefixEnd_2383977 : Nat := 4983230072969 + 3 ^ 40 * 2383977 * 2
def baseEnd_2383977 : Nat := 1224126070263724412723795

theorem tailTrace_2383977 : CollatzResearch.WordTrace tailWord_2383977 prefixEnd_2383977 1224126070263724412723795 := by
  unfold tailWord_2383977
  simp only [CollatzResearch.WordTrace]
  refine ⟨86950784484265954701774185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57967189656177303134516123 86950784484265954701774185)
  ·
    refine ⟨65213088363199466026330639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86950784484265954701774185 65213088363199466026330639)
    ·
      refine ⟨97819632544799199039495959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65213088363199466026330639 97819632544799199039495959)
      ·
        refine ⟨146729448817198798559243939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97819632544799199039495959 146729448817198798559243939)
        ·
          refine ⟨220094173225798197838865909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146729448817198798559243939 220094173225798197838865909)
          ·
            refine ⟨20633828739918581047393679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 220094173225798197838865909 20633828739918581047393679)
            ·
              refine ⟨30950743109877871571090519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20633828739918581047393679 30950743109877871571090519)
              ·
                refine ⟨46426114664816807356635779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30950743109877871571090519 46426114664816807356635779)
                ·
                  refine ⟨69639171997225211034953669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46426114664816807356635779 69639171997225211034953669)
                  ·
                    refine ⟨13057344749479727069053813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69639171997225211034953669 13057344749479727069053813)
                    ·
                      refine ⟨1224126070263724412723795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13057344749479727069053813 1224126070263724412723795)
                      ·
                        rfl

theorem cell23_2383977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_2383977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383977 prefixEnd_2383977 := by exact prefixLift 2383977
  have htrace : WordTrace (prefixWord ++ tailWord_2383977) baseStart_2383977 baseEnd_2383977 := by
    simpa [prefixWord, tailWord_2383977, baseEnd_2383977] using wordTrace_append hprefix tailTrace_2383977
  have hstable : (prefixWord ++ tailWord_2383977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383977).length < 2 ^ (prefixWord ++ tailWord_2383977).sum := by decide
  have hdescent : baseEnd_2383977 < baseStart_2383977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383981 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2383981 : Nat := 118140960795 + 2383981 * 2 ^ 59
def prefixEnd_2383981 : Nat := 4983230072969 + 3 ^ 40 * 2383981 * 2
def baseEnd_2383981 : Nat := 1224128124186342397073777

theorem tailTrace_2383981 : CollatzResearch.WordTrace tailWord_2383981 prefixEnd_2383981 1224128124186342397073777 := by
  unfold tailWord_2383981
  simp only [CollatzResearch.WordTrace]
  refine ⟨86950930376251463384919797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57967286917500975589946531 86950930376251463384919797)
  ·
    refine ⟨8151649722773574692336231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86950930376251463384919797 8151649722773574692336231)
    ·
      refine ⟨12227474584160362038504347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8151649722773574692336231 12227474584160362038504347)
      ·
        refine ⟨18341211876240543057756521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12227474584160362038504347 18341211876240543057756521)
        ·
          refine ⟨13755908907180407293317391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18341211876240543057756521 13755908907180407293317391)
          ·
            refine ⟨20633863360770610939976087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13755908907180407293317391 20633863360770610939976087)
            ·
              refine ⟨30950795041155916409964131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20633863360770610939976087 30950795041155916409964131)
              ·
                refine ⟨46426192561733874614946197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30950795041155916409964131 46426192561733874614946197)
                ·
                  refine ⟨2176227776331275372575603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46426192561733874614946197 2176227776331275372575603)
                  ·
                    refine ⟨3264341664496913058863405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2176227776331275372575603 3264341664496913058863405)
                    ·
                      refine ⟨1224128124186342397073777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3264341664496913058863405 1224128124186342397073777)
                      ·
                        rfl

theorem cell23_2383981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2383981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2383981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2383981 prefixEnd_2383981 := by exact prefixLift 2383981
  have htrace : WordTrace (prefixWord ++ tailWord_2383981) baseStart_2383981 baseEnd_2383981 := by
    simpa [prefixWord, tailWord_2383981, baseEnd_2383981] using wordTrace_append hprefix tailTrace_2383981
  have hstable : (prefixWord ++ tailWord_2383981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383981).length < 2 ^ (prefixWord ++ tailWord_2383981).sum := by decide
  have hdescent : baseEnd_2383981 < baseStart_2383981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384004 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_2384004 : Nat := 118140960795 + 2384004 * 2 ^ 59
def prefixEnd_2384004 : Nat := 4983230072969 + 3 ^ 40 * 2384004 * 2
def baseEnd_2384004 : Nat := 1224139934241395807086171

theorem tailTrace_2384004 : CollatzResearch.WordTrace tailWord_2384004 prefixEnd_2384004 1224139934241395807086171 := by
  unfold tailWord_2384004
  simp only [CollatzResearch.WordTrace]
  refine ⟨43475884627584069156503533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57967846170112092208671377 43475884627584069156503533)
  ·
    refine ⟨16303456735344025933688825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43475884627584069156503533 16303456735344025933688825)
    ·
      refine ⟨12227592551508019450266619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16303456735344025933688825 12227592551508019450266619)
      ·
        refine ⟨18341388827262029175399929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12227592551508019450266619 18341388827262029175399929)
        ·
          refine ⟨13756041620446521881549947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18341388827262029175399929 13756041620446521881549947)
          ·
            refine ⟨20634062430669782822324921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13756041620446521881549947 20634062430669782822324921)
            ·
              refine ⟨15475546823002337116743691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20634062430669782822324921 15475546823002337116743691)
              ·
                refine ⟨23213320234503505675115537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15475546823002337116743691 23213320234503505675115537)
                ·
                  refine ⟨17409990175877629256336653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23213320234503505675115537 17409990175877629256336653)
                  ·
                    refine ⟨6528746315954110971126245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17409990175877629256336653 6528746315954110971126245)
                    ·
                      refine ⟨1224139934241395807086171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6528746315954110971126245 1224139934241395807086171)
                      ·
                        rfl

theorem cell23_2384004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_2384004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384004 prefixEnd_2384004 := by exact prefixLift 2384004
  have htrace : WordTrace (prefixWord ++ tailWord_2384004) baseStart_2384004 baseEnd_2384004 := by
    simpa [prefixWord, tailWord_2384004, baseEnd_2384004] using wordTrace_append hprefix tailTrace_2384004
  have hstable : (prefixWord ++ tailWord_2384004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384004).length < 2 ^ (prefixWord ++ tailWord_2384004).sum := by decide
  have hdescent : baseEnd_2384004 < baseStart_2384004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384017 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_2384017 : Nat := 118140960795 + 2384017 * 2 ^ 59
def prefixEnd_2384017 : Nat := 4983230072969 + 3 ^ 40 * 2384017 * 2
def baseEnd_2384017 : Nat := 1224146609489904256223611

theorem tailTrace_2384017 : CollatzResearch.WordTrace tailWord_2384017 prefixEnd_2384017 1224146609489904256223611 := by
  unfold tailWord_2384017
  simp only [CollatzResearch.WordTrace]
  refine ⟨86952243404121041533230305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57968162269414027688820203 86952243404121041533230305)
  ·
    refine ⟨65214182553090781149922729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86952243404121041533230305 65214182553090781149922729)
    ·
      refine ⟨48910636914818085862442047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65214182553090781149922729 48910636914818085862442047)
      ·
        refine ⟨73365955372227128793663071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48910636914818085862442047 73365955372227128793663071)
        ·
          refine ⟨110048933058340693190494607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73365955372227128793663071 110048933058340693190494607)
          ·
            refine ⟨165073399587511039785741911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110048933058340693190494607 165073399587511039785741911)
            ·
              refine ⟨247610099381266559678612867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165073399587511039785741911 247610099381266559678612867)
              ·
                refine ⟨371415149071899839517919301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247610099381266559678612867 371415149071899839517919301)
                ·
                  refine ⟨69640340450981219909609869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371415149071899839517919301 69640340450981219909609869)
                  ·
                    refine ⟨26115127669117957466103701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69640340450981219909609869 26115127669117957466103701)
                    ·
                      refine ⟨1224146609489904256223611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26115127669117957466103701 1224146609489904256223611)
                      ·
                        rfl

theorem cell23_2384017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_2384017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384017 prefixEnd_2384017 := by exact prefixLift 2384017
  have htrace : WordTrace (prefixWord ++ tailWord_2384017) baseStart_2384017 baseEnd_2384017 := by
    simpa [prefixWord, tailWord_2384017, baseEnd_2384017] using wordTrace_append hprefix tailTrace_2384017
  have hstable : (prefixWord ++ tailWord_2384017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384017).length < 2 ^ (prefixWord ++ tailWord_2384017).sum := by decide
  have hdescent : baseEnd_2384017 < baseStart_2384017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384021 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_2384021 : Nat := 118140960795 + 2384021 * 2 ^ 59
def prefixEnd_2384021 : Nat := 4983230072969 + 3 ^ 40 * 2384021 * 2
def baseEnd_2384021 : Nat := 1224148663412522240573593

theorem tailTrace_2384021 : CollatzResearch.WordTrace tailWord_2384021 prefixEnd_2384021 1224148663412522240573593 := by
  unfold tailWord_2384021
  simp only [CollatzResearch.WordTrace]
  refine ⟨86952389296106550216375917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57968259530737700144250611 86952389296106550216375917)
  ·
    refine ⟨32607145986039956331140969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86952389296106550216375917 32607145986039956331140969)
    ·
      refine ⟨24455359489529967248355727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32607145986039956331140969 24455359489529967248355727)
      ·
        refine ⟨36683039234294950872533591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24455359489529967248355727 36683039234294950872533591)
        ·
          refine ⟨55024558851442426308800387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36683039234294950872533591 55024558851442426308800387)
          ·
            refine ⟨82536838277163639463200581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55024558851442426308800387 82536838277163639463200581)
            ·
              refine ⟨15475657176968182399350109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82536838277163639463200581 15475657176968182399350109)
              ·
                refine ⟨5803371441363068399756291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15475657176968182399350109 5803371441363068399756291)
                ·
                  refine ⟨8705057162044602599634437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5803371441363068399756291 8705057162044602599634437)
                  ·
                    refine ⟨1632198217883362987431457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8705057162044602599634437 1632198217883362987431457)
                    ·
                      refine ⟨1224148663412522240573593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632198217883362987431457 1224148663412522240573593)
                      ·
                        rfl

theorem cell23_2384021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_2384021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384021 prefixEnd_2384021 := by exact prefixLift 2384021
  have htrace : WordTrace (prefixWord ++ tailWord_2384021) baseStart_2384021 baseEnd_2384021 := by
    simpa [prefixWord, tailWord_2384021, baseEnd_2384021] using wordTrace_append hprefix tailTrace_2384021
  have hstable : (prefixWord ++ tailWord_2384021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384021).length < 2 ^ (prefixWord ++ tailWord_2384021).sum := by decide
  have hdescent : baseEnd_2384021 < baseStart_2384021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384055 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 2, 2, 2]
def baseStart_2384055 : Nat := 118140960795 + 2384055 * 2 ^ 59
def prefixEnd_2384055 : Nat := 4983230072969 + 3 ^ 40 * 2384055 * 2
def baseEnd_2384055 : Nat := 1224166121754775107548437

theorem tailTrace_2384055 : CollatzResearch.WordTrace tailWord_2384055 prefixEnd_2384055 1224166121754775107548437 := by
  unfold tailWord_2384055
  simp only [CollatzResearch.WordTrace]
  refine ⟨86953629377983374023113619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57969086251988916015409079 86953629377983374023113619)
  ·
    refine ⟨130430444066975061034670429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86953629377983374023113619 130430444066975061034670429)
    ·
      refine ⟨48911416525115647888001411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130430444066975061034670429 48911416525115647888001411)
      ·
        refine ⟨73367124787673471832002117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48911416525115647888001411 73367124787673471832002117)
        ·
          refine ⟨13756335897688775968500397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73367124787673471832002117 13756335897688775968500397)
          ·
            refine ⟨5158625961633290988187649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13756335897688775968500397 5158625961633290988187649)
            ·
              refine ⟨3868969471224968241140737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5158625961633290988187649 3868969471224968241140737)
              ·
                refine ⟨2901727103418726180855553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3868969471224968241140737 2901727103418726180855553)
                ·
                  refine ⟨2176295327564044635641665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2901727103418726180855553 2176295327564044635641665)
                  ·
                    refine ⟨1632221495673033476731249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2176295327564044635641665 1632221495673033476731249)
                    ·
                      refine ⟨1224166121754775107548437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632221495673033476731249 1224166121754775107548437)
                      ·
                        rfl

theorem cell23_2384055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_2384055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384055 prefixEnd_2384055 := by exact prefixLift 2384055
  have htrace : WordTrace (prefixWord ++ tailWord_2384055) baseStart_2384055 baseEnd_2384055 := by
    simpa [prefixWord, tailWord_2384055, baseEnd_2384055] using wordTrace_append hprefix tailTrace_2384055
  have hstable : (prefixWord ++ tailWord_2384055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384055).length < 2 ^ (prefixWord ++ tailWord_2384055).sum := by decide
  have hdescent : baseEnd_2384055 < baseStart_2384055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384074 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_2384074 : Nat := 118140960795 + 2384074 * 2 ^ 59
def prefixEnd_2384074 : Nat := 4983230072969 + 3 ^ 40 * 2384074 * 2
def baseEnd_2384074 : Nat := 408058625962403511070283

theorem tailTrace_2384074 : CollatzResearch.WordTrace tailWord_2384074 prefixEnd_2384074 408058625962403511070283 := by
  unfold tailWord_2384074
  simp only [CollatzResearch.WordTrace]
  refine ⟨21738580591228635067013819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57969548243276360178703517 21738580591228635067013819)
  ·
    refine ⟨32607870886842952600520729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21738580591228635067013819 32607870886842952600520729)
    ·
      refine ⟨24455903165132214450390547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32607870886842952600520729 24455903165132214450390547)
      ·
        refine ⟨36683854747698321675585821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24455903165132214450390547 36683854747698321675585821)
        ·
          refine ⟨13756445530386870628344683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36683854747698321675585821 13756445530386870628344683)
          ·
            refine ⟨20634668295580305942517025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13756445530386870628344683 20634668295580305942517025)
            ·
              refine ⟨15476001221685229456887769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20634668295580305942517025 15476001221685229456887769)
              ·
                refine ⟨11607000916263922092665827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15476001221685229456887769 11607000916263922092665827)
                ·
                  refine ⟨17410501374395883138998741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11607000916263922092665827 17410501374395883138998741)
                  ·
                    refine ⟨408058625962403511070283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17410501374395883138998741 408058625962403511070283)
                    ·
                      rfl

theorem cell23_2384074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_2384074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384074 prefixEnd_2384074 := by exact prefixLift 2384074
  have htrace : WordTrace (prefixWord ++ tailWord_2384074) baseStart_2384074 baseEnd_2384074 := by
    simpa [prefixWord, tailWord_2384074, baseEnd_2384074] using wordTrace_append hprefix tailTrace_2384074
  have hstable : (prefixWord ++ tailWord_2384074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384074).length < 2 ^ (prefixWord ++ tailWord_2384074).sum := by decide
  have hdescent : baseEnd_2384074 < baseStart_2384074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384181 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2384181 : Nat := 118140960795 + 2384181 * 2 ^ 59
def prefixEnd_2384181 : Nat := 4983230072969 + 3 ^ 40 * 2384181 * 2
def baseEnd_2384181 : Nat := 408076940105747204857619

theorem tailTrace_2384181 : CollatzResearch.WordTrace tailWord_2384181 prefixEnd_2384181 408076940105747204857619 := by
  unfold tailWord_2384181
  simp only [CollatzResearch.WordTrace]
  refine ⟨86958224975526897542200397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57972149983684598361466931 86958224975526897542200397)
  ·
    refine ⟨32609334365822586578325149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86958224975526897542200397 32609334365822586578325149)
    ·
      refine ⟨12228500387183469966871931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32609334365822586578325149 12228500387183469966871931)
      ·
        refine ⟨18342750580775204950307897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12228500387183469966871931 18342750580775204950307897)
        ·
          refine ⟨13757062935581403712730923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18342750580775204950307897 13757062935581403712730923)
          ·
            refine ⟨20635594403372105569096385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13757062935581403712730923 20635594403372105569096385)
            ·
              refine ⟨15476695802529079176822289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20635594403372105569096385 15476695802529079176822289)
              ·
                refine ⟨11607521851896809382616717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15476695802529079176822289 11607521851896809382616717)
                ·
                  refine ⟨4352820694461303518481269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11607521851896809382616717 4352820694461303518481269)
                  ·
                    refine ⟨408076940105747204857619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4352820694461303518481269 408076940105747204857619)
                    ·
                      rfl

theorem cell23_2384181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2384181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384181 prefixEnd_2384181 := by exact prefixLift 2384181
  have htrace : WordTrace (prefixWord ++ tailWord_2384181) baseStart_2384181 baseEnd_2384181 := by
    simpa [prefixWord, tailWord_2384181, baseEnd_2384181] using wordTrace_append hprefix tailTrace_2384181
  have hstable : (prefixWord ++ tailWord_2384181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384181).length < 2 ^ (prefixWord ++ tailWord_2384181).sum := by decide
  have hdescent : baseEnd_2384181 < baseStart_2384181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384185 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 6]
def baseStart_2384185 : Nat := 118140960795 + 2384185 * 2 ^ 59
def prefixEnd_2384185 : Nat := 4983230072969 + 3 ^ 40 * 2384185 * 2
def baseEnd_2384185 : Nat := 136025874915539955435871

theorem tailTrace_2384185 : CollatzResearch.WordTrace tailWord_2384185 prefixEnd_2384185 136025874915539955435871 := by
  unfold tailWord_2384185
  simp only [CollatzResearch.WordTrace]
  refine ⟨86958370867512406225346009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57972247245008270816897339 86958370867512406225346009)
  ·
    refine ⟨65218778150634304669009507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86958370867512406225346009 65218778150634304669009507)
    ·
      refine ⟨97828167225951457003514261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65218778150634304669009507 97828167225951457003514261)
      ·
        refine ⟨4585695338716474547039731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97828167225951457003514261 4585695338716474547039731)
        ·
          refine ⟨6878543008074711820559597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4585695338716474547039731 6878543008074711820559597)
          ·
            refine ⟨2579453628028016932709849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6878543008074711820559597 2579453628028016932709849)
            ·
              refine ⟨1934590221021012699532387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579453628028016932709849 1934590221021012699532387)
              ·
                refine ⟨2901885331531519049298581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934590221021012699532387 2901885331531519049298581)
                ·
                  refine ⟨136025874915539955435871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2901885331531519049298581 136025874915539955435871)
                  ·
                    rfl

theorem cell23_2384185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 6].length) (baseStart_2384185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384185 prefixEnd_2384185 := by exact prefixLift 2384185
  have htrace : WordTrace (prefixWord ++ tailWord_2384185) baseStart_2384185 baseEnd_2384185 := by
    simpa [prefixWord, tailWord_2384185, baseEnd_2384185] using wordTrace_append hprefix tailTrace_2384185
  have hstable : (prefixWord ++ tailWord_2384185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384185).length < 2 ^ (prefixWord ++ tailWord_2384185).sum := by decide
  have hdescent : baseEnd_2384185 < baseStart_2384185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384188 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_2384188 : Nat := 118140960795 + 2384188 * 2 ^ 59
def prefixEnd_2384188 : Nat := 4983230072969 + 3 ^ 40 * 2384188 * 2
def baseEnd_2384188 : Nat := 1224234414681823087185325

theorem tailTrace_2384188 : CollatzResearch.WordTrace tailWord_2384188 prefixEnd_2384188 1224234414681823087185325 := by
  unfold tailWord_2384188
  simp only [CollatzResearch.WordTrace]
  refine ⟨43479240143250768868852609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57972320191001025158470145 43479240143250768868852609)
  ·
    refine ⟨32609430107438076651639457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43479240143250768868852609 32609430107438076651639457)
    ·
      refine ⟨24457072580578557488729593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32609430107438076651639457 24457072580578557488729593)
      ·
        refine ⟨18342804435433918116547195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24457072580578557488729593 18342804435433918116547195)
        ·
          refine ⟨27514206653150877174820793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18342804435433918116547195 27514206653150877174820793)
          ·
            refine ⟨20635654989863157881115595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27514206653150877174820793 20635654989863157881115595)
            ·
              refine ⟨30953482484794736821673393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20635654989863157881115595 30953482484794736821673393)
              ·
                refine ⟨23215111863596052616255045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30953482484794736821673393 23215111863596052616255045)
                ·
                  refine ⟨4352833474424259865547821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23215111863596052616255045 4352833474424259865547821)
                  ·
                    refine ⟨1632312552909097449580433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4352833474424259865547821 1632312552909097449580433)
                    ·
                      refine ⟨1224234414681823087185325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632312552909097449580433 1224234414681823087185325)
                      ·
                        rfl

theorem cell23_2384188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_2384188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384188 prefixEnd_2384188 := by exact prefixLift 2384188
  have htrace : WordTrace (prefixWord ++ tailWord_2384188) baseStart_2384188 baseEnd_2384188 := by
    simpa [prefixWord, tailWord_2384188, baseEnd_2384188] using wordTrace_append hprefix tailTrace_2384188
  have hstable : (prefixWord ++ tailWord_2384188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384188).length < 2 ^ (prefixWord ++ tailWord_2384188).sum := by decide
  have hdescent : baseEnd_2384188 < baseStart_2384188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384211 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 4, 4]
def baseStart_2384211 : Nat := 118140960795 + 2384211 * 2 ^ 59
def prefixEnd_2384211 : Nat := 4983230072969 + 3 ^ 40 * 2384211 * 2
def baseEnd_2384211 : Nat := 408082074912292165732573

theorem tailTrace_2384211 : CollatzResearch.WordTrace tailWord_2384211 prefixEnd_2384211 408082074912292165732573 := by
  unfold tailWord_2384211
  simp only [CollatzResearch.WordTrace]
  refine ⟨86959319165418212665792487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57972879443612141777194991 86959319165418212665792487)
  ·
    refine ⟨130438978748127318998688731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86959319165418212665792487 130438978748127318998688731)
    ·
      refine ⟨195658468122190978498033097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130438978748127318998688731 195658468122190978498033097)
      ·
        refine ⟨146743851091643233873524823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195658468122190978498033097 146743851091643233873524823)
        ·
          refine ⟨220115776637464850810287235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146743851091643233873524823 220115776637464850810287235)
          ·
            refine ⟨330173664956197276215430853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220115776637464850810287235 330173664956197276215430853)
            ·
              refine ⟨61907562179286989290393285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 330173664956197276215430853 61907562179286989290393285)
              ·
                refine ⟨11607667908616310491948741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61907562179286989290393285 11607667908616310491948741)
                ·
                  refine ⟨2176437732865558217240389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11607667908616310491948741 2176437732865558217240389)
                  ·
                    refine ⟨408082074912292165732573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2176437732865558217240389 408082074912292165732573)
                    ·
                      rfl

theorem cell23_2384211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 4].length) (baseStart_2384211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384211 prefixEnd_2384211 := by exact prefixLift 2384211
  have htrace : WordTrace (prefixWord ++ tailWord_2384211) baseStart_2384211 baseEnd_2384211 := by
    simpa [prefixWord, tailWord_2384211, baseEnd_2384211] using wordTrace_append hprefix tailTrace_2384211
  have hstable : (prefixWord ++ tailWord_2384211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384211).length < 2 ^ (prefixWord ++ tailWord_2384211).sum := by decide
  have hdescent : baseEnd_2384211 < baseStart_2384211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384224 : List Nat := [2, 1, 1, 3, 16]
def baseStart_2384224 : Nat := 118140960795 + 2384224 * 2 ^ 59
def prefixEnd_2384224 : Nat := 4983230072969 + 3 ^ 40 * 2384224 * 2
def baseEnd_2384224 : Nat := 1679359259239211174671

theorem tailTrace_2384224 : CollatzResearch.WordTrace tailWord_2384224 prefixEnd_2384224 1679359259239211174671 := by
  unfold tailWord_2384224
  simp only [CollatzResearch.WordTrace]
  refine ⟨43479896657185557943007863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57973195542914077257343817 43479896657185557943007863)
  ·
    refine ⟨65219844985778336914511795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43479896657185557943007863 65219844985778336914511795)
    ·
      refine ⟨97829767478667505371767693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65219844985778336914511795 97829767478667505371767693)
      ·
        refine ⟨36686162804500314514412885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97829767478667505371767693 36686162804500314514412885)
        ·
          refine ⟨1679359259239211174671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 36686162804500314514412885 1679359259239211174671)
          ·
            rfl

theorem cell23_2384224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 16].length) (baseStart_2384224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384224 prefixEnd_2384224 := by exact prefixLift 2384224
  have htrace : WordTrace (prefixWord ++ tailWord_2384224) baseStart_2384224 baseEnd_2384224 := by
    simpa [prefixWord, tailWord_2384224, baseEnd_2384224] using wordTrace_append hprefix tailTrace_2384224
  have hstable : (prefixWord ++ tailWord_2384224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384224).length < 2 ^ (prefixWord ++ tailWord_2384224).sum := by decide
  have hdescent : baseEnd_2384224 < baseStart_2384224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384229 : List Nat := [1, 3, 1, 3, 1, 5, 2, 2, 1, 1, 3]
def baseStart_2384229 : Nat := 118140960795 + 2384229 * 2 ^ 59
def prefixEnd_2384229 : Nat := 4983230072969 + 3 ^ 40 * 2384229 * 2
def baseEnd_2384229 : Nat := 1224255467388657426772637

theorem tailTrace_2384229 : CollatzResearch.WordTrace tailWord_2384229 prefixEnd_2384229 1224255467388657426772637 := by
  unfold tailWord_2384229
  simp only [CollatzResearch.WordTrace]
  refine ⟨86959975679353001739947741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57973317119568667826631827 86959975679353001739947741)
  ·
    refine ⟨32609990879757375652480403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86959975679353001739947741 32609990879757375652480403)
    ·
      refine ⟨48914986319636063478720605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32609990879757375652480403 48914986319636063478720605)
      ·
        refine ⟨18343119869863523804520227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48914986319636063478720605 18343119869863523804520227)
        ·
          refine ⟨27514679804795285706780341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18343119869863523804520227 27514679804795285706780341)
          ·
            refine ⟨2579501231699558035010657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27514679804795285706780341 2579501231699558035010657)
            ·
              refine ⟨1934625923774668526257993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579501231699558035010657 1934625923774668526257993)
              ·
                refine ⟨1450969442831001394693495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1934625923774668526257993 1450969442831001394693495)
                ·
                  refine ⟨2176454164246502092040243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450969442831001394693495 2176454164246502092040243)
                  ·
                    refine ⟨3264681246369753138060365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2176454164246502092040243 3264681246369753138060365)
                    ·
                      refine ⟨1224255467388657426772637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3264681246369753138060365 1224255467388657426772637)
                      ·
                        rfl

theorem cell23_2384229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_2384229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384229 prefixEnd_2384229 := by exact prefixLift 2384229
  have htrace : WordTrace (prefixWord ++ tailWord_2384229) baseStart_2384229 baseEnd_2384229 := by
    simpa [prefixWord, tailWord_2384229, baseEnd_2384229] using wordTrace_append hprefix tailTrace_2384229
  have hstable : (prefixWord ++ tailWord_2384229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384229).length < 2 ^ (prefixWord ++ tailWord_2384229).sum := by decide
  have hdescent : baseEnd_2384229 < baseStart_2384229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384245 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2384245 : Nat := 118140960795 + 2384245 * 2 ^ 59
def prefixEnd_2384245 : Nat := 4983230072969 + 3 ^ 40 * 2384245 * 2
def baseEnd_2384245 : Nat := 408087894359709788057521

theorem tailTrace_2384245 : CollatzResearch.WordTrace tailWord_2384245 prefixEnd_2384245 408087894359709788057521 := by
  unfold tailWord_2384245
  simp only [CollatzResearch.WordTrace]
  refine ⟨86960559247295036472530189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57973706164863357648353459 86960559247295036472530189)
  ·
    refine ⟨32610209717735638677198821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86960559247295036472530189 32610209717735638677198821)
    ·
      refine ⟨6114414322075432251974779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32610209717735638677198821 6114414322075432251974779)
      ·
        refine ⟨9171621483113148377962169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6114414322075432251974779 9171621483113148377962169)
        ·
          refine ⟨6878716112334861283471627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9171621483113148377962169 6878716112334861283471627)
          ·
            refine ⟨10318074168502291925207441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6878716112334861283471627 10318074168502291925207441)
            ·
              refine ⟨7738555626376718943905581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10318074168502291925207441 7738555626376718943905581)
              ·
                refine ⟨2901958359891269603964593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7738555626376718943905581 2901958359891269603964593)
                ·
                  refine ⟨2176468769918452202973445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2901958359891269603964593 2176468769918452202973445)
                  ·
                    refine ⟨408087894359709788057521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2176468769918452202973445 408087894359709788057521)
                    ·
                      rfl

theorem cell23_2384245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2384245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384245 prefixEnd_2384245 := by exact prefixLift 2384245
  have htrace : WordTrace (prefixWord ++ tailWord_2384245) baseStart_2384245 baseEnd_2384245 := by
    simpa [prefixWord, tailWord_2384245, baseEnd_2384245] using wordTrace_append hprefix tailTrace_2384245
  have hstable : (prefixWord ++ tailWord_2384245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384245).length < 2 ^ (prefixWord ++ tailWord_2384245).sum := by decide
  have hdescent : baseEnd_2384245 < baseStart_2384245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384268 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_2384268 : Nat := 118140960795 + 2384268 * 2 ^ 59
def prefixEnd_2384268 : Nat := 4983230072969 + 3 ^ 40 * 2384268 * 2
def baseEnd_2384268 : Nat := 1224275493134182774184957

theorem tailTrace_2384268 : CollatzResearch.WordTrace tailWord_2384268 prefixEnd_2384268 1224275493134182774184957 := by
  unfold tailWord_2384268
  simp only [CollatzResearch.WordTrace]
  refine ⟨43480699063105855700308729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57974265417474474267078305 43480699063105855700308729)
  ·
    refine ⟨32610524297329391775231547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43480699063105855700308729 32610524297329391775231547)
    ·
      refine ⟨48915786445994087662847321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32610524297329391775231547 48915786445994087662847321)
      ·
        refine ⟨36686839834495565747135491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48915786445994087662847321 36686839834495565747135491)
        ·
          refine ⟨55030259751743348620703237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36686839834495565747135491 55030259751743348620703237)
          ·
            refine ⟨10318173703451877866381857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55030259751743348620703237 10318173703451877866381857)
            ·
              refine ⟨7738630277588908399786393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10318173703451877866381857 7738630277588908399786393)
              ·
                refine ⟨5803972708191681299839795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7738630277588908399786393 5803972708191681299839795)
                ·
                  refine ⟨8705959062287521949759693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5803972708191681299839795 8705959062287521949759693)
                  ·
                    refine ⟨3264734648357820731159885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8705959062287521949759693 3264734648357820731159885)
                    ·
                      refine ⟨1224275493134182774184957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3264734648357820731159885 1224275493134182774184957)
                      ·
                        rfl

theorem cell23_2384268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_2384268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384268 prefixEnd_2384268 := by exact prefixLift 2384268
  have htrace : WordTrace (prefixWord ++ tailWord_2384268) baseStart_2384268 baseEnd_2384268 := by
    simpa [prefixWord, tailWord_2384268, baseEnd_2384268] using wordTrace_append hprefix tailTrace_2384268
  have hstable : (prefixWord ++ tailWord_2384268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384268).length < 2 ^ (prefixWord ++ tailWord_2384268).sum := by decide
  have hdescent : baseEnd_2384268 < baseStart_2384268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384286 : List Nat := [4, 3, 1, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_2384286 : Nat := 118140960795 + 2384286 * 2 ^ 59
def prefixEnd_2384286 : Nat := 4983230072969 + 3 ^ 40 * 2384286 * 2
def baseEnd_2384286 : Nat := 1224284735785963703759875

theorem tailTrace_2384286 : CollatzResearch.WordTrace tailWord_2384286 prefixEnd_2384286 1224284735785963703759875 := by
  unfold tailWord_2384286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10870256830018312559346589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57974703093431000316515141 10870256830018312559346589)
  ·
    refine ⟨4076346311256867209754971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10870256830018312559346589 4076346311256867209754971)
    ·
      refine ⟨6114519466885300814632457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076346311256867209754971 6114519466885300814632457)
      ·
        refine ⟨4585889600163975610974343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6114519466885300814632457 4585889600163975610974343)
        ·
          refine ⟨6878834400245963416461515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4585889600163975610974343 6878834400245963416461515)
          ·
            refine ⟨10318251600368945124692273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6878834400245963416461515 10318251600368945124692273)
            ·
              refine ⟨7738688700276708843519205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10318251600368945124692273 7738688700276708843519205)
              ·
                refine ⟨1451004131301882908159851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7738688700276708843519205 1451004131301882908159851)
                ·
                  refine ⟨2176506196952824362239777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451004131301882908159851 2176506196952824362239777)
                  ·
                    refine ⟨1632379647714618271679833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2176506196952824362239777 1632379647714618271679833)
                    ·
                      refine ⟨1224284735785963703759875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632379647714618271679833 1224284735785963703759875)
                      ·
                        rfl

theorem cell23_2384286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_2384286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384286 prefixEnd_2384286 := by exact prefixLift 2384286
  have htrace : WordTrace (prefixWord ++ tailWord_2384286) baseStart_2384286 baseEnd_2384286 := by
    simpa [prefixWord, tailWord_2384286, baseEnd_2384286] using wordTrace_append hprefix tailTrace_2384286
  have hstable : (prefixWord ++ tailWord_2384286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384286).length < 2 ^ (prefixWord ++ tailWord_2384286).sum := by decide
  have hdescent : baseEnd_2384286 < baseStart_2384286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384328 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_2384328 : Nat := 118140960795 + 2384328 * 2 ^ 59
def prefixEnd_2384328 : Nat := 4983230072969 + 3 ^ 40 * 2384328 * 2
def baseEnd_2384328 : Nat := 1224306301973452539434681

theorem tailTrace_2384328 : CollatzResearch.WordTrace tailWord_2384328 prefixEnd_2384328 1224306301973452539434681 := by
  unfold tailWord_2384328
  simp only [CollatzResearch.WordTrace]
  refine ⟨43481793252997170823900819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57975724337329561098534425 43481793252997170823900819)
  ·
    refine ⟨65222689879495756235851229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43481793252997170823900819 65222689879495756235851229)
    ·
      refine ⟨24458508704810908588444211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65222689879495756235851229 24458508704810908588444211)
      ·
        refine ⟨36687763057216362882666317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24458508704810908588444211 36687763057216362882666317)
        ·
          refine ⟨13757911146456136080999869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36687763057216362882666317 13757911146456136080999869)
          ·
            refine ⟨5159216679921051030374951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13757911146456136080999869 5159216679921051030374951)
            ·
              refine ⟨7738825019881576545562427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159216679921051030374951 7738825019881576545562427)
              ·
                refine ⟨11608237529822364818343641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7738825019881576545562427 11608237529822364818343641)
                ·
                  refine ⟨8706178147366773613757731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11608237529822364818343641 8706178147366773613757731)
                  ·
                    refine ⟨13059267221050160420636597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8706178147366773613757731 13059267221050160420636597)
                    ·
                      refine ⟨1224306301973452539434681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13059267221050160420636597 1224306301973452539434681)
                      ·
                        rfl

theorem cell23_2384328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_2384328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384328 prefixEnd_2384328 := by exact prefixLift 2384328
  have htrace : WordTrace (prefixWord ++ tailWord_2384328) baseStart_2384328 baseEnd_2384328 := by
    simpa [prefixWord, tailWord_2384328, baseEnd_2384328] using wordTrace_append hprefix tailTrace_2384328
  have hstable : (prefixWord ++ tailWord_2384328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384328).length < 2 ^ (prefixWord ++ tailWord_2384328).sum := by decide
  have hdescent : baseEnd_2384328 < baseStart_2384328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384361 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 1, 7]
def baseStart_2384361 : Nat := 118140960795 + 2384361 * 2 ^ 59
def prefixEnd_2384361 : Nat := 4983230072969 + 3 ^ 40 * 2384361 * 2
def baseEnd_2384361 : Nat := 408107748945016970107343

theorem tailTrace_2384361 : CollatzResearch.WordTrace tailWord_2384361 prefixEnd_2384361 408107748945016970107343 := by
  unfold tailWord_2384361
  simp only [CollatzResearch.WordTrace]
  refine ⟨86964790114874788283752937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57976526743249858855835291 86964790114874788283752937)
  ·
    refine ⟨65223592586156091212814703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86964790114874788283752937 65223592586156091212814703)
    ·
      refine ⟨97835388879234136819222055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65223592586156091212814703 97835388879234136819222055)
      ·
        refine ⟨146753083318851205228833083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97835388879234136819222055 146753083318851205228833083)
        ·
          refine ⟨220129624978276807843249625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146753083318851205228833083 220129624978276807843249625)
          ·
            refine ⟨165097218733707605882437219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220129624978276807843249625 165097218733707605882437219)
            ·
              refine ⟨247645828100561408823655829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165097218733707605882437219 247645828100561408823655829)
              ·
                refine ⟨11608398192213816038608867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 247645828100561408823655829 11608398192213816038608867)
                ·
                  refine ⟨17412597288320724057913301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11608398192213816038608867 17412597288320724057913301)
                  ·
                    refine ⟨408107748945016970107343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17412597288320724057913301 408107748945016970107343)
                    ·
                      rfl

theorem cell23_2384361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_2384361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384361 prefixEnd_2384361 := by exact prefixLift 2384361
  have htrace : WordTrace (prefixWord ++ tailWord_2384361) baseStart_2384361 baseEnd_2384361 := by
    simpa [prefixWord, tailWord_2384361, baseEnd_2384361] using wordTrace_append hprefix tailTrace_2384361
  have hstable : (prefixWord ++ tailWord_2384361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384361).length < 2 ^ (prefixWord ++ tailWord_2384361).sum := by decide
  have hdescent : baseEnd_2384361 < baseStart_2384361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384371 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 7]
def baseStart_2384371 : Nat := 118140960795 + 2384371 * 2 ^ 59
def prefixEnd_2384371 : Nat := 4983230072969 + 3 ^ 40 * 2384371 * 2
def baseEnd_2384371 : Nat := 1224328381641595871196983

theorem tailTrace_2384371 : CollatzResearch.WordTrace tailWord_2384371 prefixEnd_2384371 1224328381641595871196983 := by
  unfold tailWord_2384371
  simp only [CollatzResearch.WordTrace]
  refine ⟨86965154844838559991616967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57976769896559039994411311 86965154844838559991616967)
  ·
    refine ⟨130447732267257839987425451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86965154844838559991616967 130447732267257839987425451)
    ·
      refine ⟨195671598400886759981138177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130447732267257839987425451 195671598400886759981138177)
      ·
        refine ⟨146753698800665069985853633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195671598400886759981138177 146753698800665069985853633)
        ·
          refine ⟨110065274100498802489390225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146753698800665069985853633 110065274100498802489390225)
          ·
            refine ⟨82548955575374101867042669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110065274100498802489390225 82548955575374101867042669)
            ·
              refine ⟨30955858340765288200141001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82548955575374101867042669 30955858340765288200141001)
              ·
                refine ⟨23216893755573966150105751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30955858340765288200141001 23216893755573966150105751)
                ·
                  refine ⟨34825340633360949225158627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23216893755573966150105751 34825340633360949225158627)
                  ·
                    refine ⟨52238010950041423837737941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34825340633360949225158627 52238010950041423837737941)
                    ·
                      refine ⟨1224328381641595871196983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52238010950041423837737941 1224328381641595871196983)
                      ·
                        rfl

theorem cell23_2384371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_2384371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384371 prefixEnd_2384371 := by exact prefixLift 2384371
  have htrace : WordTrace (prefixWord ++ tailWord_2384371) baseStart_2384371 baseEnd_2384371 := by
    simpa [prefixWord, tailWord_2384371, baseEnd_2384371] using wordTrace_append hprefix tailTrace_2384371
  have hstable : (prefixWord ++ tailWord_2384371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384371).length < 2 ^ (prefixWord ++ tailWord_2384371).sum := by decide
  have hdescent : baseEnd_2384371 < baseStart_2384371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384429 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2384429 : Nat := 118140960795 + 2384429 * 2 ^ 59
def prefixEnd_2384429 : Nat := 4983230072969 + 3 ^ 40 * 2384429 * 2
def baseEnd_2384429 : Nat := 408119387839852214757239

theorem tailTrace_2384429 : CollatzResearch.WordTrace tailWord_2384429 prefixEnd_2384429 408119387839852214757239 := by
  unfold tailWord_2384429
  simp only [CollatzResearch.WordTrace]
  refine ⟨86967270278628435897228341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57978180185752290598152227 86967270278628435897228341)
  ·
    refine ⟨8153181588621415865365157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86967270278628435897228341 8153181588621415865365157)
    ·
      refine ⟨1528721547866515474755967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8153181588621415865365157 1528721547866515474755967)
      ·
        refine ⟨2293082321799773212133951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1528721547866515474755967 2293082321799773212133951)
        ·
          refine ⟨3439623482699659818200927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293082321799773212133951 3439623482699659818200927)
          ·
            refine ⟨5159435224049489727301391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439623482699659818200927 5159435224049489727301391)
            ·
              refine ⟨7739152836074234590952087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159435224049489727301391 7739152836074234590952087)
              ·
                refine ⟨11608729254111351886428131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7739152836074234590952087 11608729254111351886428131)
                ·
                  refine ⟨17413093881167027829642197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11608729254111351886428131 17413093881167027829642197)
                  ·
                    refine ⟨408119387839852214757239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17413093881167027829642197 408119387839852214757239)
                    ·
                      rfl

theorem cell23_2384429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2384429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384429 prefixEnd_2384429 := by exact prefixLift 2384429
  have htrace : WordTrace (prefixWord ++ tailWord_2384429) baseStart_2384429 baseEnd_2384429 := by
    simpa [prefixWord, tailWord_2384429, baseEnd_2384429] using wordTrace_append hprefix tailTrace_2384429
  have hstable : (prefixWord ++ tailWord_2384429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384429).length < 2 ^ (prefixWord ++ tailWord_2384429).sum := by decide
  have hdescent : baseEnd_2384429 < baseStart_2384429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384442 : List Nat := [3, 1, 1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_2384442 : Nat := 118140960795 + 2384442 * 2 ^ 59
def prefixEnd_2384442 : Nat := 4983230072969 + 3 ^ 40 * 2384442 * 2
def baseEnd_2384442 : Nat := 408121612922688364469719

theorem tailTrace_2384442 : CollatzResearch.WordTrace tailWord_2384442 prefixEnd_2384442 408121612922688364469719 := by
  unfold tailWord_2384442
  simp only [CollatzResearch.WordTrace]
  refine ⟨21741936106895334779362895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57978496285054226078301053 21741936106895334779362895)
  ·
    refine ⟨32612904160343002169044343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21741936106895334779362895 32612904160343002169044343)
    ·
      refine ⟨48919356240514503253566515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32612904160343002169044343 48919356240514503253566515)
      ·
        refine ⟨73379034360771754880349773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48919356240514503253566515 73379034360771754880349773)
        ·
          refine ⟨27517137885289408080131165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73379034360771754880349773 27517137885289408080131165)
          ·
            refine ⟨10318926706983528030049187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27517137885289408080131165 10318926706983528030049187)
            ·
              refine ⟨15478390060475292045073781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10318926706983528030049187 15478390060475292045073781)
              ·
                refine ⟨1451099068169558629225667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15478390060475292045073781 1451099068169558629225667)
                ·
                  refine ⟨2176648602254337943838501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451099068169558629225667 2176648602254337943838501)
                  ·
                    refine ⟨408121612922688364469719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2176648602254337943838501 408121612922688364469719)
                    ·
                      rfl

theorem cell23_2384442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_2384442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384442 prefixEnd_2384442 := by exact prefixLift 2384442
  have htrace : WordTrace (prefixWord ++ tailWord_2384442) baseStart_2384442 baseEnd_2384442 := by
    simpa [prefixWord, tailWord_2384442, baseEnd_2384442] using wordTrace_append hprefix tailTrace_2384442
  have hstable : (prefixWord ++ tailWord_2384442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384442).length < 2 ^ (prefixWord ++ tailWord_2384442).sum := by decide
  have hdescent : baseEnd_2384442 < baseStart_2384442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384455 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 6]
def baseStart_2384455 : Nat := 118140960795 + 2384455 * 2 ^ 59
def prefixEnd_2384455 : Nat := 4983230072969 + 3 ^ 40 * 2384455 * 2
def baseEnd_2384455 : Nat := 136041279335174838060733

theorem tailTrace_2384455 : CollatzResearch.WordTrace tailWord_2384455 prefixEnd_2384455 136041279335174838060733 := by
  unfold tailWord_2384455
  simp only [CollatzResearch.WordTrace]
  refine ⟨86968218576534242337674819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57978812384356161558449879 86968218576534242337674819)
  ·
    refine ⟨130452327864801363506512229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86968218576534242337674819 130452327864801363506512229)
    ·
      refine ⟨24459811474650255657471043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130452327864801363506512229 24459811474650255657471043)
      ·
        refine ⟨36689717211975383486206565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24459811474650255657471043 36689717211975383486206565)
        ·
          refine ⟨6879321977245384403663731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36689717211975383486206565 6879321977245384403663731)
          ·
            refine ⟨10318982965868076605495597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6879321977245384403663731 10318982965868076605495597)
            ·
              refine ⟨3869618612200528727060849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10318982965868076605495597 3869618612200528727060849)
              ·
                refine ⟨2902213959150396545295637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3869618612200528727060849 2902213959150396545295637)
                ·
                  refine ⟨136041279335174838060733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2902213959150396545295637 136041279335174838060733)
                  ·
                    rfl

theorem cell23_2384455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 6].length) (baseStart_2384455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384455 prefixEnd_2384455 := by exact prefixLift 2384455
  have htrace : WordTrace (prefixWord ++ tailWord_2384455) baseStart_2384455 baseEnd_2384455 := by
    simpa [prefixWord, tailWord_2384455, baseEnd_2384455] using wordTrace_append hprefix tailTrace_2384455
  have hstable : (prefixWord ++ tailWord_2384455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384455).length < 2 ^ (prefixWord ++ tailWord_2384455).sum := by decide
  have hdescent : baseEnd_2384455 < baseStart_2384455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384458 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_2384458 : Nat := 118140960795 + 2384458 * 2 ^ 59
def prefixEnd_2384458 : Nat := 4983230072969 + 3 ^ 40 * 2384458 * 2
def baseEnd_2384458 : Nat := 1224373054458537030809083

theorem tailTrace_2384458 : CollatzResearch.WordTrace tailWord_2384458 prefixEnd_2384458 1224373054458537030809083 := by
  unfold tailWord_2384458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21742081998880843462508507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57978885330348915900022685 21742081998880843462508507)
  ·
    refine ⟨32613122998321265193762761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21742081998880843462508507 32613122998321265193762761)
    ·
      refine ⟨24459842248740948895322071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32613122998321265193762761 24459842248740948895322071)
      ·
        refine ⟨36689763373111423342983107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24459842248740948895322071 36689763373111423342983107)
        ·
          refine ⟨55034645059667135014474661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36689763373111423342983107 55034645059667135014474661)
          ·
            refine ⟨10318995948687587815213999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55034645059667135014474661 10318995948687587815213999)
            ·
              refine ⟨15478493923031381722820999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10318995948687587815213999 15478493923031381722820999)
              ·
                refine ⟨23217740884547072584231499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15478493923031381722820999 23217740884547072584231499)
                ·
                  refine ⟨34826611326820608876347249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23217740884547072584231499 34826611326820608876347249)
                  ·
                    refine ⟨26119958495115456657260437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34826611326820608876347249 26119958495115456657260437)
                    ·
                      refine ⟨1224373054458537030809083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26119958495115456657260437 1224373054458537030809083)
                      ·
                        rfl

theorem cell23_2384458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_2384458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384458 prefixEnd_2384458 := by exact prefixLift 2384458
  have htrace : WordTrace (prefixWord ++ tailWord_2384458) baseStart_2384458 baseEnd_2384458 := by
    simpa [prefixWord, tailWord_2384458, baseEnd_2384458] using wordTrace_append hprefix tailTrace_2384458
  have hstable : (prefixWord ++ tailWord_2384458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384458).length < 2 ^ (prefixWord ++ tailWord_2384458).sum := by decide
  have hdescent : baseEnd_2384458 < baseStart_2384458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384509 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_2384509 : Nat := 118140960795 + 2384509 * 2 ^ 59
def prefixEnd_2384509 : Nat := 4983230072969 + 3 ^ 40 * 2384509 * 2
def baseEnd_2384509 : Nat := 1224399241971916331271349

theorem tailTrace_2384509 : CollatzResearch.WordTrace tailWord_2384509 prefixEnd_2384509 1224399241971916331271349 := by
  unfold tailWord_2384509
  simp only [CollatzResearch.WordTrace]
  refine ⟨86970188118338609560140581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57980125412225739706760387 86970188118338609560140581)
  ·
    refine ⟨16306910272188489292526359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86970188118338609560140581 16306910272188489292526359)
    ·
      refine ⟨24460365408282733938789539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16306910272188489292526359 24460365408282733938789539)
      ·
        refine ⟨36690548112424100908184309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24460365408282733938789539 36690548112424100908184309)
        ·
          refine ⟨3439738885539759460142279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36690548112424100908184309 3439738885539759460142279)
          ·
            refine ⟨5159608328309639190213419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439738885539759460142279 5159608328309639190213419)
            ·
              refine ⟨7739412492464458785320129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159608328309639190213419 7739412492464458785320129)
              ·
                refine ⟨5804559369348344088990097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7739412492464458785320129 5804559369348344088990097)
                ·
                  refine ⟨4353419527011258066742573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5804559369348344088990097 4353419527011258066742573)
                  ·
                    refine ⟨1632532322629221775028465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4353419527011258066742573 1632532322629221775028465)
                    ·
                      refine ⟨1224399241971916331271349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632532322629221775028465 1224399241971916331271349)
                      ·
                        rfl

theorem cell23_2384509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_2384509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384509 prefixEnd_2384509 := by exact prefixLift 2384509
  have htrace : WordTrace (prefixWord ++ tailWord_2384509) baseStart_2384509 baseEnd_2384509 := by
    simpa [prefixWord, tailWord_2384509, baseEnd_2384509] using wordTrace_append hprefix tailTrace_2384509
  have hstable : (prefixWord ++ tailWord_2384509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384509).length < 2 ^ (prefixWord ++ tailWord_2384509).sum := by decide
  have hdescent : baseEnd_2384509 < baseStart_2384509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384515 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 4, 4]
def baseStart_2384515 : Nat := 118140960795 + 2384515 * 2 ^ 59
def prefixEnd_2384515 : Nat := 4983230072969 + 3 ^ 40 * 2384515 * 2
def baseEnd_2384515 : Nat := 408134107618614435932107

theorem tailTrace_2384515 : CollatzResearch.WordTrace tailWord_2384515 prefixEnd_2384515 408134107618614435932107 := by
  unfold tailWord_2384515
  simp only [CollatzResearch.WordTrace]
  refine ⟨86970406956316872584858999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57980271304211248389905999 86970406956316872584858999)
  ·
    refine ⟨130455610434475308877288499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86970406956316872584858999 130455610434475308877288499)
    ·
      refine ⟨195683415651712963315932749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130455610434475308877288499 195683415651712963315932749)
      ·
        refine ⟨73381280869392361243474781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195683415651712963315932749 73381280869392361243474781)
        ·
          refine ⟨27517980326022135466303043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73381280869392361243474781 27517980326022135466303043)
          ·
            refine ⟨41276970489033203199454565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27517980326022135466303043 41276970489033203199454565)
            ·
              refine ⟨7739431966693725599897731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41276970489033203199454565 7739431966693725599897731)
              ·
                refine ⟨11609147950040588399846597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7739431966693725599897731 11609147950040588399846597)
                ·
                  refine ⟨2176715240632610324971237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11609147950040588399846597 2176715240632610324971237)
                  ·
                    refine ⟨408134107618614435932107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2176715240632610324971237 408134107618614435932107)
                    ·
                      rfl

theorem cell23_2384515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 4].length) (baseStart_2384515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384515 prefixEnd_2384515 := by exact prefixLift 2384515
  have htrace : WordTrace (prefixWord ++ tailWord_2384515) baseStart_2384515 baseEnd_2384515 := by
    simpa [prefixWord, tailWord_2384515, baseEnd_2384515] using wordTrace_append hprefix tailTrace_2384515
  have hstable : (prefixWord ++ tailWord_2384515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384515).length < 2 ^ (prefixWord ++ tailWord_2384515).sum := by decide
  have hdescent : baseEnd_2384515 < baseStart_2384515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384535 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2384535 : Nat := 118140960795 + 2384535 * 2 ^ 59
def prefixEnd_2384535 : Nat := 4983230072969 + 3 ^ 40 * 2384535 * 2
def baseEnd_2384535 : Nat := 1224412592468933229546229

theorem tailTrace_2384535 : CollatzResearch.WordTrace tailWord_2384535 prefixEnd_2384535 1224412592468933229546229 := by
  unfold tailWord_2384535
  simp only [CollatzResearch.WordTrace]
  refine ⟨86971136416244416000587059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57980757610829610667058039 86971136416244416000587059)
  ·
    refine ⟨130456704624366624000880589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86971136416244416000587059 130456704624366624000880589)
    ·
      refine ⟨48921264234137484000330221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130456704624366624000880589 48921264234137484000330221)
      ·
        refine ⟨18345474087801556500123833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48921264234137484000330221 18345474087801556500123833)
        ·
          refine ⟨13759105565851167375092875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18345474087801556500123833 13759105565851167375092875)
          ·
            refine ⟨20638658348776751062639313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13759105565851167375092875 20638658348776751062639313)
            ·
              refine ⟨15478993761582563296979485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20638658348776751062639313 15478993761582563296979485)
              ·
                refine ⟨5804622660593461236367307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15478993761582563296979485 5804622660593461236367307)
                ·
                  refine ⟨8706933990890191854550961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5804622660593461236367307 8706933990890191854550961)
                  ·
                    refine ⟨6530200493167643890913221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8706933990890191854550961 6530200493167643890913221)
                    ·
                      refine ⟨1224412592468933229546229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6530200493167643890913221 1224412592468933229546229)
                      ·
                        rfl

theorem cell23_2384535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2384535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384535 prefixEnd_2384535 := by exact prefixLift 2384535
  have htrace : WordTrace (prefixWord ++ tailWord_2384535) baseStart_2384535 baseEnd_2384535 := by
    simpa [prefixWord, tailWord_2384535, baseEnd_2384535] using wordTrace_append hprefix tailTrace_2384535
  have hstable : (prefixWord ++ tailWord_2384535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384535).length < 2 ^ (prefixWord ++ tailWord_2384535).sum := by decide
  have hdescent : baseEnd_2384535 < baseStart_2384535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384559 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 1, 2, 3]
def baseStart_2384559 : Nat := 118140960795 + 2384559 * 2 ^ 59
def prefixEnd_2384559 : Nat := 4983230072969 + 3 ^ 40 * 2384559 * 2
def baseEnd_2384559 : Nat := 1224424916004641135646119

theorem tailTrace_2384559 : CollatzResearch.WordTrace tailWord_2384559 prefixEnd_2384559 1224424916004641135646119 := by
  unfold tailWord_2384559
  simp only [CollatzResearch.WordTrace]
  refine ⟨86972011768157468099460731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57981341178771645399640487 86972011768157468099460731)
  ·
    refine ⟨130458017652236202149191097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86972011768157468099460731 130458017652236202149191097)
    ·
      refine ⟨97843513239177151611893323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130458017652236202149191097 97843513239177151611893323)
      ·
        refine ⟨146765269858765727417839985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97843513239177151611893323 146765269858765727417839985)
        ·
          refine ⟨110073952394074295563379989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146765269858765727417839985 110073952394074295563379989)
          ·
            refine ⟨5159716518472232604533437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110073952394074295563379989 5159716518472232604533437)
            ·
              refine ⟨1934893694427087226700039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5159716518472232604533437 1934893694427087226700039)
              ·
                refine ⟨2902340541640630840050059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934893694427087226700039 2902340541640630840050059)
                ·
                  refine ⟨4353510812460946260075089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902340541640630840050059 4353510812460946260075089)
                  ·
                    refine ⟨3265133109345709695056317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4353510812460946260075089 3265133109345709695056317)
                    ·
                      refine ⟨1224424916004641135646119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3265133109345709695056317 1224424916004641135646119)
                      ·
                        rfl

theorem cell23_2384559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 2, 3].length) (baseStart_2384559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384559 prefixEnd_2384559 := by exact prefixLift 2384559
  have htrace : WordTrace (prefixWord ++ tailWord_2384559) baseStart_2384559 baseEnd_2384559 := by
    simpa [prefixWord, tailWord_2384559, baseEnd_2384559] using wordTrace_append hprefix tailTrace_2384559
  have hstable : (prefixWord ++ tailWord_2384559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384559).length < 2 ^ (prefixWord ++ tailWord_2384559).sum := by decide
  have hdescent : baseEnd_2384559 < baseStart_2384559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384568 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2384568 : Nat := 118140960795 + 2384568 * 2 ^ 59
def prefixEnd_2384568 : Nat := 4983230072969 + 3 ^ 40 * 2384568 * 2
def baseEnd_2384568 : Nat := 1224429537330531600433577

theorem tailTrace_2384568 : CollatzResearch.WordTrace tailWord_2384568 prefixEnd_2384568 1224429537330531600433577 := by
  unfold tailWord_2384568
  simp only [CollatzResearch.WordTrace]
  refine ⟨43486170012562431318269179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57981560016749908424358905 43486170012562431318269179)
  ·
    refine ⟨65229255018843646977403769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43486170012562431318269179 65229255018843646977403769)
    ·
      refine ⟨48921941264132735233052827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65229255018843646977403769 48921941264132735233052827)
      ·
        refine ⟨73382911896199102849579241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48921941264132735233052827 73382911896199102849579241)
        ·
          refine ⟨55037183922149327137184431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73382911896199102849579241 55037183922149327137184431)
          ·
            refine ⟨82555775883223990705776647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55037183922149327137184431 82555775883223990705776647)
            ·
              refine ⟨123833663824835986058664971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82555775883223990705776647 123833663824835986058664971)
              ·
                refine ⟨185750495737253979087997457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123833663824835986058664971 185750495737253979087997457)
                ·
                  refine ⟨139312871802940484315998093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185750495737253979087997457 139312871802940484315998093)
                  ·
                    refine ⟨52242326926102681618499285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139312871802940484315998093 52242326926102681618499285)
                    ·
                      refine ⟨1224429537330531600433577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52242326926102681618499285 1224429537330531600433577)
                      ·
                        rfl

theorem cell23_2384568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2384568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384568 prefixEnd_2384568 := by exact prefixLift 2384568
  have htrace : WordTrace (prefixWord ++ tailWord_2384568) baseStart_2384568 baseEnd_2384568 := by
    simpa [prefixWord, tailWord_2384568, baseEnd_2384568] using wordTrace_append hprefix tailTrace_2384568
  have hstable : (prefixWord ++ tailWord_2384568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384568).length < 2 ^ (prefixWord ++ tailWord_2384568).sum := by decide
  have hdescent : baseEnd_2384568 < baseStart_2384568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384573 : List Nat := [1, 4, 1, 2, 1, 3, 4, 2, 1, 2, 2]
def baseStart_2384573 : Nat := 118140960795 + 2384573 * 2 ^ 59
def prefixEnd_2384573 : Nat := 4983230072969 + 3 ^ 40 * 2384573 * 2
def baseEnd_2384573 : Nat := 1224432104733804080871055

theorem tailTrace_2384573 : CollatzResearch.WordTrace tailWord_2384573 prefixEnd_2384573 1224432104733804080871055 := by
  unfold tailWord_2384573
  simp only [CollatzResearch.WordTrace]
  refine ⟨86972522390106748490470373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57981681593404498993646915 86972522390106748490470373)
  ·
    refine ⟨16307347948145015341963195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86972522390106748490470373 16307347948145015341963195)
    ·
      refine ⟨24461021922217523012944793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16307347948145015341963195 24461021922217523012944793)
      ·
        refine ⟨18345766441663142259708595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24461021922217523012944793 18345766441663142259708595)
        ·
          refine ⟨27518649662494713389562893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18345766441663142259708595 27518649662494713389562893)
          ·
            refine ⟨10319493623435517521086085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27518649662494713389562893 10319493623435517521086085)
            ·
              refine ⟨1934905054394159535203641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10319493623435517521086085 1934905054394159535203641)
              ·
                refine ⟨1451178790795619651402731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1934905054394159535203641 1451178790795619651402731)
                ·
                  refine ⟨2176768186193429477104097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451178790795619651402731 2176768186193429477104097)
                  ·
                    refine ⟨1632576139645072107828073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2176768186193429477104097 1632576139645072107828073)
                    ·
                      refine ⟨1224432104733804080871055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632576139645072107828073 1224432104733804080871055)
                      ·
                        rfl

theorem cell23_2384573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_2384573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384573 prefixEnd_2384573 := by exact prefixLift 2384573
  have htrace : WordTrace (prefixWord ++ tailWord_2384573) baseStart_2384573 baseEnd_2384573 := by
    simpa [prefixWord, tailWord_2384573, baseEnd_2384573] using wordTrace_append hprefix tailTrace_2384573
  have hstable : (prefixWord ++ tailWord_2384573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384573).length < 2 ^ (prefixWord ++ tailWord_2384573).sum := by decide
  have hdescent : baseEnd_2384573 < baseStart_2384573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384616 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_2384616 : Nat := 118140960795 + 2384616 * 2 ^ 59
def prefixEnd_2384616 : Nat := 4983230072969 + 3 ^ 40 * 2384616 * 2
def baseEnd_2384616 : Nat := 1224454184401947412633357

theorem tailTrace_2384616 : CollatzResearch.WordTrace tailWord_2384616 prefixEnd_2384616 1224454184401947412633357 := by
  unfold tailWord_2384616
  simp only [CollatzResearch.WordTrace]
  refine ⟨43487045364475483417142851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57982727152633977889523801 43487045364475483417142851)
  ·
    refine ⟨65230568046713225125714277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43487045364475483417142851 65230568046713225125714277)
    ·
      refine ⟨12230731508758729711071427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65230568046713225125714277 12230731508758729711071427)
      ·
        refine ⟨18346097263138094566607141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12230731508758729711071427 18346097263138094566607141)
        ·
          refine ⟨3439893236838392731238839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18346097263138094566607141 3439893236838392731238839)
          ·
            refine ⟨5159839855257589096858259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439893236838392731238839 5159839855257589096858259)
            ·
              refine ⟨7739759782886383645287389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159839855257589096858259 7739759782886383645287389)
              ·
                refine ⟨2902409918582393866982771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7739759782886383645287389 2902409918582393866982771)
                ·
                  refine ⟨4353614877873590800474157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902409918582393866982771 4353614877873590800474157)
                  ·
                    refine ⟨1632605579202596550177809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4353614877873590800474157 1632605579202596550177809)
                    ·
                      refine ⟨1224454184401947412633357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632605579202596550177809 1224454184401947412633357)
                      ·
                        rfl

theorem cell23_2384616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_2384616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384616 prefixEnd_2384616 := by exact prefixLift 2384616
  have htrace : WordTrace (prefixWord ++ tailWord_2384616) baseStart_2384616 baseEnd_2384616 := by
    simpa [prefixWord, tailWord_2384616, baseEnd_2384616] using wordTrace_append hprefix tailTrace_2384616
  have hstable : (prefixWord ++ tailWord_2384616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384616).length < 2 ^ (prefixWord ++ tailWord_2384616).sum := by decide
  have hdescent : baseEnd_2384616 < baseStart_2384616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384625 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_2384625 : Nat := 118140960795 + 2384625 * 2 ^ 59
def prefixEnd_2384625 : Nat := 4983230072969 + 3 ^ 40 * 2384625 * 2
def baseEnd_2384625 : Nat := 1224458805727837877420815

theorem tailTrace_2384625 : CollatzResearch.WordTrace tailWord_2384625 prefixEnd_2384625 1224458805727837877420815 := by
  unfold tailWord_2384625
  simp only [CollatzResearch.WordTrace]
  refine ⟨86974418985918361371363329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57982945990612240914242219 86974418985918361371363329)
  ·
    refine ⟨65230814239438771028522497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86974418985918361371363329 65230814239438771028522497)
    ·
      refine ⟨48923110679579078271391873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65230814239438771028522497 48923110679579078271391873)
      ·
        refine ⟨36692333009684308703543905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48923110679579078271391873 36692333009684308703543905)
        ·
          refine ⟨27519249757263231527657929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36692333009684308703543905 27519249757263231527657929)
          ·
            refine ⟨20639437317947423645743447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27519249757263231527657929 20639437317947423645743447)
            ·
              refine ⟨30959155976921135468615171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20639437317947423645743447 30959155976921135468615171)
              ·
                refine ⟨46438733965381703202922757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30959155976921135468615171 46438733965381703202922757)
                ·
                  refine ⟨8707262618509069350548017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46438733965381703202922757 8707262618509069350548017)
                  ·
                    refine ⟨6530446963881802012911013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8707262618509069350548017 6530446963881802012911013)
                    ·
                      refine ⟨1224458805727837877420815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6530446963881802012911013 1224458805727837877420815)
                      ·
                        rfl

theorem cell23_2384625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_2384625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384625 prefixEnd_2384625 := by exact prefixLift 2384625
  have htrace : WordTrace (prefixWord ++ tailWord_2384625) baseStart_2384625 baseEnd_2384625 := by
    simpa [prefixWord, tailWord_2384625, baseEnd_2384625] using wordTrace_append hprefix tailTrace_2384625
  have hstable : (prefixWord ++ tailWord_2384625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384625).length < 2 ^ (prefixWord ++ tailWord_2384625).sum := by decide
  have hdescent : baseEnd_2384625 < baseStart_2384625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384675 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 5]
def baseStart_2384675 : Nat := 118140960795 + 2384675 * 2 ^ 59
def prefixEnd_2384675 : Nat := 4983230072969 + 3 ^ 40 * 2384675 * 2
def baseEnd_2384675 : Nat := 1224484479760562681795585

theorem tailTrace_2384675 : CollatzResearch.WordTrace tailWord_2384675 prefixEnd_2384675 1224484479760562681795585 := by
  unfold tailWord_2384675
  simp only [CollatzResearch.WordTrace]
  refine ⟨86976242635737219910683479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57984161757158146607122319 86976242635737219910683479)
  ·
    refine ⟨130464363953605829866025219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86976242635737219910683479 130464363953605829866025219)
    ·
      refine ⟨195696545930408744799037829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130464363953605829866025219 195696545930408744799037829)
      ·
        refine ⟨36693102361951639649819593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195696545930408744799037829 36693102361951639649819593)
        ·
          refine ⟨27519826771463729737364695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36693102361951639649819593 27519826771463729737364695)
          ·
            refine ⟨41279740157195594606047043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27519826771463729737364695 41279740157195594606047043)
            ·
              refine ⟨61919610235793391909070565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41279740157195594606047043 61919610235793391909070565)
              ·
                refine ⟨11609926919211260982950731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61919610235793391909070565 11609926919211260982950731)
                ·
                  refine ⟨17414890378816891474426097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11609926919211260982950731 17414890378816891474426097)
                  ·
                    refine ⟨13061167784112668605819573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17414890378816891474426097 13061167784112668605819573)
                    ·
                      refine ⟨1224484479760562681795585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13061167784112668605819573 1224484479760562681795585)
                      ·
                        rfl

theorem cell23_2384675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_2384675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384675 prefixEnd_2384675 := by exact prefixLift 2384675
  have htrace : WordTrace (prefixWord ++ tailWord_2384675) baseStart_2384675 baseEnd_2384675 := by
    simpa [prefixWord, tailWord_2384675, baseEnd_2384675] using wordTrace_append hprefix tailTrace_2384675
  have hstable : (prefixWord ++ tailWord_2384675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384675).length < 2 ^ (prefixWord ++ tailWord_2384675).sum := by decide
  have hdescent : baseEnd_2384675 < baseStart_2384675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384712 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 5, 4]
def baseStart_2384712 : Nat := 118140960795 + 2384712 * 2 ^ 59
def prefixEnd_2384712 : Nat := 4983230072969 + 3 ^ 40 * 2384712 * 2
def baseEnd_2384712 : Nat := 408167826181593012344305

theorem tailTrace_2384712 : CollatzResearch.WordTrace tailWord_2384712 prefixEnd_2384712 408167826181593012344305 := by
  unfold tailWord_2384712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43488796068301587614890195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57985061424402116819853593 43488796068301587614890195)
  ·
    refine ⟨65233194102452381422335293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43488796068301587614890195 65233194102452381422335293)
    ·
      refine ⟨24462447788419643033375735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65233194102452381422335293 24462447788419643033375735)
      ·
        refine ⟨36693671682629464550063603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24462447788419643033375735 36693671682629464550063603)
        ·
          refine ⟨55040507523944196825095405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36693671682629464550063603 55040507523944196825095405)
          ·
            refine ⟨20640190321479073809410777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55040507523944196825095405 20640190321479073809410777)
            ·
              refine ⟨15480142741109305357058083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20640190321479073809410777 15480142741109305357058083)
              ·
                refine ⟨23220214111663958035587125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15480142741109305357058083 23220214111663958035587125)
                ·
                  refine ⟨2176895072968496065836293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23220214111663958035587125 2176895072968496065836293)
                  ·
                    refine ⟨408167826181593012344305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2176895072968496065836293 408167826181593012344305)
                    ·
                      rfl

theorem cell23_2384712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_2384712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384712 prefixEnd_2384712 := by exact prefixLift 2384712
  have htrace : WordTrace (prefixWord ++ tailWord_2384712) baseStart_2384712 baseEnd_2384712 := by
    simpa [prefixWord, tailWord_2384712, baseEnd_2384712] using wordTrace_append hprefix tailTrace_2384712
  have hstable : (prefixWord ++ tailWord_2384712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384712).length < 2 ^ (prefixWord ++ tailWord_2384712).sum := by decide
  have hdescent : baseEnd_2384712 < baseStart_2384712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384739 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 3]
def baseStart_2384739 : Nat := 118140960795 + 2384739 * 2 ^ 59
def prefixEnd_2384739 : Nat := 4983230072969 + 3 ^ 40 * 2384739 * 2
def baseEnd_2384739 : Nat := 1224517342522450431395291

theorem tailTrace_2384739 : CollatzResearch.WordTrace tailWord_2384739 prefixEnd_2384739 1224517342522450431395291 := by
  unfold tailWord_2384739
  simp only [CollatzResearch.WordTrace]
  refine ⟨86978576907505358841013271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57985717938336905894008847 86978576907505358841013271)
  ·
    refine ⟨130467865361258038261519907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86978576907505358841013271 130467865361258038261519907)
    ·
      refine ⟨195701798041887057392279861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130467865361258038261519907 195701798041887057392279861)
      ·
        refine ⟨18347043566426911630526237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195701798041887057392279861 18347043566426911630526237)
        ·
          refine ⟨6880141337410091861447339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18347043566426911630526237 6880141337410091861447339)
          ·
            refine ⟨10320212006115137792171009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6880141337410091861447339 10320212006115137792171009)
            ·
              refine ⟨7740159004586353344128257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10320212006115137792171009 7740159004586353344128257)
              ·
                refine ⟨5805119253439765008096193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7740159004586353344128257 5805119253439765008096193)
                ·
                  refine ⟨4353839440079823756072145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5805119253439765008096193 4353839440079823756072145)
                  ·
                    refine ⟨3265379580059867817054109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4353839440079823756072145 3265379580059867817054109)
                    ·
                      refine ⟨1224517342522450431395291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3265379580059867817054109 1224517342522450431395291)
                      ·
                        rfl

theorem cell23_2384739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_2384739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384739 prefixEnd_2384739 := by exact prefixLift 2384739
  have htrace : WordTrace (prefixWord ++ tailWord_2384739) baseStart_2384739 baseEnd_2384739 := by
    simpa [prefixWord, tailWord_2384739, baseEnd_2384739] using wordTrace_append hprefix tailTrace_2384739
  have hstable : (prefixWord ++ tailWord_2384739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384739).length < 2 ^ (prefixWord ++ tailWord_2384739).sum := by decide
  have hdescent : baseEnd_2384739 < baseStart_2384739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384770 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2384770 : Nat := 118140960795 + 2384770 * 2 ^ 59
def prefixEnd_2384770 : Nat := 4983230072969 + 3 ^ 40 * 2384770 * 2
def baseEnd_2384770 : Nat := 1224533260422739810107649

theorem tailTrace_2384770 : CollatzResearch.WordTrace tailWord_2384770 prefixEnd_2384770 1224533260422739810107649 := by
  unfold tailWord_2384770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21744926892598262783847941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57986471713595367423594509 21744926892598262783847941)
  ·
    refine ⟨4077173792362174271971489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21744926892598262783847941 4077173792362174271971489)
    ·
      refine ⟨3057880344271630703978617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4077173792362174271971489 3057880344271630703978617)
      ·
        refine ⟨2293410258203723027983963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3057880344271630703978617 2293410258203723027983963)
        ·
          refine ⟨3440115387305584541975945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293410258203723027983963 3440115387305584541975945)
          ·
            refine ⟨2580086540479188406481959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3440115387305584541975945 2580086540479188406481959)
            ·
              refine ⟨3870129810718782609722939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580086540479188406481959 3870129810718782609722939)
              ·
                refine ⟨5805194716078173914584409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870129810718782609722939 5805194716078173914584409)
                ·
                  refine ⟨4353896037058630435938307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5805194716078173914584409 4353896037058630435938307)
                  ·
                    refine ⟨6530844055587945653907461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4353896037058630435938307 6530844055587945653907461)
                    ·
                      refine ⟨1224533260422739810107649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6530844055587945653907461 1224533260422739810107649)
                      ·
                        rfl

theorem cell23_2384770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2384770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384770 prefixEnd_2384770 := by exact prefixLift 2384770
  have htrace : WordTrace (prefixWord ++ tailWord_2384770) baseStart_2384770 baseEnd_2384770 := by
    simpa [prefixWord, tailWord_2384770, baseEnd_2384770] using wordTrace_append hprefix tailTrace_2384770
  have hstable : (prefixWord ++ tailWord_2384770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384770).length < 2 ^ (prefixWord ++ tailWord_2384770).sum := by decide
  have hdescent : baseEnd_2384770 < baseStart_2384770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384789 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_2384789 : Nat := 118140960795 + 2384789 * 2 ^ 59
def prefixEnd_2384789 : Nat := 4983230072969 + 3 ^ 40 * 2384789 * 2
def baseEnd_2384789 : Nat := 408181005518391745256687

theorem tailTrace_2384789 : CollatzResearch.WordTrace tailWord_2384789 prefixEnd_2384789 408181005518391745256687 := by
  unfold tailWord_2384789
  simp only [CollatzResearch.WordTrace]
  refine ⟨86980400557324217380333421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57986933704882811586888947 86980400557324217380333421)
  ·
    refine ⟨32617650208996581517625033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86980400557324217380333421 32617650208996581517625033)
    ·
      refine ⟨24463237656747436138218775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32617650208996581517625033 24463237656747436138218775)
      ·
        refine ⟨36694856485121154207328163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24463237656747436138218775 36694856485121154207328163)
        ·
          refine ⟨55042284727681731310992245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36694856485121154207328163 55042284727681731310992245)
          ·
            refine ⟨5160214193220162310405523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55042284727681731310992245 5160214193220162310405523)
            ·
              refine ⟨7740321289830243465608285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5160214193220162310405523 7740321289830243465608285)
              ·
                refine ⟨2902620483686341299603107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7740321289830243465608285 2902620483686341299603107)
                ·
                  refine ⟨4353930725529511949404661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902620483686341299603107 4353930725529511949404661)
                  ·
                    refine ⟨408181005518391745256687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4353930725529511949404661 408181005518391745256687)
                    ·
                      rfl

theorem cell23_2384789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_2384789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384789 prefixEnd_2384789 := by exact prefixLift 2384789
  have htrace : WordTrace (prefixWord ++ tailWord_2384789) baseStart_2384789 baseEnd_2384789 := by
    simpa [prefixWord, tailWord_2384789, baseEnd_2384789] using wordTrace_append hprefix tailTrace_2384789
  have hstable : (prefixWord ++ tailWord_2384789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384789).length < 2 ^ (prefixWord ++ tailWord_2384789).sum := by decide
  have hdescent : baseEnd_2384789 < baseStart_2384789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384812 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_2384812 : Nat := 118140960795 + 2384812 * 2 ^ 59
def prefixEnd_2384812 : Nat := 4983230072969 + 3 ^ 40 * 2384812 * 2
def baseEnd_2384812 : Nat := 1224554826610228645782455

theorem tailTrace_2384812 : CollatzResearch.WordTrace tailWord_2384812 prefixEnd_2384812 1224554826610228645782455 := by
  unfold tailWord_2384812
  simp only [CollatzResearch.WordTrace]
  refine ⟨43490619718120446154210345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57987492957493928205613793 43490619718120446154210345)
  ·
    refine ⟨32617964788590334615657759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43490619718120446154210345 32617964788590334615657759)
    ·
      refine ⟨48926947182885501923486639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32617964788590334615657759 48926947182885501923486639)
      ·
        refine ⟨73390420774328252885229959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48926947182885501923486639 73390420774328252885229959)
        ·
          refine ⟨110085631161492379327844939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73390420774328252885229959 110085631161492379327844939)
          ·
            refine ⟨165128446742238568991767409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110085631161492379327844939 165128446742238568991767409)
            ·
              refine ⟨123846335056678926743825557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165128446742238568991767409 123846335056678926743825557)
              ·
                refine ⟨5805296955781824691116823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123846335056678926743825557 5805296955781824691116823)
                ·
                  refine ⟨8707945433672737036675235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5805296955781824691116823 8707945433672737036675235)
                  ·
                    refine ⟨13061918150509105555012853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8707945433672737036675235 13061918150509105555012853)
                    ·
                      refine ⟨1224554826610228645782455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13061918150509105555012853 1224554826610228645782455)
                      ·
                        rfl

theorem cell23_2384812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_2384812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384812 prefixEnd_2384812 := by exact prefixLift 2384812
  have htrace : WordTrace (prefixWord ++ tailWord_2384812) baseStart_2384812 baseEnd_2384812 := by
    simpa [prefixWord, tailWord_2384812, baseEnd_2384812] using wordTrace_append hprefix tailTrace_2384812
  have hstable : (prefixWord ++ tailWord_2384812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384812).length < 2 ^ (prefixWord ++ tailWord_2384812).sum := by decide
  have hdescent : baseEnd_2384812 < baseStart_2384812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384826 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2]
def baseStart_2384826 : Nat := 118140960795 + 2384826 * 2 ^ 59
def prefixEnd_2384826 : Nat := 4983230072969 + 3 ^ 40 * 2384826 * 2
def baseEnd_2384826 : Nat := 1224562015339391591007391

theorem tailTrace_2384826 : CollatzResearch.WordTrace tailWord_2384826 prefixEnd_2384826 1224562015339391591007391 := by
  unfold tailWord_2384826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21745437514547543174857583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57987833372126781799620221 21745437514547543174857583)
  ·
    refine ⟨32618156271821314762286375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21745437514547543174857583 32618156271821314762286375)
    ·
      refine ⟨48927234407731972143429563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32618156271821314762286375 48927234407731972143429563)
      ·
        refine ⟨73390851611597958215144345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48927234407731972143429563 73390851611597958215144345)
        ·
          refine ⟨55043138708698468661358259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73390851611597958215144345 55043138708698468661358259)
          ·
            refine ⟨82564708063047702992037389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55043138708698468661358259 82564708063047702992037389)
            ·
              refine ⟨30961765523642888622014021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82564708063047702992037389 30961765523642888622014021)
              ·
                refine ⟨5805331035683041616627629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30961765523642888622014021 5805331035683041616627629)
                ·
                  refine ⟨2176999138381140606235361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5805331035683041616627629 2176999138381140606235361)
                  ·
                    refine ⟨1632749353785855454676521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2176999138381140606235361 1632749353785855454676521)
                    ·
                      refine ⟨1224562015339391591007391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632749353785855454676521 1224562015339391591007391)
                      ·
                        rfl

theorem cell23_2384826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_2384826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384826 prefixEnd_2384826 := by exact prefixLift 2384826
  have htrace : WordTrace (prefixWord ++ tailWord_2384826) baseStart_2384826 baseEnd_2384826 := by
    simpa [prefixWord, tailWord_2384826, baseEnd_2384826] using wordTrace_append hprefix tailTrace_2384826
  have hstable : (prefixWord ++ tailWord_2384826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384826).length < 2 ^ (prefixWord ++ tailWord_2384826).sum := by decide
  have hdescent : baseEnd_2384826 < baseStart_2384826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384832 : List Nat := [2, 1, 1, 2, 3, 4, 1, 9]
def baseStart_2384832 : Nat := 118140960795 + 2384832 * 2 ^ 59
def prefixEnd_2384832 : Nat := 4983230072969 + 3 ^ 40 * 2384832 * 2
def baseEnd_2384832 : Nat := 45354262823085872871569

theorem tailTrace_2384832 : CollatzResearch.WordTrace tailWord_2384832 prefixEnd_2384832 45354262823085872871569 := by
  unfold tailWord_2384832
  simp only [CollatzResearch.WordTrace]
  refine ⟨43490984448084217862074375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57987979264112290482765833 43490984448084217862074375)
  ·
    refine ⟨65236476672126326793111563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43490984448084217862074375 65236476672126326793111563)
    ·
      refine ⟨97854715008189490189667345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65236476672126326793111563 97854715008189490189667345)
      ·
        refine ⟨73391036256142117642250509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97854715008189490189667345 73391036256142117642250509)
        ·
          refine ⟨27521638596053294115843941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73391036256142117642250509 27521638596053294115843941)
          ·
            refine ⟨5160307236759992646720739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27521638596053294115843941 5160307236759992646720739)
            ·
              refine ⟨7740460855139988970081109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5160307236759992646720739 7740460855139988970081109)
              ·
                refine ⟨45354262823085872871569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7740460855139988970081109 45354262823085872871569)
                ·
                  rfl

theorem cell23_2384832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 9].length) (baseStart_2384832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384832 prefixEnd_2384832 := by exact prefixLift 2384832
  have htrace : WordTrace (prefixWord ++ tailWord_2384832) baseStart_2384832 baseEnd_2384832 := by
    simpa [prefixWord, tailWord_2384832, baseEnd_2384832] using wordTrace_append hprefix tailTrace_2384832
  have hstable : (prefixWord ++ tailWord_2384832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384832).length < 2 ^ (prefixWord ++ tailWord_2384832).sum := by decide
  have hdescent : baseEnd_2384832 < baseStart_2384832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384846 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_2384846 : Nat := 118140960795 + 2384846 * 2 ^ 59
def prefixEnd_2384846 : Nat := 4983230072969 + 3 ^ 40 * 2384846 * 2
def baseEnd_2384846 : Nat := 1224572284952481512757299

theorem tailTrace_2384846 : CollatzResearch.WordTrace tailWord_2384846 prefixEnd_2384846 1224572284952481512757299 := by
  unfold tailWord_2384846
  simp only [CollatzResearch.WordTrace]
  refine ⟨10872809939764714514394799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57988319678745144076772261 10872809939764714514394799)
  ·
    refine ⟨16309214909647071771592199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10872809939764714514394799 16309214909647071771592199)
    ·
      refine ⟨24463822364470607657388299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16309214909647071771592199 24463822364470607657388299)
      ·
        refine ⟨36695733546705911486082449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24463822364470607657388299 36695733546705911486082449)
        ·
          refine ⟨27521800160029433614561837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36695733546705911486082449 27521800160029433614561837)
          ·
            refine ⟨10320675060011037605460689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27521800160029433614561837 10320675060011037605460689)
            ·
              refine ⟨7740506295008278204095517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10320675060011037605460689 7740506295008278204095517)
              ·
                refine ⟨2902689860628104326535819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7740506295008278204095517 2902689860628104326535819)
                ·
                  refine ⟨4354034790942156489803729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902689860628104326535819 4354034790942156489803729)
                  ·
                    refine ⟨3265526093206617367352797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4354034790942156489803729 3265526093206617367352797)
                    ·
                      refine ⟨1224572284952481512757299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3265526093206617367352797 1224572284952481512757299)
                      ·
                        rfl

theorem cell23_2384846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_2384846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384846 prefixEnd_2384846 := by exact prefixLift 2384846
  have htrace : WordTrace (prefixWord ++ tailWord_2384846) baseStart_2384846 baseEnd_2384846 := by
    simpa [prefixWord, tailWord_2384846, baseEnd_2384846] using wordTrace_append hprefix tailTrace_2384846
  have hstable : (prefixWord ++ tailWord_2384846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384846).length < 2 ^ (prefixWord ++ tailWord_2384846).sum := by decide
  have hdescent : baseEnd_2384846 < baseStart_2384846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384866 : List Nat := [3, 3, 3, 1, 1, 2, 2, 8]
def baseStart_2384866 : Nat := 118140960795 + 2384866 * 2 ^ 59
def prefixEnd_2384866 : Nat := 4983230072969 + 3 ^ 40 * 2384866 * 2
def baseEnd_2384866 : Nat := 45354909428354497574341

theorem tailTrace_2384866 : CollatzResearch.WordTrace tailWord_2384866 prefixEnd_2384866 45354909428354497574341 := by
  unfold tailWord_2384866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21745802244511314882721613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57988805985363506353924301 21745802244511314882721613)
  ·
    refine ⟨8154675841691743081020605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21745802244511314882721613 8154675841691743081020605)
    ·
      refine ⟨3058003440634403655382727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8154675841691743081020605 3058003440634403655382727)
      ·
        refine ⟨4587005160951605483074091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058003440634403655382727 4587005160951605483074091)
        ·
          refine ⟨6880507741427408224611137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4587005160951605483074091 6880507741427408224611137)
          ·
            refine ⟨5160380806070556168458353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6880507741427408224611137 5160380806070556168458353)
            ·
              refine ⟨3870285604552917126343765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5160380806070556168458353 3870285604552917126343765)
              ·
                refine ⟨45354909428354497574341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3870285604552917126343765 45354909428354497574341)
                ·
                  rfl

theorem cell23_2384866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 8].length) (baseStart_2384866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384866 prefixEnd_2384866 := by exact prefixLift 2384866
  have htrace : WordTrace (prefixWord ++ tailWord_2384866) baseStart_2384866 baseEnd_2384866 := by
    simpa [prefixWord, tailWord_2384866, baseEnd_2384866] using wordTrace_append hprefix tailTrace_2384866
  have hstable : (prefixWord ++ tailWord_2384866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384866).length < 2 ^ (prefixWord ++ tailWord_2384866).sum := by decide
  have hdescent : baseEnd_2384866 < baseStart_2384866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384929 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2384929 : Nat := 118140960795 + 2384929 * 2 ^ 59
def prefixEnd_2384929 : Nat := 4983230072969 + 3 ^ 40 * 2384929 * 2
def baseEnd_2384929 : Nat := 1224614903846804688019417

theorem tailTrace_2384929 : CollatzResearch.WordTrace tailWord_2384929 prefixEnd_2384929 1224614903846804688019417 := by
  unfold tailWord_2384929
  simp only [CollatzResearch.WordTrace]
  refine ⟨86985506776817021290429841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57990337851211347526953227 86985506776817021290429841)
  ·
    refine ⟨65239130082612765967822381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86985506776817021290429841 65239130082612765967822381)
    ·
      refine ⟨24464673780979787237933393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65239130082612765967822381 24464673780979787237933393)
      ·
        refine ⟨18348505335734840428450045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24464673780979787237933393 18348505335734840428450045)
        ·
          refine ⟨6880689500900565160668767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18348505335734840428450045 6880689500900565160668767)
          ·
            refine ⟨10321034251350847741003151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6880689500900565160668767 10321034251350847741003151)
            ·
              refine ⟨15481551377026271611504727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10321034251350847741003151 15481551377026271611504727)
              ·
                refine ⟨23222327065539407417257091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15481551377026271611504727 23222327065539407417257091)
                ·
                  refine ⟨34833490598309111125885637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23222327065539407417257091 34833490598309111125885637)
                  ·
                    refine ⟨6531279487182958336103557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34833490598309111125885637 6531279487182958336103557)
                    ·
                      refine ⟨1224614903846804688019417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6531279487182958336103557 1224614903846804688019417)
                      ·
                        rfl

theorem cell23_2384929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2384929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384929 prefixEnd_2384929 := by exact prefixLift 2384929
  have htrace : WordTrace (prefixWord ++ tailWord_2384929) baseStart_2384929 baseEnd_2384929 := by
    simpa [prefixWord, tailWord_2384929, baseEnd_2384929] using wordTrace_append hprefix tailTrace_2384929
  have hstable : (prefixWord ++ tailWord_2384929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384929).length < 2 ^ (prefixWord ++ tailWord_2384929).sum := by decide
  have hdescent : baseEnd_2384929 < baseStart_2384929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384933 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 2, 2, 2]
def baseStart_2384933 : Nat := 118140960795 + 2384933 * 2 ^ 59
def prefixEnd_2384933 : Nat := 4983230072969 + 3 ^ 40 * 2384933 * 2
def baseEnd_2384933 : Nat := 1224616957769422672369399

theorem tailTrace_2384933 : CollatzResearch.WordTrace tailWord_2384933 prefixEnd_2384933 1224616957769422672369399 := by
  unfold tailWord_2384933
  simp only [CollatzResearch.WordTrace]
  refine ⟨86985652668802529973575453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57990435112535019982383635 86985652668802529973575453)
  ·
    refine ⟨32619619750800948740090795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86985652668802529973575453 32619619750800948740090795)
    ·
      refine ⟨48929429626201423110136193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32619619750800948740090795 48929429626201423110136193)
      ·
        refine ⟨36697072219651067332602145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48929429626201423110136193 36697072219651067332602145)
        ·
          refine ⟨27522804164738300499451609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36697072219651067332602145 27522804164738300499451609)
          ·
            refine ⟨20642103123553725374588707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27522804164738300499451609 20642103123553725374588707)
            ·
              refine ⟨30963154685330588061883061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20642103123553725374588707 30963154685330588061883061)
              ·
                refine ⟨2902795751749742630801537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30963154685330588061883061 2902795751749742630801537)
                ·
                  refine ⟨2177096813812306973101153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2902795751749742630801537 2177096813812306973101153)
                  ·
                    refine ⟨1632822610359230229825865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2177096813812306973101153 1632822610359230229825865)
                    ·
                      refine ⟨1224616957769422672369399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632822610359230229825865 1224616957769422672369399)
                      ·
                        rfl

theorem cell23_2384933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_2384933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384933 prefixEnd_2384933 := by exact prefixLift 2384933
  have htrace : WordTrace (prefixWord ++ tailWord_2384933) baseStart_2384933 baseEnd_2384933 := by
    simpa [prefixWord, tailWord_2384933, baseEnd_2384933] using wordTrace_append hprefix tailTrace_2384933
  have hstable : (prefixWord ++ tailWord_2384933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384933).length < 2 ^ (prefixWord ++ tailWord_2384933).sum := by decide
  have hdescent : baseEnd_2384933 < baseStart_2384933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384949 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_2384949 : Nat := 118140960795 + 2384949 * 2 ^ 59
def prefixEnd_2384949 : Nat := 4983230072969 + 3 ^ 40 * 2384949 * 2
def baseEnd_2384949 : Nat := 1224625173459894609769325

theorem tailTrace_2384949 : CollatzResearch.WordTrace tailWord_2384949 prefixEnd_2384949 1224625173459894609769325 := by
  unfold tailWord_2384949
  simp only [CollatzResearch.WordTrace]
  refine ⟨86986236236744564706157901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57990824157829709804105267 86986236236744564706157901)
  ·
    refine ⟨32619838588779211764809213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86986236236744564706157901 32619838588779211764809213)
    ·
      refine ⟨12232439470792204411803455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32619838588779211764809213 12232439470792204411803455)
      ·
        refine ⟨18348659206188306617705183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12232439470792204411803455 18348659206188306617705183)
        ·
          refine ⟨27522988809282459926557775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18348659206188306617705183 27522988809282459926557775)
          ·
            refine ⟨41284483213923689889836663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27522988809282459926557775 41284483213923689889836663)
            ·
              refine ⟨61926724820885534834754995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41284483213923689889836663 61926724820885534834754995)
              ·
                refine ⟨92890087231328302252132493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61926724820885534834754995 92890087231328302252132493)
                ·
                  refine ⟨34833782711748113344549685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92890087231328302252132493 34833782711748113344549685)
                  ·
                    refine ⟨3265667129226385626051533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34833782711748113344549685 3265667129226385626051533)
                    ·
                      refine ⟨1224625173459894609769325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3265667129226385626051533 1224625173459894609769325)
                      ·
                        rfl

theorem cell23_2384949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_2384949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384949 prefixEnd_2384949 := by exact prefixLift 2384949
  have htrace : WordTrace (prefixWord ++ tailWord_2384949) baseStart_2384949 baseEnd_2384949 := by
    simpa [prefixWord, tailWord_2384949, baseEnd_2384949] using wordTrace_append hprefix tailTrace_2384949
  have hstable : (prefixWord ++ tailWord_2384949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384949).length < 2 ^ (prefixWord ++ tailWord_2384949).sum := by decide
  have hdescent : baseEnd_2384949 < baseStart_2384949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384956 : List Nat := [2, 2, 2, 2, 2, 2, 1, 5, 5]
def baseStart_2384956 : Nat := 118140960795 + 2384956 * 2 ^ 59
def prefixEnd_2384956 : Nat := 4983230072969 + 3 ^ 40 * 2384956 * 2
def baseEnd_2384956 : Nat := 136069863091608453597977

theorem tailTrace_2384956 : CollatzResearch.WordTrace tailWord_2384956 prefixEnd_2384956 136069863091608453597977 := by
  unfold tailWord_2384956
  simp only [CollatzResearch.WordTrace]
  refine ⟨43493245773859602450831361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57990994365146136601108481 43493245773859602450831361)
  ·
    refine ⟨32619934330394701838123521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43493245773859602450831361 32619934330394701838123521)
    ·
      refine ⟨24464950747796026378592641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32619934330394701838123521 24464950747796026378592641)
      ·
        refine ⟨18348713060847019783944481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24464950747796026378592641 18348713060847019783944481)
        ·
          refine ⟨13761534795635264837958361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18348713060847019783944481 13761534795635264837958361)
          ·
            refine ⟨10321151096726448628468771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13761534795635264837958361 10321151096726448628468771)
            ·
              refine ⟨15481726645089672942703157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10321151096726448628468771 15481726645089672942703157)
              ·
                refine ⟨1451411872977156838378421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15481726645089672942703157 1451411872977156838378421)
                ·
                  refine ⟨136069863091608453597977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1451411872977156838378421 136069863091608453597977)
                  ·
                    rfl

theorem cell23_2384956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_2384956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384956 prefixEnd_2384956 := by exact prefixLift 2384956
  have htrace : WordTrace (prefixWord ++ tailWord_2384956) baseStart_2384956 baseEnd_2384956 := by
    simpa [prefixWord, tailWord_2384956, baseEnd_2384956] using wordTrace_append hprefix tailTrace_2384956
  have hstable : (prefixWord ++ tailWord_2384956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384956).length < 2 ^ (prefixWord ++ tailWord_2384956).sum := by decide
  have hdescent : baseEnd_2384956 < baseStart_2384956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384973 : List Nat := [1, 6, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2384973 : Nat := 118140960795 + 2384973 * 2 ^ 59
def prefixEnd_2384973 : Nat := 4983230072969 + 3 ^ 40 * 2384973 * 2
def baseEnd_2384973 : Nat := 136070832999511390652135

theorem tailTrace_2384973 : CollatzResearch.WordTrace tailWord_2384973 prefixEnd_2384973 136070832999511390652135 := by
  unfold tailWord_2384973
  simp only [CollatzResearch.WordTrace]
  refine ⟨86987111588657616805031573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57991407725771744536687715 86987111588657616805031573)
  ·
    refine ⟨4077520855718325787735855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86987111588657616805031573 4077520855718325787735855)
    ·
      refine ⟨6116281283577488681603783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4077520855718325787735855 6116281283577488681603783)
      ·
        refine ⟨9174421925366233022405675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6116281283577488681603783 9174421925366233022405675)
        ·
          refine ⟨13761632888049349533608513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9174421925366233022405675 13761632888049349533608513)
          ·
            refine ⟨10321224666037012150206385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13761632888049349533608513 10321224666037012150206385)
            ·
              refine ⟨7740918499527759112654789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10321224666037012150206385 7740918499527759112654789)
              ·
                refine ⟨1451422218661454833622773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7740918499527759112654789 1451422218661454833622773)
                ·
                  refine ⟨136070832999511390652135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1451422218661454833622773 136070832999511390652135)
                  ·
                    rfl

theorem cell23_2384973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2384973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2384973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2384973 prefixEnd_2384973 := by exact prefixLift 2384973
  have htrace : WordTrace (prefixWord ++ tailWord_2384973) baseStart_2384973 baseEnd_2384973 := by
    simpa [prefixWord, tailWord_2384973, baseEnd_2384973] using wordTrace_append hprefix tailTrace_2384973
  have hstable : (prefixWord ++ tailWord_2384973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384973).length < 2 ^ (prefixWord ++ tailWord_2384973).sum := by decide
  have hdescent : baseEnd_2384973 < baseStart_2384973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385006 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2385006 : Nat := 118140960795 + 2385006 * 2 ^ 59
def prefixEnd_2385006 : Nat := 4983230072969 + 3 ^ 40 * 2385006 * 2
def baseEnd_2385006 : Nat := 1224654441857200886756563

theorem tailTrace_2385006 : CollatzResearch.WordTrace tailWord_2385006 prefixEnd_2385006 1224654441857200886756563 := by
  unfold tailWord_2385006
  simp only [CollatzResearch.WordTrace]
  refine ⟨10873539399692257930122859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57992210131692042293988581 10873539399692257930122859)
  ·
    refine ⟨16310309099538386895184289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10873539399692257930122859 16310309099538386895184289)
    ·
      refine ⟨12232731824653790171388217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16310309099538386895184289 12232731824653790171388217)
      ·
        refine ⟨9174548868490342628541163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12232731824653790171388217 9174548868490342628541163)
        ·
          refine ⟨13761823302735513942811745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9174548868490342628541163 13761823302735513942811745)
          ·
            refine ⟨10321367477051635457108809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13761823302735513942811745 10321367477051635457108809)
            ·
              refine ⟨7741025607788726592831607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10321367477051635457108809 7741025607788726592831607)
              ·
                refine ⟨11611538411683089889247411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7741025607788726592831607 11611538411683089889247411)
                ·
                  refine ⟨17417307617524634833871117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11611538411683089889247411 17417307617524634833871117)
                  ·
                    refine ⟨6531490356571738062701669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17417307617524634833871117 6531490356571738062701669)
                    ·
                      refine ⟨1224654441857200886756563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6531490356571738062701669 1224654441857200886756563)
                      ·
                        rfl

theorem cell23_2385006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2385006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385006 prefixEnd_2385006 := by exact prefixLift 2385006
  have htrace : WordTrace (prefixWord ++ tailWord_2385006) baseStart_2385006 baseEnd_2385006 := by
    simpa [prefixWord, tailWord_2385006, baseEnd_2385006] using wordTrace_append hprefix tailTrace_2385006
  have hstable : (prefixWord ++ tailWord_2385006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385006).length < 2 ^ (prefixWord ++ tailWord_2385006).sum := by decide
  have hdescent : baseEnd_2385006 < baseStart_2385006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385033 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 3, 4]
def baseStart_2385033 : Nat := 118140960795 + 2385033 * 2 ^ 59
def prefixEnd_2385033 : Nat := 4983230072969 + 3 ^ 40 * 2385033 * 2
def baseEnd_2385033 : Nat := 408222768611624093706313

theorem tailTrace_2385033 : CollatzResearch.WordTrace tailWord_2385033 prefixEnd_2385033 408222768611624093706313 := by
  unfold tailWord_2385033
  simp only [CollatzResearch.WordTrace]
  refine ⟨86989299968440247052215753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57992866645626831368143835 86989299968440247052215753)
  ·
    refine ⟨65241974976330185289161815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86989299968440247052215753 65241974976330185289161815)
    ·
      refine ⟨97862962464495277933742723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65241974976330185289161815 97862962464495277933742723)
      ·
        refine ⟨146794443696742916900614085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97862962464495277933742723 146794443696742916900614085)
        ·
          refine ⟨27523958193139296918865141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146794443696742916900614085 27523958193139296918865141)
          ·
            refine ⟨2580371080606809086143607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27523958193139296918865141 2580371080606809086143607)
            ·
              refine ⟨3870556620910213629215411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580371080606809086143607 3870556620910213629215411)
              ·
                refine ⟨5805834931365320443823117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870556620910213629215411 5805834931365320443823117)
                ·
                  refine ⟨2177188099261995166433669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5805834931365320443823117 2177188099261995166433669)
                  ·
                    refine ⟨408222768611624093706313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2177188099261995166433669 408222768611624093706313)
                    ·
                      rfl

theorem cell23_2385033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 4].length) (baseStart_2385033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385033 prefixEnd_2385033 := by exact prefixLift 2385033
  have htrace : WordTrace (prefixWord ++ tailWord_2385033) baseStart_2385033 baseEnd_2385033 := by
    simpa [prefixWord, tailWord_2385033, baseEnd_2385033] using wordTrace_append hprefix tailTrace_2385033
  have hstable : (prefixWord ++ tailWord_2385033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385033).length < 2 ^ (prefixWord ++ tailWord_2385033).sum := by decide
  have hdescent : baseEnd_2385033 < baseStart_2385033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385039 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 3]
def baseStart_2385039 : Nat := 118140960795 + 2385039 * 2 ^ 59
def prefixEnd_2385039 : Nat := 4983230072969 + 3 ^ 40 * 2385039 * 2
def baseEnd_2385039 : Nat := 1224671386718799257643911

theorem tailTrace_2385039 : CollatzResearch.WordTrace tailWord_2385039 prefixEnd_2385039 1224671386718799257643911 := by
  unfold tailWord_2385039
  simp only [CollatzResearch.WordTrace]
  refine ⟨86989518806418510076934171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57993012537612340051289447 86989518806418510076934171)
  ·
    refine ⟨130484278209627765115401257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86989518806418510076934171 130484278209627765115401257)
    ·
      refine ⟨97863208657220823836550943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130484278209627765115401257 97863208657220823836550943)
      ·
        refine ⟨146794812985831235754826415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97863208657220823836550943 146794812985831235754826415)
        ·
          refine ⟨220192219478746853632239623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146794812985831235754826415 220192219478746853632239623)
          ·
            refine ⟨330288329218120280448359435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220192219478746853632239623 330288329218120280448359435)
            ·
              refine ⟨495432493827180420672539153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330288329218120280448359435 495432493827180420672539153)
              ·
                refine ⟨371574370370385315504404365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495432493827180420672539153 371574370370385315504404365)
                ·
                  refine ⟨139340388888894493314151637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371574370370385315504404365 139340388888894493314151637)
                  ·
                    refine ⟨3265790364583464687050429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 139340388888894493314151637 3265790364583464687050429)
                    ·
                      refine ⟨1224671386718799257643911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3265790364583464687050429 1224671386718799257643911)
                      ·
                        rfl

theorem cell23_2385039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_2385039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385039 prefixEnd_2385039 := by exact prefixLift 2385039
  have htrace : WordTrace (prefixWord ++ tailWord_2385039) baseStart_2385039 baseEnd_2385039 := by
    simpa [prefixWord, tailWord_2385039, baseEnd_2385039] using wordTrace_append hprefix tailTrace_2385039
  have hstable : (prefixWord ++ tailWord_2385039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385039).length < 2 ^ (prefixWord ++ tailWord_2385039).sum := by decide
  have hdescent : baseEnd_2385039 < baseStart_2385039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385096 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_2385096 : Nat := 118140960795 + 2385096 * 2 ^ 59
def prefixEnd_2385096 : Nat := 4983230072969 + 3 ^ 40 * 2385096 * 2
def baseEnd_2385096 : Nat := 1224700655116105534631149

theorem tailTrace_2385096 : CollatzResearch.WordTrace tailWord_2385096 prefixEnd_2385096 1224700655116105534631149 := by
  unfold tailWord_2385096
  simp only [CollatzResearch.WordTrace]
  refine ⟨43495798883606004405879571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57994398511474672541172761 43495798883606004405879571)
  ·
    refine ⟨65243698325409006608819357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43495798883606004405879571 65243698325409006608819357)
    ·
      refine ⟨24466386872028377478307259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65243698325409006608819357 24466386872028377478307259)
      ·
        refine ⟨36699580308042566217460889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24466386872028377478307259 36699580308042566217460889)
        ·
          refine ⟨27524685231031924663095667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36699580308042566217460889 27524685231031924663095667)
          ·
            refine ⟨41287027846547886994643501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27524685231031924663095667 41287027846547886994643501)
            ·
              refine ⟨15482635442455457622991313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41287027846547886994643501 15482635442455457622991313)
              ·
                refine ⟨11611976581841593217243485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15482635442455457622991313 11611976581841593217243485)
                ·
                  refine ⟨4354491218190597456466307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11611976581841593217243485 4354491218190597456466307)
                  ·
                    refine ⟨6531736827285896184699461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4354491218190597456466307 6531736827285896184699461)
                    ·
                      refine ⟨1224700655116105534631149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6531736827285896184699461 1224700655116105534631149)
                      ·
                        rfl

theorem cell23_2385096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_2385096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385096 prefixEnd_2385096 := by exact prefixLift 2385096
  have htrace : WordTrace (prefixWord ++ tailWord_2385096) baseStart_2385096 baseEnd_2385096 := by
    simpa [prefixWord, tailWord_2385096, baseEnd_2385096] using wordTrace_append hprefix tailTrace_2385096
  have hstable : (prefixWord ++ tailWord_2385096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385096).length < 2 ^ (prefixWord ++ tailWord_2385096).sum := by decide
  have hdescent : baseEnd_2385096 < baseStart_2385096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385119 : List Nat := [1, 1, 2, 3, 2, 1, 2, 11]
def baseStart_2385119 : Nat := 118140960795 + 2385119 * 2 ^ 59
def prefixEnd_2385119 : Nat := 4983230072969 + 3 ^ 40 * 2385119 * 2
def baseEnd_2385119 : Nat := 45359720932265146097909

theorem tailTrace_2385119 : CollatzResearch.WordTrace tailWord_2385119 prefixEnd_2385119 45359720932265146097909 := by
  unfold tailWord_2385119
  simp only [CollatzResearch.WordTrace]
  refine ⟨86992436646128683739846411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57994957764085789159897607 86992436646128683739846411)
  ·
    refine ⟨130488654969193025609769617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86992436646128683739846411 130488654969193025609769617)
    ·
      refine ⟨97866491226894769207327213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130488654969193025609769617 97866491226894769207327213)
      ·
        refine ⟨36699934210085538452747705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97866491226894769207327213 36699934210085538452747705)
        ·
          refine ⟨27524950657564153839560779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36699934210085538452747705 27524950657564153839560779)
          ·
            refine ⟨41287425986346230759341169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27524950657564153839560779 41287425986346230759341169)
            ·
              refine ⟨30965569489759673069505877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41287425986346230759341169 30965569489759673069505877)
              ·
                refine ⟨45359720932265146097909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 30965569489759673069505877 45359720932265146097909)
                ·
                  rfl

theorem cell23_2385119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 11].length) (baseStart_2385119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385119 prefixEnd_2385119 := by exact prefixLift 2385119
  have htrace : WordTrace (prefixWord ++ tailWord_2385119) baseStart_2385119 baseEnd_2385119 := by
    simpa [prefixWord, tailWord_2385119, baseEnd_2385119] using wordTrace_append hprefix tailTrace_2385119
  have hstable : (prefixWord ++ tailWord_2385119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385119).length < 2 ^ (prefixWord ++ tailWord_2385119).sum := by decide
  have hdescent : baseEnd_2385119 < baseStart_2385119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385127 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 1, 5]
def baseStart_2385127 : Nat := 118140960795 + 2385127 * 2 ^ 59
def prefixEnd_2385127 : Nat := 4983230072969 + 3 ^ 40 * 2385127 * 2
def baseEnd_2385127 : Nat := 408238857672131637781169

theorem tailTrace_2385127 : CollatzResearch.WordTrace tailWord_2385127 prefixEnd_2385127 408238857672131637781169 := by
  unfold tailWord_2385127
  simp only [CollatzResearch.WordTrace]
  refine ⟨86992728430099701106137635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57995152286733134070758423 86992728430099701106137635)
  ·
    refine ⟨130489092645149551659206453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86992728430099701106137635 130489092645149551659206453)
    ·
      refine ⟨12233352435482770468050605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130489092645149551659206453 12233352435482770468050605)
      ·
        refine ⟨4587507163306038925518977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12233352435482770468050605 4587507163306038925518977)
        ·
          refine ⟨3440630372479529194139233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4587507163306038925518977 3440630372479529194139233)
          ·
            refine ⟨2580472779359646895604425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3440630372479529194139233 2580472779359646895604425)
            ·
              refine ⟨1935354584519735171703319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2580472779359646895604425 1935354584519735171703319)
              ·
                refine ⟨2903031876779602757554979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935354584519735171703319 2903031876779602757554979)
                ·
                  refine ⟨4354547815169404136332469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903031876779602757554979 4354547815169404136332469)
                  ·
                    refine ⟨408238857672131637781169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4354547815169404136332469 408238857672131637781169)
                    ·
                      rfl

theorem cell23_2385127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_2385127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385127 prefixEnd_2385127 := by exact prefixLift 2385127
  have htrace : WordTrace (prefixWord ++ tailWord_2385127) baseStart_2385127 baseEnd_2385127 := by
    simpa [prefixWord, tailWord_2385127, baseEnd_2385127] using wordTrace_append hprefix tailTrace_2385127
  have hstable : (prefixWord ++ tailWord_2385127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385127).length < 2 ^ (prefixWord ++ tailWord_2385127).sum := by decide
  have hdescent : baseEnd_2385127 < baseStart_2385127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385130 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_2385130 : Nat := 118140960795 + 2385130 * 2 ^ 59
def prefixEnd_2385130 : Nat := 4983230072969 + 3 ^ 40 * 2385130 * 2
def baseEnd_2385130 : Nat := 1224718113458358401605993

theorem tailTrace_2385130 : CollatzResearch.WordTrace tailWord_2385130 prefixEnd_2385130 1224718113458358401605993 := by
  unfold tailWord_2385130
  simp only [CollatzResearch.WordTrace]
  refine ⟨21748209462272208154624211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57995225232725888412331229 21748209462272208154624211)
  ·
    refine ⟨32622314193408312231936317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21748209462272208154624211 32622314193408312231936317)
    ·
      refine ⟨12233367822528117086976119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32622314193408312231936317 12233367822528117086976119)
      ·
        refine ⟨18350051733792175630464179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12233367822528117086976119 18350051733792175630464179)
        ·
          refine ⟨27525077600688263445696269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18350051733792175630464179 27525077600688263445696269)
          ·
            refine ⟨10321904100258098792136101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27525077600688263445696269 10321904100258098792136101)
            ·
              refine ⟨1935357018798393523525519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10321904100258098792136101 1935357018798393523525519)
              ·
                refine ⟨2903035528197590285288279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935357018798393523525519 2903035528197590285288279)
                ·
                  refine ⟨4354553292296385427932419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903035528197590285288279 4354553292296385427932419)
                  ·
                    refine ⟨6531829938444578141898629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4354553292296385427932419 6531829938444578141898629)
                    ·
                      refine ⟨1224718113458358401605993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6531829938444578141898629 1224718113458358401605993)
                      ·
                        rfl

theorem cell23_2385130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_2385130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385130 prefixEnd_2385130 := by exact prefixLift 2385130
  have htrace : WordTrace (prefixWord ++ tailWord_2385130) baseStart_2385130 baseEnd_2385130 := by
    simpa [prefixWord, tailWord_2385130, baseEnd_2385130] using wordTrace_append hprefix tailTrace_2385130
  have hstable : (prefixWord ++ tailWord_2385130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385130).length < 2 ^ (prefixWord ++ tailWord_2385130).sum := by decide
  have hdescent : baseEnd_2385130 < baseStart_2385130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385160 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_2385160 : Nat := 118140960795 + 2385160 * 2 ^ 59
def prefixEnd_2385160 : Nat := 4983230072969 + 3 ^ 40 * 2385160 * 2
def baseEnd_2385160 : Nat := 1224733517877993284230855

theorem tailTrace_2385160 : CollatzResearch.WordTrace tailWord_2385160 prefixEnd_2385160 1224733517877993284230855 := by
  unfold tailWord_2385160
  simp only [CollatzResearch.WordTrace]
  refine ⟨43496966019490073871044467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57995954692653431828059289 43496966019490073871044467)
  ·
    refine ⟨65245449029235110806566701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43496966019490073871044467 65245449029235110806566701)
    ·
      refine ⟨24467043385963166552462513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65245449029235110806566701 24467043385963166552462513)
      ·
        refine ⟨18350282539472374914346885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24467043385963166552462513 18350282539472374914346885)
        ·
          refine ⟨3440677976151070296440041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18350282539472374914346885 3440677976151070296440041)
          ·
            refine ⟨2580508482113302722330031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3440677976151070296440041 2580508482113302722330031)
            ·
              refine ⟨3870762723169954083495047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580508482113302722330031 3870762723169954083495047)
              ·
                refine ⟨5806144084754931125242571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870762723169954083495047 5806144084754931125242571)
                ·
                  refine ⟨8709216127132396687863857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5806144084754931125242571 8709216127132396687863857)
                  ·
                    refine ⟨6531912095349297515897893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8709216127132396687863857 6531912095349297515897893)
                    ·
                      refine ⟨1224733517877993284230855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6531912095349297515897893 1224733517877993284230855)
                      ·
                        rfl

theorem cell23_2385160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_2385160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385160 prefixEnd_2385160 := by exact prefixLift 2385160
  have htrace : WordTrace (prefixWord ++ tailWord_2385160) baseStart_2385160 baseEnd_2385160 := by
    simpa [prefixWord, tailWord_2385160, baseEnd_2385160] using wordTrace_append hprefix tailTrace_2385160
  have hstable : (prefixWord ++ tailWord_2385160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385160).length < 2 ^ (prefixWord ++ tailWord_2385160).sum := by decide
  have hdescent : baseEnd_2385160 < baseStart_2385160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385163 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 3]
def baseStart_2385163 : Nat := 118140960795 + 2385163 * 2 ^ 59
def prefixEnd_2385163 : Nat := 4983230072969 + 3 ^ 40 * 2385163 * 2
def baseEnd_2385163 : Nat := 1224735058319956772493341

theorem tailTrace_2385163 : CollatzResearch.WordTrace tailWord_2385163 prefixEnd_2385163 1224735058319956772493341 := by
  unfold tailWord_2385163
  simp only [CollatzResearch.WordTrace]
  refine ⟨86994041457969279254448143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57996027638646186169632095 86994041457969279254448143)
  ·
    refine ⟨130491062186953918881672215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86994041457969279254448143 130491062186953918881672215)
    ·
      refine ⟨195736593280430878322508323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130491062186953918881672215 195736593280430878322508323)
      ·
        refine ⟨293604889920646317483762485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195736593280430878322508323 293604889920646317483762485)
        ·
          refine ⟨27525458430060592264102733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 293604889920646317483762485 27525458430060592264102733)
          ·
            refine ⟨10322046911272722099038525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27525458430060592264102733 10322046911272722099038525)
            ·
              refine ⟨3870767591727270787139447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10322046911272722099038525 3870767591727270787139447)
              ·
                refine ⟨5806151387590906180709171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870767591727270787139447 5806151387590906180709171)
                ·
                  refine ⟨8709227081386359271063757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5806151387590906180709171 8709227081386359271063757)
                  ·
                    refine ⟨3265960155519884726648909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8709227081386359271063757 3265960155519884726648909)
                    ·
                      refine ⟨1224735058319956772493341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3265960155519884726648909 1224735058319956772493341)
                      ·
                        rfl

theorem cell23_2385163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 3].length) (baseStart_2385163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385163 prefixEnd_2385163 := by exact prefixLift 2385163
  have htrace : WordTrace (prefixWord ++ tailWord_2385163) baseStart_2385163 baseEnd_2385163 := by
    simpa [prefixWord, tailWord_2385163, baseEnd_2385163] using wordTrace_append hprefix tailTrace_2385163
  have hstable : (prefixWord ++ tailWord_2385163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385163).length < 2 ^ (prefixWord ++ tailWord_2385163).sum := by decide
  have hdescent : baseEnd_2385163 < baseStart_2385163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385170 : List Nat := [3, 2, 4, 2, 1, 1, 1, 9]
def baseStart_2385170 : Nat := 118140960795 + 2385170 * 2 ^ 59
def prefixEnd_2385170 : Nat := 4983230072969 + 3 ^ 40 * 2385170 * 2
def baseEnd_2385170 : Nat := 45360690840168083152067

theorem tailTrace_2385170 : CollatzResearch.WordTrace tailWord_2385170 prefixEnd_2385170 45360690840168083152067 := by
  unfold tailWord_2385170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21748574192235979862488241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57996197845962612966635309 21748574192235979862488241)
  ·
    refine ⟨16311430644176984896866181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21748574192235979862488241 16311430644176984896866181)
    ·
      refine ⟨3058393245783184668162409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16311430644176984896866181 3058393245783184668162409)
      ·
        refine ⟨2293794934337388501121807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3058393245783184668162409 2293794934337388501121807)
        ·
          refine ⟨3440692401506082751682711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293794934337388501121807 3440692401506082751682711)
          ·
            refine ⟨5161038602259124127524067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3440692401506082751682711 5161038602259124127524067)
            ·
              refine ⟨7741557903388686191286101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161038602259124127524067 7741557903388686191286101)
              ·
                refine ⟨45360690840168083152067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7741557903388686191286101 45360690840168083152067)
                ·
                  rfl

theorem cell23_2385170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 9].length) (baseStart_2385170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385170 prefixEnd_2385170 := by exact prefixLift 2385170
  have htrace : WordTrace (prefixWord ++ tailWord_2385170) baseStart_2385170 baseEnd_2385170 := by
    simpa [prefixWord, tailWord_2385170, baseEnd_2385170] using wordTrace_append hprefix tailTrace_2385170
  have hstable : (prefixWord ++ tailWord_2385170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385170).length < 2 ^ (prefixWord ++ tailWord_2385170).sum := by decide
  have hdescent : baseEnd_2385170 < baseStart_2385170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385176 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2385176 : Nat := 118140960795 + 2385176 * 2 ^ 59
def prefixEnd_2385176 : Nat := 4983230072969 + 3 ^ 40 * 2385176 * 2
def baseEnd_2385176 : Nat := 1224741733568465221630781

theorem tailTrace_2385176 : CollatzResearch.WordTrace tailWord_2385176 prefixEnd_2385176 1224741733568465221630781 := by
  unfold tailWord_2385176
  simp only [CollatzResearch.WordTrace]
  refine ⟨43497257803461091237335691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57996343737948121649780921 43497257803461091237335691)
  ·
    refine ⟨65245886705191636856003537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43497257803461091237335691 65245886705191636856003537)
    ·
      refine ⟨48934415028893727642002653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65245886705191636856003537 48934415028893727642002653)
      ·
        refine ⟨18350405635835147865750995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48934415028893727642002653 18350405635835147865750995)
        ·
          refine ⟨27525608453752721798626493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18350405635835147865750995 27525608453752721798626493)
          ·
            refine ⟨10322103170157270674484935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27525608453752721798626493 10322103170157270674484935)
            ·
              refine ⟨15483154755235906011727403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10322103170157270674484935 15483154755235906011727403)
              ·
                refine ⟨23224732132853859017591105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15483154755235906011727403 23224732132853859017591105)
                ·
                  refine ⟨17418549099640394263193329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23224732132853859017591105 17418549099640394263193329)
                  ·
                    refine ⟨13063911824730295697394997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17418549099640394263193329 13063911824730295697394997)
                    ·
                      refine ⟨1224741733568465221630781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13063911824730295697394997 1224741733568465221630781)
                      ·
                        rfl

theorem cell23_2385176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2385176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385176 prefixEnd_2385176 := by exact prefixLift 2385176
  have htrace : WordTrace (prefixWord ++ tailWord_2385176) baseStart_2385176 baseEnd_2385176 := by
    simpa [prefixWord, tailWord_2385176, baseEnd_2385176] using wordTrace_append hprefix tailTrace_2385176
  have hstable : (prefixWord ++ tailWord_2385176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385176).length < 2 ^ (prefixWord ++ tailWord_2385176).sum := by decide
  have hdescent : baseEnd_2385176 < baseStart_2385176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385181 : List Nat := [1, 4, 2, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_2385181 : Nat := 118140960795 + 2385181 * 2 ^ 59
def prefixEnd_2385181 : Nat := 4983230072969 + 3 ^ 40 * 2385181 * 2
def baseEnd_2385181 : Nat := 1224744300971737702068259

theorem tailTrace_2385181 : CollatzResearch.WordTrace tailWord_2385181 prefixEnd_2385181 1224744300971737702068259 := by
  unfold tailWord_2385181
  simp only [CollatzResearch.WordTrace]
  refine ⟨86994697971904068328603397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57996465314602712219068931 86994697971904068328603397)
  ·
    refine ⟨16311505869732012811613137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86994697971904068328603397 16311505869732012811613137)
    ·
      refine ⟨12233629402299009608709853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16311505869732012811613137 12233629402299009608709853)
      ·
        refine ⟨4587611025862128603266195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12233629402299009608709853 4587611025862128603266195)
        ·
          refine ⟨6881416538793192904899293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4587611025862128603266195 6881416538793192904899293)
          ·
            refine ⟨2580531202047447339337235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6881416538793192904899293 2580531202047447339337235)
            ·
              refine ⟨3870796803071171009005853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580531202047447339337235 3870796803071171009005853)
              ·
                refine ⟨1451548801151689128377195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3870796803071171009005853 1451548801151689128377195)
                ·
                  refine ⟨2177323201727533692565793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451548801151689128377195 2177323201727533692565793)
                  ·
                    refine ⟨1632992401295650269424345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2177323201727533692565793 1632992401295650269424345)
                    ·
                      refine ⟨1224744300971737702068259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1632992401295650269424345 1224744300971737702068259)
                      ·
                        rfl

theorem cell23_2385181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_2385181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385181 prefixEnd_2385181 := by exact prefixLift 2385181
  have htrace : WordTrace (prefixWord ++ tailWord_2385181) baseStart_2385181 baseEnd_2385181 := by
    simpa [prefixWord, tailWord_2385181, baseEnd_2385181] using wordTrace_append hprefix tailTrace_2385181
  have hstable : (prefixWord ++ tailWord_2385181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385181).length < 2 ^ (prefixWord ++ tailWord_2385181).sum := by decide
  have hdescent : baseEnd_2385181 < baseStart_2385181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385197 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2385197 : Nat := 118140960795 + 2385197 * 2 ^ 59
def prefixEnd_2385197 : Nat := 4983230072969 + 3 ^ 40 * 2385197 * 2
def baseEnd_2385197 : Nat := 1224752516662209639468185

theorem tailTrace_2385197 : CollatzResearch.WordTrace tailWord_2385197 prefixEnd_2385197 1224752516662209639468185 := by
  unfold tailWord_2385197
  simp only [CollatzResearch.WordTrace]
  refine ⟨86995281539846103061185845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57996854359897402040790563 86995281539846103061185845)
  ·
    refine ⟨8155807644360572161986173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86995281539846103061185845 8155807644360572161986173)
    ·
      refine ⟨3058427866635214560744815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8155807644360572161986173 3058427866635214560744815)
      ·
        refine ⟨4587641799952821841117223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058427866635214560744815 4587641799952821841117223)
        ·
          refine ⟨6881462699929232761675835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4587641799952821841117223 6881462699929232761675835)
          ·
            refine ⟨10322194049893849142513753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6881462699929232761675835 10322194049893849142513753)
            ·
              refine ⟨7741645537420386856885315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10322194049893849142513753 7741645537420386856885315)
              ·
                refine ⟨11612468306130580285327973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7741645537420386856885315 11612468306130580285327973)
                ·
                  refine ⟨2177337807399483803498995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11612468306130580285327973 2177337807399483803498995)
                  ·
                    refine ⟨3266006711099225705248493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2177337807399483803498995 3266006711099225705248493)
                    ·
                      refine ⟨1224752516662209639468185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3266006711099225705248493 1224752516662209639468185)
                      ·
                        rfl

theorem cell23_2385197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2385197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385197 prefixEnd_2385197 := by exact prefixLift 2385197
  have htrace : WordTrace (prefixWord ++ tailWord_2385197) baseStart_2385197 baseEnd_2385197 := by
    simpa [prefixWord, tailWord_2385197, baseEnd_2385197] using wordTrace_append hprefix tailTrace_2385197
  have hstable : (prefixWord ++ tailWord_2385197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385197).length < 2 ^ (prefixWord ++ tailWord_2385197).sum := by decide
  have hdescent : baseEnd_2385197 < baseStart_2385197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385216 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_2385216 : Nat := 118140960795 + 2385216 * 2 ^ 59
def prefixEnd_2385216 : Nat := 4983230072969 + 3 ^ 40 * 2385216 * 2
def baseEnd_2385216 : Nat := 1224762272794645065130597

theorem tailTrace_2385216 : CollatzResearch.WordTrace tailWord_2385216 prefixEnd_2385216 1224762272794645065130597 := by
  unfold tailWord_2385216
  simp only [CollatzResearch.WordTrace]
  refine ⟨43497987263388634653063751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57997316351184846204085001 43497987263388634653063751)
  ·
    refine ⟨65246980895082951979595627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43497987263388634653063751 65246980895082951979595627)
    ·
      refine ⟨97870471342624427969393441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65246980895082951979595627 97870471342624427969393441)
      ·
        refine ⟨73402853506968320977045081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97870471342624427969393441 73402853506968320977045081)
        ·
          refine ⟨55052140130226240732783811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73402853506968320977045081 55052140130226240732783811)
          ·
            refine ⟨82578210195339361099175717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55052140130226240732783811 82578210195339361099175717)
            ·
              refine ⟨15483414411626130206095447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82578210195339361099175717 15483414411626130206095447)
              ·
                refine ⟨23225121617439195309143171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15483414411626130206095447 23225121617439195309143171)
                ·
                  refine ⟨34837682426158792963714757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23225121617439195309143171 34837682426158792963714757)
                  ·
                    refine ⟨6532065454904773680696517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34837682426158792963714757 6532065454904773680696517)
                    ·
                      refine ⟨1224762272794645065130597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6532065454904773680696517 1224762272794645065130597)
                      ·
                        rfl

theorem cell23_2385216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_2385216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385216 prefixEnd_2385216 := by exact prefixLift 2385216
  have htrace : WordTrace (prefixWord ++ tailWord_2385216) baseStart_2385216 baseEnd_2385216 := by
    simpa [prefixWord, tailWord_2385216, baseEnd_2385216] using wordTrace_append hprefix tailTrace_2385216
  have hstable : (prefixWord ++ tailWord_2385216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385216).length < 2 ^ (prefixWord ++ tailWord_2385216).sum := by decide
  have hdescent : baseEnd_2385216 < baseStart_2385216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385226 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 7]
def baseStart_2385226 : Nat := 118140960795 + 2385226 * 2 ^ 59
def prefixEnd_2385226 : Nat := 4983230072969 + 3 ^ 40 * 2385226 * 2
def baseEnd_2385226 : Nat := 136085267511243336222839

theorem tailTrace_2385226 : CollatzResearch.WordTrace tailWord_2385226 prefixEnd_2385226 136085267511243336222839 := by
  unfold tailWord_2385226
  simp only [CollatzResearch.WordTrace]
  refine ⟨21749084814185260253497883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57997559504494027342661021 21749084814185260253497883)
  ·
    refine ⟨32623627221277890380246825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21749084814185260253497883 32623627221277890380246825)
    ·
      refine ⟨24467720415958417785185119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32623627221277890380246825 24467720415958417785185119)
      ·
        refine ⟨36701580623937626677777679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24467720415958417785185119 36701580623937626677777679)
        ·
          refine ⟨55052370935906440016666519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36701580623937626677777679 55052370935906440016666519)
          ·
            refine ⟨82578556403859660024999779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55052370935906440016666519 82578556403859660024999779)
            ·
              refine ⟨123867834605789490037499669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82578556403859660024999779 123867834605789490037499669)
              ·
                refine ⟨5806304747146382345507797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123867834605789490037499669 5806304747146382345507797)
                ·
                  refine ⟨136085267511243336222839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5806304747146382345507797 136085267511243336222839)
                  ·
                    rfl

theorem cell23_2385226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_2385226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385226 prefixEnd_2385226 := by exact prefixLift 2385226
  have htrace : WordTrace (prefixWord ++ tailWord_2385226) baseStart_2385226 baseEnd_2385226 := by
    simpa [prefixWord, tailWord_2385226, baseEnd_2385226] using wordTrace_append hprefix tailTrace_2385226
  have hstable : (prefixWord ++ tailWord_2385226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385226).length < 2 ^ (prefixWord ++ tailWord_2385226).sum := by decide
  have hdescent : baseEnd_2385226 < baseStart_2385226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385253 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_2385253 : Nat := 118140960795 + 2385253 * 2 ^ 59
def prefixEnd_2385253 : Nat := 4983230072969 + 3 ^ 40 * 2385253 * 2
def baseEnd_2385253 : Nat := 1224781271578861420367927

theorem tailTrace_2385253 : CollatzResearch.WordTrace tailWord_2385253 prefixEnd_2385253 1224781271578861420367927 := by
  unfold tailWord_2385253
  simp only [CollatzResearch.WordTrace]
  refine ⟨86997324027643224625224413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57998216018428816416816275 86997324027643224625224413)
  ·
    refine ⟨32623996510366209234459155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86997324027643224625224413 32623996510366209234459155)
    ·
      refine ⟨48935994765549313851688733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32623996510366209234459155 48935994765549313851688733)
      ·
        refine ⟨18350998037080992694383275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48935994765549313851688733 18350998037080992694383275)
        ·
          refine ⟨27526497055621489041574913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18350998037080992694383275 27526497055621489041574913)
          ·
            refine ⟨20644872791716116781181185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27526497055621489041574913 20644872791716116781181185)
            ·
              refine ⟨15483654593787087585885889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20644872791716116781181185 15483654593787087585885889)
              ·
                refine ⟨11612740945340315689414417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15483654593787087585885889 11612740945340315689414417)
                ·
                  refine ⟨8709555709005236767060813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11612740945340315689414417 8709555709005236767060813)
                  ·
                    refine ⟨3266083390876963787647805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8709555709005236767060813 3266083390876963787647805)
                    ·
                      refine ⟨1224781271578861420367927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3266083390876963787647805 1224781271578861420367927)
                      ·
                        rfl

theorem cell23_2385253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_2385253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385253 prefixEnd_2385253 := by exact prefixLift 2385253
  have htrace : WordTrace (prefixWord ++ tailWord_2385253) baseStart_2385253 baseEnd_2385253 := by
    simpa [prefixWord, tailWord_2385253, baseEnd_2385253] using wordTrace_append hprefix tailTrace_2385253
  have hstable : (prefixWord ++ tailWord_2385253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385253).length < 2 ^ (prefixWord ++ tailWord_2385253).sum := by decide
  have hdescent : baseEnd_2385253 < baseStart_2385253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385260 : List Nat := [2, 2, 1, 1, 5, 2, 1, 4, 5]
def baseStart_2385260 : Nat := 118140960795 + 2385260 * 2 ^ 59
def prefixEnd_2385260 : Nat := 4983230072969 + 3 ^ 40 * 2385260 * 2
def baseEnd_2385260 : Nat := 136087207327049210331155

theorem tailTrace_2385260 : CollatzResearch.WordTrace tailWord_2385260 prefixEnd_2385260 136087207327049210331155 := by
  unfold tailWord_2385260
  simp only [CollatzResearch.WordTrace]
  refine ⟨43498789669308932410364617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57998386225745243213819489 43498789669308932410364617)
  ·
    refine ⟨32624092251981699307773463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43498789669308932410364617 32624092251981699307773463)
    ·
      refine ⟨48936138377972548961660195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32624092251981699307773463 48936138377972548961660195)
      ·
        refine ⟨73404207566958823442490293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48936138377972548961660195 73404207566958823442490293)
        ·
          refine ⟨6881644459402389697733465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73404207566958823442490293 6881644459402389697733465)
          ·
            refine ⟨5161233344551792273300099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6881644459402389697733465 5161233344551792273300099)
            ·
              refine ⟨7741850016827688409950149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161233344551792273300099 7741850016827688409950149)
              ·
                refine ⟨1451596878155191576865653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7741850016827688409950149 1451596878155191576865653)
                ·
                  refine ⟨136087207327049210331155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1451596878155191576865653 136087207327049210331155)
                  ·
                    rfl

theorem cell23_2385260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_2385260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385260 prefixEnd_2385260 := by exact prefixLift 2385260
  have htrace : WordTrace (prefixWord ++ tailWord_2385260) baseStart_2385260 baseEnd_2385260 := by
    simpa [prefixWord, tailWord_2385260, baseEnd_2385260] using wordTrace_append hprefix tailTrace_2385260
  have hstable : (prefixWord ++ tailWord_2385260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385260).length < 2 ^ (prefixWord ++ tailWord_2385260).sum := by decide
  have hdescent : baseEnd_2385260 < baseStart_2385260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385263 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 1, 7, 2]
def baseStart_2385263 : Nat := 118140960795 + 2385263 * 2 ^ 59
def prefixEnd_2385263 : Nat := 4983230072969 + 3 ^ 40 * 2385263 * 2
def baseEnd_2385263 : Nat := 1224786406385406381242881

theorem tailTrace_2385263 : CollatzResearch.WordTrace tailWord_2385263 prefixEnd_2385263 1224786406385406381242881 := by
  unfold tailWord_2385263
  simp only [CollatzResearch.WordTrace]
  refine ⟨86997688757606996333088443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57998459171737997555392295 86997688757606996333088443)
  ·
    refine ⟨130496533136410494499632665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86997688757606996333088443 130496533136410494499632665)
    ·
      refine ⟨97872399852307870874724499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130496533136410494499632665 97872399852307870874724499)
      ·
        refine ⟨146808599778461806312086749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97872399852307870874724499 146808599778461806312086749)
        ·
          refine ⟨55053224916923177367032531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146808599778461806312086749 55053224916923177367032531)
          ·
            refine ⟨82579837375384766050548797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55053224916923177367032531 82579837375384766050548797)
            ·
              refine ⟨30967439015769287268955799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82579837375384766050548797 30967439015769287268955799)
              ·
                refine ⟨46451158523653930903433699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30967439015769287268955799 46451158523653930903433699)
                ·
                  refine ⟨69676737785480896355150549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46451158523653930903433699 69676737785480896355150549)
                  ·
                    refine ⟨1633048541847208508323841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 69676737785480896355150549 1633048541847208508323841)
                    ·
                      refine ⟨1224786406385406381242881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633048541847208508323841 1224786406385406381242881)
                      ·
                        rfl

theorem cell23_2385263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 7, 2].length) (baseStart_2385263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385263 prefixEnd_2385263 := by exact prefixLift 2385263
  have htrace : WordTrace (prefixWord ++ tailWord_2385263) baseStart_2385263 baseEnd_2385263 := by
    simpa [prefixWord, tailWord_2385263, baseEnd_2385263] using wordTrace_append hprefix tailTrace_2385263
  have hstable : (prefixWord ++ tailWord_2385263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385263).length < 2 ^ (prefixWord ++ tailWord_2385263).sum := by decide
  have hdescent : baseEnd_2385263 < baseStart_2385263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385303 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 7, 4]
def baseStart_2385303 : Nat := 118140960795 + 2385303 * 2 ^ 59
def prefixEnd_2385303 : Nat := 4983230072969 + 3 ^ 40 * 2385303 * 2
def baseEnd_2385303 : Nat := 408268981870528741580899

theorem tailTrace_2385303 : CollatzResearch.WordTrace tailWord_2385303 prefixEnd_2385303 408268981870528741580899 := by
  unfold tailWord_2385303
  simp only [CollatzResearch.WordTrace]
  refine ⟨86999147677462083164544563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57999431784974722109696375 86999147677462083164544563)
  ·
    refine ⟨130498721516193124746816845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86999147677462083164544563 130498721516193124746816845)
    ·
      refine ⟨48937020568572421780056317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130498721516193124746816845 48937020568572421780056317)
      ·
        refine ⟨18351382713214658167521119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48937020568572421780056317 18351382713214658167521119)
        ·
          refine ⟨27527074069821987251281679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18351382713214658167521119 27527074069821987251281679)
          ·
            refine ⟨41290611104732980876922519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27527074069821987251281679 41290611104732980876922519)
            ·
              refine ⟨61935916657099471315383779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41290611104732980876922519 61935916657099471315383779)
              ·
                refine ⟨92903874985649206973075669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61935916657099471315383779 92903874985649206973075669)
                ·
                  refine ⟨2177434569976153288431461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 92903874985649206973075669 2177434569976153288431461)
                  ·
                    refine ⟨408268981870528741580899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2177434569976153288431461 408268981870528741580899)
                    ·
                      rfl

theorem cell23_2385303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_2385303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385303 prefixEnd_2385303 := by exact prefixLift 2385303
  have htrace : WordTrace (prefixWord ++ tailWord_2385303) baseStart_2385303 baseEnd_2385303 := by
    simpa [prefixWord, tailWord_2385303, baseEnd_2385303] using wordTrace_append hprefix tailTrace_2385303
  have hstable : (prefixWord ++ tailWord_2385303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385303).length < 2 ^ (prefixWord ++ tailWord_2385303).sum := by decide
  have hdescent : baseEnd_2385303 < baseStart_2385303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385354 : List Nat := [3, 1, 2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_2385354 : Nat := 118140960795 + 2385354 * 2 ^ 59
def prefixEnd_2385354 : Nat := 4983230072969 + 3 ^ 40 * 2385354 * 2
def baseEnd_2385354 : Nat := 408277711041655175068321

theorem tailTrace_2385354 : CollatzResearch.WordTrace tailWord_2385354 prefixEnd_2385354 408277711041655175068321 := by
  unfold tailWord_2385354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21750251950069329718662779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58000671866851545916434077 21750251950069329718662779)
  ·
    refine ⟨32625377925103994577994169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21750251950069329718662779 32625377925103994577994169)
    ·
      refine ⟨24469033443827995933495627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32625377925103994577994169 24469033443827995933495627)
      ·
        refine ⟨36703550165741993900243441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24469033443827995933495627 36703550165741993900243441)
        ·
          refine ⟨27527662624306495425182581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36703550165741993900243441 27527662624306495425182581)
          ·
            refine ⟨2580718371028733946110867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27527662624306495425182581 2580718371028733946110867)
            ·
              refine ⟨3871077556543100919166301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580718371028733946110867 3871077556543100919166301)
              ·
                refine ⟨1451654083703662844687363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3871077556543100919166301 1451654083703662844687363)
                ·
                  refine ⟨2177481125555494267031045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451654083703662844687363 2177481125555494267031045)
                  ·
                    refine ⟨408277711041655175068321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2177481125555494267031045 408277711041655175068321)
                    ·
                      rfl

theorem cell23_2385354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_2385354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385354 prefixEnd_2385354 := by exact prefixLift 2385354
  have htrace : WordTrace (prefixWord ++ tailWord_2385354) baseStart_2385354 baseEnd_2385354 := by
    simpa [prefixWord, tailWord_2385354, baseEnd_2385354] using wordTrace_append hprefix tailTrace_2385354
  have hstable : (prefixWord ++ tailWord_2385354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385354).length < 2 ^ (prefixWord ++ tailWord_2385354).sum := by decide
  have hdescent : baseEnd_2385354 < baseStart_2385354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385377 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_2385377 : Nat := 118140960795 + 2385377 * 2 ^ 59
def prefixEnd_2385377 : Nat := 4983230072969 + 3 ^ 40 * 2385377 * 2
def baseEnd_2385377 : Nat := 1224844943180018935217357

theorem tailTrace_2385377 : CollatzResearch.WordTrace tailWord_2385377 prefixEnd_2385377 1224844943180018935217357 := by
  unfold tailWord_2385377
  simp only [CollatzResearch.WordTrace]
  refine ⟨87001846679193993802738385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58001231119462662535158923 87001846679193993802738385)
  ·
    refine ⟨65251385009395495352053789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87001846679193993802738385 65251385009395495352053789)
    ·
      refine ⟨24469269378523310757020171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65251385009395495352053789 24469269378523310757020171)
      ·
        refine ⟨36703904067784966135530257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24469269378523310757020171 36703904067784966135530257)
        ·
          refine ⟨27527928050838724601647693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36703904067784966135530257 27527928050838724601647693)
          ·
            refine ⟨10322973019064521725617885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27527928050838724601647693 10322973019064521725617885)
            ·
              refine ⟨3871114882149195647106707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10322973019064521725617885 3871114882149195647106707)
              ·
                refine ⟨5806672323223793470660061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3871114882149195647106707 5806672323223793470660061)
                ·
                  refine ⟨2177502121208922551497523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5806672323223793470660061 2177502121208922551497523)
                  ·
                    refine ⟨3266253181813383827246285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2177502121208922551497523 3266253181813383827246285)
                    ·
                      refine ⟨1224844943180018935217357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3266253181813383827246285 1224844943180018935217357)
                      ·
                        rfl

theorem cell23_2385377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_2385377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385377 prefixEnd_2385377 := by exact prefixLift 2385377
  have htrace : WordTrace (prefixWord ++ tailWord_2385377) baseStart_2385377 baseEnd_2385377 := by
    simpa [prefixWord, tailWord_2385377, baseEnd_2385377] using wordTrace_append hprefix tailTrace_2385377
  have hstable : (prefixWord ++ tailWord_2385377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385377).length < 2 ^ (prefixWord ++ tailWord_2385377).sum := by decide
  have hdescent : baseEnd_2385377 < baseStart_2385377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385397 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2385397 : Nat := 118140960795 + 2385397 * 2 ^ 59
def prefixEnd_2385397 : Nat := 4983230072969 + 3 ^ 40 * 2385397 * 2
def baseEnd_2385397 : Nat := 408285070931036285655755

theorem tailTrace_2385397 : CollatzResearch.WordTrace tailWord_2385397 prefixEnd_2385397 408285070931036285655755 := by
  unfold tailWord_2385397
  simp only [CollatzResearch.WordTrace]
  refine ⟨87002576139121537218466445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58001717426081024812310963 87002576139121537218466445)
  ·
    refine ⟨32625966052170576456924917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87002576139121537218466445 32625966052170576456924917)
    ·
      refine ⟨3058684317390991542836711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32625966052170576456924917 3058684317390991542836711)
      ·
        refine ⟨4588026476086487314255067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058684317390991542836711 4588026476086487314255067)
        ·
          refine ⟨6882039714129730971382601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4588026476086487314255067 6882039714129730971382601)
          ·
            refine ⟨5161529785597298228536951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6882039714129730971382601 5161529785597298228536951)
            ·
              refine ⟨7742294678395947342805427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161529785597298228536951 7742294678395947342805427)
              ·
                refine ⟨11613442017593921014208141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7742294678395947342805427 11613442017593921014208141)
                ·
                  refine ⟨4355040756597720380328053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11613442017593921014208141 4355040756597720380328053)
                  ·
                    refine ⟨408285070931036285655755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4355040756597720380328053 408285070931036285655755)
                    ·
                      rfl

theorem cell23_2385397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2385397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385397 prefixEnd_2385397 := by exact prefixLift 2385397
  have htrace : WordTrace (prefixWord ++ tailWord_2385397) baseStart_2385397 baseEnd_2385397 := by
    simpa [prefixWord, tailWord_2385397, baseEnd_2385397] using wordTrace_append hprefix tailTrace_2385397
  have hstable : (prefixWord ++ tailWord_2385397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385397).length < 2 ^ (prefixWord ++ tailWord_2385397).sum := by decide
  have hdescent : baseEnd_2385397 < baseStart_2385397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385400 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_2385400 : Nat := 118140960795 + 2385400 * 2 ^ 59
def prefixEnd_2385400 : Nat := 4983230072969 + 3 ^ 40 * 2385400 * 2
def baseEnd_2385400 : Nat := 1224856753235072345229751

theorem tailTrace_2385400 : CollatzResearch.WordTrace tailWord_2385400 prefixEnd_2385400 1224856753235072345229751 := by
  unfold tailWord_2385400
  simp only [CollatzResearch.WordTrace]
  refine ⟨43501342779055334365412827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58001790372073779153883769 43501342779055334365412827)
  ·
    refine ⟨65252014168583001548119241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43501342779055334365412827 65252014168583001548119241)
    ·
      refine ⟨48939010626437251161089431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65252014168583001548119241 48939010626437251161089431)
      ·
        refine ⟨73408515939655876741634147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48939010626437251161089431 73408515939655876741634147)
        ·
          refine ⟨110112773909483815112451221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73408515939655876741634147 110112773909483815112451221)
          ·
            refine ⟨5161536277007053833396151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110112773909483815112451221 5161536277007053833396151)
            ·
              refine ⟨7742304415510580750094227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161536277007053833396151 7742304415510580750094227)
              ·
                refine ⟨11613456623265871125141341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7742304415510580750094227 11613456623265871125141341)
                ·
                  refine ⟨4355046233724701671928003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11613456623265871125141341 4355046233724701671928003)
                  ·
                    refine ⟨6532569350587052507892005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4355046233724701671928003 6532569350587052507892005)
                    ·
                      refine ⟨1224856753235072345229751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6532569350587052507892005 1224856753235072345229751)
                      ·
                        rfl

theorem cell23_2385400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_2385400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385400 prefixEnd_2385400 := by exact prefixLift 2385400
  have htrace : WordTrace (prefixWord ++ tailWord_2385400) baseStart_2385400 baseEnd_2385400 := by
    simpa [prefixWord, tailWord_2385400, baseEnd_2385400] using wordTrace_append hprefix tailTrace_2385400
  have hstable : (prefixWord ++ tailWord_2385400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385400).length < 2 ^ (prefixWord ++ tailWord_2385400).sum := by decide
  have hdescent : baseEnd_2385400 < baseStart_2385400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385403 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 3]
def baseStart_2385403 : Nat := 118140960795 + 2385403 * 2 ^ 59
def prefixEnd_2385403 : Nat := 4983230072969 + 3 ^ 40 * 2385403 * 2
def baseEnd_2385403 : Nat := 1224858293677035833492237

theorem tailTrace_2385403 : CollatzResearch.WordTrace tailWord_2385403 prefixEnd_2385403 1224858293677035833492237 := by
  unfold tailWord_2385403
  simp only [CollatzResearch.WordTrace]
  refine ⟨87002794977099800243184863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58001863318066533495456575 87002794977099800243184863)
  ·
    refine ⟨130504192465649700364777295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87002794977099800243184863 130504192465649700364777295)
    ·
      refine ⟨195756288698474550547165943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130504192465649700364777295 195756288698474550547165943)
      ·
        refine ⟨293634433047711825820748915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195756288698474550547165943 293634433047711825820748915)
        ·
          refine ⟨440451649571567738731123373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293634433047711825820748915 440451649571567738731123373)
          ·
            refine ⟨165169368589337902024171265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 440451649571567738731123373 165169368589337902024171265)
            ·
              refine ⟨123877026442003426518128449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165169368589337902024171265 123877026442003426518128449)
              ·
                refine ⟨92907769831502569888596337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123877026442003426518128449 92907769831502569888596337)
                ·
                  refine ⟨69680827373626927416447253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92907769831502569888596337 69680827373626927416447253)
                  ·
                    refine ⟨3266288783138762222645965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69680827373626927416447253 3266288783138762222645965)
                    ·
                      refine ⟨1224858293677035833492237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3266288783138762222645965 1224858293677035833492237)
                      ·
                        rfl

theorem cell23_2385403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 3].length) (baseStart_2385403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385403 prefixEnd_2385403 := by exact prefixLift 2385403
  have htrace : WordTrace (prefixWord ++ tailWord_2385403) baseStart_2385403 baseEnd_2385403 := by
    simpa [prefixWord, tailWord_2385403, baseEnd_2385403] using wordTrace_append hprefix tailTrace_2385403
  have hstable : (prefixWord ++ tailWord_2385403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385403).length < 2 ^ (prefixWord ++ tailWord_2385403).sum := by decide
  have hdescent : baseEnd_2385403 < baseStart_2385403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385417 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 1, 1, 4]
def baseStart_2385417 : Nat := 118140960795 + 2385417 * 2 ^ 59
def prefixEnd_2385417 : Nat := 4983230072969 + 3 ^ 40 * 2385417 * 2
def baseEnd_2385417 : Nat := 1224865482406198778717173

theorem tailTrace_2385417 : CollatzResearch.WordTrace tailWord_2385417 prefixEnd_2385417 1224865482406198778717173 := by
  unfold tailWord_2385417
  simp only [CollatzResearch.WordTrace]
  refine ⟨87003305599049080634194505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58002203732699387089463003 87003305599049080634194505)
  ·
    refine ⟨65252479199286810475645879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87003305599049080634194505 65252479199286810475645879)
    ·
      refine ⟨97878718798930215713468819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65252479199286810475645879 97878718798930215713468819)
      ·
        refine ⟨146818078198395323570203229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97878718798930215713468819 146818078198395323570203229)
        ·
          refine ⟨55056779324398246338826211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146818078198395323570203229 55056779324398246338826211)
          ·
            refine ⟨82585168986597369508239317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55056779324398246338826211 82585168986597369508239317)
            ·
              refine ⟨1935589898123375847849359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82585168986597369508239317 1935589898123375847849359)
              ·
                refine ⟨2903384847185063771774039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935589898123375847849359 2903384847185063771774039)
                ·
                  refine ⟨4355077270777595657661059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903384847185063771774039 4355077270777595657661059)
                  ·
                    refine ⟨6532615906166393486491589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4355077270777595657661059 6532615906166393486491589)
                    ·
                      refine ⟨1224865482406198778717173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6532615906166393486491589 1224865482406198778717173)
                      ·
                        rfl

theorem cell23_2385417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 1, 4].length) (baseStart_2385417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385417 prefixEnd_2385417 := by exact prefixLift 2385417
  have htrace : WordTrace (prefixWord ++ tailWord_2385417) baseStart_2385417 baseEnd_2385417 := by
    simpa [prefixWord, tailWord_2385417, baseEnd_2385417] using wordTrace_append hprefix tailTrace_2385417
  have hstable : (prefixWord ++ tailWord_2385417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385417).length < 2 ^ (prefixWord ++ tailWord_2385417).sum := by decide
  have hdescent : baseEnd_2385417 < baseStart_2385417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385427 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 2, 4]
def baseStart_2385427 : Nat := 118140960795 + 2385427 * 2 ^ 59
def prefixEnd_2385427 : Nat := 4983230072969 + 3 ^ 40 * 2385427 * 2
def baseEnd_2385427 : Nat := 408290205737581246530709

theorem tailTrace_2385427 : CollatzResearch.WordTrace tailWord_2385427 prefixEnd_2385427 408290205737581246530709 := by
  unfold tailWord_2385427
  simp only [CollatzResearch.WordTrace]
  refine ⟨87003670329012852342058535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58002446886008568228039023 87003670329012852342058535)
  ·
    refine ⟨130505505493519278513087803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87003670329012852342058535 130505505493519278513087803)
    ·
      refine ⟨195758258240278917769631705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130505505493519278513087803 195758258240278917769631705)
      ·
        refine ⟨146818693680209188327223779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195758258240278917769631705 146818693680209188327223779)
        ·
          refine ⟨220228040520313782490835669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146818693680209188327223779 220228040520313782490835669)
          ·
            refine ⟨5161594699694854277128961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 220228040520313782490835669 5161594699694854277128961)
            ·
              refine ⟨3871196024771140707846721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5161594699694854277128961 3871196024771140707846721)
              ·
                refine ⟨2903397018578355530885041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3871196024771140707846721 2903397018578355530885041)
                ·
                  refine ⟨2177547763933766648163781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2903397018578355530885041 2177547763933766648163781)
                  ·
                    refine ⟨408290205737581246530709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2177547763933766648163781 408290205737581246530709)
                    ·
                      rfl

theorem cell23_2385427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 4].length) (baseStart_2385427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385427 prefixEnd_2385427 := by exact prefixLift 2385427
  have htrace : WordTrace (prefixWord ++ tailWord_2385427) baseStart_2385427 baseEnd_2385427 := by
    simpa [prefixWord, tailWord_2385427, baseEnd_2385427] using wordTrace_append hprefix tailTrace_2385427
  have hstable : (prefixWord ++ tailWord_2385427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385427).length < 2 ^ (prefixWord ++ tailWord_2385427).sum := by decide
  have hdescent : baseEnd_2385427 < baseStart_2385427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385428 : List Nat := [2, 4, 3, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_2385428 : Nat := 118140960795 + 2385428 * 2 ^ 59
def prefixEnd_2385428 : Nat := 4983230072969 + 3 ^ 40 * 2385428 * 2
def baseEnd_2385428 : Nat := 1224871130693398235679623

theorem tailTrace_2385428 : CollatzResearch.WordTrace tailWord_2385428 prefixEnd_2385428 1224871130693398235679623 := by
  unfold tailWord_2385428
  simp only [CollatzResearch.WordTrace]
  refine ⟨43501853401004614756422469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58002471201339486341896625 43501853401004614756422469)
  ·
    refine ⟨8156597512688365266829213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43501853401004614756422469 8156597512688365266829213)
    ·
      refine ⟨3058724067258136975060955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8156597512688365266829213 3058724067258136975060955)
      ·
        refine ⟨4588086100887205462591433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058724067258136975060955 4588086100887205462591433)
        ·
          refine ⟨3441064575665404096943575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4588086100887205462591433 3441064575665404096943575)
          ·
            refine ⟨5161596863498106145415363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441064575665404096943575 5161596863498106145415363)
            ·
              refine ⟨7742395295247159218123045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161596863498106145415363 7742395295247159218123045)
              ·
                refine ⟨1451699117858842353398071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7742395295247159218123045 1451699117858842353398071)
                ·
                  refine ⟨2177548676788263530097107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451699117858842353398071 2177548676788263530097107)
                  ·
                    refine ⟨3266323015182395295145661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2177548676788263530097107 3266323015182395295145661)
                    ·
                      refine ⟨1224871130693398235679623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3266323015182395295145661 1224871130693398235679623)
                      ·
                        rfl

theorem cell23_2385428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_2385428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385428 prefixEnd_2385428 := by exact prefixLift 2385428
  have htrace : WordTrace (prefixWord ++ tailWord_2385428) baseStart_2385428 baseEnd_2385428 := by
    simpa [prefixWord, tailWord_2385428, baseEnd_2385428] using wordTrace_append hprefix tailTrace_2385428
  have hstable : (prefixWord ++ tailWord_2385428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385428).length < 2 ^ (prefixWord ++ tailWord_2385428).sum := by decide
  have hdescent : baseEnd_2385428 < baseStart_2385428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385440 : List Nat := [2, 1, 1, 6, 1, 1, 3, 8]
def baseStart_2385440 : Nat := 118140960795 + 2385440 * 2 ^ 59
def prefixEnd_2385440 : Nat := 4983230072969 + 3 ^ 40 * 2385440 * 2
def baseEnd_2385440 : Nat := 45365825646713044027021

theorem tailTrace_2385440 : CollatzResearch.WordTrace tailWord_2385440 prefixEnd_2385440 45365825646713044027021 := by
  unfold tailWord_2385440
  simp only [CollatzResearch.WordTrace]
  refine ⟨43502072238982877781140887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58002762985310503708187849 43502072238982877781140887)
  ·
    refine ⟨65253108358474316671711331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43502072238982877781140887 65253108358474316671711331)
    ·
      refine ⟨97879662537711475007566997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65253108358474316671711331 97879662537711475007566997)
      ·
        refine ⟨4588109181455225390979703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97879662537711475007566997 4588109181455225390979703)
        ·
          refine ⟨6882163772182838086469555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4588109181455225390979703 6882163772182838086469555)
          ·
            refine ⟨10323245658274257129704333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6882163772182838086469555 10323245658274257129704333)
            ·
              refine ⟨3871217121852846423639125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10323245658274257129704333 3871217121852846423639125)
              ·
                refine ⟨45365825646713044027021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3871217121852846423639125 45365825646713044027021)
                ·
                  rfl

theorem cell23_2385440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 8].length) (baseStart_2385440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385440 prefixEnd_2385440 := by exact prefixLift 2385440
  have htrace : WordTrace (prefixWord ++ tailWord_2385440) baseStart_2385440 baseEnd_2385440 := by
    simpa [prefixWord, tailWord_2385440, baseEnd_2385440] using wordTrace_append hprefix tailTrace_2385440
  have hstable : (prefixWord ++ tailWord_2385440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385440).length < 2 ^ (prefixWord ++ tailWord_2385440).sum := by decide
  have hdescent : baseEnd_2385440 < baseStart_2385440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385468 : List Nat := [2, 2, 2, 2, 4, 1, 2, 3, 1, 2, 2]
def baseStart_2385468 : Nat := 118140960795 + 2385468 * 2 ^ 59
def prefixEnd_2385468 : Nat := 4983230072969 + 3 ^ 40 * 2385468 * 2
def baseEnd_2385468 : Nat := 1224891669919578079179439

theorem tailTrace_2385468 : CollatzResearch.WordTrace tailWord_2385468 prefixEnd_2385468 1224891669919578079179439 := by
  unfold tailWord_2385468
  simp only [CollatzResearch.WordTrace]
  refine ⟨43502582860932158172150529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58003443814576210896200705 43502582860932158172150529)
  ·
    refine ⟨32626937145699118629112897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43502582860932158172150529 32626937145699118629112897)
    ·
      refine ⟨24470202859274338971834673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32626937145699118629112897 24470202859274338971834673)
      ·
        refine ⟨18352652144455754228876005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24470202859274338971834673 18352652144455754228876005)
        ·
          refine ⟨3441122277085453917914251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18352652144455754228876005 3441122277085453917914251)
          ·
            refine ⟨5161683415628180876871377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441122277085453917914251 5161683415628180876871377)
            ·
              refine ⟨3871262561721135657653533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5161683415628180876871377 3871262561721135657653533)
              ·
                refine ⟨1451723460645425871620075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3871262561721135657653533 1451723460645425871620075)
                ·
                  refine ⟨2177585190968138807430113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451723460645425871620075 2177585190968138807430113)
                  ·
                    refine ⟨1633188893226104105572585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2177585190968138807430113 1633188893226104105572585)
                    ·
                      refine ⟨1224891669919578079179439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633188893226104105572585 1224891669919578079179439)
                      ·
                        rfl

theorem cell23_2385468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_2385468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385468 prefixEnd_2385468 := by exact prefixLift 2385468
  have htrace : WordTrace (prefixWord ++ tailWord_2385468) baseStart_2385468 baseEnd_2385468 := by
    simpa [prefixWord, tailWord_2385468, baseEnd_2385468] using wordTrace_append hprefix tailTrace_2385468
  have hstable : (prefixWord ++ tailWord_2385468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385468).length < 2 ^ (prefixWord ++ tailWord_2385468).sum := by decide
  have hdescent : baseEnd_2385468 < baseStart_2385468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385478 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_2385478 : Nat := 118140960795 + 2385478 * 2 ^ 59
def prefixEnd_2385478 : Nat := 4983230072969 + 3 ^ 40 * 2385478 * 2
def baseEnd_2385478 : Nat := 408298934908707680018131

theorem tailTrace_2385478 : CollatzResearch.WordTrace tailWord_2385478 prefixEnd_2385478 408298934908707680018131 := by
  unfold tailWord_2385478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718922826619627751630159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58003686967885392034776725 2718922826619627751630159)
  ·
    refine ⟨4078384239929441627445239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2718922826619627751630159 4078384239929441627445239)
    ·
      refine ⟨6117576359894162441167859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4078384239929441627445239 6117576359894162441167859)
      ·
        refine ⟨9176364539841243661751789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6117576359894162441167859 9176364539841243661751789)
        ·
          refine ⟨3441136702440466373156921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9176364539841243661751789 3441136702440466373156921)
          ·
            refine ⟨2580852526830349779867691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3441136702440466373156921 2580852526830349779867691)
            ·
              refine ⟨3871278790245524669801537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580852526830349779867691 3871278790245524669801537)
              ·
                refine ⟨2903459092684143502351153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3871278790245524669801537 2903459092684143502351153)
                ·
                  refine ⟨2177594319513107626763365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2903459092684143502351153 2177594319513107626763365)
                  ·
                    refine ⟨408298934908707680018131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2177594319513107626763365 408298934908707680018131)
                    ·
                      rfl

theorem cell23_2385478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_2385478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385478 prefixEnd_2385478 := by exact prefixLift 2385478
  have htrace : WordTrace (prefixWord ++ tailWord_2385478) baseStart_2385478 baseEnd_2385478 := by
    simpa [prefixWord, tailWord_2385478, baseEnd_2385478] using wordTrace_append hprefix tailTrace_2385478
  have hstable : (prefixWord ++ tailWord_2385478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385478).length < 2 ^ (prefixWord ++ tailWord_2385478).sum := by decide
  have hdescent : baseEnd_2385478 < baseStart_2385478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385484 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2385484 : Nat := 118140960795 + 2385484 * 2 ^ 59
def prefixEnd_2385484 : Nat := 4983230072969 + 3 ^ 40 * 2385484 * 2
def baseEnd_2385484 : Nat := 1224899885610050016579365

theorem tailTrace_2385484 : CollatzResearch.WordTrace tailWord_2385484 prefixEnd_2385484 1224899885610050016579365 := by
  unfold tailWord_2385484
  simp only [CollatzResearch.WordTrace]
  refine ⟨43502874644903175538441753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58003832859870900717922337 43502874644903175538441753)
  ·
    refine ⟨32627155983677381653831315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43502874644903175538441753 32627155983677381653831315)
    ·
      refine ⟨48940733975516072480746973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32627155983677381653831315 48940733975516072480746973)
      ·
        refine ⟨18352775240818527180280115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48940733975516072480746973 18352775240818527180280115)
        ·
          refine ⟨27529162861227790770420173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18352775240818527180280115 27529162861227790770420173)
          ·
            refine ⟨10323436072960421538907565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27529162861227790770420173 10323436072960421538907565)
            ·
              refine ⟨3871288527360158077090337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10323436072960421538907565 3871288527360158077090337)
              ·
                refine ⟨2903466395520118557817753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3871288527360158077090337 2903466395520118557817753)
                ·
                  refine ⟨2177599796640088918363315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2903466395520118557817753 2177599796640088918363315)
                  ·
                    refine ⟨3266399694960133377544973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2177599796640088918363315 3266399694960133377544973)
                    ·
                      refine ⟨1224899885610050016579365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3266399694960133377544973 1224899885610050016579365)
                      ·
                        rfl

theorem cell23_2385484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2385484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385484 prefixEnd_2385484 := by exact prefixLift 2385484
  have htrace : WordTrace (prefixWord ++ tailWord_2385484) baseStart_2385484 baseEnd_2385484 := by
    simpa [prefixWord, tailWord_2385484, baseEnd_2385484] using wordTrace_append hprefix tailTrace_2385484
  have hstable : (prefixWord ++ tailWord_2385484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385484).length < 2 ^ (prefixWord ++ tailWord_2385484).sum := by decide
  have hdescent : baseEnd_2385484 < baseStart_2385484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385597 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_2385597 : Nat := 118140960795 + 2385597 * 2 ^ 59
def prefixEnd_2385597 : Nat := 4983230072969 + 3 ^ 40 * 2385597 * 2
def baseEnd_2385597 : Nat := 1224957908924008074466345

theorem tailTrace_2385597 : CollatzResearch.WordTrace tailWord_2385597 prefixEnd_2385597 1224957908924008074466345 := by
  unfold tailWord_2385597
  simp only [CollatzResearch.WordTrace]
  refine ⟨87009870738396971375747045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58006580492264647583831363 87009870738396971375747045)
  ·
    refine ⟨16314350763449432132952571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87009870738396971375747045 16314350763449432132952571)
    ·
      refine ⟨24471526145174148199428857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16314350763449432132952571 24471526145174148199428857)
      ·
        refine ⟨18353644608880611149571643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24471526145174148199428857 18353644608880611149571643)
        ·
          refine ⟨27530466913320916724357465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18353644608880611149571643 27530466913320916724357465)
          ·
            refine ⟨20647850184990687543268099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27530466913320916724357465 20647850184990687543268099)
            ·
              refine ⟨30971775277486031314902149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20647850184990687543268099 30971775277486031314902149)
              ·
                refine ⟨5807207864528630871544153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30971775277486031314902149 5807207864528630871544153)
                ·
                  refine ⟨4355405898396473153658115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5807207864528630871544153 4355405898396473153658115)
                  ·
                    refine ⟨6533108847594709730487173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4355405898396473153658115 6533108847594709730487173)
                    ·
                      refine ⟨1224957908924008074466345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6533108847594709730487173 1224957908924008074466345)
                      ·
                        rfl

theorem cell23_2385597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_2385597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385597 prefixEnd_2385597 := by exact prefixLift 2385597
  have htrace : WordTrace (prefixWord ++ tailWord_2385597) baseStart_2385597 baseEnd_2385597 := by
    simpa [prefixWord, tailWord_2385597, baseEnd_2385597] using wordTrace_append hprefix tailTrace_2385597
  have hstable : (prefixWord ++ tailWord_2385597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385597).length < 2 ^ (prefixWord ++ tailWord_2385597).sum := by decide
  have hdescent : baseEnd_2385597 < baseStart_2385597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385600 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_2385600 : Nat := 118140960795 + 2385600 * 2 ^ 59
def prefixEnd_2385600 : Nat := 4983230072969 + 3 ^ 40 * 2385600 * 2
def baseEnd_2385600 : Nat := 1224959449365971562728831

theorem tailTrace_2385600 : CollatzResearch.WordTrace tailWord_2385600 prefixEnd_2385600 1224959449365971562728831 := by
  unfold tailWord_2385600
  simp only [CollatzResearch.WordTrace]
  refine ⟨43504990078693051444053127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58006653438257401925404169 43504990078693051444053127)
  ·
    refine ⟨65257485118039577166079691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43504990078693051444053127 65257485118039577166079691)
    ·
      refine ⟨97886227677059365749119537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65257485118039577166079691 97886227677059365749119537)
      ·
        refine ⟨73414670757794524311839653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97886227677059365749119537 73414670757794524311839653)
        ·
          refine ⟨13765250767086473308469935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73414670757794524311839653 13765250767086473308469935)
          ·
            refine ⟨20647876150629709962704903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13765250767086473308469935 20647876150629709962704903)
            ·
              refine ⟨30971814225944564944057355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20647876150629709962704903 30971814225944564944057355)
              ·
                refine ⟨46457721338916847416086033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30971814225944564944057355 46457721338916847416086033)
                ·
                  refine ⟨34843291004187635562064525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46457721338916847416086033 34843291004187635562064525)
                  ·
                    refine ⟨13066234126570363335774197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34843291004187635562064525 13066234126570363335774197)
                    ·
                      refine ⟨1224959449365971562728831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13066234126570363335774197 1224959449365971562728831)
                      ·
                        rfl

theorem cell23_2385600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_2385600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385600 prefixEnd_2385600 := by exact prefixLift 2385600
  have htrace : WordTrace (prefixWord ++ tailWord_2385600) baseStart_2385600 baseEnd_2385600 := by
    simpa [prefixWord, tailWord_2385600, baseEnd_2385600] using wordTrace_append hprefix tailTrace_2385600
  have hstable : (prefixWord ++ tailWord_2385600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385600).length < 2 ^ (prefixWord ++ tailWord_2385600).sum := by decide
  have hdescent : baseEnd_2385600 < baseStart_2385600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385607 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 3, 4]
def baseStart_2385607 : Nat := 118140960795 + 2385607 * 2 ^ 59
def prefixEnd_2385607 : Nat := 4983230072969 + 3 ^ 40 * 2385607 * 2
def baseEnd_2385607 : Nat := 408321014576851011780433

theorem tailTrace_2385607 : CollatzResearch.WordTrace tailWord_2385607 prefixEnd_2385607 408321014576851011780433 := by
  unfold tailWord_2385607
  simp only [CollatzResearch.WordTrace]
  refine ⟨87010235468360743083611075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58006823645573828722407383 87010235468360743083611075)
  ·
    refine ⟨130515353202541114625416613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87010235468360743083611075 130515353202541114625416613)
    ·
      refine ⟨24471628725476458992265615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130515353202541114625416613 24471628725476458992265615)
      ·
        refine ⟨36707443088214688488398423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24471628725476458992265615 36707443088214688488398423)
        ·
          refine ⟨55061164632322032732597635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36707443088214688488398423 55061164632322032732597635)
          ·
            refine ⟨82591746948483049098896453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55061164632322032732597635 82591746948483049098896453)
            ·
              refine ⟨15485952552840571706043085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82591746948483049098896453 15485952552840571706043085)
              ·
                refine ⟨5807232207315214389766157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15485952552840571706043085 5807232207315214389766157)
                ·
                  refine ⟨2177712077743205396162309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5807232207315214389766157 2177712077743205396162309)
                  ·
                    refine ⟨408321014576851011780433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2177712077743205396162309 408321014576851011780433)
                    ·
                      rfl

theorem cell23_2385607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_2385607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385607 prefixEnd_2385607 := by exact prefixLift 2385607
  have htrace : WordTrace (prefixWord ++ tailWord_2385607) baseStart_2385607 baseEnd_2385607 := by
    simpa [prefixWord, tailWord_2385607, baseEnd_2385607] using wordTrace_append hprefix tailTrace_2385607
  have hstable : (prefixWord ++ tailWord_2385607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385607).length < 2 ^ (prefixWord ++ tailWord_2385607).sum := by decide
  have hdescent : baseEnd_2385607 < baseStart_2385607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385614 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_2385614 : Nat := 118140960795 + 2385614 * 2 ^ 59
def prefixEnd_2385614 : Nat := 4983230072969 + 3 ^ 40 * 2385614 * 2
def baseEnd_2385614 : Nat := 1224966638095134507953767

theorem tailTrace_2385614 : CollatzResearch.WordTrace tailWord_2385614 prefixEnd_2385614 1224966638095134507953767 := by
  unfold tailWord_2385614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10876311347416922909889487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58006993852890255519410597 10876311347416922909889487)
  ·
    refine ⟨16314467021125384364834231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10876311347416922909889487 16314467021125384364834231)
    ·
      refine ⟨24471700531688076547251347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16314467021125384364834231 24471700531688076547251347)
      ·
        refine ⟨36707550797532114820877021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24471700531688076547251347 36707550797532114820877021)
        ·
          refine ⟨13765331549074543057828883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36707550797532114820877021 13765331549074543057828883)
          ·
            refine ⟨20647997323611814586743325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13765331549074543057828883 20647997323611814586743325)
            ·
              refine ⟨7742998996354430470028747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20647997323611814586743325 7742998996354430470028747)
              ·
                refine ⟨11614498494531645705043121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7742998996354430470028747 11614498494531645705043121)
                ·
                  refine ⟨8710873870898734278782341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11614498494531645705043121 8710873870898734278782341)
                  ·
                    refine ⟨1633288850793512677271689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8710873870898734278782341 1633288850793512677271689)
                    ·
                      refine ⟨1224966638095134507953767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633288850793512677271689 1224966638095134507953767)
                      ·
                        rfl

theorem cell23_2385614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_2385614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385614 prefixEnd_2385614 := by exact prefixLift 2385614
  have htrace : WordTrace (prefixWord ++ tailWord_2385614) baseStart_2385614 baseEnd_2385614 := by
    simpa [prefixWord, tailWord_2385614, baseEnd_2385614] using wordTrace_append hprefix tailTrace_2385614
  have hstable : (prefixWord ++ tailWord_2385614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385614).length < 2 ^ (prefixWord ++ tailWord_2385614).sum := by decide
  have hdescent : baseEnd_2385614 < baseStart_2385614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385628 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2385628 : Nat := 118140960795 + 2385628 * 2 ^ 59
def prefixEnd_2385628 : Nat := 4983230072969 + 3 ^ 40 * 2385628 * 2
def baseEnd_2385628 : Nat := 408324608941432484392901

theorem tailTrace_2385628 : CollatzResearch.WordTrace tailWord_2385628 prefixEnd_2385628 408324608941432484392901 := by
  unfold tailWord_2385628
  simp only [CollatzResearch.WordTrace]
  refine ⟨43505500700642331835062769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58007334267523109113417025 43505500700642331835062769)
  ·
    refine ⟨32629125525481748876297077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43505500700642331835062769 32629125525481748876297077)
    ·
      refine ⟨3058980518013913957152851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32629125525481748876297077 3058980518013913957152851)
      ·
        refine ⟨4588470777020870935729277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058980518013913957152851 4588470777020870935729277)
        ·
          refine ⟨1720676541382826600898479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4588470777020870935729277 1720676541382826600898479)
          ·
            refine ⟨2581014812074239901347719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720676541382826600898479 2581014812074239901347719)
            ·
              refine ⟨3871522218111359852021579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581014812074239901347719 3871522218111359852021579)
              ·
                refine ⟨5807283327167039778032369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3871522218111359852021579 5807283327167039778032369)
                ·
                  refine ⟨4355462495375279833524277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5807283327167039778032369 4355462495375279833524277)
                  ·
                    refine ⟨408324608941432484392901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4355462495375279833524277 408324608941432484392901)
                    ·
                      rfl

theorem cell23_2385628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2385628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385628 prefixEnd_2385628 := by exact prefixLift 2385628
  have htrace : WordTrace (prefixWord ++ tailWord_2385628) baseStart_2385628 baseEnd_2385628 := by
    simpa [prefixWord, tailWord_2385628, baseEnd_2385628] using wordTrace_append hprefix tailTrace_2385628
  have hstable : (prefixWord ++ tailWord_2385628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385628).length < 2 ^ (prefixWord ++ tailWord_2385628).sum := by decide
  have hdescent : baseEnd_2385628 < baseStart_2385628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385654 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_2385654 : Nat := 118140960795 + 2385654 * 2 ^ 59
def prefixEnd_2385654 : Nat := 4983230072969 + 3 ^ 40 * 2385654 * 2
def baseEnd_2385654 : Nat := 136109686369034927939287

theorem tailTrace_2385654 : CollatzResearch.WordTrace tailWord_2385654 prefixEnd_2385654 136109686369034927939287 := by
  unfold tailWord_2385654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5438246856199404381910751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58007966466126980073714677 5438246856199404381910751)
  ·
    refine ⟨8157370284299106572866127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5438246856199404381910751 8157370284299106572866127)
    ·
      refine ⟨12236055426448659859299191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8157370284299106572866127 12236055426448659859299191)
      ·
        refine ⟨18354083139672989788948787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12236055426448659859299191 18354083139672989788948787)
        ·
          refine ⟨27531124709509484683423181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18354083139672989788948787 27531124709509484683423181)
          ·
            refine ⟨10324171766066056756283693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27531124709509484683423181 10324171766066056756283693)
            ·
              refine ⟨3871564412274771283606385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10324171766066056756283693 3871564412274771283606385)
              ·
                refine ⟨2903673309206078462704789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3871564412274771283606385 2903673309206078462704789)
                ·
                  refine ⟨136109686369034927939287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2903673309206078462704789 136109686369034927939287)
                  ·
                    rfl

theorem cell23_2385654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_2385654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385654 prefixEnd_2385654 := by exact prefixLift 2385654
  have htrace : WordTrace (prefixWord ++ tailWord_2385654) baseStart_2385654 baseEnd_2385654 := by
    simpa [prefixWord, tailWord_2385654, baseEnd_2385654] using wordTrace_append hprefix tailTrace_2385654
  have hstable : (prefixWord ++ tailWord_2385654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385654).length < 2 ^ (prefixWord ++ tailWord_2385654).sum := by decide
  have hdescent : baseEnd_2385654 < baseStart_2385654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385671 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 6]
def baseStart_2385671 : Nat := 118140960795 + 2385671 * 2 ^ 59
def prefixEnd_2385671 : Nat := 4983230072969 + 3 ^ 40 * 2385671 * 2
def baseEnd_2385671 : Nat := 136110656276937864993445

theorem tailTrace_2385671 : CollatzResearch.WordTrace tailWord_2385671 prefixEnd_2385671 136110656276937864993445 := by
  unfold tailWord_2385671
  simp only [CollatzResearch.WordTrace]
  refine ⟨87012569740128882013940867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58008379826752588009293911 87012569740128882013940867)
  ·
    refine ⟨130518854610193323020911301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87012569740128882013940867 130518854610193323020911301)
    ·
      refine ⟨24472285239411248066420869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130518854610193323020911301 24472285239411248066420869)
      ·
        refine ⟨4588553482389609012453913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24472285239411248066420869 4588553482389609012453913)
        ·
          refine ⟨3441415111792206759340435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4588553482389609012453913 3441415111792206759340435)
          ·
            refine ⟨5162122667688310139010653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441415111792206759340435 5162122667688310139010653)
            ·
              refine ⟨1935796000383116302128995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5162122667688310139010653 1935796000383116302128995)
              ·
                refine ⟨2903694000574674453193493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935796000383116302128995 2903694000574674453193493)
                ·
                  refine ⟨136110656276937864993445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2903694000574674453193493 136110656276937864993445)
                  ·
                    rfl

theorem cell23_2385671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 6].length) (baseStart_2385671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385671 prefixEnd_2385671 := by exact prefixLift 2385671
  have htrace : WordTrace (prefixWord ++ tailWord_2385671) baseStart_2385671 baseEnd_2385671 := by
    simpa [prefixWord, tailWord_2385671, baseEnd_2385671] using wordTrace_append hprefix tailTrace_2385671
  have hstable : (prefixWord ++ tailWord_2385671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385671).length < 2 ^ (prefixWord ++ tailWord_2385671).sum := by decide
  have hdescent : baseEnd_2385671 < baseStart_2385671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385674 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_2385674 : Nat := 118140960795 + 2385674 * 2 ^ 59
def prefixEnd_2385674 : Nat := 4983230072969 + 3 ^ 40 * 2385674 * 2
def baseEnd_2385674 : Nat := 1224997446934404273203491

theorem tailTrace_2385674 : CollatzResearch.WordTrace tailWord_2385674 prefixEnd_2385674 1224997446934404273203491 := by
  unfold tailWord_2385674
  simp only [CollatzResearch.WordTrace]
  refine ⟨21753169789779503381575019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58008452772745342350866717 21753169789779503381575019)
  ·
    refine ⟨32629754684669255072362529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21753169789779503381575019 32629754684669255072362529)
    ·
      refine ⟨24472316013501941304271897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32629754684669255072362529 24472316013501941304271897)
      ·
        refine ⟨18354237010126455978203923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24472316013501941304271897 18354237010126455978203923)
        ·
          refine ⟨27531355515189683967305885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18354237010126455978203923 27531355515189683967305885)
          ·
            refine ⟨10324258318196131487739707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27531355515189683967305885 10324258318196131487739707)
            ·
              refine ⟨15486387477294197231609561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10324258318196131487739707 15486387477294197231609561)
              ·
                refine ⟨11614790607970647923707171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15486387477294197231609561 11614790607970647923707171)
                ·
                  refine ⟨17422185911955971885560757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11614790607970647923707171 17422185911955971885560757)
                  ·
                    refine ⟨1633329929245872364271321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17422185911955971885560757 1633329929245872364271321)
                    ·
                      refine ⟨1224997446934404273203491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633329929245872364271321 1224997446934404273203491)
                      ·
                        rfl

theorem cell23_2385674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_2385674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385674 prefixEnd_2385674 := by exact prefixLift 2385674
  have htrace : WordTrace (prefixWord ++ tailWord_2385674) baseStart_2385674 baseEnd_2385674 := by
    simpa [prefixWord, tailWord_2385674, baseEnd_2385674] using wordTrace_append hprefix tailTrace_2385674
  have hstable : (prefixWord ++ tailWord_2385674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385674).length < 2 ^ (prefixWord ++ tailWord_2385674).sum := by decide
  have hdescent : baseEnd_2385674 < baseStart_2385674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385714 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_2385714 : Nat := 118140960795 + 2385714 * 2 ^ 59
def prefixEnd_2385714 : Nat := 4983230072969 + 3 ^ 40 * 2385714 * 2
def baseEnd_2385714 : Nat := 408339328720194705567769

theorem tailTrace_2385714 : CollatzResearch.WordTrace tailWord_2385714 prefixEnd_2385714 408339328720194705567769 := by
  unfold tailWord_2385714
  simp only [CollatzResearch.WordTrace]
  refine ⟨21753534519743275089439049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58009425385982066905170797 21753534519743275089439049)
  ·
    refine ⟨16315150889807456317079287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21753534519743275089439049 16315150889807456317079287)
    ·
      refine ⟨24472726334711184475618931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16315150889807456317079287 24472726334711184475618931)
      ·
        refine ⟨36709089502066776713428397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24472726334711184475618931 36709089502066776713428397)
        ·
          refine ⟨13765908563275041267535649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36709089502066776713428397 13765908563275041267535649)
          ·
            refine ⟨10324431422456280950651737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13765908563275041267535649 10324431422456280950651737)
            ·
              refine ⟨7743323566842210712988803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10324431422456280950651737 7743323566842210712988803)
              ·
                refine ⟨11614985350263316069483205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7743323566842210712988803 11614985350263316069483205)
                ·
                  refine ⟨2177809753174371763028101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11614985350263316069483205 2177809753174371763028101)
                  ·
                    refine ⟨408339328720194705567769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2177809753174371763028101 408339328720194705567769)
                    ·
                      rfl

theorem cell23_2385714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_2385714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385714 prefixEnd_2385714 := by exact prefixLift 2385714
  have htrace : WordTrace (prefixWord ++ tailWord_2385714) baseStart_2385714 baseEnd_2385714 := by
    simpa [prefixWord, tailWord_2385714, baseEnd_2385714] using wordTrace_append hprefix tailTrace_2385714
  have hstable : (prefixWord ++ tailWord_2385714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385714).length < 2 ^ (prefixWord ++ tailWord_2385714).sum := by decide
  have hdescent : baseEnd_2385714 < baseStart_2385714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385715 : List Nat := [1, 1, 1, 2, 7, 1, 3, 2, 1, 1, 3]
def baseStart_2385715 : Nat := 118140960795 + 2385715 * 2 ^ 59
def prefixEnd_2385715 : Nat := 4983230072969 + 3 ^ 40 * 2385715 * 2
def baseEnd_2385715 : Nat := 1225018499641238612790803

theorem tailTrace_2385715 : CollatzResearch.WordTrace tailWord_2385715 prefixEnd_2385715 1225018499641238612790803 := by
  unfold tailWord_2385715
  simp only [CollatzResearch.WordTrace]
  refine ⟨87014174551969477528542599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58009449701312985019028399 87014174551969477528542599)
  ·
    refine ⟨130521261827954216292813899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87014174551969477528542599 130521261827954216292813899)
    ·
      refine ⟨195781892741931324439220849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130521261827954216292813899 195781892741931324439220849)
      ·
        refine ⟨146836419556448493329415637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195781892741931324439220849 146836419556448493329415637)
        ·
          refine ⟨3441478583354261562408179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 146836419556448493329415637 3441478583354261562408179)
          ·
            refine ⟨5162217875031392343612269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441478583354261562408179 5162217875031392343612269)
            ·
              refine ⟨1935831703136772128854601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5162217875031392343612269 1935831703136772128854601)
              ·
                refine ⟨1451873777352579096640951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1935831703136772128854601 1451873777352579096640951)
                ·
                  refine ⟨2177810666028868644961427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451873777352579096640951 2177810666028868644961427)
                  ·
                    refine ⟨3266715999043302967442141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2177810666028868644961427 3266715999043302967442141)
                    ·
                      refine ⟨1225018499641238612790803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3266715999043302967442141 1225018499641238612790803)
                      ·
                        rfl

theorem cell23_2385715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 1, 3].length) (baseStart_2385715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385715 prefixEnd_2385715 := by exact prefixLift 2385715
  have htrace : WordTrace (prefixWord ++ tailWord_2385715) baseStart_2385715 baseEnd_2385715 := by
    simpa [prefixWord, tailWord_2385715, baseEnd_2385715] using wordTrace_append hprefix tailTrace_2385715
  have hstable : (prefixWord ++ tailWord_2385715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385715).length < 2 ^ (prefixWord ++ tailWord_2385715).sum := by decide
  have hdescent : baseEnd_2385715 < baseStart_2385715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385731 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 2, 4]
def baseStart_2385731 : Nat := 118140960795 + 2385731 * 2 ^ 59
def prefixEnd_2385731 : Nat := 4983230072969 + 3 ^ 40 * 2385731 * 2
def baseEnd_2385731 : Nat := 408342238443903516730243

theorem tailTrace_2385731 : CollatzResearch.WordTrace tailWord_2385731 prefixEnd_2385731 408342238443903516730243 := by
  unfold tailWord_2385731
  simp only [CollatzResearch.WordTrace]
  refine ⟨87014758119911512261125047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58009838746607674840750031 87014758119911512261125047)
  ·
    refine ⟨130522137179867268391687571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87014758119911512261125047 130522137179867268391687571)
    ·
      refine ⟨195783205769800902587531357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130522137179867268391687571 195783205769800902587531357)
      ·
        refine ⟨73418702163675338470324259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195783205769800902587531357 73418702163675338470324259)
        ·
          refine ⟨110128053245513007705486389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73418702163675338470324259 110128053245513007705486389)
          ·
            refine ⟨10324504991766844472389349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110128053245513007705486389 10324504991766844472389349)
            ·
              refine ⟨1935844685956283338573003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10324504991766844472389349 1935844685956283338573003)
              ·
                refine ⟨2903767028934425007859505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935844685956283338573003 2903767028934425007859505)
                ·
                  refine ⟨2177825271700818755894629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2903767028934425007859505 2177825271700818755894629)
                  ·
                    refine ⟨408342238443903516730243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2177825271700818755894629 408342238443903516730243)
                    ·
                      rfl

theorem cell23_2385731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 4].length) (baseStart_2385731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385731 prefixEnd_2385731 := by exact prefixLift 2385731
  have htrace : WordTrace (prefixWord ++ tailWord_2385731) baseStart_2385731 baseEnd_2385731 := by
    simpa [prefixWord, tailWord_2385731, baseEnd_2385731] using wordTrace_append hprefix tailTrace_2385731
  have hstable : (prefixWord ++ tailWord_2385731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385731).length < 2 ^ (prefixWord ++ tailWord_2385731).sum := by decide
  have hdescent : baseEnd_2385731 < baseStart_2385731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385754 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_2385754 : Nat := 118140960795 + 2385754 * 2 ^ 59
def prefixEnd_2385754 : Nat := 4983230072969 + 3 ^ 40 * 2385754 * 2
def baseEnd_2385754 : Nat := 1225038525386763960203123

theorem tailTrace_2385754 : CollatzResearch.WordTrace tailWord_2385754 prefixEnd_2385754 1225038525386763960203123 := by
  unfold tailWord_2385754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21753899249707046797303079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58010397999218791459474877 21753899249707046797303079)
  ·
    refine ⟨32630848874560570195954619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21753899249707046797303079 32630848874560570195954619)
    ·
      refine ⟨48946273311840855293931929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32630848874560570195954619 48946273311840855293931929)
      ·
        refine ⟨36709704983880641470448947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48946273311840855293931929 36709704983880641470448947)
        ·
          refine ⟨55064557475820962205673421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36709704983880641470448947 55064557475820962205673421)
          ·
            refine ⟨20649209053432860827127533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55064557475820962205673421 20649209053432860827127533)
            ·
              refine ⟨7743453395037322810172825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20649209053432860827127533 7743453395037322810172825)
              ·
                refine ⟨5807590046277992107629619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7743453395037322810172825 5807590046277992107629619)
                ·
                  refine ⟨8711385069416988161444429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5807590046277992107629619 8711385069416988161444429)
                  ·
                    refine ⟨3266769401031370560541661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8711385069416988161444429 3266769401031370560541661)
                    ·
                      refine ⟨1225038525386763960203123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3266769401031370560541661 1225038525386763960203123)
                      ·
                        rfl

theorem cell23_2385754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_2385754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385754 prefixEnd_2385754 := by exact prefixLift 2385754
  have htrace : WordTrace (prefixWord ++ tailWord_2385754) baseStart_2385754 baseEnd_2385754 := by
    simpa [prefixWord, tailWord_2385754, baseEnd_2385754] using wordTrace_append hprefix tailTrace_2385754
  have hstable : (prefixWord ++ tailWord_2385754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385754).length < 2 ^ (prefixWord ++ tailWord_2385754).sum := by decide
  have hdescent : baseEnd_2385754 < baseStart_2385754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385772 : List Nat := [2, 2, 1, 1, 4, 4, 2, 2, 1, 2, 2]
def baseStart_2385772 : Nat := 118140960795 + 2385772 * 2 ^ 59
def prefixEnd_2385772 : Nat := 4983230072969 + 3 ^ 40 * 2385772 * 2
def baseEnd_2385772 : Nat := 1225047768038544889778041

theorem tailTrace_2385772 : CollatzResearch.WordTrace tailWord_2385772 prefixEnd_2385772 1225047768038544889778041 := by
  unfold tailWord_2385772
  simp only [CollatzResearch.WordTrace]
  refine ⟨43508126756381488131683785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58010835675175317508911713 43508126756381488131683785)
  ·
    refine ⟨32631095067286116098762839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43508126756381488131683785 32631095067286116098762839)
    ·
      refine ⟨48946642600929174148144259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32631095067286116098762839 48946642600929174148144259)
      ·
        refine ⟨73419963901393761222216389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48946642600929174148144259 73419963901393761222216389)
        ·
          refine ⟨13766243231511330229165573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73419963901393761222216389 13766243231511330229165573)
          ·
            refine ⟨2581170605908374417968545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13766243231511330229165573 2581170605908374417968545)
            ·
              refine ⟨1935877954431280813476409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2581170605908374417968545 1935877954431280813476409)
              ·
                refine ⟨1451908465823460610107307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1935877954431280813476409 1451908465823460610107307)
                ·
                  refine ⟨2177862698735190915160961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451908465823460610107307 2177862698735190915160961)
                  ·
                    refine ⟨1633397024051393186370721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2177862698735190915160961 1633397024051393186370721)
                    ·
                      refine ⟨1225047768038544889778041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633397024051393186370721 1225047768038544889778041)
                      ·
                        rfl

theorem cell23_2385772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 2, 2].length) (baseStart_2385772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385772 prefixEnd_2385772 := by exact prefixLift 2385772
  have htrace : WordTrace (prefixWord ++ tailWord_2385772) baseStart_2385772 baseEnd_2385772 := by
    simpa [prefixWord, tailWord_2385772, baseEnd_2385772] using wordTrace_append hprefix tailTrace_2385772
  have hstable : (prefixWord ++ tailWord_2385772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385772).length < 2 ^ (prefixWord ++ tailWord_2385772).sum := by decide
  have hdescent : baseEnd_2385772 < baseStart_2385772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385774 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2385774 : Nat := 118140960795 + 2385774 * 2 ^ 59
def prefixEnd_2385774 : Nat := 4983230072969 + 3 ^ 40 * 2385774 * 2
def baseEnd_2385774 : Nat := 408349598333284627317677

theorem tailTrace_2385774 : CollatzResearch.WordTrace tailWord_2385774 prefixEnd_2385774 408349598333284627317677 := by
  unfold tailWord_2385774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10877040807344466325617547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58010884305837153736626917 10877040807344466325617547)
  ·
    refine ⟨16315561211016699488426321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10877040807344466325617547 16315561211016699488426321)
    ·
      refine ⟨12236670908262524616319741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16315561211016699488426321 12236670908262524616319741)
      ·
        refine ⟨4588751590598446731119903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12236670908262524616319741 4588751590598446731119903)
        ·
          refine ⟨6883127385897670096679855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4588751590598446731119903 6883127385897670096679855)
          ·
            refine ⟨10324691078846505145019783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6883127385897670096679855 10324691078846505145019783)
            ·
              refine ⟨15487036618269757717529675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10324691078846505145019783 15487036618269757717529675)
              ·
                refine ⟨23230554927404636576294513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15487036618269757717529675 23230554927404636576294513)
                ·
                  refine ⟨17422916195553477432220885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23230554927404636576294513 17422916195553477432220885)
                  ·
                    refine ⟨408349598333284627317677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17422916195553477432220885 408349598333284627317677)
                    ·
                      rfl

theorem cell23_2385774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2385774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385774 prefixEnd_2385774 := by exact prefixLift 2385774
  have htrace : WordTrace (prefixWord ++ tailWord_2385774) baseStart_2385774 baseEnd_2385774 := by
    simpa [prefixWord, tailWord_2385774, baseEnd_2385774] using wordTrace_append hprefix tailTrace_2385774
  have hstable : (prefixWord ++ tailWord_2385774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385774).length < 2 ^ (prefixWord ++ tailWord_2385774).sum := by decide
  have hdescent : baseEnd_2385774 < baseStart_2385774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385777 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_2385777 : Nat := 118140960795 + 2385777 * 2 ^ 59
def prefixEnd_2385777 : Nat := 4983230072969 + 3 ^ 40 * 2385777 * 2
def baseEnd_2385777 : Nat := 1225050335441817370215517

theorem tailTrace_2385777 : CollatzResearch.WordTrace tailWord_2385777 prefixEnd_2385777 1225050335441817370215517 := by
  unfold tailWord_2385777
  simp only [CollatzResearch.WordTrace]
  refine ⟨87016435877744862117299585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58010957251829908078199723 87016435877744862117299585)
  ·
    refine ⟨65262326908308646587974689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87016435877744862117299585 65262326908308646587974689)
    ·
      refine ⟨48946745181231484940981017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65262326908308646587974689 48946745181231484940981017)
      ·
        refine ⟨36710058885923613705735763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48946745181231484940981017 36710058885923613705735763)
        ·
          refine ⟨55065088328885420558603645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36710058885923613705735763 55065088328885420558603645)
          ·
            refine ⟨20649408123332032709476367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55065088328885420558603645 20649408123332032709476367)
            ·
              refine ⟨30974112184998049064214551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20649408123332032709476367 30974112184998049064214551)
              ·
                refine ⟨46461168277497073596321827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30974112184998049064214551 46461168277497073596321827)
                ·
                  refine ⟨69691752416245610394482741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46461168277497073596321827 69691752416245610394482741)
                  ·
                    refine ⟨6533601789023025974482757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69691752416245610394482741 6533601789023025974482757)
                    ·
                      refine ⟨1225050335441817370215517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6533601789023025974482757 1225050335441817370215517)
                      ·
                        rfl

theorem cell23_2385777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_2385777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385777 prefixEnd_2385777 := by exact prefixLift 2385777
  have htrace : WordTrace (prefixWord ++ tailWord_2385777) baseStart_2385777 baseEnd_2385777 := by
    simpa [prefixWord, tailWord_2385777, baseEnd_2385777] using wordTrace_append hprefix tailTrace_2385777
  have hstable : (prefixWord ++ tailWord_2385777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385777).length < 2 ^ (prefixWord ++ tailWord_2385777).sum := by decide
  have hdescent : baseEnd_2385777 < baseStart_2385777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385781 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_2385781 : Nat := 118140960795 + 2385781 * 2 ^ 59
def prefixEnd_2385781 : Nat := 4983230072969 + 3 ^ 40 * 2385781 * 2
def baseEnd_2385781 : Nat := 1225052389364435354565499

theorem tailTrace_2385781 : CollatzResearch.WordTrace tailWord_2385781 prefixEnd_2385781 1225052389364435354565499 := by
  unfold tailWord_2385781
  simp only [CollatzResearch.WordTrace]
  refine ⟨87016581769730370800445197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58011054513153580533630131 87016581769730370800445197)
  ·
    refine ⟨32631218163648889050166949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87016581769730370800445197 32631218163648889050166949)
    ·
      refine ⟨6118353405684166696906303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32631218163648889050166949 6118353405684166696906303)
      ·
        refine ⟨9177530108526250045359455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6118353405684166696906303 9177530108526250045359455)
        ·
          refine ⟨13766295162789375068039183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9177530108526250045359455 13766295162789375068039183)
          ·
            refine ⟨20649442744184062602058775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13766295162789375068039183 20649442744184062602058775)
            ·
              refine ⟨30974164116276093903088163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20649442744184062602058775 30974164116276093903088163)
              ·
                refine ⟨46461246174414140854632245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30974164116276093903088163 46461246174414140854632245)
                ·
                  refine ⟨4355741828851325705121773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46461246174414140854632245 4355741828851325705121773)
                  ·
                    refine ⟨1633403185819247139420665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4355741828851325705121773 1633403185819247139420665)
                    ·
                      refine ⟨1225052389364435354565499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633403185819247139420665 1225052389364435354565499)
                      ·
                        rfl

theorem cell23_2385781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_2385781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385781 prefixEnd_2385781 := by exact prefixLift 2385781
  have htrace : WordTrace (prefixWord ++ tailWord_2385781) baseStart_2385781 baseEnd_2385781 := by
    simpa [prefixWord, tailWord_2385781, baseEnd_2385781] using wordTrace_append hprefix tailTrace_2385781
  have hstable : (prefixWord ++ tailWord_2385781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385781).length < 2 ^ (prefixWord ++ tailWord_2385781).sum := by decide
  have hdescent : baseEnd_2385781 < baseStart_2385781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385815 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 1, 3, 2]
def baseStart_2385815 : Nat := 118140960795 + 2385815 * 2 ^ 59
def prefixEnd_2385815 : Nat := 4983230072969 + 3 ^ 40 * 2385815 * 2
def baseEnd_2385815 : Nat := 1225069847706688221540343

theorem tailTrace_2385815 : CollatzResearch.WordTrace tailWord_2385815 prefixEnd_2385815 1225069847706688221540343 := by
  unfold tailWord_2385815
  simp only [CollatzResearch.WordTrace]
  refine ⟨87017821851607194607182899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58011881234404796404788599 87017821851607194607182899)
  ·
    refine ⟨130526732777410791910774349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87017821851607194607182899 130526732777410791910774349)
    ·
      refine ⟨48947524791529046966540381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130526732777410791910774349 48947524791529046966540381)
      ·
        refine ⟨18355321796823392612452643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48947524791529046966540381 18355321796823392612452643)
        ·
          refine ⟨27532982695235088918678965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18355321796823392612452643 27532982695235088918678965)
          ·
            refine ⟨2581217127678289586126153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27532982695235088918678965 2581217127678289586126153)
            ·
              refine ⟨1935912845758717189594615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2581217127678289586126153 1935912845758717189594615)
              ·
                refine ⟨2903869268638075784391923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935912845758717189594615 2903869268638075784391923)
                ·
                  refine ⟨4355803902957113676587885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903869268638075784391923 4355803902957113676587885)
                  ·
                    refine ⟨1633426463608917628720457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4355803902957113676587885 1633426463608917628720457)
                    ·
                      refine ⟨1225069847706688221540343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633426463608917628720457 1225069847706688221540343)
                      ·
                        rfl

theorem cell23_2385815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_2385815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385815 prefixEnd_2385815 := by exact prefixLift 2385815
  have htrace : WordTrace (prefixWord ++ tailWord_2385815) baseStart_2385815 baseEnd_2385815 := by
    simpa [prefixWord, tailWord_2385815, baseEnd_2385815] using wordTrace_append hprefix tailTrace_2385815
  have hstable : (prefixWord ++ tailWord_2385815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385815).length < 2 ^ (prefixWord ++ tailWord_2385815).sum := by decide
  have hdescent : baseEnd_2385815 < baseStart_2385815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385828 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_2385828 : Nat := 118140960795 + 2385828 * 2 ^ 59
def prefixEnd_2385828 : Nat := 4983230072969 + 3 ^ 40 * 2385828 * 2
def baseEnd_2385828 : Nat := 1225076522955196670677783

theorem tailTrace_2385828 : CollatzResearch.WordTrace tailWord_2385828 prefixEnd_2385828 1225076522955196670677783 := by
  unfold tailWord_2385828
  simp only [CollatzResearch.WordTrace]
  refine ⟨43509148000280048913703069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58012197333706731884937425 43509148000280048913703069)
  ·
    refine ⟨16315930500105018342638651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43509148000280048913703069 16315930500105018342638651)
    ·
      refine ⟨24473895750157527513957977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16315930500105018342638651 24473895750157527513957977)
      ·
        refine ⟨18355421812618145635468483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24473895750157527513957977 18355421812618145635468483)
        ·
          refine ⟨27533132718927218453202725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18355421812618145635468483 27533132718927218453202725)
          ·
            refine ⟨5162462384798853459975511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27533132718927218453202725 5162462384798853459975511)
            ·
              refine ⟨7743693577198280189963267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5162462384798853459975511 7743693577198280189963267)
              ·
                refine ⟨11615540365797420284944901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7743693577198280189963267 11615540365797420284944901)
                ·
                  refine ⟨2177913818587016303427169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11615540365797420284944901 2177913818587016303427169)
                  ·
                    refine ⟨1633435363940262227570377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2177913818587016303427169 1633435363940262227570377)
                    ·
                      refine ⟨1225076522955196670677783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633435363940262227570377 1225076522955196670677783)
                      ·
                        rfl

theorem cell23_2385828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_2385828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385828 prefixEnd_2385828 := by exact prefixLift 2385828
  have htrace : WordTrace (prefixWord ++ tailWord_2385828) baseStart_2385828 baseEnd_2385828 := by
    simpa [prefixWord, tailWord_2385828, baseEnd_2385828] using wordTrace_append hprefix tailTrace_2385828
  have hstable : (prefixWord ++ tailWord_2385828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385828).length < 2 ^ (prefixWord ++ tailWord_2385828).sum := by decide
  have hdescent : baseEnd_2385828 < baseStart_2385828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385864 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 1, 7]
def baseStart_2385864 : Nat := 118140960795 + 2385864 * 2 ^ 59
def prefixEnd_2385864 : Nat := 4983230072969 + 3 ^ 40 * 2385864 * 2
def baseEnd_2385864 : Nat := 408365002752919509942539

theorem tailTrace_2385864 : CollatzResearch.WordTrace tailWord_2385864 prefixEnd_2385864 408365002752919509942539 := by
  unfold tailWord_2385864
  simp only [CollatzResearch.WordTrace]
  refine ⟨43509804514214837987858323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58013072685619783983811097 43509804514214837987858323)
  ·
    refine ⟨65264706771322256981787485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43509804514214837987858323 65264706771322256981787485)
    ·
      refine ⟨24474265039245846368170307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65264706771322256981787485 24474265039245846368170307)
      ·
        refine ⟨36711397558868769552255461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24474265039245846368170307 36711397558868769552255461)
        ·
          refine ⟨6883387042287894291047899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36711397558868769552255461 6883387042287894291047899)
          ·
            refine ⟨10325080563431841436571849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6883387042287894291047899 10325080563431841436571849)
            ·
              refine ⟨7743810422573881077428887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10325080563431841436571849 7743810422573881077428887)
              ·
                refine ⟨11615715633860821616143331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7743810422573881077428887 11615715633860821616143331)
                ·
                  refine ⟨17423573450791232424214997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11615715633860821616143331 17423573450791232424214997)
                  ·
                    refine ⟨408365002752919509942539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17423573450791232424214997 408365002752919509942539)
                    ·
                      rfl

theorem cell23_2385864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_2385864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385864 prefixEnd_2385864 := by exact prefixLift 2385864
  have htrace : WordTrace (prefixWord ++ tailWord_2385864) baseStart_2385864 baseEnd_2385864 := by
    simpa [prefixWord, tailWord_2385864, baseEnd_2385864] using wordTrace_append hprefix tailTrace_2385864
  have hstable : (prefixWord ++ tailWord_2385864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385864).length < 2 ^ (prefixWord ++ tailWord_2385864).sum := by decide
  have hdescent : baseEnd_2385864 < baseStart_2385864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385868 : List Nat := [2, 2, 1, 4, 1, 4, 1, 3, 5]
def baseStart_2385868 : Nat := 118140960795 + 2385868 * 2 ^ 59
def prefixEnd_2385868 : Nat := 4983230072969 + 3 ^ 40 * 2385868 * 2
def baseEnd_2385868 : Nat := 136121895797930723797511

theorem tailTrace_2385868 : CollatzResearch.WordTrace tailWord_2385868 prefixEnd_2385868 136121895797930723797511 := by
  unfold tailWord_2385868
  simp only [CollatzResearch.WordTrace]
  refine ⟨43509877460207592329431129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58013169946943456439241505 43509877460207592329431129)
  ·
    refine ⟨32632408095155694247073347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43509877460207592329431129 32632408095155694247073347)
    ·
      refine ⟨48948612142733541370610021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32632408095155694247073347 48948612142733541370610021)
      ·
        refine ⟨9177864776762539006989379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48948612142733541370610021 9177864776762539006989379)
        ·
          refine ⟨13766797165143808510484069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9177864776762539006989379 13766797165143808510484069)
          ·
            refine ⟨2581274468464464095715763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13766797165143808510484069 2581274468464464095715763)
            ·
              refine ⟨3871911702696696143573645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581274468464464095715763 3871911702696696143573645)
              ·
                refine ⟨1451966888511261053840117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3871911702696696143573645 1451966888511261053840117)
                ·
                  refine ⟨136121895797930723797511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1451966888511261053840117 136121895797930723797511)
                  ·
                    rfl

theorem cell23_2385868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_2385868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385868 prefixEnd_2385868 := by exact prefixLift 2385868
  have htrace : WordTrace (prefixWord ++ tailWord_2385868) baseStart_2385868 baseEnd_2385868 := by
    simpa [prefixWord, tailWord_2385868, baseEnd_2385868] using wordTrace_append hprefix tailTrace_2385868
  have hstable : (prefixWord ++ tailWord_2385868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385868).length < 2 ^ (prefixWord ++ tailWord_2385868).sum := by decide
  have hdescent : baseEnd_2385868 < baseStart_2385868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385881 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 2, 5]
def baseStart_2385881 : Nat := 118140960795 + 2385881 * 2 ^ 59
def prefixEnd_2385881 : Nat := 4983230072969 + 3 ^ 40 * 2385881 * 2
def baseEnd_2385881 : Nat := 408367912476628321105013

theorem tailTrace_2385881 : CollatzResearch.WordTrace tailWord_2385881 prefixEnd_2385881 408367912476628321105013 := by
  unfold tailWord_2385881
  simp only [CollatzResearch.WordTrace]
  refine ⟨87020229069368087879085497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58013486046245391919390331 87020229069368087879085497)
  ·
    refine ⟨65265171802026065909314123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87020229069368087879085497 65265171802026065909314123)
    ·
      refine ⟨97897757703039098863971185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65265171802026065909314123 97897757703039098863971185)
      ·
        refine ⟨73423318277279324147978389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97897757703039098863971185 73423318277279324147978389)
        ·
          refine ⟨3441718044247468319436487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73423318277279324147978389 3441718044247468319436487)
          ·
            refine ⟨5162577066371202479154731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441718044247468319436487 5162577066371202479154731)
            ·
              refine ⟨7743865599556803718732097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5162577066371202479154731 7743865599556803718732097)
              ·
                refine ⟨5807899199667602789049073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7743865599556803718732097 5807899199667602789049073)
                ·
                  refine ⟨4355924399750702091786805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5807899199667602789049073 4355924399750702091786805)
                  ·
                    refine ⟨408367912476628321105013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4355924399750702091786805 408367912476628321105013)
                    ·
                      rfl

theorem cell23_2385881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_2385881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385881 prefixEnd_2385881 := by exact prefixLift 2385881
  have htrace : WordTrace (prefixWord ++ tailWord_2385881) baseStart_2385881 baseEnd_2385881 := by
    simpa [prefixWord, tailWord_2385881, baseEnd_2385881] using wordTrace_append hprefix tailTrace_2385881
  have hstable : (prefixWord ++ tailWord_2385881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385881).length < 2 ^ (prefixWord ++ tailWord_2385881).sum := by decide
  have hdescent : baseEnd_2385881 < baseStart_2385881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385885 : List Nat := [1, 4, 3, 1, 3, 1, 3, 2, 5]
def baseStart_2385885 : Nat := 118140960795 + 2385885 * 2 ^ 59
def prefixEnd_2385885 : Nat := 4983230072969 + 3 ^ 40 * 2385885 * 2
def baseEnd_2385885 : Nat := 136122865705833660851669

theorem tailTrace_2385885 : CollatzResearch.WordTrace tailWord_2385885 prefixEnd_2385885 136122865705833660851669 := by
  unfold tailWord_2385885
  simp only [CollatzResearch.WordTrace]
  refine ⟨87020374961353596562231109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58013583307569064374820739 87020374961353596562231109)
  ·
    refine ⟨16316320305253799355418333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87020374961353596562231109 16316320305253799355418333)
    ·
      refine ⟨6118620114470174758281875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16316320305253799355418333 6118620114470174758281875)
      ·
        refine ⟨9177930171705262137422813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6118620114470174758281875 9177930171705262137422813)
        ·
          refine ⟨3441723814389473301533555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9177930171705262137422813 3441723814389473301533555)
          ·
            refine ⟨5162585721584209952300333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441723814389473301533555 5162585721584209952300333)
            ·
              refine ⟨1935969645594078732112625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5162585721584209952300333 1935969645594078732112625)
              ·
                refine ⟨1451977234195559049084469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1935969645594078732112625 1451977234195559049084469)
                ·
                  refine ⟨136122865705833660851669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1451977234195559049084469 136122865705833660851669)
                  ·
                    rfl

theorem cell23_2385885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_2385885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385885 prefixEnd_2385885 := by exact prefixLift 2385885
  have htrace : WordTrace (prefixWord ++ tailWord_2385885) baseStart_2385885 baseEnd_2385885 := by
    simpa [prefixWord, tailWord_2385885, baseEnd_2385885] using wordTrace_append hprefix tailTrace_2385885
  have hstable : (prefixWord ++ tailWord_2385885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385885).length < 2 ^ (prefixWord ++ tailWord_2385885).sum := by decide
  have hdescent : baseEnd_2385885 < baseStart_2385885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385904 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 3]
def baseStart_2385904 : Nat := 118140960795 + 2385904 * 2 ^ 59
def prefixEnd_2385904 : Nat := 4983230072969 + 3 ^ 40 * 2385904 * 2
def baseEnd_2385904 : Nat := 1225115547484938373327433

theorem tailTrace_2385904 : CollatzResearch.WordTrace tailWord_2385904 prefixEnd_2385904 1225115547484938373327433 := by
  unfold tailWord_2385904
  simp only [CollatzResearch.WordTrace]
  refine ⟨43510533974142381403586383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58014045298856508538115177 43510533974142381403586383)
  ·
    refine ⟨65265800961213572105379575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43510533974142381403586383 65265800961213572105379575)
    ·
      refine ⟨97898701441820358158069363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65265800961213572105379575 97898701441820358158069363)
      ·
        refine ⟨146848052162730537237104045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97898701441820358158069363 146848052162730537237104045)
        ·
          refine ⟨55068019561023951463914017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146848052162730537237104045 55068019561023951463914017)
          ·
            refine ⟨41301014670767963597935513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55068019561023951463914017 41301014670767963597935513)
            ·
              refine ⟨30975761003075972698451635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41301014670767963597935513 30975761003075972698451635)
              ·
                refine ⟨46463641504613959047677453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30975761003075972698451635 46463641504613959047677453)
                ·
                  refine ⟨17423865564230234642879045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46463641504613959047677453 17423865564230234642879045)
                  ·
                    refine ⟨3266974793293168995539821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17423865564230234642879045 3266974793293168995539821)
                    ·
                      refine ⟨1225115547484938373327433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3266974793293168995539821 1225115547484938373327433)
                      ·
                        rfl

theorem cell23_2385904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_2385904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385904 prefixEnd_2385904 := by exact prefixLift 2385904
  have htrace : WordTrace (prefixWord ++ tailWord_2385904) baseStart_2385904 baseEnd_2385904 := by
    simpa [prefixWord, tailWord_2385904, baseEnd_2385904] using wordTrace_append hprefix tailTrace_2385904
  have hstable : (prefixWord ++ tailWord_2385904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385904).length < 2 ^ (prefixWord ++ tailWord_2385904).sum := by decide
  have hdescent : baseEnd_2385904 < baseStart_2385904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385918 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2385918 : Nat := 118140960795 + 2385918 * 2 ^ 59
def prefixEnd_2385918 : Nat := 4983230072969 + 3 ^ 40 * 2385918 * 2
def baseEnd_2385918 : Nat := 1225122736214101318552369

theorem tailTrace_2385918 : CollatzResearch.WordTrace tailWord_2385918 prefixEnd_2385918 1225122736214101318552369 := by
  unfold tailWord_2385918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10877697321279255399772801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58014385713489362132121605 10877697321279255399772801)
  ·
    refine ⟨8158272990959441549829601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10877697321279255399772801 8158272990959441549829601)
    ·
      refine ⟨6118704743219581162372201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8158272990959441549829601 6118704743219581162372201)
      ·
        refine ⟨4589028557414685871779151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6118704743219581162372201 4589028557414685871779151)
        ·
          refine ⟨6883542836122028807668727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589028557414685871779151 6883542836122028807668727)
          ·
            refine ⟨10325314254183043211503091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6883542836122028807668727 10325314254183043211503091)
            ·
              refine ⟨15487971381274564817254637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10325314254183043211503091 15487971381274564817254637)
              ·
                refine ⟨5807989267977961806470489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15487971381274564817254637 5807989267977961806470489)
                ·
                  refine ⟨4355991950983471354852867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5807989267977961806470489 4355991950983471354852867)
                  ·
                    refine ⟨6533987926475207032279301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4355991950983471354852867 6533987926475207032279301)
                    ·
                      refine ⟨1225122736214101318552369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6533987926475207032279301 1225122736214101318552369)
                      ·
                        rfl

theorem cell23_2385918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2385918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385918 prefixEnd_2385918 := by exact prefixLift 2385918
  have htrace : WordTrace (prefixWord ++ tailWord_2385918) baseStart_2385918 baseEnd_2385918 := by
    simpa [prefixWord, tailWord_2385918, baseEnd_2385918] using wordTrace_append hprefix tailTrace_2385918
  have hstable : (prefixWord ++ tailWord_2385918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385918).length < 2 ^ (prefixWord ++ tailWord_2385918).sum := by decide
  have hdescent : baseEnd_2385918 < baseStart_2385918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385928 : List Nat := [2, 1, 3, 2, 1, 2, 2, 5, 1, 4]
def baseStart_2385928 : Nat := 118140960795 + 2385928 * 2 ^ 59
def prefixEnd_2385928 : Nat := 4983230072969 + 3 ^ 40 * 2385928 * 2
def baseEnd_2385928 : Nat := 408375957006882093142441

theorem tailTrace_2385928 : CollatzResearch.WordTrace tailWord_2385928 prefixEnd_2385928 408375957006882093142441 := by
  unfold tailWord_2385928
  simp only [CollatzResearch.WordTrace]
  refine ⟨43510971650098907453023219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58014628866798543270697625 43510971650098907453023219)
  ·
    refine ⟨65266457475148361179534829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43510971650098907453023219 65266457475148361179534829)
    ·
      refine ⟨24474921553180635442325561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65266457475148361179534829 24474921553180635442325561)
      ·
        refine ⟨18356191164885476581744171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24474921553180635442325561 18356191164885476581744171)
        ·
          refine ⟨27534286747328214872616257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18356191164885476581744171 27534286747328214872616257)
          ·
            refine ⟨20650715060496161154462193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27534286747328214872616257 20650715060496161154462193)
            ·
              refine ⟨15488036295372120865846645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20650715060496161154462193 15488036295372120865846645)
              ·
                refine ⟨1452003402691136331173123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15488036295372120865846645 1452003402691136331173123)
                ·
                  refine ⟨2178005104036704496759685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452003402691136331173123 2178005104036704496759685)
                  ·
                    refine ⟨408375957006882093142441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2178005104036704496759685 408375957006882093142441)
                    ·
                      rfl

theorem cell23_2385928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_2385928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385928 prefixEnd_2385928 := by exact prefixLift 2385928
  have htrace : WordTrace (prefixWord ++ tailWord_2385928) baseStart_2385928 baseEnd_2385928 := by
    simpa [prefixWord, tailWord_2385928, baseEnd_2385928] using wordTrace_append hprefix tailTrace_2385928
  have hstable : (prefixWord ++ tailWord_2385928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385928).length < 2 ^ (prefixWord ++ tailWord_2385928).sum := by decide
  have hdescent : baseEnd_2385928 < baseStart_2385928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385944 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2385944 : Nat := 118140960795 + 2385944 * 2 ^ 59
def prefixEnd_2385944 : Nat := 4983230072969 + 3 ^ 40 * 2385944 * 2
def baseEnd_2385944 : Nat := 1225136086711118216827249

theorem tailTrace_2385944 : CollatzResearch.WordTrace tailWord_2385944 prefixEnd_2385944 1225136086711118216827249 := by
  unfold tailWord_2385944
  simp only [CollatzResearch.WordTrace]
  refine ⟨43511263434069924819314443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58015017912093233092419257 43511263434069924819314443)
  ·
    refine ⟨65266895151104887228971665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43511263434069924819314443 65266895151104887228971665)
    ·
      refine ⟨48950171363328665421728749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65266895151104887228971665 48950171363328665421728749)
      ·
        refine ⟨18356314261248249533148281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48950171363328665421728749 18356314261248249533148281)
        ·
          refine ⟨13767235695936187149861211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18356314261248249533148281 13767235695936187149861211)
          ·
            refine ⟨20650853543904280724791817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13767235695936187149861211 20650853543904280724791817)
            ·
              refine ⟨15488140157928210543593863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20650853543904280724791817 15488140157928210543593863)
              ·
                refine ⟨23232210236892315815390795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15488140157928210543593863 23232210236892315815390795)
                ·
                  refine ⟨34848315355338473723086193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23232210236892315815390795 34848315355338473723086193)
                  ·
                    refine ⟨26136236516503855292314645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34848315355338473723086193 26136236516503855292314645)
                    ·
                      refine ⟨1225136086711118216827249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26136236516503855292314645 1225136086711118216827249)
                      ·
                        rfl

theorem cell23_2385944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2385944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385944 prefixEnd_2385944 := by exact prefixLift 2385944
  have htrace : WordTrace (prefixWord ++ tailWord_2385944) baseStart_2385944 baseEnd_2385944 := by
    simpa [prefixWord, tailWord_2385944, baseEnd_2385944] using wordTrace_append hprefix tailTrace_2385944
  have hstable : (prefixWord ++ tailWord_2385944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385944).length < 2 ^ (prefixWord ++ tailWord_2385944).sum := by decide
  have hdescent : baseEnd_2385944 < baseStart_2385944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385968 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 3, 1, 3]
def baseStart_2385968 : Nat := 118140960795 + 2385968 * 2 ^ 59
def prefixEnd_2385968 : Nat := 4983230072969 + 3 ^ 40 * 2385968 * 2
def baseEnd_2385968 : Nat := 1225148410246826122927139

theorem tailTrace_2385968 : CollatzResearch.WordTrace tailWord_2385968 prefixEnd_2385968 1225148410246826122927139 := by
  unfold tailWord_2385968
  simp only [CollatzResearch.WordTrace]
  refine ⟨43511701110026450868751279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58015601480035267825001705 43511701110026450868751279)
  ·
    refine ⟨65267551665039676303126919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43511701110026450868751279 65267551665039676303126919)
    ·
      refine ⟨97901327497559514454690379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65267551665039676303126919 97901327497559514454690379)
      ·
        refine ⟨146851991246339271682035569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97901327497559514454690379 146851991246339271682035569)
        ·
          refine ⟨110138993434754453761526677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146851991246339271682035569 110138993434754453761526677)
          ·
            refine ⟨5162765317254115020071563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110138993434754453761526677 5162765317254115020071563)
            ·
              refine ⟨7744147975881172530107345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5162765317254115020071563 7744147975881172530107345)
              ·
                refine ⟨5808110981910879397580509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7744147975881172530107345 5808110981910879397580509)
                ·
                  refine ⟨2178041618216579774092691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5808110981910879397580509 2178041618216579774092691)
                  ·
                    refine ⟨3267062427324869661139037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2178041618216579774092691 3267062427324869661139037)
                    ·
                      refine ⟨1225148410246826122927139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3267062427324869661139037 1225148410246826122927139)
                      ·
                        rfl

theorem cell23_2385968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 1, 3].length) (baseStart_2385968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385968 prefixEnd_2385968 := by exact prefixLift 2385968
  have htrace : WordTrace (prefixWord ++ tailWord_2385968) baseStart_2385968 baseEnd_2385968 := by
    simpa [prefixWord, tailWord_2385968, baseEnd_2385968] using wordTrace_append hprefix tailTrace_2385968
  have hstable : (prefixWord ++ tailWord_2385968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385968).length < 2 ^ (prefixWord ++ tailWord_2385968).sum := by decide
  have hdescent : baseEnd_2385968 < baseStart_2385968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385972 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2385972 : Nat := 118140960795 + 2385972 * 2 ^ 59
def prefixEnd_2385972 : Nat := 4983230072969 + 3 ^ 40 * 2385972 * 2
def baseEnd_2385972 : Nat := 1225150464169444107277121

theorem tailTrace_2385972 : CollatzResearch.WordTrace tailWord_2385972 prefixEnd_2385972 1225150464169444107277121 := by
  unfold tailWord_2385972
  simp only [CollatzResearch.WordTrace]
  refine ⟨43511774056019205210324085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58015698741358940280432113 43511774056019205210324085)
  ·
    refine ⟨4079228817751800488467883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43511774056019205210324085 4079228817751800488467883)
    ·
      refine ⟨6118843226627700732701825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4079228817751800488467883 6118843226627700732701825)
      ·
        refine ⟨4589132419970775549526369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6118843226627700732701825 4589132419970775549526369)
        ·
          refine ⟨3441849314978081662144777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4589132419970775549526369 3441849314978081662144777)
          ·
            refine ⟨2581386986233561246608583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3441849314978081662144777 2581386986233561246608583)
            ·
              refine ⟨3872080479350341869912875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581386986233561246608583 3872080479350341869912875)
              ·
                refine ⟨5808120719025512804869313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3872080479350341869912875 5808120719025512804869313)
                ·
                  refine ⟨4356090539269134603651985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5808120719025512804869313 4356090539269134603651985)
                  ·
                    refine ⟨3267067904451850952738989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4356090539269134603651985 3267067904451850952738989)
                    ·
                      refine ⟨1225150464169444107277121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3267067904451850952738989 1225150464169444107277121)
                      ·
                        rfl

theorem cell23_2385972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2385972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2385972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2385972 prefixEnd_2385972 := by exact prefixLift 2385972
  have htrace : WordTrace (prefixWord ++ tailWord_2385972) baseStart_2385972 baseEnd_2385972 := by
    simpa [prefixWord, tailWord_2385972, baseEnd_2385972] using wordTrace_append hprefix tailTrace_2385972
  have hstable : (prefixWord ++ tailWord_2385972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385972).length < 2 ^ (prefixWord ++ tailWord_2385972).sum := by decide
  have hdescent : baseEnd_2385972 < baseStart_2385972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386021 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2386021 : Nat := 118140960795 + 2386021 * 2 ^ 59
def prefixEnd_2386021 : Nat := 4983230072969 + 3 ^ 40 * 2386021 * 2
def baseEnd_2386021 : Nat := 1225175624721514415564395

theorem tailTrace_2386021 : CollatzResearch.WordTrace tailWord_2386021 prefixEnd_2386021 1225175624721514415564395 := by
  unfold tailWord_2386021
  simp only [CollatzResearch.WordTrace]
  refine ⟨87025335288860891789181917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58016890192573927859454611 87025335288860891789181917)
  ·
    refine ⟨32634500733322834420943219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87025335288860891789181917 32634500733322834420943219)
    ·
      refine ⟨48951751099984251631414829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32634500733322834420943219 48951751099984251631414829)
      ·
        refine ⟨18356906662494094361780561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48951751099984251631414829 18356906662494094361780561)
        ·
          refine ⟨13767679996870570771335421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18356906662494094361780561 13767679996870570771335421)
          ·
            refine ⟨5162879998826464039250783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13767679996870570771335421 5162879998826464039250783)
            ·
              refine ⟨7744319998239696058876175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5162879998826464039250783 7744319998239696058876175)
              ·
                refine ⟨11616479997359544088314263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7744319998239696058876175 11616479997359544088314263)
                ·
                  refine ⟨17424719996039316132471395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11616479997359544088314263 17424719996039316132471395)
                  ·
                    refine ⟨26137079994058974198707093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17424719996039316132471395 26137079994058974198707093)
                    ·
                      refine ⟨1225175624721514415564395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26137079994058974198707093 1225175624721514415564395)
                      ·
                        rfl

theorem cell23_2386021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2386021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386021 prefixEnd_2386021 := by exact prefixLift 2386021
  have htrace : WordTrace (prefixWord ++ tailWord_2386021) baseStart_2386021 baseEnd_2386021 := by
    simpa [prefixWord, tailWord_2386021, baseEnd_2386021] using wordTrace_append hprefix tailTrace_2386021
  have hstable : (prefixWord ++ tailWord_2386021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386021).length < 2 ^ (prefixWord ++ tailWord_2386021).sum := by decide
  have hdescent : baseEnd_2386021 < baseStart_2386021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386028 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 3]
def baseStart_2386028 : Nat := 118140960795 + 2386028 * 2 ^ 59
def prefixEnd_2386028 : Nat := 4983230072969 + 3 ^ 40 * 2386028 * 2
def baseEnd_2386028 : Nat := 1225179219086095888176863

theorem tailTrace_2386028 : CollatzResearch.WordTrace tailWord_2386028 prefixEnd_2386028 1225179219086095888176863 := by
  unfold tailWord_2386028
  simp only [CollatzResearch.WordTrace]
  refine ⟨43512795299917765992343369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58017060399890354656457825 43512795299917765992343369)
  ·
    refine ⟨32634596474938324494257527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43512795299917765992343369 32634596474938324494257527)
    ·
      refine ⟨48951894712407486741386291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32634596474938324494257527 48951894712407486741386291)
      ·
        refine ⟨73427842068611230112079437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48951894712407486741386291 73427842068611230112079437)
        ·
          refine ⟨27535440775729211292029789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73427842068611230112079437 27535440775729211292029789)
          ·
            refine ⟨10325790290898454234511171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27535440775729211292029789 10325790290898454234511171)
            ·
              refine ⟨15488685436347681351766757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10325790290898454234511171 15488685436347681351766757)
              ·
                refine ⟨2904128519315190253456267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15488685436347681351766757 2904128519315190253456267)
                ·
                  refine ⟨4356192778972785380184401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904128519315190253456267 4356192778972785380184401)
                  ·
                    refine ⟨3267144584229589035138301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4356192778972785380184401 3267144584229589035138301)
                    ·
                      refine ⟨1225179219086095888176863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3267144584229589035138301 1225179219086095888176863)
                      ·
                        rfl

theorem cell23_2386028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_2386028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386028 prefixEnd_2386028 := by exact prefixLift 2386028
  have htrace : WordTrace (prefixWord ++ tailWord_2386028) baseStart_2386028 baseEnd_2386028 := by
    simpa [prefixWord, tailWord_2386028, baseEnd_2386028] using wordTrace_append hprefix tailTrace_2386028
  have hstable : (prefixWord ++ tailWord_2386028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386028).length < 2 ^ (prefixWord ++ tailWord_2386028).sum := by decide
  have hdescent : baseEnd_2386028 < baseStart_2386028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386031 : List Nat := [1, 1, 2, 1, 3, 4, 4, 7]
def baseStart_2386031 : Nat := 118140960795 + 2386031 * 2 ^ 59
def prefixEnd_2386031 : Nat := 4983230072969 + 3 ^ 40 * 2386031 * 2
def baseEnd_2386031 : Nat := 45377065167705902831087

theorem tailTrace_2386031 : CollatzResearch.WordTrace tailWord_2386031 prefixEnd_2386031 45377065167705902831087 := by
  unfold tailWord_2386031
  simp only [CollatzResearch.WordTrace]
  refine ⟨87025700018824663497045947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58017133345883108998030631 87025700018824663497045947)
  ·
    refine ⟨130538550028236995245568921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87025700018824663497045947 130538550028236995245568921)
    ·
      refine ⟨97903912521177746434176691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130538550028236995245568921 97903912521177746434176691)
      ·
        refine ⟨146855868781766619651265037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97903912521177746434176691 146855868781766619651265037)
        ·
          refine ⟨55070950793162482369224389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146855868781766619651265037 55070950793162482369224389)
          ·
            refine ⟨10325803273717965444229573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55070950793162482369224389 10325803273717965444229573)
            ·
              refine ⟨1936088113822118520793045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10325803273717965444229573 1936088113822118520793045)
              ·
                refine ⟨45377065167705902831087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1936088113822118520793045 45377065167705902831087)
                ·
                  rfl

theorem cell23_2386031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 7].length) (baseStart_2386031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386031 prefixEnd_2386031 := by exact prefixLift 2386031
  have htrace : WordTrace (prefixWord ++ tailWord_2386031) baseStart_2386031 baseEnd_2386031 := by
    simpa [prefixWord, tailWord_2386031, baseEnd_2386031] using wordTrace_append hprefix tailTrace_2386031
  have hstable : (prefixWord ++ tailWord_2386031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386031).length < 2 ^ (prefixWord ++ tailWord_2386031).sum := by decide
  have hdescent : baseEnd_2386031 < baseStart_2386031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386111 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_2386111 : Nat := 118140960795 + 2386111 * 2 ^ 59
def prefixEnd_2386111 : Nat := 4983230072969 + 3 ^ 40 * 2386111 * 2
def baseEnd_2386111 : Nat := 1225221837980419063438981

theorem tailTrace_2386111 : CollatzResearch.WordTrace tailWord_2386111 prefixEnd_2386111 1225221837980419063438981 := by
  unfold tailWord_2386111
  simp only [CollatzResearch.WordTrace]
  refine ⟨87028617858534837159958187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58019078572356558106638791 87028617858534837159958187)
  ·
    refine ⟨130542926787802255739937281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87028617858534837159958187 130542926787802255739937281)
    ·
      refine ⟨97907195090851691804952961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130542926787802255739937281 97907195090851691804952961)
      ·
        refine ⟨73430396318138768853714721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97907195090851691804952961 73430396318138768853714721)
        ·
          refine ⟨55072797238604076640286041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73430396318138768853714721 55072797238604076640286041)
          ·
            refine ⟨41304597928953057480214531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55072797238604076640286041 41304597928953057480214531)
            ·
              refine ⟨61956896893429586220321797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41304597928953057480214531 61956896893429586220321797)
              ·
                refine ⟨11616918167518047416310337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61956896893429586220321797 11616918167518047416310337)
                ·
                  refine ⟨8712688625638535562232753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11616918167518047416310337 8712688625638535562232753)
                  ·
                    refine ⟨6534516469228901671674565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8712688625638535562232753 6534516469228901671674565)
                    ·
                      refine ⟨1225221837980419063438981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6534516469228901671674565 1225221837980419063438981)
                      ·
                        rfl

theorem cell23_2386111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_2386111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386111 prefixEnd_2386111 := by exact prefixLift 2386111
  have htrace : WordTrace (prefixWord ++ tailWord_2386111) baseStart_2386111 baseEnd_2386111 := by
    simpa [prefixWord, tailWord_2386111, baseEnd_2386111] using wordTrace_append hprefix tailTrace_2386111
  have hstable : (prefixWord ++ tailWord_2386111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386111).length < 2 ^ (prefixWord ++ tailWord_2386111).sum := by decide
  have hdescent : baseEnd_2386111 < baseStart_2386111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386161 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_2386161 : Nat := 118140960795 + 2386161 * 2 ^ 59
def prefixEnd_2386161 : Nat := 4983230072969 + 3 ^ 40 * 2386161 * 2
def baseEnd_2386161 : Nat := 1225247512013143867813751

theorem tailTrace_2386161 : CollatzResearch.WordTrace tailWord_2386161 prefixEnd_2386161 1225247512013143867813751 := by
  unfold tailWord_2386161
  simp only [CollatzResearch.WordTrace]
  refine ⟨87030441508353695699278337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58020294338902463799518891 87030441508353695699278337)
  ·
    refine ⟨65272831131265271774458753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87030441508353695699278337 65272831131265271774458753)
    ·
      refine ⟨48954623348448953830844065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65272831131265271774458753 48954623348448953830844065)
      ·
        refine ⟨36715967511336715373133049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48954623348448953830844065 36715967511336715373133049)
        ·
          refine ⟨27536975633502536529849787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36715967511336715373133049 27536975633502536529849787)
          ·
            refine ⟨41305463450253804794774681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27536975633502536529849787 41305463450253804794774681)
            ·
              refine ⟨30979097587690353596081011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41305463450253804794774681 30979097587690353596081011)
              ·
                refine ⟨46468646381535530394121517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30979097587690353596081011 46468646381535530394121517)
                ·
                  refine ⟨17425742393075823897795569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46468646381535530394121517 17425742393075823897795569)
                  ·
                    refine ⟨13069306794806867923346677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17425742393075823897795569 13069306794806867923346677)
                    ·
                      refine ⟨1225247512013143867813751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13069306794806867923346677 1225247512013143867813751)
                      ·
                        rfl

theorem cell23_2386161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_2386161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386161 prefixEnd_2386161 := by exact prefixLift 2386161
  have htrace : WordTrace (prefixWord ++ tailWord_2386161) baseStart_2386161 baseEnd_2386161 := by
    simpa [prefixWord, tailWord_2386161, baseEnd_2386161] using wordTrace_append hprefix tailTrace_2386161
  have hstable : (prefixWord ++ tailWord_2386161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386161).length < 2 ^ (prefixWord ++ tailWord_2386161).sum := by decide
  have hdescent : baseEnd_2386161 < baseStart_2386161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386211 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 10]
def baseStart_2386211 : Nat := 118140960795 + 2386211 * 2 ^ 59
def prefixEnd_2386211 : Nat := 4983230072969 + 3 ^ 40 * 2386211 * 2
def baseEnd_2386211 : Nat := 136141465116207630243169

theorem tailTrace_2386211 : CollatzResearch.WordTrace tailWord_2386211 prefixEnd_2386211 136141465116207630243169 := by
  unfold tailWord_2386211
  simp only [CollatzResearch.WordTrace]
  refine ⟨87032265158172554238598487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58021510105448369492398991 87032265158172554238598487)
  ·
    refine ⟨130548397737258831357897731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87032265158172554238598487 130548397737258831357897731)
    ·
      refine ⟨195822596605888247036846597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130548397737258831357897731 195822596605888247036846597)
      ·
        refine ⟨36716736863604046319408737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195822596605888247036846597 36716736863604046319408737)
        ·
          refine ⟨27537552647703034739556553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36716736863604046319408737 27537552647703034739556553)
          ·
            refine ⟨20653164485777276054667415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27537552647703034739556553 20653164485777276054667415)
            ·
              refine ⟨30979746728665914082001123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20653164485777276054667415 30979746728665914082001123)
              ·
                refine ⟨46469620092998871123001685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30979746728665914082001123 46469620092998871123001685)
                ·
                  refine ⟨136141465116207630243169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 46469620092998871123001685 136141465116207630243169)
                  ·
                    rfl

theorem cell23_2386211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 10].length) (baseStart_2386211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386211 prefixEnd_2386211 := by exact prefixLift 2386211
  have htrace : WordTrace (prefixWord ++ tailWord_2386211) baseStart_2386211 baseEnd_2386211 := by
    simpa [prefixWord, tailWord_2386211, baseEnd_2386211] using wordTrace_append hprefix tailTrace_2386211
  have hstable : (prefixWord ++ tailWord_2386211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386211).length < 2 ^ (prefixWord ++ tailWord_2386211).sum := by decide
  have hdescent : baseEnd_2386211 < baseStart_2386211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386231 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_2386231 : Nat := 118140960795 + 2386231 * 2 ^ 59
def prefixEnd_2386231 : Nat := 4983230072969 + 3 ^ 40 * 2386231 * 2
def baseEnd_2386231 : Nat := 1225283455658958593938429

theorem tailTrace_2386231 : CollatzResearch.WordTrace tailWord_2386231 prefixEnd_2386231 1225283455658958593938429 := by
  unfold tailWord_2386231
  simp only [CollatzResearch.WordTrace]
  refine ⟨87032994618100097654326547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58021996412066731769551031 87032994618100097654326547)
  ·
    refine ⟨130549491927150146481489821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87032994618100097654326547 130549491927150146481489821)
    ·
      refine ⟨48956059472681304930558683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130549491927150146481489821 48956059472681304930558683)
      ·
        refine ⟨73434089209021957395838025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48956059472681304930558683 73434089209021957395838025)
        ·
          refine ⟨55075566906766468046878519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73434089209021957395838025 55075566906766468046878519)
          ·
            refine ⟨82613350360149702070317779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55075566906766468046878519 82613350360149702070317779)
            ·
              refine ⟨123920025540224553105476669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82613350360149702070317779 123920025540224553105476669)
              ·
                refine ⟨46470009577584207414553751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123920025540224553105476669 46470009577584207414553751)
                ·
                  refine ⟨69705014366376311121830627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46470009577584207414553751 69705014366376311121830627)
                  ·
                    refine ⟨104557521549564466682745941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69705014366376311121830627 104557521549564466682745941)
                    ·
                      refine ⟨1225283455658958593938429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 104557521549564466682745941 1225283455658958593938429)
                      ·
                        rfl

theorem cell23_2386231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_2386231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386231 prefixEnd_2386231 := by exact prefixLift 2386231
  have htrace : WordTrace (prefixWord ++ tailWord_2386231) baseStart_2386231 baseEnd_2386231 := by
    simpa [prefixWord, tailWord_2386231, baseEnd_2386231] using wordTrace_append hprefix tailTrace_2386231
  have hstable : (prefixWord ++ tailWord_2386231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386231).length < 2 ^ (prefixWord ++ tailWord_2386231).sum := by decide
  have hdescent : baseEnd_2386231 < baseStart_2386231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386251 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 7]
def baseStart_2386251 : Nat := 118140960795 + 2386251 * 2 ^ 59
def prefixEnd_2386251 : Nat := 4983230072969 + 3 ^ 40 * 2386251 * 2
def baseEnd_2386251 : Nat := 1225293725272048515688337

theorem tailTrace_2386251 : CollatzResearch.WordTrace tailWord_2386251 prefixEnd_2386251 1225293725272048515688337 := by
  unfold tailWord_2386251
  simp only [CollatzResearch.WordTrace]
  refine ⟨87033724078027641070054607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58022482718685094046703071 87033724078027641070054607)
  ·
    refine ⟨130550586117041461605081911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87033724078027641070054607 130550586117041461605081911)
    ·
      refine ⟨195825879175562192407622867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130550586117041461605081911 195825879175562192407622867)
      ·
        refine ⟨293738818763343288611434301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195825879175562192407622867 293738818763343288611434301)
        ·
          refine ⟨110152057036253733229287863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293738818763343288611434301 110152057036253733229287863)
          ·
            refine ⟨165228085554380599843931795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110152057036253733229287863 165228085554380599843931795)
            ·
              refine ⟨247842128331570899765897693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165228085554380599843931795 247842128331570899765897693)
              ·
                refine ⟨92940798124339087412211635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247842128331570899765897693 92940798124339087412211635)
                ·
                  refine ⟨139411197186508631118317453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92940798124339087412211635 139411197186508631118317453)
                  ·
                    refine ⟨52279198944940736669369045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139411197186508631118317453 52279198944940736669369045)
                    ·
                      refine ⟨1225293725272048515688337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52279198944940736669369045 1225293725272048515688337)
                      ·
                        rfl

theorem cell23_2386251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_2386251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386251 prefixEnd_2386251 := by exact prefixLift 2386251
  have htrace : WordTrace (prefixWord ++ tailWord_2386251) baseStart_2386251 baseEnd_2386251 := by
    simpa [prefixWord, tailWord_2386251, baseEnd_2386251] using wordTrace_append hprefix tailTrace_2386251
  have hstable : (prefixWord ++ tailWord_2386251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386251).length < 2 ^ (prefixWord ++ tailWord_2386251).sum := by decide
  have hdescent : baseEnd_2386251 < baseStart_2386251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386298 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_2386298 : Nat := 118140960795 + 2386298 * 2 ^ 59
def prefixEnd_2386298 : Nat := 4983230072969 + 3 ^ 40 * 2386298 * 2
def baseEnd_2386298 : Nat := 1225317858862809831800621

theorem tailTrace_2386298 : CollatzResearch.WordTrace tailWord_2386298 prefixEnd_2386298 1225317858862809831800621 := by
  unfold tailWord_2386298
  simp only [CollatzResearch.WordTrace]
  refine ⟨21758859577214342024253887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58023625539238245398010365 21758859577214342024253887)
  ·
    refine ⟨32638289365821513036380831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21758859577214342024253887 32638289365821513036380831)
    ·
      refine ⟨48957434048732269554571247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32638289365821513036380831 48957434048732269554571247)
      ·
        refine ⟨73436151073098404331856871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48957434048732269554571247 73436151073098404331856871)
        ·
          refine ⟨110154226609647606497785307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73436151073098404331856871 110154226609647606497785307)
          ·
            refine ⟨165231339914471409746677961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110154226609647606497785307 165231339914471409746677961)
            ·
              refine ⟨123923504935853557310008471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165231339914471409746677961 123923504935853557310008471)
              ·
                refine ⟨185885257403780335965012707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123923504935853557310008471 185885257403780335965012707)
                ·
                  refine ⟨278827886105670503947519061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185885257403780335965012707 278827886105670503947519061)
                  ·
                    refine ⟨3267514290300826218134989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 278827886105670503947519061 3267514290300826218134989)
                    ·
                      refine ⟨1225317858862809831800621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3267514290300826218134989 1225317858862809831800621)
                      ·
                        rfl

theorem cell23_2386298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_2386298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386298 prefixEnd_2386298 := by exact prefixLift 2386298
  have htrace : WordTrace (prefixWord ++ tailWord_2386298) baseStart_2386298 baseEnd_2386298 := by
    simpa [prefixWord, tailWord_2386298, baseEnd_2386298] using wordTrace_append hprefix tailTrace_2386298
  have hstable : (prefixWord ++ tailWord_2386298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386298).length < 2 ^ (prefixWord ++ tailWord_2386298).sum := by decide
  have hdescent : baseEnd_2386298 < baseStart_2386298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386305 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2386305 : Nat := 118140960795 + 2386305 * 2 ^ 59
def prefixEnd_2386305 : Nat := 4983230072969 + 3 ^ 40 * 2386305 * 2
def baseEnd_2386305 : Nat := 408440484409130434804363

theorem tailTrace_2386305 : CollatzResearch.WordTrace tailWord_2386305 prefixEnd_2386305 408440484409130434804363 := by
  unfold tailWord_2386305
  simp only [CollatzResearch.WordTrace]
  refine ⟨87035693619832008292520369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58023795746554672195013579 87035693619832008292520369)
  ·
    refine ⟨65276770214874006219390277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87035693619832008292520369 65276770214874006219390277)
    ·
      refine ⟨12239394415288876166135677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65276770214874006219390277 12239394415288876166135677)
      ·
        refine ⟨4589772905733328562300879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12239394415288876166135677 4589772905733328562300879)
        ·
          refine ⟨6884659358599992843451319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589772905733328562300879 6884659358599992843451319)
          ·
            refine ⟨10326989037899989265176979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6884659358599992843451319 10326989037899989265176979)
            ·
              refine ⟨15490483556849983897765469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10326989037899989265176979 15490483556849983897765469)
              ·
                refine ⟨5808931333818743961662051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15490483556849983897765469 5808931333818743961662051)
                ·
                  refine ⟨8713397000728115942493077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5808931333818743961662051 8713397000728115942493077)
                  ·
                    refine ⟨408440484409130434804363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8713397000728115942493077 408440484409130434804363)
                    ·
                      rfl

theorem cell23_2386305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2386305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386305 prefixEnd_2386305 := by exact prefixLift 2386305
  have htrace : WordTrace (prefixWord ++ tailWord_2386305) baseStart_2386305 baseEnd_2386305 := by
    simpa [prefixWord, tailWord_2386305, baseEnd_2386305] using wordTrace_append hprefix tailTrace_2386305
  have hstable : (prefixWord ++ tailWord_2386305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386305).length < 2 ^ (prefixWord ++ tailWord_2386305).sum := by decide
  have hdescent : baseEnd_2386305 < baseStart_2386305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386306 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2386306 : Nat := 118140960795 + 2386306 * 2 ^ 59
def prefixEnd_2386306 : Nat := 4983230072969 + 3 ^ 40 * 2386306 * 2
def baseEnd_2386306 : Nat := 1225321966708045800500585

theorem tailTrace_2386306 : CollatzResearch.WordTrace tailWord_2386306 prefixEnd_2386306 1225321966708045800500585 := by
  unfold tailWord_2386306
  simp only [CollatzResearch.WordTrace]
  refine ⟨21758932523207096365826693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58023820061885590308871181 21758932523207096365826693)
  ·
    refine ⟨4079799848101330568592505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21758932523207096365826693 4079799848101330568592505)
    ·
      refine ⟨3059849886075997926444379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4079799848101330568592505 3059849886075997926444379)
      ·
        refine ⟨4589774829113996889666569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3059849886075997926444379 4589774829113996889666569)
        ·
          refine ⟨3442331121835497667249927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4589774829113996889666569 3442331121835497667249927)
          ·
            refine ⟨5163496682753246500874891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442331121835497667249927 5163496682753246500874891)
            ·
              refine ⟨7745245024129869751312337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163496682753246500874891 7745245024129869751312337)
              ·
                refine ⟨5808933768097402313484253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7745245024129869751312337 5808933768097402313484253)
                ·
                  refine ⟨2178350163036525867556595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5808933768097402313484253 2178350163036525867556595)
                  ·
                    refine ⟨3267525244554788801334893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2178350163036525867556595 3267525244554788801334893)
                    ·
                      refine ⟨1225321966708045800500585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3267525244554788801334893 1225321966708045800500585)
                      ·
                        rfl

theorem cell23_2386306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2386306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386306 prefixEnd_2386306 := by exact prefixLift 2386306
  have htrace : WordTrace (prefixWord ++ tailWord_2386306) baseStart_2386306 baseEnd_2386306 := by
    simpa [prefixWord, tailWord_2386306, baseEnd_2386306] using wordTrace_append hprefix tailTrace_2386306
  have hstable : (prefixWord ++ tailWord_2386306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386306).length < 2 ^ (prefixWord ++ tailWord_2386306).sum := by decide
  have hdescent : baseEnd_2386306 < baseStart_2386306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386315 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 3]
def baseStart_2386315 : Nat := 118140960795 + 2386315 * 2 ^ 59
def prefixEnd_2386315 : Nat := 4983230072969 + 3 ^ 40 * 2386315 * 2
def baseEnd_2386315 : Nat := 1225326588033936265288043

theorem tailTrace_2386315 : CollatzResearch.WordTrace tailWord_2386315 prefixEnd_2386315 1225326588033936265288043 := by
  unfold tailWord_2386315
  simp only [CollatzResearch.WordTrace]
  refine ⟨87036058349795780000384399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58024038899863853333589599 87036058349795780000384399)
  ·
    refine ⟨130554087524693670000576599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87036058349795780000384399 130554087524693670000576599)
    ·
      refine ⟨195831131287040505000864899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130554087524693670000576599 195831131287040505000864899)
      ·
        refine ⟨293746696930560757501297349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195831131287040505000864899 293746696930560757501297349)
        ·
          refine ⟨55077505674480142031493253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293746696930560757501297349 55077505674480142031493253)
          ·
            refine ⟨10327032313965026630904985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55077505674480142031493253 10327032313965026630904985)
            ·
              refine ⟨7745274235473769973178739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10327032313965026630904985 7745274235473769973178739)
              ·
                refine ⟨11617911353210654959768109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7745274235473769973178739 11617911353210654959768109)
                ·
                  refine ⟨4356716757453995609913041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11617911353210654959768109 4356716757453995609913041)
                  ·
                    refine ⟨3267537568090496707434781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4356716757453995609913041 3267537568090496707434781)
                    ·
                      refine ⟨1225326588033936265288043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3267537568090496707434781 1225326588033936265288043)
                      ·
                        rfl

theorem cell23_2386315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 3].length) (baseStart_2386315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386315 prefixEnd_2386315 := by exact prefixLift 2386315
  have htrace : WordTrace (prefixWord ++ tailWord_2386315) baseStart_2386315 baseEnd_2386315 := by
    simpa [prefixWord, tailWord_2386315, baseEnd_2386315] using wordTrace_append hprefix tailTrace_2386315
  have hstable : (prefixWord ++ tailWord_2386315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386315).length < 2 ^ (prefixWord ++ tailWord_2386315).sum := by decide
  have hdescent : baseEnd_2386315 < baseStart_2386315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386356 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2386356 : Nat := 118140960795 + 2386356 * 2 ^ 59
def prefixEnd_2386356 : Nat := 4983230072969 + 3 ^ 40 * 2386356 * 2
def baseEnd_2386356 : Nat := 408449213580256868291785

theorem tailTrace_2386356 : CollatzResearch.WordTrace tailWord_2386356 prefixEnd_2386356 408449213580256868291785 := by
  unfold tailWord_2386356
  simp only [CollatzResearch.WordTrace]
  refine ⟨43518776871323622001313461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58025035828431496001751281 43518776871323622001313461)
  ·
    refine ⟨4079885331686589562623137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43518776871323622001313461 4079885331686589562623137)
    ·
      refine ⟨3059913998764942171967353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4079885331686589562623137 3059913998764942171967353)
      ·
        refine ⟨2294935499073706628975515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3059913998764942171967353 2294935499073706628975515)
        ·
          refine ⟨3442403248610559943463273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294935499073706628975515 3442403248610559943463273)
          ·
            refine ⟨2581802436457919957597455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3442403248610559943463273 2581802436457919957597455)
            ·
              refine ⟨3872703654686879936396183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581802436457919957597455 3872703654686879936396183)
              ·
                refine ⟨5809055482030319904594275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3872703654686879936396183 5809055482030319904594275)
                ·
                  refine ⟨8713583223045479856891413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5809055482030319904594275 8713583223045479856891413)
                  ·
                    refine ⟨408449213580256868291785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8713583223045479856891413 408449213580256868291785)
                    ·
                      rfl

theorem cell23_2386356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2386356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386356 prefixEnd_2386356 := by exact prefixLift 2386356
  have htrace : WordTrace (prefixWord ++ tailWord_2386356) baseStart_2386356 baseEnd_2386356 := by
    simpa [prefixWord, tailWord_2386356, baseEnd_2386356] using wordTrace_append hprefix tailTrace_2386356
  have hstable : (prefixWord ++ tailWord_2386356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386356).length < 2 ^ (prefixWord ++ tailWord_2386356).sum := by decide
  have hdescent : baseEnd_2386356 < baseStart_2386356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386362 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3]
def baseStart_2386362 : Nat := 118140960795 + 2386362 * 2 ^ 59
def prefixEnd_2386362 : Nat := 4983230072969 + 3 ^ 40 * 2386362 * 2
def baseEnd_2386362 : Nat := 1225350721624697581400327

theorem tailTrace_2386362 : CollatzResearch.WordTrace tailWord_2386362 prefixEnd_2386362 1225350721624697581400327 := by
  unfold tailWord_2386362
  simp only [CollatzResearch.WordTrace]
  refine ⟨21759443145156376756836335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58025181720417004684896893 21759443145156376756836335)
  ·
    refine ⟨32639164717734565135254503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21759443145156376756836335 32639164717734565135254503)
    ·
      refine ⟨48958747076601847702881755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32639164717734565135254503 48958747076601847702881755)
      ·
        refine ⟨73438120614902771554322633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48958747076601847702881755 73438120614902771554322633)
        ·
          refine ⟨55078590461177078665741975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73438120614902771554322633 55078590461177078665741975)
          ·
            refine ⟨82617885691765617998612963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55078590461177078665741975 82617885691765617998612963)
            ·
              refine ⟨123926828537648426997919445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82617885691765617998612963 123926828537648426997919445)
              ·
                refine ⟨2904535043851135007763737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 123926828537648426997919445 2904535043851135007763737)
                ·
                  refine ⟨2178401282888351255822803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2904535043851135007763737 2178401282888351255822803)
                  ·
                    refine ⟨3267601924332526883734205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2178401282888351255822803 3267601924332526883734205)
                    ·
                      refine ⟨1225350721624697581400327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3267601924332526883734205 1225350721624697581400327)
                      ·
                        rfl

theorem cell23_2386362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_2386362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386362 prefixEnd_2386362 := by exact prefixLift 2386362
  have htrace : WordTrace (prefixWord ++ tailWord_2386362) baseStart_2386362 baseEnd_2386362 := by
    simpa [prefixWord, tailWord_2386362, baseEnd_2386362] using wordTrace_append hprefix tailTrace_2386362
  have hstable : (prefixWord ++ tailWord_2386362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386362).length < 2 ^ (prefixWord ++ tailWord_2386362).sum := by decide
  have hdescent : baseEnd_2386362 < baseStart_2386362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386369 : List Nat := [1, 2, 7, 1, 1, 1, 1, 9]
def baseStart_2386369 : Nat := 118140960795 + 2386369 * 2 ^ 59
def prefixEnd_2386369 : Nat := 4983230072969 + 3 ^ 40 * 2386369 * 2
def baseEnd_2386369 : Nat := 45383493184788113111585

theorem tailTrace_2386369 : CollatzResearch.WordTrace tailWord_2386369 prefixEnd_2386369 45383493184788113111585 := by
  unfold tailWord_2386369
  simp only [CollatzResearch.WordTrace]
  refine ⟨87038027891600147222850161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58025351927733431481900107 87038027891600147222850161)
  ·
    refine ⟨65278520918700110417137621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87038027891600147222850161 65278520918700110417137621)
    ·
      refine ⟨1529965334032033837901663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 65278520918700110417137621 1529965334032033837901663)
      ·
        refine ⟨2294948001048050756852495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529965334032033837901663 2294948001048050756852495)
        ·
          refine ⟨3442422001572076135278743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294948001048050756852495 3442422001572076135278743)
          ·
            refine ⟨5163633002358114202918115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442422001572076135278743 5163633002358114202918115)
            ·
              refine ⟨7745449503537171304377173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163633002358114202918115 7745449503537171304377173)
              ·
                refine ⟨45383493184788113111585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7745449503537171304377173 45383493184788113111585)
                ·
                  rfl

theorem cell23_2386369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 9].length) (baseStart_2386369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386369 prefixEnd_2386369 := by exact prefixLift 2386369
  have htrace : WordTrace (prefixWord ++ tailWord_2386369) baseStart_2386369 baseEnd_2386369 := by
    simpa [prefixWord, tailWord_2386369, baseEnd_2386369] using wordTrace_append hprefix tailTrace_2386369
  have hstable : (prefixWord ++ tailWord_2386369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386369).length < 2 ^ (prefixWord ++ tailWord_2386369).sum := by decide
  have hdescent : baseEnd_2386369 < baseStart_2386369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386380 : List Nat := [2, 2, 1, 4, 4, 1, 1, 3, 1, 2, 2]
def baseStart_2386380 : Nat := 118140960795 + 2386380 * 2 ^ 59
def prefixEnd_2386380 : Nat := 4983230072969 + 3 ^ 40 * 2386380 * 2
def baseEnd_2386380 : Nat := 1225359964276478510975245

theorem tailTrace_2386380 : CollatzResearch.WordTrace tailWord_2386380 prefixEnd_2386380 1225359964276478510975245 := by
  unfold tailWord_2386380
  simp only [CollatzResearch.WordTrace]
  refine ⟨43519214547280148050750297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58025619396373530734333729 43519214547280148050750297)
  ·
    refine ⟨32639410910460111038062723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43519214547280148050750297 32639410910460111038062723)
    ·
      refine ⟨48959116365690166557094085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32639410910460111038062723 48959116365690166557094085)
      ·
        refine ⟨9179834318566906229455141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48959116365690166557094085 9179834318566906229455141)
        ·
          refine ⟨1721218934731294918022839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9179834318566906229455141 1721218934731294918022839)
          ·
            refine ⟨2581828402096942377034259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721218934731294918022839 2581828402096942377034259)
            ·
              refine ⟨3872742603145413565551389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581828402096942377034259 3872742603145413565551389)
              ·
                refine ⟨1452278476179530087081771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3872742603145413565551389 1452278476179530087081771)
                ·
                  refine ⟨2178417714269295130622657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452278476179530087081771 2178417714269295130622657)
                  ·
                    refine ⟨1633813285701971347966993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2178417714269295130622657 1633813285701971347966993)
                    ·
                      refine ⟨1225359964276478510975245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633813285701971347966993 1225359964276478510975245)
                      ·
                        rfl

theorem cell23_2386380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_2386380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386380 prefixEnd_2386380 := by exact prefixLift 2386380
  have htrace : WordTrace (prefixWord ++ tailWord_2386380) baseStart_2386380 baseEnd_2386380 := by
    simpa [prefixWord, tailWord_2386380, baseEnd_2386380] using wordTrace_append hprefix tailTrace_2386380
  have hstable : (prefixWord ++ tailWord_2386380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386380).length < 2 ^ (prefixWord ++ tailWord_2386380).sum := by decide
  have hdescent : baseEnd_2386380 < baseStart_2386380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386389 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_2386389 : Nat := 118140960795 + 2386389 * 2 ^ 59
def prefixEnd_2386389 : Nat := 4983230072969 + 3 ^ 40 * 2386389 * 2
def baseEnd_2386389 : Nat := 1225364585602368975762703

theorem tailTrace_2386389 : CollatzResearch.WordTrace tailWord_2386389 prefixEnd_2386389 1225364585602368975762703 := by
  unfold tailWord_2386389
  simp only [CollatzResearch.WordTrace]
  refine ⟨87038757351527690638578221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58025838234351793759052147 87038757351527690638578221)
  ·
    refine ⟨32639534006822883989466833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87038757351527690638578221 32639534006822883989466833)
    ·
      refine ⟨24479650505117162992100125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32639534006822883989466833 24479650505117162992100125)
      ·
        refine ⟨9179868939418936122037547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24479650505117162992100125 9179868939418936122037547)
        ·
          refine ⟨13769803409128404183056321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9179868939418936122037547 13769803409128404183056321)
          ·
            refine ⟨10327352556846303137292241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13769803409128404183056321 10327352556846303137292241)
            ·
              refine ⟨7745514417634727352969181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10327352556846303137292241 7745514417634727352969181)
              ·
                refine ⟨2904567906613022757363443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7745514417634727352969181 2904567906613022757363443)
                ·
                  refine ⟨4356851859919534136045165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904567906613022757363443 4356851859919534136045165)
                  ·
                    refine ⟨1633819447469825301016937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4356851859919534136045165 1633819447469825301016937)
                    ·
                      refine ⟨1225364585602368975762703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633819447469825301016937 1225364585602368975762703)
                      ·
                        rfl

theorem cell23_2386389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_2386389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386389 prefixEnd_2386389 := by exact prefixLift 2386389
  have htrace : WordTrace (prefixWord ++ tailWord_2386389) baseStart_2386389 baseEnd_2386389 := by
    simpa [prefixWord, tailWord_2386389, baseEnd_2386389] using wordTrace_append hprefix tailTrace_2386389
  have hstable : (prefixWord ++ tailWord_2386389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386389).length < 2 ^ (prefixWord ++ tailWord_2386389).sum := by decide
  have hdescent : baseEnd_2386389 < baseStart_2386389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386413 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2386413 : Nat := 118140960795 + 2386413 * 2 ^ 59
def prefixEnd_2386413 : Nat := 4983230072969 + 3 ^ 40 * 2386413 * 2
def baseEnd_2386413 : Nat := 1225376909138076881862593

theorem tailTrace_2386413 : CollatzResearch.WordTrace tailWord_2386413 prefixEnd_2386413 1225376909138076881862593 := by
  unfold tailWord_2386413
  simp only [CollatzResearch.WordTrace]
  refine ⟨87039632703440742737451893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58026421802293828491634595 87039632703440742737451893)
  ·
    refine ⟨8159965565947569631636115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87039632703440742737451893 8159965565947569631636115)
    ·
      refine ⟨12239948348921354447454173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8159965565947569631636115 12239948348921354447454173)
      ·
        refine ⟨4589980630845507917795315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12239948348921354447454173 4589980630845507917795315)
        ·
          refine ⟨6884970946268261876692973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589980630845507917795315 6884970946268261876692973)
          ·
            refine ⟨2581864104850598203759865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6884970946268261876692973 2581864104850598203759865)
            ·
              refine ⟨1936398078637948652819899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2581864104850598203759865 1936398078637948652819899)
              ·
                refine ⟨2904597117956922979229849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1936398078637948652819899 2904597117956922979229849)
                ·
                  refine ⟨2178447838467692234422387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2904597117956922979229849 2178447838467692234422387)
                  ·
                    refine ⟨3267671757701538351633581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2178447838467692234422387 3267671757701538351633581)
                    ·
                      refine ⟨1225376909138076881862593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3267671757701538351633581 1225376909138076881862593)
                      ·
                        rfl

theorem cell23_2386413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2386413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386413 prefixEnd_2386413 := by exact prefixLift 2386413
  have htrace : WordTrace (prefixWord ++ tailWord_2386413) baseStart_2386413 baseEnd_2386413 := by
    simpa [prefixWord, tailWord_2386413, baseEnd_2386413] using wordTrace_append hprefix tailTrace_2386413
  have hstable : (prefixWord ++ tailWord_2386413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386413).length < 2 ^ (prefixWord ++ tailWord_2386413).sum := by decide
  have hdescent : baseEnd_2386413 < baseStart_2386413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386419 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 2, 2, 2]
def baseStart_2386419 : Nat := 118140960795 + 2386419 * 2 ^ 59
def prefixEnd_2386419 : Nat := 4983230072969 + 3 ^ 40 * 2386419 * 2
def baseEnd_2386419 : Nat := 1225379990022003858387565

theorem tailTrace_2386419 : CollatzResearch.WordTrace tailWord_2386419 prefixEnd_2386419 1225379990022003858387565 := by
  unfold tailWord_2386419
  simp only [CollatzResearch.WordTrace]
  refine ⟨87039851541419005762170311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58026567694279337174780207 87039851541419005762170311)
  ·
    refine ⟨130559777312128508643255467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87039851541419005762170311 130559777312128508643255467)
    ·
      refine ⟨195839665968192762964883201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130559777312128508643255467 195839665968192762964883201)
      ·
        refine ⟨146879749476144572223662401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195839665968192762964883201 146879749476144572223662401)
        ·
          refine ⟨110159812107108429167746801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146879749476144572223662401 110159812107108429167746801)
          ·
            refine ⟨82619859080331321875810101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110159812107108429167746801 82619859080331321875810101)
            ·
              refine ⟨7745611788781061425857197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82619859080331321875810101 7745611788781061425857197)
              ·
                refine ⟨2904604420792898034696449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7745611788781061425857197 2904604420792898034696449)
                ·
                  refine ⟨2178453315594673526022337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2904604420792898034696449 2178453315594673526022337)
                  ·
                    refine ⟨1633839986696005144516753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2178453315594673526022337 1633839986696005144516753)
                    ·
                      refine ⟨1225379990022003858387565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1633839986696005144516753 1225379990022003858387565)
                      ·
                        rfl

theorem cell23_2386419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 2, 2].length) (baseStart_2386419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386419 prefixEnd_2386419 := by exact prefixLift 2386419
  have htrace : WordTrace (prefixWord ++ tailWord_2386419) baseStart_2386419 baseEnd_2386419 := by
    simpa [prefixWord, tailWord_2386419, baseEnd_2386419] using wordTrace_append hprefix tailTrace_2386419
  have hstable : (prefixWord ++ tailWord_2386419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386419).length < 2 ^ (prefixWord ++ tailWord_2386419).sum := by decide
  have hdescent : baseEnd_2386419 < baseStart_2386419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386442 : List Nat := [3, 1, 2, 2, 2, 1, 2, 5, 5]
def baseStart_2386442 : Nat := 118140960795 + 2386442 * 2 ^ 59
def prefixEnd_2386442 : Nat := 4983230072969 + 3 ^ 40 * 2386442 * 2
def baseEnd_2386442 : Nat := 136154644453006363155551

theorem tailTrace_2386442 : CollatzResearch.WordTrace tailWord_2386442 prefixEnd_2386442 136154644453006363155551 := by
  unfold tailWord_2386442
  simp only [CollatzResearch.WordTrace]
  refine ⟨21760172605083920172564395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58027126946890453793505053 21760172605083920172564395)
  ·
    refine ⟨32640258907625880258846593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21760172605083920172564395 32640258907625880258846593)
    ·
      refine ⟨24480194180719410194134945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32640258907625880258846593 24480194180719410194134945)
      ·
        refine ⟨18360145635539557645601209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24480194180719410194134945 18360145635539557645601209)
        ·
          refine ⟨13770109226654668234200907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18360145635539557645601209 13770109226654668234200907)
          ·
            refine ⟨20655163839982002351301361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13770109226654668234200907 20655163839982002351301361)
            ·
              refine ⟨15491372879986501763476021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20655163839982002351301361 15491372879986501763476021)
              ·
                refine ⟨1452316207498734540325877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15491372879986501763476021 1452316207498734540325877)
                ·
                  refine ⟨136154644453006363155551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1452316207498734540325877 136154644453006363155551)
                  ·
                    rfl

theorem cell23_2386442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_2386442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386442 prefixEnd_2386442 := by exact prefixLift 2386442
  have htrace : WordTrace (prefixWord ++ tailWord_2386442) baseStart_2386442 baseEnd_2386442 := by
    simpa [prefixWord, tailWord_2386442, baseEnd_2386442] using wordTrace_append hprefix tailTrace_2386442
  have hstable : (prefixWord ++ tailWord_2386442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386442).length < 2 ^ (prefixWord ++ tailWord_2386442).sum := by decide
  have hdescent : baseEnd_2386442 < baseStart_2386442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386465 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2386465 : Nat := 118140960795 + 2386465 * 2 ^ 59
def prefixEnd_2386465 : Nat := 4983230072969 + 3 ^ 40 * 2386465 * 2
def baseEnd_2386465 : Nat := 1225403610132110678412353

theorem tailTrace_2386465 : CollatzResearch.WordTrace tailWord_2386465 prefixEnd_2386465 1225403610132110678412353 := by
  unfold tailWord_2386465
  simp only [CollatzResearch.WordTrace]
  refine ⟨87041529299252355618344849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58027686199501570412229899 87041529299252355618344849)
  ·
    refine ⟨65281146974439266713758637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87041529299252355618344849 65281146974439266713758637)
    ·
      refine ⟨24480430115414725017659489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65281146974439266713758637 24480430115414725017659489)
      ·
        refine ⟨18360322586561043763244617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24480430115414725017659489 18360322586561043763244617)
        ·
          refine ⟨13770241939920782822433463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18360322586561043763244617 13770241939920782822433463)
          ·
            refine ⟨20655362909881174233650195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13770241939920782822433463 20655362909881174233650195)
            ·
              refine ⟨30983044364821761350475293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20655362909881174233650195 30983044364821761350475293)
              ·
                refine ⟨11618641636808160506428235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30983044364821761350475293 11618641636808160506428235)
                ·
                  refine ⟨17427962455212240759642353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11618641636808160506428235 17427962455212240759642353)
                  ·
                    refine ⟨13070971841409180569731765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17427962455212240759642353 13070971841409180569731765)
                    ·
                      refine ⟨1225403610132110678412353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13070971841409180569731765 1225403610132110678412353)
                      ·
                        rfl

theorem cell23_2386465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2386465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386465 prefixEnd_2386465 := by exact prefixLift 2386465
  have htrace : WordTrace (prefixWord ++ tailWord_2386465) baseStart_2386465 baseEnd_2386465 := by
    simpa [prefixWord, tailWord_2386465, baseEnd_2386465] using wordTrace_append hprefix tailTrace_2386465
  have hstable : (prefixWord ++ tailWord_2386465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386465).length < 2 ^ (prefixWord ++ tailWord_2386465).sum := by decide
  have hdescent : baseEnd_2386465 < baseStart_2386465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386475 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 4]
def baseStart_2386475 : Nat := 118140960795 + 2386475 * 2 ^ 59
def prefixEnd_2386475 : Nat := 4983230072969 + 3 ^ 40 * 2386475 * 2
def baseEnd_2386475 : Nat := 1225408744938655639287307

theorem tailTrace_2386475 : CollatzResearch.WordTrace tailWord_2386475 prefixEnd_2386475 1225408744938655639287307 := by
  unfold tailWord_2386475
  simp only [CollatzResearch.WordTrace]
  refine ⟨87041894029216127326208879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58027929352810751550805919 87041894029216127326208879)
  ·
    refine ⟨130562841043824190989313319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87041894029216127326208879 130562841043824190989313319)
    ·
      refine ⟨195844261565736286483969979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130562841043824190989313319 195844261565736286483969979)
      ·
        refine ⟨293766392348604429725954969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195844261565736286483969979 293766392348604429725954969)
        ·
          refine ⟨220324794261453322294466227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293766392348604429725954969 220324794261453322294466227)
          ·
            refine ⟨330487191392179983441699341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220324794261453322294466227 330487191392179983441699341)
            ·
              refine ⟨123932696772067493790637253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 330487191392179983441699341 123932696772067493790637253)
              ·
                refine ⟨23237380644762655085744485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123932696772067493790637253 23237380644762655085744485)
                ·
                  refine ⟨4357008870892997828577091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23237380644762655085744485 4357008870892997828577091)
                  ·
                    refine ⟨6535513306339496742865637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4357008870892997828577091 6535513306339496742865637)
                    ·
                      refine ⟨1225408744938655639287307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6535513306339496742865637 1225408744938655639287307)
                      ·
                        rfl

theorem cell23_2386475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 4].length) (baseStart_2386475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386475 prefixEnd_2386475 := by exact prefixLift 2386475
  have htrace : WordTrace (prefixWord ++ tailWord_2386475) baseStart_2386475 baseEnd_2386475 := by
    simpa [prefixWord, tailWord_2386475, baseEnd_2386475] using wordTrace_append hprefix tailTrace_2386475
  have hstable : (prefixWord ++ tailWord_2386475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386475).length < 2 ^ (prefixWord ++ tailWord_2386475).sum := by decide
  have hdescent : baseEnd_2386475 < baseStart_2386475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386492 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_2386492 : Nat := 118140960795 + 2386492 * 2 ^ 59
def prefixEnd_2386492 : Nat := 4983230072969 + 3 ^ 40 * 2386492 * 2
def baseEnd_2386492 : Nat := 1225417474109782072774729

theorem tailTrace_2386492 : CollatzResearch.WordTrace tailWord_2386492 prefixEnd_2386492 1225417474109782072774729 := by
  unfold tailWord_2386492
  simp only [CollatzResearch.WordTrace]
  refine ⟨43521257035077269614788865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58028342713436359486385153 43521257035077269614788865)
  ·
    refine ⟨32640942776307952211091649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43521257035077269614788865 32640942776307952211091649)
    ·
      refine ⟨24480707082230964158318737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32640942776307952211091649 24480707082230964158318737)
      ·
        refine ⟨18360530311673223118739053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24480707082230964158318737 18360530311673223118739053)
        ·
          refine ⟨6885198866877458669527145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18360530311673223118739053 6885198866877458669527145)
          ·
            refine ⟨5163899150158094002145359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6885198866877458669527145 5163899150158094002145359)
            ·
              refine ⟨7745848725237141003218039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163899150158094002145359 7745848725237141003218039)
              ·
                refine ⟨11618773087855711504827059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7745848725237141003218039 11618773087855711504827059)
                ·
                  refine ⟨17428159631783567257240589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11618773087855711504827059 17428159631783567257240589)
                  ·
                    refine ⟨6535559861918837721465221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17428159631783567257240589 6535559861918837721465221)
                    ·
                      refine ⟨1225417474109782072774729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6535559861918837721465221 1225417474109782072774729)
                      ·
                        rfl

theorem cell23_2386492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_2386492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386492 prefixEnd_2386492 := by exact prefixLift 2386492
  have htrace : WordTrace (prefixWord ++ tailWord_2386492) baseStart_2386492 baseEnd_2386492 := by
    simpa [prefixWord, tailWord_2386492, baseEnd_2386492] using wordTrace_append hprefix tailTrace_2386492
  have hstable : (prefixWord ++ tailWord_2386492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386492).length < 2 ^ (prefixWord ++ tailWord_2386492).sum := by decide
  have hdescent : baseEnd_2386492 < baseStart_2386492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386519 : List Nat := [1, 1, 3, 2, 2, 2, 1, 6, 1, 4]
def baseStart_2386519 : Nat := 118140960795 + 2386519 * 2 ^ 59
def prefixEnd_2386519 : Nat := 4983230072969 + 3 ^ 40 * 2386519 * 2
def baseEnd_2386519 : Nat := 408477112695817822379035

theorem tailTrace_2386519 : CollatzResearch.WordTrace tailWord_2386519 prefixEnd_2386519 408477112695817822379035 := by
  unfold tailWord_2386519
  simp only [CollatzResearch.WordTrace]
  refine ⟨87043498841056722840810611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58028999227371148560540407 87043498841056722840810611)
  ·
    refine ⟨130565248261585084261215917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87043498841056722840810611 130565248261585084261215917)
    ·
      refine ⟨48961968098094406597955969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130565248261585084261215917 48961968098094406597955969)
      ·
        refine ⟨36721476073570804948466977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48961968098094406597955969 36721476073570804948466977)
        ·
          refine ⟨27541107055178103711350233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36721476073570804948466977 27541107055178103711350233)
          ·
            refine ⟨20655830291383577783512675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27541107055178103711350233 20655830291383577783512675)
            ·
              refine ⟨30983745437075366675269013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20655830291383577783512675 30983745437075366675269013)
              ·
                refine ⟨1452363067362907812903235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30983745437075366675269013 1452363067362907812903235)
                ·
                  refine ⟨2178544601044361719354853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452363067362907812903235 2178544601044361719354853)
                  ·
                    refine ⟨408477112695817822379035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2178544601044361719354853 408477112695817822379035)
                    ·
                      rfl

theorem cell23_2386519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_2386519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386519 prefixEnd_2386519 := by exact prefixLift 2386519
  have htrace : WordTrace (prefixWord ++ tailWord_2386519) baseStart_2386519 baseEnd_2386519 := by
    simpa [prefixWord, tailWord_2386519, baseEnd_2386519] using wordTrace_append hprefix tailTrace_2386519
  have hstable : (prefixWord ++ tailWord_2386519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386519).length < 2 ^ (prefixWord ++ tailWord_2386519).sum := by decide
  have hdescent : baseEnd_2386519 < baseStart_2386519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386535 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2386535 : Nat := 118140960795 + 2386535 * 2 ^ 59
def prefixEnd_2386535 : Nat := 4983230072969 + 3 ^ 40 * 2386535 * 2
def baseEnd_2386535 : Nat := 1225439553777925404537031

theorem tailTrace_2386535 : CollatzResearch.WordTrace tailWord_2386535 prefixEnd_2386535 1225439553777925404537031 := by
  unfold tailWord_2386535
  simp only [CollatzResearch.WordTrace]
  refine ⟨87044082408998757573393059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58029388272665838382262039 87044082408998757573393059)
  ·
    refine ⟨130566123613498136360089589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87044082408998757573393059 130566123613498136360089589)
    ·
      refine ⟨12240574088765450283758399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130566123613498136360089589 12240574088765450283758399)
      ·
        refine ⟨18360861133148175425637599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12240574088765450283758399 18360861133148175425637599)
        ·
          refine ⟨27541291699722263138456399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18360861133148175425637599 27541291699722263138456399)
          ·
            refine ⟨41311937549583394707684599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27541291699722263138456399 41311937549583394707684599)
            ·
              refine ⟨61967906324375092061526899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41311937549583394707684599 61967906324375092061526899)
              ·
                refine ⟨92951859486562638092290349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61967906324375092061526899 92951859486562638092290349)
                ·
                  refine ⟨34856947307460989284608881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92951859486562638092290349 34856947307460989284608881)
                  ·
                    refine ⟨26142710480595741963456661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34856947307460989284608881 26142710480595741963456661)
                    ·
                      refine ⟨1225439553777925404537031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26142710480595741963456661 1225439553777925404537031)
                      ·
                        rfl

theorem cell23_2386535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2386535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386535 prefixEnd_2386535 := by exact prefixLift 2386535
  have htrace : WordTrace (prefixWord ++ tailWord_2386535) baseStart_2386535 baseEnd_2386535 := by
    simpa [prefixWord, tailWord_2386535, baseEnd_2386535] using wordTrace_append hprefix tailTrace_2386535
  have hstable : (prefixWord ++ tailWord_2386535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386535).length < 2 ^ (prefixWord ++ tailWord_2386535).sum := by decide
  have hdescent : baseEnd_2386535 < baseStart_2386535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386575 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 3, 6]
def baseStart_2386575 : Nat := 118140960795 + 2386575 * 2 ^ 59
def prefixEnd_2386575 : Nat := 4983230072969 + 3 ^ 40 * 2386575 * 2
def baseEnd_2386575 : Nat := 408486697668035082678949

theorem tailTrace_2386575 : CollatzResearch.WordTrace tailWord_2386575 prefixEnd_2386575 408486697668035082678949 := by
  unfold tailWord_2386575
  simp only [CollatzResearch.WordTrace]
  refine ⟨87045541328853844404849179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58030360885902562936566119 87045541328853844404849179)
  ·
    refine ⟨130568311993280766607273769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87045541328853844404849179 130568311993280766607273769)
    ·
      refine ⟨97926233994960574955455327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130568311993280766607273769 97926233994960574955455327)
      ·
        refine ⟨146889350992440862433182991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97926233994960574955455327 146889350992440862433182991)
        ·
          refine ⟨220334026488661293649774487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146889350992440862433182991 220334026488661293649774487)
          ·
            refine ⟨330501039732991940474661731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220334026488661293649774487 330501039732991940474661731)
            ·
              refine ⟨495751559599487910711992597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330501039732991940474661731 495751559599487910711992597)
              ·
                refine ⟨23238354356225995814624653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 495751559599487910711992597 23238354356225995814624653)
                ·
                  refine ⟨8714382883584748430484245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23238354356225995814624653 8714382883584748430484245)
                  ·
                    refine ⟨408486697668035082678949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8714382883584748430484245 408486697668035082678949)
                    ·
                      rfl

theorem cell23_2386575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_2386575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386575 prefixEnd_2386575 := by exact prefixLift 2386575
  have htrace : WordTrace (prefixWord ++ tailWord_2386575) baseStart_2386575 baseEnd_2386575 := by
    simpa [prefixWord, tailWord_2386575, baseEnd_2386575] using wordTrace_append hprefix tailTrace_2386575
  have hstable : (prefixWord ++ tailWord_2386575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386575).length < 2 ^ (prefixWord ++ tailWord_2386575).sum := by decide
  have hdescent : baseEnd_2386575 < baseStart_2386575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386649 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 3]
def baseStart_2386649 : Nat := 118140960795 + 2386649 * 2 ^ 59
def prefixEnd_2386649 : Nat := 4983230072969 + 3 ^ 40 * 2386649 * 2
def baseEnd_2386649 : Nat := 1225498090572537958511507

theorem tailTrace_2386649 : CollatzResearch.WordTrace tailWord_2386649 prefixEnd_2386649 1225498090572537958511507 := by
  unfold tailWord_2386649
  simp only [CollatzResearch.WordTrace]
  refine ⟨87048240330585755043043001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58032160220390503362028667 87048240330585755043043001)
  ·
    refine ⟨65286180247939316282282251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87048240330585755043043001 65286180247939316282282251)
    ·
      refine ⟨97929270371908974423423377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65286180247939316282282251 97929270371908974423423377)
      ·
        refine ⟨73446952778931730817567533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97929270371908974423423377 73446952778931730817567533)
        ·
          refine ⟨27542607292099399056587825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73446952778931730817567533 27542607292099399056587825)
          ·
            refine ⟨20656955469074549292440869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27542607292099399056587825 20656955469074549292440869)
            ·
              refine ⟨3873179150451477992332663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20656955469074549292440869 3873179150451477992332663)
              ·
                refine ⟨5809768725677216988498995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3873179150451477992332663 5809768725677216988498995)
                ·
                  refine ⟨8714653088515825482748493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5809768725677216988498995 8714653088515825482748493)
                  ·
                    refine ⟨3267994908193434556030685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8714653088515825482748493 3267994908193434556030685)
                    ·
                      refine ⟨1225498090572537958511507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3267994908193434556030685 1225498090572537958511507)
                      ·
                        rfl

theorem cell23_2386649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_2386649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386649 prefixEnd_2386649 := by exact prefixLift 2386649
  have htrace : WordTrace (prefixWord ++ tailWord_2386649) baseStart_2386649 baseEnd_2386649 := by
    simpa [prefixWord, tailWord_2386649, baseEnd_2386649] using wordTrace_append hprefix tailTrace_2386649
  have hstable : (prefixWord ++ tailWord_2386649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386649).length < 2 ^ (prefixWord ++ tailWord_2386649).sum := by decide
  have hdescent : baseEnd_2386649 < baseStart_2386649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386677 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2386677 : Nat := 118140960795 + 2386677 * 2 ^ 59
def prefixEnd_2386677 : Nat := 4983230072969 + 3 ^ 40 * 2386677 * 2
def baseEnd_2386677 : Nat := 408504156010287949653793

theorem tailTrace_2386677 : CollatzResearch.WordTrace tailWord_2386677 prefixEnd_2386677 408504156010287949653793 := by
  unfold tailWord_2386677
  simp only [CollatzResearch.WordTrace]
  refine ⟨87049261574484315825062285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58032841049656210550041523 87049261574484315825062285)
  ·
    refine ⟨32643473090431618434398357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87049261574484315825062285 32643473090431618434398357)
    ·
      refine ⟨1530162801113982114112423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32643473090431618434398357 1530162801113982114112423)
      ·
        refine ⟨2295244201670973171168635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530162801113982114112423 2295244201670973171168635)
        ·
          refine ⟨3442866302506459756752953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295244201670973171168635 3442866302506459756752953)
          ·
            refine ⟨2582149726879844817564715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3442866302506459756752953 2582149726879844817564715)
            ·
              refine ⟨3873224590319767226347073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582149726879844817564715 3873224590319767226347073)
              ·
                refine ⟨2904918442739825419760305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873224590319767226347073 2904918442739825419760305)
                ·
                  refine ⟨2178688832054869064820229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2904918442739825419760305 2178688832054869064820229)
                  ·
                    refine ⟨408504156010287949653793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2178688832054869064820229 408504156010287949653793)
                    ·
                      rfl

theorem cell23_2386677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2386677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386677 prefixEnd_2386677 := by exact prefixLift 2386677
  have htrace : WordTrace (prefixWord ++ tailWord_2386677) baseStart_2386677 baseEnd_2386677 := by
    simpa [prefixWord, tailWord_2386677, baseEnd_2386677] using wordTrace_append hprefix tailTrace_2386677
  have hstable : (prefixWord ++ tailWord_2386677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386677).length < 2 ^ (prefixWord ++ tailWord_2386677).sum := by decide
  have hdescent : baseEnd_2386677 < baseStart_2386677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386682 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_2386682 : Nat := 118140960795 + 2386682 * 2 ^ 59
def prefixEnd_2386682 : Nat := 4983230072969 + 3 ^ 40 * 2386682 * 2
def baseEnd_2386682 : Nat := 408505011811378776466285

theorem tailTrace_2386682 : CollatzResearch.WordTrace tailWord_2386682 prefixEnd_2386682 408505011811378776466285 := by
  unfold tailWord_2386682
  simp only [CollatzResearch.WordTrace]
  refine ⟨21762360984866550419748575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58032962626310801119329533 21762360984866550419748575)
  ·
    refine ⟨32643541477299825629622863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21762360984866550419748575 32643541477299825629622863)
    ·
      refine ⟨48965312215949738444434295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32643541477299825629622863 48965312215949738444434295)
      ·
        refine ⟨73447968323924607666651443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48965312215949738444434295 73447968323924607666651443)
        ·
          refine ⟨110171952485886911499977165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73447968323924607666651443 110171952485886911499977165)
          ·
            refine ⟨41314482182207591812491437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110171952485886911499977165 41314482182207591812491437)
            ·
              refine ⟨15492930818327846929684289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41314482182207591812491437 15492930818327846929684289)
              ·
                refine ⟨11619698113745885197263217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15492930818327846929684289 11619698113745885197263217)
                ·
                  refine ⟨8714773585309413897947413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11619698113745885197263217 8714773585309413897947413)
                  ·
                    refine ⟨408505011811378776466285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8714773585309413897947413 408505011811378776466285)
                    ·
                      rfl

theorem cell23_2386682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_2386682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386682 prefixEnd_2386682 := by exact prefixLift 2386682
  have htrace : WordTrace (prefixWord ++ tailWord_2386682) baseStart_2386682 baseEnd_2386682 := by
    simpa [prefixWord, tailWord_2386682, baseEnd_2386682] using wordTrace_append hprefix tailTrace_2386682
  have hstable : (prefixWord ++ tailWord_2386682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386682).length < 2 ^ (prefixWord ++ tailWord_2386682).sum := by decide
  have hdescent : baseEnd_2386682 < baseStart_2386682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386746 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 7]
def baseStart_2386746 : Nat := 118140960795 + 2386746 * 2 ^ 59
def prefixEnd_2386746 : Nat := 4983230072969 + 3 ^ 40 * 2386746 * 2
def baseEnd_2386746 : Nat := 136171988688447119888729

theorem tailTrace_2386746 : CollatzResearch.WordTrace tailWord_2386746 prefixEnd_2386746 136171988688447119888729 := by
  unfold tailWord_2386746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21762944552808585152331023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58034518807489560406216061 21762944552808585152331023)
  ·
    refine ⟨32644416829212877728496535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21762944552808585152331023 32644416829212877728496535)
    ·
      refine ⟨48966625243819316592744803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32644416829212877728496535 48966625243819316592744803)
      ·
        refine ⟨73449937865728974889117205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48966625243819316592744803 73449937865728974889117205)
        ·
          refine ⟨3442965837456045697927369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73449937865728974889117205 3442965837456045697927369)
          ·
            refine ⟨2582224378092034273445527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3442965837456045697927369 2582224378092034273445527)
            ·
              refine ⟨3873336567138051410168291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582224378092034273445527 3873336567138051410168291)
              ·
                refine ⟨5810004850707077115252437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3873336567138051410168291 5810004850707077115252437)
                ·
                  refine ⟨136171988688447119888729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5810004850707077115252437 136171988688447119888729)
                  ·
                    rfl

theorem cell23_2386746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_2386746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386746 prefixEnd_2386746 := by exact prefixLift 2386746
  have htrace : WordTrace (prefixWord ++ tailWord_2386746) baseStart_2386746 baseEnd_2386746 := by
    simpa [prefixWord, tailWord_2386746, baseEnd_2386746] using wordTrace_append hprefix tailTrace_2386746
  have hstable : (prefixWord ++ tailWord_2386746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386746).length < 2 ^ (prefixWord ++ tailWord_2386746).sum := by decide
  have hdescent : baseEnd_2386746 < baseStart_2386746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386796 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 2, 4, 2]
def baseStart_2386796 : Nat := 118140960795 + 2386796 * 2 ^ 59
def prefixEnd_2386796 : Nat := 4983230072969 + 3 ^ 40 * 2386796 * 2
def baseEnd_2386796 : Nat := 1225573572228748883373331

theorem tailTrace_2386796 : CollatzResearch.WordTrace tailWord_2386796 prefixEnd_2386796 1225573572228748883373331 := by
  unfold tailWord_2386796
  simp only [CollatzResearch.WordTrace]
  refine ⟨43526800930526599574322121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58035734574035466099096161 43526800930526599574322121)
  ·
    refine ⟨32645100697894949680741591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43526800930526599574322121 32645100697894949680741591)
    ·
      refine ⟨48967651046842424521112387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32645100697894949680741591 48967651046842424521112387)
      ·
        refine ⟨73451476570263636781668581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48967651046842424521112387 73451476570263636781668581)
        ·
          refine ⟨13772151856924431896562859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73451476570263636781668581 13772151856924431896562859)
          ·
            refine ⟨20658227785386647844844289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13772151856924431896562859 20658227785386647844844289)
            ·
              refine ⟨15493670839039985883633217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20658227785386647844844289 15493670839039985883633217)
              ·
                refine ⟨11620253129279989412724913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15493670839039985883633217 11620253129279989412724913)
                ·
                  refine ⟨8715189846959992059543685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11620253129279989412724913 8715189846959992059543685)
                  ·
                    refine ⟨1634098096304998511164441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8715189846959992059543685 1634098096304998511164441)
                    ·
                      refine ⟨1225573572228748883373331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634098096304998511164441 1225573572228748883373331)
                      ·
                        rfl

theorem cell23_2386796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_2386796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386796 prefixEnd_2386796 := by exact prefixLift 2386796
  have htrace : WordTrace (prefixWord ++ tailWord_2386796) baseStart_2386796 baseEnd_2386796 := by
    simpa [prefixWord, tailWord_2386796, baseEnd_2386796] using wordTrace_append hprefix tailTrace_2386796
  have hstable : (prefixWord ++ tailWord_2386796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386796).length < 2 ^ (prefixWord ++ tailWord_2386796).sum := by decide
  have hdescent : baseEnd_2386796 < baseStart_2386796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386819 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 6]
def baseStart_2386819 : Nat := 118140960795 + 2386819 * 2 ^ 59
def prefixEnd_2386819 : Nat := 4983230072969 + 3 ^ 40 * 2386819 * 2
def baseEnd_2386819 : Nat := 136176153587089143709525

theorem tailTrace_2386819 : CollatzResearch.WordTrace tailWord_2386819 prefixEnd_2386819 136176153587089143709525 := by
  unfold tailWord_2386819
  simp only [CollatzResearch.WordTrace]
  refine ⟨87054440739969874076731511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58036293826646582717821007 87054440739969874076731511)
  ·
    refine ⟨130581661109954811115097267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87054440739969874076731511 130581661109954811115097267)
    ·
      refine ⟨195872491664932216672645901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130581661109954811115097267 195872491664932216672645901)
      ·
        refine ⟨73452184374349581252242213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195872491664932216672645901 73452184374349581252242213)
        ·
          refine ⟨13772284570190546484795415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73452184374349581252242213 13772284570190546484795415)
          ·
            refine ⟨20658426855285819727193123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13772284570190546484795415 20658426855285819727193123)
            ·
              refine ⟨30987640282928729590789685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20658426855285819727193123 30987640282928729590789685)
              ·
                refine ⟨2905091276524568399136533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30987640282928729590789685 2905091276524568399136533)
                ·
                  refine ⟨136176153587089143709525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2905091276524568399136533 136176153587089143709525)
                  ·
                    rfl

theorem cell23_2386819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 6].length) (baseStart_2386819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386819 prefixEnd_2386819 := by exact prefixLift 2386819
  have htrace : WordTrace (prefixWord ++ tailWord_2386819) baseStart_2386819 baseEnd_2386819 := by
    simpa [prefixWord, tailWord_2386819, baseEnd_2386819] using wordTrace_append hprefix tailTrace_2386819
  have hstable : (prefixWord ++ tailWord_2386819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386819).length < 2 ^ (prefixWord ++ tailWord_2386819).sum := by decide
  have hdescent : baseEnd_2386819 < baseStart_2386819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386879 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 1, 6]
def baseStart_2386879 : Nat := 118140960795 + 2386879 * 2 ^ 59
def prefixEnd_2386879 : Nat := 4983230072969 + 3 ^ 40 * 2386879 * 2
def baseEnd_2386879 : Nat := 408538730374357352878483

theorem tailTrace_2386879 : CollatzResearch.WordTrace tailWord_2386879 prefixEnd_2386879 408538730374357352878483 := by
  unfold tailWord_2386879
  simp only [CollatzResearch.WordTrace]
  refine ⟨87056629119752504323915691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58037752746501669549277127 87056629119752504323915691)
  ·
    refine ⟨130584943679628756485873537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87056629119752504323915691 130584943679628756485873537)
    ·
      refine ⟨97938707759721567364405153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130584943679628756485873537 97938707759721567364405153)
      ·
        refine ⟨73454030819791175523303865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97938707759721567364405153 73454030819791175523303865)
        ·
          refine ⟨55090523114843381642477899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73454030819791175523303865 55090523114843381642477899)
          ·
            refine ⟨82635784672265072463716849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55090523114843381642477899 82635784672265072463716849)
            ·
              refine ⟨61976838504198804347787637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82635784672265072463716849 61976838504198804347787637)
              ·
                refine ⟨5810328609768637907605091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61976838504198804347787637 5810328609768637907605091)
                ·
                  refine ⟨8715492914652956861407637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5810328609768637907605091 8715492914652956861407637)
                  ·
                    refine ⟨408538730374357352878483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8715492914652956861407637 408538730374357352878483)
                    ·
                      rfl

theorem cell23_2386879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_2386879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386879 prefixEnd_2386879 := by exact prefixLift 2386879
  have htrace : WordTrace (prefixWord ++ tailWord_2386879) baseStart_2386879 baseEnd_2386879 := by
    simpa [prefixWord, tailWord_2386879, baseEnd_2386879] using wordTrace_append hprefix tailTrace_2386879
  have hstable : (prefixWord ++ tailWord_2386879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386879).length < 2 ^ (prefixWord ++ tailWord_2386879).sum := by decide
  have hdescent : baseEnd_2386879 < baseStart_2386879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386906 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_2386906 : Nat := 118140960795 + 2386906 * 2 ^ 59
def prefixEnd_2386906 : Nat := 4983230072969 + 3 ^ 40 * 2386906 * 2
def baseEnd_2386906 : Nat := 1225630055100743452997825

theorem tailTrace_2386906 : CollatzResearch.WordTrace tailWord_2386906 prefixEnd_2386906 1225630055100743452997825 := by
  unfold tailWord_2386906
  simp only [CollatzResearch.WordTrace]
  refine ⟨21764403472663671983787143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58038409260436458623432381 21764403472663671983787143)
  ·
    refine ⟨32646605208995507975680715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21764403472663671983787143 32646605208995507975680715)
    ·
      refine ⟨48969907813493261963521073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32646605208995507975680715 48969907813493261963521073)
      ·
        refine ⟨36727430860119946472640805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48969907813493261963521073 36727430860119946472640805)
        ·
          refine ⟨6886393286272489963620151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36727430860119946472640805 6886393286272489963620151)
          ·
            refine ⟨10329589929408734945430227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6886393286272489963620151 10329589929408734945430227)
            ·
              refine ⟨15494384894113102418145341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10329589929408734945430227 15494384894113102418145341)
              ·
                refine ⟨5810394335292413406804503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15494384894113102418145341 5810394335292413406804503)
                ·
                  refine ⟨8715591502938620110206755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5810394335292413406804503 8715591502938620110206755)
                  ·
                    refine ⟨13073387254407930165310133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8715591502938620110206755 13073387254407930165310133)
                    ·
                      refine ⟨1225630055100743452997825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13073387254407930165310133 1225630055100743452997825)
                      ·
                        rfl

theorem cell23_2386906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_2386906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386906 prefixEnd_2386906 := by exact prefixLift 2386906
  have htrace : WordTrace (prefixWord ++ tailWord_2386906) baseStart_2386906 baseEnd_2386906 := by
    simpa [prefixWord, tailWord_2386906, baseEnd_2386906] using wordTrace_append hprefix tailTrace_2386906
  have hstable : (prefixWord ++ tailWord_2386906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386906).length < 2 ^ (prefixWord ++ tailWord_2386906).sum := by decide
  have hdescent : baseEnd_2386906 < baseStart_2386906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386920 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_2386920 : Nat := 118140960795 + 2386920 * 2 ^ 59
def prefixEnd_2386920 : Nat := 4983230072969 + 3 ^ 40 * 2386920 * 2
def baseEnd_2386920 : Nat := 1225637243829906398222761

theorem tailTrace_2386920 : CollatzResearch.WordTrace tailWord_2386920 prefixEnd_2386920 1225637243829906398222761 := by
  unfold tailWord_2386920
  simp only [CollatzResearch.WordTrace]
  refine ⟨43529062256301984163079107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58038749675069312217438809 43529062256301984163079107)
  ·
    refine ⟨65293593384452976244618661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43529062256301984163079107 65293593384452976244618661)
    ·
      refine ⟨12242548759584933045865999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65293593384452976244618661 12242548759584933045865999)
      ·
        refine ⟨18363823139377399568798999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12242548759584933045865999 18363823139377399568798999)
        ·
          refine ⟨27545734709066099353198499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18363823139377399568798999 27545734709066099353198499)
          ·
            refine ⟨41318602063599149029797749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27545734709066099353198499 41318602063599149029797749)
            ·
              refine ⟨3873618943462420221543539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41318602063599149029797749 3873618943462420221543539)
              ·
                refine ⟨5810428415193630332315309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3873618943462420221543539 5810428415193630332315309)
                ·
                  refine ⟨2178910655697611374618241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5810428415193630332315309 2178910655697611374618241)
                  ·
                    refine ⟨1634182991773208530963681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2178910655697611374618241 1634182991773208530963681)
                    ·
                      refine ⟨1225637243829906398222761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634182991773208530963681 1225637243829906398222761)
                      ·
                        rfl

theorem cell23_2386920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_2386920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386920 prefixEnd_2386920 := by exact prefixLift 2386920
  have htrace : WordTrace (prefixWord ++ tailWord_2386920) baseStart_2386920 baseEnd_2386920 := by
    simpa [prefixWord, tailWord_2386920, baseEnd_2386920] using wordTrace_append hprefix tailTrace_2386920
  have hstable : (prefixWord ++ tailWord_2386920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386920).length < 2 ^ (prefixWord ++ tailWord_2386920).sum := by decide
  have hdescent : baseEnd_2386920 < baseStart_2386920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386936 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_2386936 : Nat := 118140960795 + 2386936 * 2 ^ 59
def prefixEnd_2386936 : Nat := 4983230072969 + 3 ^ 40 * 2386936 * 2
def baseEnd_2386936 : Nat := 1225645459520378335622687

theorem tailTrace_2386936 : CollatzResearch.WordTrace tailWord_2386936 prefixEnd_2386936 1225645459520378335622687 := by
  unfold tailWord_2386936
  simp only [CollatzResearch.WordTrace]
  refine ⟨43529354040273001529370331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58039138720364002039160441 43529354040273001529370331)
  ·
    refine ⟨65294031060409502294055497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43529354040273001529370331 65294031060409502294055497)
    ·
      refine ⟨48970523295307126720541623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65294031060409502294055497 48970523295307126720541623)
      ·
        refine ⟨73455784942960690080812435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48970523295307126720541623 73455784942960690080812435)
        ·
          refine ⟨110183677414441035121218653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73455784942960690080812435 110183677414441035121218653)
          ·
            refine ⟨41318879030415388170456995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110183677414441035121218653 41318879030415388170456995)
            ·
              refine ⟨61978318545623082255685493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41318879030415388170456995 61978318545623082255685493)
              ·
                refine ⟨5810467363652163961470515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61978318545623082255685493 5810467363652163961470515)
                ·
                  refine ⟨8715701045478245942205773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5810467363652163961470515 8715701045478245942205773)
                  ·
                    refine ⟨3268387892054342228327165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8715701045478245942205773 3268387892054342228327165)
                    ·
                      refine ⟨1225645459520378335622687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3268387892054342228327165 1225645459520378335622687)
                      ·
                        rfl

theorem cell23_2386936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_2386936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386936 prefixEnd_2386936 := by exact prefixLift 2386936
  have htrace : WordTrace (prefixWord ++ tailWord_2386936) baseStart_2386936 baseEnd_2386936 := by
    simpa [prefixWord, tailWord_2386936, baseEnd_2386936] using wordTrace_append hprefix tailTrace_2386936
  have hstable : (prefixWord ++ tailWord_2386936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386936).length < 2 ^ (prefixWord ++ tailWord_2386936).sum := by decide
  have hdescent : baseEnd_2386936 < baseStart_2386936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386940 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_2386940 : Nat := 118140960795 + 2386940 * 2 ^ 59
def prefixEnd_2386940 : Nat := 4983230072969 + 3 ^ 40 * 2386940 * 2
def baseEnd_2386940 : Nat := 1225647513442996319972669

theorem tailTrace_2386940 : CollatzResearch.WordTrace tailWord_2386940 prefixEnd_2386940 1225647513442996319972669 := by
  unfold tailWord_2386940
  simp only [CollatzResearch.WordTrace]
  refine ⟨43529426986265755870943137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58039235981687674494590849 43529426986265755870943137)
  ·
    refine ⟨32647070239699316903207353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43529426986265755870943137 32647070239699316903207353)
    ·
      refine ⟨24485302679774487677405515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32647070239699316903207353 24485302679774487677405515)
      ·
        refine ⟨36727954019661731516108273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24485302679774487677405515 36727954019661731516108273)
        ·
          refine ⟨27545965514746298637081205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36727954019661731516108273 27545965514746298637081205)
          ·
            refine ⟨2582434267007465497226363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27545965514746298637081205 2582434267007465497226363)
            ·
              refine ⟨3873651400511198245839545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582434267007465497226363 3873651400511198245839545)
              ·
                refine ⟨2905238550383398684379659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873651400511198245839545 2905238550383398684379659)
                ·
                  refine ⟨4357857825575098026569489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905238550383398684379659 4357857825575098026569489)
                  ·
                    refine ⟨3268393369181323519927117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4357857825575098026569489 3268393369181323519927117)
                    ·
                      refine ⟨1225647513442996319972669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3268393369181323519927117 1225647513442996319972669)
                      ·
                        rfl

theorem cell23_2386940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_2386940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386940 prefixEnd_2386940 := by exact prefixLift 2386940
  have htrace : WordTrace (prefixWord ++ tailWord_2386940) baseStart_2386940 baseEnd_2386940 := by
    simpa [prefixWord, tailWord_2386940, baseEnd_2386940] using wordTrace_append hprefix tailTrace_2386940
  have hstable : (prefixWord ++ tailWord_2386940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386940).length < 2 ^ (prefixWord ++ tailWord_2386940).sum := by decide
  have hdescent : baseEnd_2386940 < baseStart_2386940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386970 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3]
def baseStart_2386970 : Nat := 118140960795 + 2386970 * 2 ^ 59
def prefixEnd_2386970 : Nat := 4983230072969 + 3 ^ 40 * 2386970 * 2
def baseEnd_2386970 : Nat := 1225662917862631202597531

theorem tailTrace_2386970 : CollatzResearch.WordTrace tailWord_2386970 prefixEnd_2386970 1225662917862631202597531 := by
  unfold tailWord_2386970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21764987040605706716369591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58039965441615217910318909 21764987040605706716369591)
  ·
    refine ⟨32647480560908560074554387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21764987040605706716369591 32647480560908560074554387)
    ·
      refine ⟨48971220841362840111831581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32647480560908560074554387 48971220841362840111831581)
      ·
        refine ⟨18364207815511065041936843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48971220841362840111831581 18364207815511065041936843)
        ·
          refine ⟨27546311723266597562905265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18364207815511065041936843 27546311723266597562905265)
          ·
            refine ⟨20659733792449948172178949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27546311723266597562905265 20659733792449948172178949)
            ·
              refine ⟨3873700086084365282283553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20659733792449948172178949 3873700086084365282283553)
              ·
                refine ⟨2905275064563273961712665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873700086084365282283553 2905275064563273961712665)
                ·
                  refine ⟨2178956298422455471284499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2905275064563273961712665 2178956298422455471284499)
                  ·
                    refine ⟨3268434447633683206926749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2178956298422455471284499 3268434447633683206926749)
                    ·
                      refine ⟨1225662917862631202597531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3268434447633683206926749 1225662917862631202597531)
                      ·
                        rfl

theorem cell23_2386970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_2386970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386970 prefixEnd_2386970 := by exact prefixLift 2386970
  have htrace : WordTrace (prefixWord ++ tailWord_2386970) baseStart_2386970 baseEnd_2386970 := by
    simpa [prefixWord, tailWord_2386970, baseEnd_2386970] using wordTrace_append hprefix tailTrace_2386970
  have hstable : (prefixWord ++ tailWord_2386970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386970).length < 2 ^ (prefixWord ++ tailWord_2386970).sum := by decide
  have hdescent : baseEnd_2386970 < baseStart_2386970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386980 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_2386980 : Nat := 118140960795 + 2386980 * 2 ^ 59
def prefixEnd_2386980 : Nat := 4983230072969 + 3 ^ 40 * 2386980 * 2
def baseEnd_2386980 : Nat := 1225668052669176163472485

theorem tailTrace_2386980 : CollatzResearch.WordTrace tailWord_2386980 prefixEnd_2386980 1225668052669176163472485 := by
  unfold tailWord_2386980
  simp only [CollatzResearch.WordTrace]
  refine ⟨43530156446193299286671197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58040208594924399048894929 43530156446193299286671197)
  ·
    refine ⟨16323808667322487232501699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43530156446193299286671197 16323808667322487232501699)
    ·
      refine ⟨24485713000983730848752549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16323808667322487232501699 24485713000983730848752549)
      ·
        refine ⟨4591071187684449534141103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24485713000983730848752549 4591071187684449534141103)
        ·
          refine ⟨6886606781526674301211655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591071187684449534141103 6886606781526674301211655)
          ·
            refine ⟨10329910172290011451817483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6886606781526674301211655 10329910172290011451817483)
            ·
              refine ⟨15494865258435017177726225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10329910172290011451817483 15494865258435017177726225)
              ·
                refine ⟨11621148943826262883294669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15494865258435017177726225 11621148943826262883294669)
                ·
                  refine ⟨4357930853934848581235501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11621148943826262883294669 4357930853934848581235501)
                  ·
                    refine ⟨1634224070225568217963313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4357930853934848581235501 1634224070225568217963313)
                    ·
                      refine ⟨1225668052669176163472485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634224070225568217963313 1225668052669176163472485)
                      ·
                        rfl

theorem cell23_2386980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_2386980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2386980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2386980 prefixEnd_2386980 := by exact prefixLift 2386980
  have htrace : WordTrace (prefixWord ++ tailWord_2386980) baseStart_2386980 baseEnd_2386980 := by
    simpa [prefixWord, tailWord_2386980, baseEnd_2386980] using wordTrace_append hprefix tailTrace_2386980
  have hstable : (prefixWord ++ tailWord_2386980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386980).length < 2 ^ (prefixWord ++ tailWord_2386980).sum := by decide
  have hdescent : baseEnd_2386980 < baseStart_2386980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387014 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_2387014 : Nat := 118140960795 + 2387014 * 2 ^ 59
def prefixEnd_2387014 : Nat := 4983230072969 + 3 ^ 40 * 2387014 * 2
def baseEnd_2387014 : Nat := 1225685511011429030447329

theorem tailTrace_2387014 : CollatzResearch.WordTrace tailWord_2387014 prefixEnd_2387014 1225685511011429030447329 := by
  unfold tailWord_2387014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2720673530445731949377503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58041035316175614920053397 2720673530445731949377503)
  ·
    refine ⟨4081010295668597924066255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2720673530445731949377503 4081010295668597924066255)
    ·
      refine ⟨6121515443502896886099383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081010295668597924066255 6121515443502896886099383)
      ·
        refine ⟨9182273165254345329149075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6121515443502896886099383 9182273165254345329149075)
        ·
          refine ⟨13773409747881517993723613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9182273165254345329149075 13773409747881517993723613)
          ·
            refine ⟨5165028655455569247646355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13773409747881517993723613 5165028655455569247646355)
            ·
              refine ⟨7747542983183353871469533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165028655455569247646355 7747542983183353871469533)
              ·
                refine ⟨2905328618693757701801075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7747542983183353871469533 2905328618693757701801075)
                ·
                  refine ⟨4357992928040636552701613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905328618693757701801075 4357992928040636552701613)
                  ·
                    refine ⟨1634247348015238707263105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4357992928040636552701613 1634247348015238707263105)
                    ·
                      refine ⟨1225685511011429030447329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634247348015238707263105 1225685511011429030447329)
                      ·
                        rfl

theorem cell23_2387014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_2387014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387014 prefixEnd_2387014 := by exact prefixLift 2387014
  have htrace : WordTrace (prefixWord ++ tailWord_2387014) baseStart_2387014 baseEnd_2387014 := by
    simpa [prefixWord, tailWord_2387014, baseEnd_2387014] using wordTrace_append hprefix tailTrace_2387014
  have hstable : (prefixWord ++ tailWord_2387014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387014).length < 2 ^ (prefixWord ++ tailWord_2387014).sum := by decide
  have hdescent : baseEnd_2387014 < baseStart_2387014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387080 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 2, 5]
def baseStart_2387080 : Nat := 118140960795 + 2387080 * 2 ^ 59
def prefixEnd_2387080 : Nat := 4983230072969 + 3 ^ 40 * 2387080 * 2
def baseEnd_2387080 : Nat := 408573133578208590740675

theorem tailTrace_2387080 : CollatzResearch.WordTrace tailWord_2387080 prefixEnd_2387080 408573133578208590740675 := by
  unfold tailWord_2387080
  simp only [CollatzResearch.WordTrace]
  refine ⟨43531980096012157825991347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58042640128016210434655129 43531980096012157825991347)
  ·
    refine ⟨65297970144018236738987021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43531980096012157825991347 65297970144018236738987021)
    ·
      refine ⟨24486738804006838777120133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65297970144018236738987021 24486738804006838777120133)
      ·
        refine ⟨4591263525751282270710025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24486738804006838777120133 4591263525751282270710025)
        ·
          refine ⟨3443447644313461703032519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4591263525751282270710025 3443447644313461703032519)
          ·
            refine ⟨5165171466470192554548779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443447644313461703032519 5165171466470192554548779)
            ·
              refine ⟨7747757199705288831823169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165171466470192554548779 7747757199705288831823169)
              ·
                refine ⟨5810817899778966623867377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7747757199705288831823169 5810817899778966623867377)
                ·
                  refine ⟨4358113424834224967900533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5810817899778966623867377 4358113424834224967900533)
                  ·
                    refine ⟨408573133578208590740675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4358113424834224967900533 408573133578208590740675)
                    ·
                      rfl

theorem cell23_2387080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_2387080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387080 prefixEnd_2387080 := by exact prefixLift 2387080
  have htrace : WordTrace (prefixWord ++ tailWord_2387080) baseStart_2387080 baseEnd_2387080 := by
    simpa [prefixWord, tailWord_2387080, baseEnd_2387080] using wordTrace_append hprefix tailTrace_2387080
  have hstable : (prefixWord ++ tailWord_2387080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387080).length < 2 ^ (prefixWord ++ tailWord_2387080).sum := by decide
  have hdescent : baseEnd_2387080 < baseStart_2387080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387083 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 4, 4, 2]
def baseStart_2387083 : Nat := 118140960795 + 2387083 * 2 ^ 59
def prefixEnd_2387083 : Nat := 4983230072969 + 3 ^ 40 * 2387083 * 2
def baseEnd_2387083 : Nat := 1225720941176589260484511

theorem tailTrace_2387083 : CollatzResearch.WordTrace tailWord_2387083 prefixEnd_2387083 1225720941176589260484511 := by
  unfold tailWord_2387083
  simp only [CollatzResearch.WordTrace]
  refine ⟨87064069611013447164341903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58042713074008964776227935 87064069611013447164341903)
  ·
    refine ⟨130596104416520170746512855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87064069611013447164341903 130596104416520170746512855)
    ·
      refine ⟨195894156624780256119769283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130596104416520170746512855 195894156624780256119769283)
      ·
        refine ⟨293841234937170384179653925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195894156624780256119769283 293841234937170384179653925)
        ·
          refine ⟨55095231550719447033685111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293841234937170384179653925 55095231550719447033685111)
          ·
            refine ⟨82642847326079170550527667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55095231550719447033685111 82642847326079170550527667)
            ·
              refine ⟨123964270989118755825791501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82642847326079170550527667 123964270989118755825791501)
              ·
                refine ⟨46486601620919533434671813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123964270989118755825791501 46486601620919533434671813)
                ·
                  refine ⟨8716237803922412519000965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46486601620919533434671813 8716237803922412519000965)
                  ·
                    refine ⟨1634294588235452347312681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8716237803922412519000965 1634294588235452347312681)
                    ·
                      refine ⟨1225720941176589260484511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634294588235452347312681 1225720941176589260484511)
                      ·
                        rfl

theorem cell23_2387083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 4, 2].length) (baseStart_2387083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387083 prefixEnd_2387083 := by exact prefixLift 2387083
  have htrace : WordTrace (prefixWord ++ tailWord_2387083) baseStart_2387083 baseEnd_2387083 := by
    simpa [prefixWord, tailWord_2387083, baseEnd_2387083] using wordTrace_append hprefix tailTrace_2387083
  have hstable : (prefixWord ++ tailWord_2387083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387083).length < 2 ^ (prefixWord ++ tailWord_2387083).sum := by decide
  have hdescent : baseEnd_2387083 < baseStart_2387083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387093 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_2387093 : Nat := 118140960795 + 2387093 * 2 ^ 59
def prefixEnd_2387093 : Nat := 4983230072969 + 3 ^ 40 * 2387093 * 2
def baseEnd_2387093 : Nat := 408575358661044740453155

theorem tailTrace_2387093 : CollatzResearch.WordTrace tailWord_2387093 prefixEnd_2387093 408575358661044740453155 := by
  unfold tailWord_2387093
  simp only [CollatzResearch.WordTrace]
  refine ⟨87064434340977218872205933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58042956227318145914803955 87064434340977218872205933)
  ·
    refine ⟨32649162877866457077077225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87064434340977218872205933 32649162877866457077077225)
    ·
      refine ⟨24486872158399842807807919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32649162877866457077077225 24486872158399842807807919)
      ·
        refine ⟨36730308237599764211711879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24486872158399842807807919 36730308237599764211711879)
        ·
          refine ⟨55095462356399646317567819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36730308237599764211711879 55095462356399646317567819)
          ·
            refine ⟨82643193534599469476351729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55095462356399646317567819 82643193534599469476351729)
            ·
              refine ⟨61982395150949602107263797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82643193534599469476351729 61982395150949602107263797)
              ·
                refine ⟨5810849545401525197555981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61982395150949602107263797 5810849545401525197555981)
                ·
                  refine ⟨2179068579525571949083493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5810849545401525197555981 2179068579525571949083493)
                  ·
                    refine ⟨408575358661044740453155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2179068579525571949083493 408575358661044740453155)
                    ·
                      rfl

theorem cell23_2387093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_2387093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387093 prefixEnd_2387093 := by exact prefixLift 2387093
  have htrace : WordTrace (prefixWord ++ tailWord_2387093) baseStart_2387093 baseEnd_2387093 := by
    simpa [prefixWord, tailWord_2387093, baseEnd_2387093] using wordTrace_append hprefix tailTrace_2387093
  have hstable : (prefixWord ++ tailWord_2387093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387093).length < 2 ^ (prefixWord ++ tailWord_2387093).sum := by decide
  have hdescent : baseEnd_2387093 < baseStart_2387093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387117 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2387117 : Nat := 118140960795 + 2387117 * 2 ^ 59
def prefixEnd_2387117 : Nat := 4983230072969 + 3 ^ 40 * 2387117 * 2
def baseEnd_2387117 : Nat := 1225738399518842127459355

theorem tailTrace_2387117 : CollatzResearch.WordTrace tailWord_2387117 prefixEnd_2387117 1225738399518842127459355 := by
  unfold tailWord_2387117
  simp only [CollatzResearch.WordTrace]
  refine ⟨87065309692890270971079605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58043539795260180647386403 87065309692890270971079605)
  ·
    refine ⟨8162372783708462903538713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87065309692890270971079605 8162372783708462903538713)
    ·
      refine ⟨6121779587781347177654035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8162372783708462903538713 6121779587781347177654035)
      ·
        refine ⟨9182669381672020766481053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6121779587781347177654035 9182669381672020766481053)
        ·
          refine ⟨3443501018127007787430395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9182669381672020766481053 3443501018127007787430395)
          ·
            refine ⟨5165251527190511681145593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443501018127007787430395 5165251527190511681145593)
            ·
              refine ⟨3873938645392883760859195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5165251527190511681145593 3873938645392883760859195)
              ·
                refine ⟨5810907968089325641288793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3873938645392883760859195 5810907968089325641288793)
                ·
                  refine ⟨4358180976066994230966595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5810907968089325641288793 4358180976066994230966595)
                  ·
                    refine ⟨6537271464100491346449893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4358180976066994230966595 6537271464100491346449893)
                    ·
                      refine ⟨1225738399518842127459355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6537271464100491346449893 1225738399518842127459355)
                      ·
                        rfl

theorem cell23_2387117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2387117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387117 prefixEnd_2387117 := by exact prefixLift 2387117
  have htrace : WordTrace (prefixWord ++ tailWord_2387117) baseStart_2387117 baseEnd_2387117 := by
    simpa [prefixWord, tailWord_2387117, baseEnd_2387117] using wordTrace_append hprefix tailTrace_2387117
  have hstable : (prefixWord ++ tailWord_2387117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387117).length < 2 ^ (prefixWord ++ tailWord_2387117).sum := by decide
  have hdescent : baseEnd_2387117 < baseStart_2387117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387137 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2387137 : Nat := 118140960795 + 2387137 * 2 ^ 59
def prefixEnd_2387137 : Nat := 4983230072969 + 3 ^ 40 * 2387137 * 2
def baseEnd_2387137 : Nat := 1225748669131932049209263

theorem tailTrace_2387137 : CollatzResearch.WordTrace tailWord_2387137 prefixEnd_2387137 1225748669131932049209263 := by
  unfold tailWord_2387137
  simp only [CollatzResearch.WordTrace]
  refine ⟨87066039152817814386807665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58044026101878542924538443 87066039152817814386807665)
  ·
    refine ⟨65299529364613360790105749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87066039152817814386807665 65299529364613360790105749)
    ·
      refine ⟨3060915438966251287036207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65299529364613360790105749 3060915438966251287036207)
      ·
        refine ⟨4591373158449376930554311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060915438966251287036207 4591373158449376930554311)
        ·
          refine ⟨6887059737674065395831467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591373158449376930554311 6887059737674065395831467)
          ·
            refine ⟨10330589606511098093747201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6887059737674065395831467 10330589606511098093747201)
            ·
              refine ⟨7747942204883323570310401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10330589606511098093747201 7747942204883323570310401)
              ·
                refine ⟨5810956653662492677732801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7747942204883323570310401 5810956653662492677732801)
                ·
                  refine ⟨4358217490246869508299601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5810956653662492677732801 4358217490246869508299601)
                  ·
                    refine ⟨3268663117685152131224701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4358217490246869508299601 3268663117685152131224701)
                    ·
                      refine ⟨1225748669131932049209263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3268663117685152131224701 1225748669131932049209263)
                      ·
                        rfl

theorem cell23_2387137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2387137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387137 prefixEnd_2387137 := by exact prefixLift 2387137
  have htrace : WordTrace (prefixWord ++ tailWord_2387137) baseStart_2387137 baseEnd_2387137 := by
    simpa [prefixWord, tailWord_2387137, baseEnd_2387137] using wordTrace_append hprefix tailTrace_2387137
  have hstable : (prefixWord ++ tailWord_2387137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387137).length < 2 ^ (prefixWord ++ tailWord_2387137).sum := by decide
  have hdescent : baseEnd_2387137 < baseStart_2387137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387187 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 1, 5]
def baseStart_2387187 : Nat := 118140960795 + 2387187 * 2 ^ 59
def prefixEnd_2387187 : Nat := 4983230072969 + 3 ^ 40 * 2387187 * 2
def baseEnd_2387187 : Nat := 408591447721552284528011

theorem tailTrace_2387187 : CollatzResearch.WordTrace tailWord_2387187 prefixEnd_2387187 408591447721552284528011 := by
  unfold tailWord_2387187
  simp only [CollatzResearch.WordTrace]
  refine ⟨87067862802636672926127815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58045241868424448617418543 87067862802636672926127815)
  ·
    refine ⟨130601794203955009389191723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87067862802636672926127815 130601794203955009389191723)
    ·
      refine ⟨195902691305932514083787585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130601794203955009389191723 195902691305932514083787585)
      ·
        refine ⟨146927018479449385562840689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195902691305932514083787585 146927018479449385562840689)
        ·
          refine ⟨110195263859587039172130517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146927018479449385562840689 110195263859587039172130517)
          ·
            refine ⟨2582701496709071230596809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 110195263859587039172130517 2582701496709071230596809)
            ·
              refine ⟨1937026122531803422947607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2582701496709071230596809 1937026122531803422947607)
              ·
                refine ⟨2905539183797705134421411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937026122531803422947607 2905539183797705134421411)
                ·
                  refine ⟨4358308775696557701632117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905539183797705134421411 4358308775696557701632117)
                  ·
                    refine ⟨408591447721552284528011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4358308775696557701632117 408591447721552284528011)
                    ·
                      rfl

theorem cell23_2387187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 5].length) (baseStart_2387187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387187 prefixEnd_2387187 := by exact prefixLift 2387187
  have htrace : WordTrace (prefixWord ++ tailWord_2387187) baseStart_2387187 baseEnd_2387187 := by
    simpa [prefixWord, tailWord_2387187, baseEnd_2387187] using wordTrace_append hprefix tailTrace_2387187
  have hstable : (prefixWord ++ tailWord_2387187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387187).length < 2 ^ (prefixWord ++ tailWord_2387187).sum := by decide
  have hdescent : baseEnd_2387187 < baseStart_2387187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387193 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_2387193 : Nat := 118140960795 + 2387193 * 2 ^ 59
def prefixEnd_2387193 : Nat := 4983230072969 + 3 ^ 40 * 2387193 * 2
def baseEnd_2387193 : Nat := 1225777424048583830109005

theorem tailTrace_2387193 : CollatzResearch.WordTrace tailWord_2387193 prefixEnd_2387193 1225777424048583830109005 := by
  unfold tailWord_2387193
  simp only [CollatzResearch.WordTrace]
  refine ⟨87068081640614935950846233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58045387760409957300564155 87068081640614935950846233)
  ·
    refine ⟨65301061230461201963134675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87068081640614935950846233 65301061230461201963134675)
    ·
      refine ⟨97951591845691802944702013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65301061230461201963134675 97951591845691802944702013)
      ·
        refine ⟨36731846942134426104263255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97951591845691802944702013 36731846942134426104263255)
        ·
          refine ⟨55097770413201639156394883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36731846942134426104263255 55097770413201639156394883)
          ·
            refine ⟨82646655619802458734592325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55097770413201639156394883 82646655619802458734592325)
            ·
              refine ⟨15496247928712961012736061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82646655619802458734592325 15496247928712961012736061)
              ·
                refine ⟨5811092973267360379776023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15496247928712961012736061 5811092973267360379776023)
                ·
                  refine ⟨8716639459901040569664035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5811092973267360379776023 8716639459901040569664035)
                  ·
                    refine ⟨13074959189851560854496053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8716639459901040569664035 13074959189851560854496053)
                    ·
                      refine ⟨1225777424048583830109005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13074959189851560854496053 1225777424048583830109005)
                      ·
                        rfl

theorem cell23_2387193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_2387193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387193 prefixEnd_2387193 := by exact prefixLift 2387193
  have htrace : WordTrace (prefixWord ++ tailWord_2387193) baseStart_2387193 baseEnd_2387193 := by
    simpa [prefixWord, tailWord_2387193, baseEnd_2387193] using wordTrace_append hprefix tailTrace_2387193
  have hstable : (prefixWord ++ tailWord_2387193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387193).length < 2 ^ (prefixWord ++ tailWord_2387193).sum := by decide
  have hdescent : baseEnd_2387193 < baseStart_2387193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387217 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 2, 4]
def baseStart_2387217 : Nat := 118140960795 + 2387217 * 2 ^ 59
def prefixEnd_2387217 : Nat := 4983230072969 + 3 ^ 40 * 2387217 * 2
def baseEnd_2387217 : Nat := 408596582528097245402965

theorem tailTrace_2387217 : CollatzResearch.WordTrace tailWord_2387217 prefixEnd_2387217 408596582528097245402965 := by
  unfold tailWord_2387217
  simp only [CollatzResearch.WordTrace]
  refine ⟨87068956992527988049719905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58045971328351992033146603 87068956992527988049719905)
  ·
    refine ⟨65301717744395991037289929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87068956992527988049719905 65301717744395991037289929)
    ·
      refine ⟨48976288308296993277967447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65301717744395991037289929 48976288308296993277967447)
      ·
        refine ⟨73464432462445489916951171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48976288308296993277967447 73464432462445489916951171)
        ·
          refine ⟨110196648693668234875426757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73464432462445489916951171 110196648693668234875426757)
          ·
            refine ⟨20661871630062794039142517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110196648693668234875426757 20661871630062794039142517)
            ·
              refine ⟨1937050465318386941169611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20661871630062794039142517 1937050465318386941169611)
              ·
                refine ⟨2905575697977580411754417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937050465318386941169611 2905575697977580411754417)
                ·
                  refine ⟨2179181773483185308815813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2905575697977580411754417 2179181773483185308815813)
                  ·
                    refine ⟨408596582528097245402965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2179181773483185308815813 408596582528097245402965)
                    ·
                      rfl

theorem cell23_2387217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_2387217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387217 prefixEnd_2387217 := by exact prefixLift 2387217
  have htrace : WordTrace (prefixWord ++ tailWord_2387217) baseStart_2387217 baseEnd_2387217 := by
    simpa [prefixWord, tailWord_2387217, baseEnd_2387217] using wordTrace_append hprefix tailTrace_2387217
  have hstable : (prefixWord ++ tailWord_2387217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387217).length < 2 ^ (prefixWord ++ tailWord_2387217).sum := by decide
  have hdescent : baseEnd_2387217 < baseStart_2387217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387273 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 2, 6]
def baseStart_2387273 : Nat := 118140960795 + 2387273 * 2 ^ 59
def prefixEnd_2387273 : Nat := 4983230072969 + 3 ^ 40 * 2387273 * 2
def baseEnd_2387273 : Nat := 408606167500314505702879

theorem tailTrace_2387273 : CollatzResearch.WordTrace tailWord_2387273 prefixEnd_2387273 408606167500314505702879 := by
  unfold tailWord_2387273
  simp only [CollatzResearch.WordTrace]
  refine ⟨87070999480325109613758473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58047332986883406409172315 87070999480325109613758473)
  ·
    refine ⟨65303249610243832210318855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87070999480325109613758473 65303249610243832210318855)
    ·
      refine ⟨97954874415365748315478283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65303249610243832210318855 97954874415365748315478283)
      ·
        refine ⟨146932311623048622473217425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97954874415365748315478283 146932311623048622473217425)
        ·
          refine ⟨110199233717286466854913069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146932311623048622473217425 110199233717286466854913069)
          ·
            refine ⟨41324712643982425070592401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110199233717286466854913069 41324712643982425070592401)
            ·
              refine ⟨30993534482986818802944301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41324712643982425070592401 30993534482986818802944301)
              ·
                refine ⟨11622575431120057051104113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30993534482986818802944301 11622575431120057051104113)
                ·
                  refine ⟨8716931573340042788328085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11622575431120057051104113 8716931573340042788328085)
                  ·
                    refine ⟨408606167500314505702879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8716931573340042788328085 408606167500314505702879)
                    ·
                      rfl

theorem cell23_2387273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_2387273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387273 prefixEnd_2387273 := by exact prefixLift 2387273
  have htrace : WordTrace (prefixWord ++ tailWord_2387273) baseStart_2387273 baseEnd_2387273 := by
    simpa [prefixWord, tailWord_2387273, baseEnd_2387273] using wordTrace_append hprefix tailTrace_2387273
  have hstable : (prefixWord ++ tailWord_2387273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387273).length < 2 ^ (prefixWord ++ tailWord_2387273).sum := by decide
  have hdescent : baseEnd_2387273 < baseStart_2387273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387283 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 5]
def baseStart_2387283 : Nat := 118140960795 + 2387283 * 2 ^ 59
def prefixEnd_2387283 : Nat := 4983230072969 + 3 ^ 40 * 2387283 * 2
def baseEnd_2387283 : Nat := 1225823637307488477983591

theorem tailTrace_2387283 : CollatzResearch.WordTrace tailWord_2387283 prefixEnd_2387283 1225823637307488477983591 := by
  unfold tailWord_2387283
  simp only [CollatzResearch.WordTrace]
  refine ⟨87071364210288881321622503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58047576140192587547748335 87071364210288881321622503)
  ·
    refine ⟨130607046315433321982433755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87071364210288881321622503 130607046315433321982433755)
    ·
      refine ⟨195910569473149982973650633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130607046315433321982433755 195910569473149982973650633)
      ·
        refine ⟨146932927104862487230237975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195910569473149982973650633 146932927104862487230237975)
        ·
          refine ⟨220399390657293730845356963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146932927104862487230237975 220399390657293730845356963)
          ·
            refine ⟨330599085985940596268035445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220399390657293730845356963 330599085985940596268035445)
            ·
              refine ⟨30993664311181930900128323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 330599085985940596268035445 30993664311181930900128323)
              ·
                refine ⟨46490496466772896350192485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30993664311181930900128323 46490496466772896350192485)
                ·
                  refine ⟨8716968087519918065661091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46490496466772896350192485 8716968087519918065661091)
                  ·
                    refine ⟨13075452131279877098491637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8716968087519918065661091 13075452131279877098491637)
                    ·
                      refine ⟨1225823637307488477983591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13075452131279877098491637 1225823637307488477983591)
                      ·
                        rfl

theorem cell23_2387283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_2387283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387283 prefixEnd_2387283 := by exact prefixLift 2387283
  have htrace : WordTrace (prefixWord ++ tailWord_2387283) baseStart_2387283 baseEnd_2387283 := by
    simpa [prefixWord, tailWord_2387283, baseEnd_2387283] using wordTrace_append hprefix tailTrace_2387283
  have hstable : (prefixWord ++ tailWord_2387283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387283).length < 2 ^ (prefixWord ++ tailWord_2387283).sum := by decide
  have hdescent : baseEnd_2387283 < baseStart_2387283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387297 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_2387297 : Nat := 118140960795 + 2387297 * 2 ^ 59
def prefixEnd_2387297 : Nat := 4983230072969 + 3 ^ 40 * 2387297 * 2
def baseEnd_2387297 : Nat := 1225830826036651423208527

theorem tailTrace_2387297 : CollatzResearch.WordTrace tailWord_2387297 prefixEnd_2387297 1225830826036651423208527 := by
  unfold tailWord_2387297
  simp only [CollatzResearch.WordTrace]
  refine ⟨87071874832238161712632145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58047916554825441141754763 87071874832238161712632145)
  ·
    refine ⟨65303906124178621284474109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87071874832238161712632145 65303906124178621284474109)
    ·
      refine ⟨24488964796566982981677791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65303906124178621284474109 24488964796566982981677791)
      ·
        refine ⟨36733447194850474472516687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24488964796566982981677791 36733447194850474472516687)
        ·
          refine ⟨55100170792275711708775031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36733447194850474472516687 55100170792275711708775031)
          ·
            refine ⟨82650256188413567563162547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55100170792275711708775031 82650256188413567563162547)
            ·
              refine ⟨123975384282620351344743821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82650256188413567563162547 123975384282620351344743821)
              ·
                refine ⟨46490769105982631754278933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123975384282620351344743821 46490769105982631754278933)
                ·
                  refine ⟨2179254801842935863481825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46490769105982631754278933 2179254801842935863481825)
                  ·
                    refine ⟨1634441101382201897611369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2179254801842935863481825 1634441101382201897611369)
                    ·
                      refine ⟨1225830826036651423208527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634441101382201897611369 1225830826036651423208527)
                      ·
                        rfl

theorem cell23_2387297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_2387297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387297 prefixEnd_2387297 := by exact prefixLift 2387297
  have htrace : WordTrace (prefixWord ++ tailWord_2387297) baseStart_2387297 baseEnd_2387297 := by
    simpa [prefixWord, tailWord_2387297, baseEnd_2387297] using wordTrace_append hprefix tailTrace_2387297
  have hstable : (prefixWord ++ tailWord_2387297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387297).length < 2 ^ (prefixWord ++ tailWord_2387297).sum := by decide
  have hdescent : baseEnd_2387297 < baseStart_2387297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387300 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_2387300 : Nat := 118140960795 + 2387300 * 2 ^ 59
def prefixEnd_2387300 : Nat := 4983230072969 + 3 ^ 40 * 2387300 * 2
def baseEnd_2387300 : Nat := 1225832366478614911471013

theorem tailTrace_2387300 : CollatzResearch.WordTrace tailWord_2387300 prefixEnd_2387300 1225832366478614911471013 := by
  unfold tailWord_2387300
  simp only [CollatzResearch.WordTrace]
  refine ⟨43535992125613646612495677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58047989500818195483327569 43535992125613646612495677)
  ·
    refine ⟨16325997047105117479685879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43535992125613646612495677 16325997047105117479685879)
    ·
      refine ⟨24488995570657676219528819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16325997047105117479685879 24488995570657676219528819)
      ·
        refine ⟨36733493355986514329293229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24488995570657676219528819 36733493355986514329293229)
        ·
          refine ⟨13775060008494942873484961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36733493355986514329293229 13775060008494942873484961)
          ·
            refine ⟨10331295006371207155113721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13775060008494942873484961 10331295006371207155113721)
            ·
              refine ⟨7748471254778405366335291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10331295006371207155113721 7748471254778405366335291)
              ·
                refine ⟨11622706882167608049502937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7748471254778405366335291 11622706882167608049502937)
                ·
                  refine ⟨8717030161625706037127203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11622706882167608049502937 8717030161625706037127203)
                  ·
                    refine ⟨13075545242438559055690805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8717030161625706037127203 13075545242438559055690805)
                    ·
                      refine ⟨1225832366478614911471013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13075545242438559055690805 1225832366478614911471013)
                      ·
                        rfl

theorem cell23_2387300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_2387300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387300 prefixEnd_2387300 := by exact prefixLift 2387300
  have htrace : WordTrace (prefixWord ++ tailWord_2387300) baseStart_2387300 baseEnd_2387300 := by
    simpa [prefixWord, tailWord_2387300, baseEnd_2387300] using wordTrace_append hprefix tailTrace_2387300
  have hstable : (prefixWord ++ tailWord_2387300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387300).length < 2 ^ (prefixWord ++ tailWord_2387300).sum := by decide
  have hdescent : baseEnd_2387300 < baseStart_2387300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387313 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2387313 : Nat := 118140960795 + 2387313 * 2 ^ 59
def prefixEnd_2387313 : Nat := 4983230072969 + 3 ^ 40 * 2387313 * 2
def baseEnd_2387313 : Nat := 1225839041727123360608453

theorem tailTrace_2387313 : CollatzResearch.WordTrace tailWord_2387313 prefixEnd_2387313 1225839041727123360608453 := by
  unfold tailWord_2387313
  simp only [CollatzResearch.WordTrace]
  refine ⟨87072458400180196445214593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58048305600120130963476395 87072458400180196445214593)
  ·
    refine ⟨65304343800135147333910945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87072458400180196445214593 65304343800135147333910945)
    ·
      refine ⟨48978257850101360500433209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65304343800135147333910945 48978257850101360500433209)
      ·
        refine ⟨36733693387576020375324907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48978257850101360500433209 36733693387576020375324907)
        ·
          refine ⟨55100540081364030562987361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36733693387576020375324907 55100540081364030562987361)
          ·
            refine ⟨41325405061023022922240521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55100540081364030562987361 41325405061023022922240521)
            ·
              refine ⟨30994053795767267191680391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41325405061023022922240521 30994053795767267191680391)
              ·
                refine ⟨46491080693650900787520587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30994053795767267191680391 46491080693650900787520587)
                ·
                  refine ⟨69736621040476351181280881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46491080693650900787520587 69736621040476351181280881)
                  ·
                    refine ⟨52302465780357263385960661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69736621040476351181280881 52302465780357263385960661)
                    ·
                      refine ⟨1225839041727123360608453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52302465780357263385960661 1225839041727123360608453)
                      ·
                        rfl

theorem cell23_2387313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2387313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387313 prefixEnd_2387313 := by exact prefixLift 2387313
  have htrace : WordTrace (prefixWord ++ tailWord_2387313) baseStart_2387313 baseEnd_2387313 := by
    simpa [prefixWord, tailWord_2387313, baseEnd_2387313] using wordTrace_append hprefix tailTrace_2387313
  have hstable : (prefixWord ++ tailWord_2387313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387313).length < 2 ^ (prefixWord ++ tailWord_2387313).sum := by decide
  have hdescent : baseEnd_2387313 < baseStart_2387313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387343 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_2387343 : Nat := 118140960795 + 2387343 * 2 ^ 59
def prefixEnd_2387343 : Nat := 4983230072969 + 3 ^ 40 * 2387343 * 2
def baseEnd_2387343 : Nat := 1225854446146758243233315

theorem tailTrace_2387343 : CollatzResearch.WordTrace tailWord_2387343 prefixEnd_2387343 1225854446146758243233315 := by
  unfold tailWord_2387343
  simp only [CollatzResearch.WordTrace]
  refine ⟨87073552590071511568806683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58049035060047674379204455 87073552590071511568806683)
  ·
    refine ⟨130610328885107267353210025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87073552590071511568806683 130610328885107267353210025)
    ·
      refine ⟨97957746663830450514907519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130610328885107267353210025 97957746663830450514907519)
      ·
        refine ⟨146936619995745675772361279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97957746663830450514907519 146936619995745675772361279)
        ·
          refine ⟨220404929993618513658541919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146936619995745675772361279 220404929993618513658541919)
          ·
            refine ⟨330607394990427770487812879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220404929993618513658541919 330607394990427770487812879)
            ·
              refine ⟨495911092485641655731719319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330607394990427770487812879 495911092485641655731719319)
              ·
                refine ⟨743866638728462483597578979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495911092485641655731719319 743866638728462483597578979)
                ·
                  refine ⟨1115799958092693725396368469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743866638728462483597578979 1115799958092693725396368469)
                  ·
                    refine ⟨13075780758898754594488693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1115799958092693725396368469 13075780758898754594488693)
                    ·
                      refine ⟨1225854446146758243233315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13075780758898754594488693 1225854446146758243233315)
                      ·
                        rfl

theorem cell23_2387343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_2387343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387343 prefixEnd_2387343 := by exact prefixLift 2387343
  have htrace : WordTrace (prefixWord ++ tailWord_2387343) baseStart_2387343 baseEnd_2387343 := by
    simpa [prefixWord, tailWord_2387343, baseEnd_2387343] using wordTrace_append hprefix tailTrace_2387343
  have hstable : (prefixWord ++ tailWord_2387343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387343).length < 2 ^ (prefixWord ++ tailWord_2387343).sum := by decide
  have hdescent : baseEnd_2387343 < baseStart_2387343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387400 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_2387400 : Nat := 118140960795 + 2387400 * 2 ^ 59
def prefixEnd_2387400 : Nat := 4983230072969 + 3 ^ 40 * 2387400 * 2
def baseEnd_2387400 : Nat := 1225883714544064520220553

theorem tailTrace_2387400 : CollatzResearch.WordTrace tailWord_2387400 prefixEnd_2387400 1225883714544064520220553 := by
  unfold tailWord_2387400
  simp only [CollatzResearch.WordTrace]
  refine ⟨43537815775432505151815827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58050421033910006869087769 43537815775432505151815827)
  ·
    refine ⟨65306723663148757727723741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43537815775432505151815827 65306723663148757727723741)
    ·
      refine ⟨24490021373680784147896403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65306723663148757727723741 24490021373680784147896403)
      ·
        refine ⟨36735032060521176221844605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24490021373680784147896403 36735032060521176221844605)
        ·
          refine ⟨13775637022695441083191727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36735032060521176221844605 13775637022695441083191727)
          ·
            refine ⟨20663455534043161624787591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13775637022695441083191727 20663455534043161624787591)
            ·
              refine ⟨30995183301064742437181387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20663455534043161624787591 30995183301064742437181387)
              ·
                refine ⟨46492774951597113655772081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30995183301064742437181387 46492774951597113655772081)
                ·
                  refine ⟨34869581213697835241829061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46492774951597113655772081 34869581213697835241829061)
                  ·
                    refine ⟨6538046477568344107842949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34869581213697835241829061 6538046477568344107842949)
                    ·
                      refine ⟨1225883714544064520220553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6538046477568344107842949 1225883714544064520220553)
                      ·
                        rfl

theorem cell23_2387400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_2387400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387400 prefixEnd_2387400 := by exact prefixLift 2387400
  have htrace : WordTrace (prefixWord ++ tailWord_2387400) baseStart_2387400 baseEnd_2387400 := by
    simpa [prefixWord, tailWord_2387400, baseEnd_2387400] using wordTrace_append hprefix tailTrace_2387400
  have hstable : (prefixWord ++ tailWord_2387400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387400).length < 2 ^ (prefixWord ++ tailWord_2387400).sum := by decide
  have hdescent : baseEnd_2387400 < baseStart_2387400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387447 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 1, 5, 2]
def baseStart_2387447 : Nat := 118140960795 + 2387447 * 2 ^ 59
def prefixEnd_2387447 : Nat := 4983230072969 + 3 ^ 40 * 2387447 * 2
def baseEnd_2387447 : Nat := 1225907848134825836332837

theorem tailTrace_2387447 : CollatzResearch.WordTrace tailWord_2387447 prefixEnd_2387447 1225907848134825836332837 := by
  unfold tailWord_2387447
  simp only [CollatzResearch.WordTrace]
  refine ⟨87077345781694737330592595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58051563854463158220395063 87077345781694737330592595)
  ·
    refine ⟨130616018672542105995888893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87077345781694737330592595 130616018672542105995888893)
    ·
      refine ⟨48981007002203289748458335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130616018672542105995888893 48981007002203289748458335)
      ·
        refine ⟨73471510503304934622687503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48981007002203289748458335 73471510503304934622687503)
        ·
          refine ⟨110207265754957401934031255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73471510503304934622687503 110207265754957401934031255)
          ·
            refine ⟨165310898632436102901046883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110207265754957401934031255 165310898632436102901046883)
            ·
              refine ⟨247966347948654154351570325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165310898632436102901046883 247966347948654154351570325)
              ·
                refine ⟨11623422560093163485229859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 247966347948654154351570325 11623422560093163485229859)
                ·
                  refine ⟨17435133840139745227844789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11623422560093163485229859 17435133840139745227844789)
                  ·
                    refine ⟨1634543797513101115110449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17435133840139745227844789 1634543797513101115110449)
                    ·
                      refine ⟨1225907848134825836332837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634543797513101115110449 1225907848134825836332837)
                      ·
                        rfl

theorem cell23_2387447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_2387447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387447 prefixEnd_2387447 := by exact prefixLift 2387447
  have htrace : WordTrace (prefixWord ++ tailWord_2387447) baseStart_2387447 baseEnd_2387447 := by
    simpa [prefixWord, tailWord_2387447, baseEnd_2387447] using wordTrace_append hprefix tailTrace_2387447
  have hstable : (prefixWord ++ tailWord_2387447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387447).length < 2 ^ (prefixWord ++ tailWord_2387447).sum := by decide
  have hdescent : baseEnd_2387447 < baseStart_2387447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387464 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_2387464 : Nat := 118140960795 + 2387464 * 2 ^ 59
def prefixEnd_2387464 : Nat := 4983230072969 + 3 ^ 40 * 2387464 * 2
def baseEnd_2387464 : Nat := 1225916577305952269820259

theorem tailTrace_2387464 : CollatzResearch.WordTrace tailWord_2387464 prefixEnd_2387464 1225916577305952269820259 := by
  unfold tailWord_2387464
  simp only [CollatzResearch.WordTrace]
  refine ⟨43538982911316574616980723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58051977215088766155974297 43538982911316574616980723)
  ·
    refine ⟨65308474366974861925471085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43538982911316574616980723 65308474366974861925471085)
    ·
      refine ⟨24490677887615573222051657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65308474366974861925471085 24490677887615573222051657)
      ·
        refine ⟨18368008415711679916538743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24490677887615573222051657 18368008415711679916538743)
        ·
          refine ⟨27552012623567519874808115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18368008415711679916538743 27552012623567519874808115)
          ·
            refine ⟨41328018935351279812212173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27552012623567519874808115 41328018935351279812212173)
            ·
              refine ⟨15498007100756729929579565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41328018935351279812212173 15498007100756729929579565)
              ·
                refine ⟨5811752662783773723592337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15498007100756729929579565 5811752662783773723592337)
                ·
                  refine ⟨4358814497087830292694253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5811752662783773723592337 4358814497087830292694253)
                  ·
                    refine ⟨1634555436407936359760345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4358814497087830292694253 1634555436407936359760345)
                    ·
                      refine ⟨1225916577305952269820259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634555436407936359760345 1225916577305952269820259)
                      ·
                        rfl

theorem cell23_2387464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_2387464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387464 prefixEnd_2387464 := by exact prefixLift 2387464
  have htrace : WordTrace (prefixWord ++ tailWord_2387464) baseStart_2387464 baseEnd_2387464 := by
    simpa [prefixWord, tailWord_2387464, baseEnd_2387464] using wordTrace_append hprefix tailTrace_2387464
  have hstable : (prefixWord ++ tailWord_2387464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387464).length < 2 ^ (prefixWord ++ tailWord_2387464).sum := by decide
  have hdescent : baseEnd_2387464 < baseStart_2387464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387487 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 4, 4]
def baseStart_2387487 : Nat := 118140960795 + 2387487 * 2 ^ 59
def prefixEnd_2387487 : Nat := 4983230072969 + 3 ^ 40 * 2387487 * 2
def baseEnd_2387487 : Nat := 408642795787001893277551

theorem tailTrace_2387487 : CollatzResearch.WordTrace tailWord_2387487 prefixEnd_2387487 408642795787001893277551 := by
  unfold tailWord_2387487
  simp only [CollatzResearch.WordTrace]
  refine ⟨87078804701549824162048715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58052536467699882774699143 87078804701549824162048715)
  ·
    refine ⟨130618207052324736243073073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87078804701549824162048715 130618207052324736243073073)
    ·
      refine ⟨97963655289243552182304805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130618207052324736243073073 97963655289243552182304805)
      ·
        refine ⟨18368185366733166034182151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97963655289243552182304805 18368185366733166034182151)
        ·
          refine ⟨27552278050099749051273227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18368185366733166034182151 27552278050099749051273227)
          ·
            refine ⟨41328417075149623576909841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27552278050099749051273227 41328417075149623576909841)
            ·
              refine ⟨30996312806362217682682381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41328417075149623576909841 30996312806362217682682381)
              ·
                refine ⟨11623617302385831631005893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30996312806362217682682381 11623617302385831631005893)
                ·
                  refine ⟨2179428244197343430813605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11623617302385831631005893 2179428244197343430813605)
                  ·
                    refine ⟨408642795787001893277551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2179428244197343430813605 408642795787001893277551)
                    ·
                      rfl

theorem cell23_2387487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 4].length) (baseStart_2387487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387487 prefixEnd_2387487 := by exact prefixLift 2387487
  have htrace : WordTrace (prefixWord ++ tailWord_2387487) baseStart_2387487 baseEnd_2387487 := by
    simpa [prefixWord, tailWord_2387487, baseEnd_2387487] using wordTrace_append hprefix tailTrace_2387487
  have hstable : (prefixWord ++ tailWord_2387487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387487).length < 2 ^ (prefixWord ++ tailWord_2387487).sum := by decide
  have hdescent : baseEnd_2387487 < baseStart_2387487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387488 : List Nat := [2, 1, 1, 6, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2387488 : Nat := 118140960795 + 2387488 * 2 ^ 59
def prefixEnd_2387488 : Nat := 4983230072969 + 3 ^ 40 * 2387488 * 2
def baseEnd_2387488 : Nat := 1225928900841660175920149

theorem tailTrace_2387488 : CollatzResearch.WordTrace tailWord_2387488 prefixEnd_2387488 1225928900841660175920149 := by
  unfold tailWord_2387488
  simp only [CollatzResearch.WordTrace]
  refine ⟨43539420587273100666417559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58052560783030800888556745 43539420587273100666417559)
  ·
    refine ⟨65309130880909650999626339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43539420587273100666417559 65309130880909650999626339)
    ·
      refine ⟨97963696321364476499439509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65309130880909650999626339 97963696321364476499439509)
      ·
        refine ⟨4592048265063959835911227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97963696321364476499439509 4592048265063959835911227)
        ·
          refine ⟨6888072397595939753866841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4592048265063959835911227 6888072397595939753866841)
          ·
            refine ⟨5166054298196954815400131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6888072397595939753866841 5166054298196954815400131)
            ·
              refine ⟨7749081447295432223100197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166054298196954815400131 7749081447295432223100197)
              ·
                refine ⟨1452952771367893541831287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7749081447295432223100197 1452952771367893541831287)
                ·
                  refine ⟨2179429157051840312746931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452952771367893541831287 2179429157051840312746931)
                  ·
                    refine ⟨3269143735577760469120397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2179429157051840312746931 3269143735577760469120397)
                    ·
                      refine ⟨1225928900841660175920149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3269143735577760469120397 1225928900841660175920149)
                      ·
                        rfl

theorem cell23_2387488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2387488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387488 prefixEnd_2387488 := by exact prefixLift 2387488
  have htrace : WordTrace (prefixWord ++ tailWord_2387488) baseStart_2387488 baseEnd_2387488 := by
    simpa [prefixWord, tailWord_2387488, baseEnd_2387488] using wordTrace_append hprefix tailTrace_2387488
  have hstable : (prefixWord ++ tailWord_2387488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387488).length < 2 ^ (prefixWord ++ tailWord_2387488).sum := by decide
  have hdescent : baseEnd_2387488 < baseStart_2387488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387507 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 4]
def baseStart_2387507 : Nat := 118140960795 + 2387507 * 2 ^ 59
def prefixEnd_2387507 : Nat := 4983230072969 + 3 ^ 40 * 2387507 * 2
def baseEnd_2387507 : Nat := 1225938656974095601582561

theorem tailTrace_2387507 : CollatzResearch.WordTrace tailWord_2387507 prefixEnd_2387507 1225938656974095601582561 := by
  unfold tailWord_2387507
  simp only [CollatzResearch.WordTrace]
  refine ⟨87079534161477367577776775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58053022774318245051851183 87079534161477367577776775)
  ·
    refine ⟨130619301242216051366665163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87079534161477367577776775 130619301242216051366665163)
    ·
      refine ⟨195928951863324077049997745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130619301242216051366665163 195928951863324077049997745)
      ·
        refine ⟨146946713897493057787498309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195928951863324077049997745 146946713897493057787498309)
        ·
          refine ⟨27552508855779948335155933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146946713897493057787498309 27552508855779948335155933)
          ·
            refine ⟨10332190820917480625683475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27552508855779948335155933 10332190820917480625683475)
            ·
              refine ⟨15498286231376220938525213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10332190820917480625683475 15498286231376220938525213)
              ·
                refine ⟨5811857336766082851946955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15498286231376220938525213 5811857336766082851946955)
                ·
                  refine ⟨8717786005149124277920433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5811857336766082851946955 8717786005149124277920433)
                  ·
                    refine ⟨6538339503861843208440325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8717786005149124277920433 6538339503861843208440325)
                    ·
                      refine ⟨1225938656974095601582561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6538339503861843208440325 1225938656974095601582561)
                      ·
                        rfl

theorem cell23_2387507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_2387507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387507 prefixEnd_2387507 := by exact prefixLift 2387507
  have htrace : WordTrace (prefixWord ++ tailWord_2387507) baseStart_2387507 baseEnd_2387507 := by
    simpa [prefixWord, tailWord_2387507, baseEnd_2387507] using wordTrace_append hprefix tailTrace_2387507
  have hstable : (prefixWord ++ tailWord_2387507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387507).length < 2 ^ (prefixWord ++ tailWord_2387507).sum := by decide
  have hdescent : baseEnd_2387507 < baseStart_2387507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387511 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 3, 2, 2]
def baseStart_2387511 : Nat := 118140960795 + 2387511 * 2 ^ 59
def prefixEnd_2387511 : Nat := 4983230072969 + 3 ^ 40 * 2387511 * 2
def baseEnd_2387511 : Nat := 1225940710896713585932543

theorem tailTrace_2387511 : CollatzResearch.WordTrace tailWord_2387511 prefixEnd_2387511 1225940710896713585932543 := by
  unfold tailWord_2387511
  simp only [CollatzResearch.WordTrace]
  refine ⟨87079680053462876260922387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58053120035641917507281591 87079680053462876260922387)
  ·
    refine ⟨130619520080194314391383581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87079680053462876260922387 130619520080194314391383581)
    ·
      refine ⟨48982320030072867896768843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130619520080194314391383581 48982320030072867896768843)
      ·
        refine ⟨73473480045109301845153265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48982320030072867896768843 73473480045109301845153265)
        ·
          refine ⟨55105110033831976383864949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73473480045109301845153265 55105110033831976383864949)
          ·
            refine ⟨5166104065671747785987339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55105110033831976383864949 5166104065671747785987339)
            ·
              refine ⟨7749156098507621678981009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166104065671747785987339 7749156098507621678981009)
              ·
                refine ⟨5811867073880716259235757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7749156098507621678981009 5811867073880716259235757)
                ·
                  refine ⟨2179450152705268597213409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5811867073880716259235757 2179450152705268597213409)
                  ·
                    refine ⟨1634587614528951447910057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2179450152705268597213409 1634587614528951447910057)
                    ·
                      refine ⟨1225940710896713585932543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634587614528951447910057 1225940710896713585932543)
                      ·
                        rfl

theorem cell23_2387511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_2387511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387511 prefixEnd_2387511 := by exact prefixLift 2387511
  have htrace : WordTrace (prefixWord ++ tailWord_2387511) baseStart_2387511 baseEnd_2387511 := by
    simpa [prefixWord, tailWord_2387511, baseEnd_2387511] using wordTrace_append hprefix tailTrace_2387511
  have hstable : (prefixWord ++ tailWord_2387511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387511).length < 2 ^ (prefixWord ++ tailWord_2387511).sum := by decide
  have hdescent : baseEnd_2387511 < baseStart_2387511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387514 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3]
def baseStart_2387514 : Nat := 118140960795 + 2387514 * 2 ^ 59
def prefixEnd_2387514 : Nat := 4983230072969 + 3 ^ 40 * 2387514 * 2
def baseEnd_2387514 : Nat := 1225942251338677074195029

theorem tailTrace_2387514 : CollatzResearch.WordTrace tailWord_2387514 prefixEnd_2387514 1225942251338677074195029 := by
  unfold tailWord_2387514
  simp only [CollatzResearch.WordTrace]
  refine ⟨21769947368113001943320399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58053192981634671848854397 21769947368113001943320399)
  ·
    refine ⟨32654921052169502914980599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21769947368113001943320399 32654921052169502914980599)
    ·
      refine ⟨48982381578254254372470899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32654921052169502914980599 48982381578254254372470899)
      ·
        refine ⟨73473572367381381558706349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48982381578254254372470899 73473572367381381558706349)
        ·
          refine ⟨27552589637768018084514881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73473572367381381558706349 27552589637768018084514881)
          ·
            refine ⟨20664442228326013563386161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27552589637768018084514881 20664442228326013563386161)
            ·
              refine ⟨15498331671244510172539621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20664442228326013563386161 15498331671244510172539621)
              ·
                refine ⟨2905937188358345657351179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15498331671244510172539621 2905937188358345657351179)
                ·
                  refine ⟨4358905782537518486026769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905937188358345657351179 4358905782537518486026769)
                  ·
                    refine ⟨3269179336903138864520077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4358905782537518486026769 3269179336903138864520077)
                    ·
                      refine ⟨1225942251338677074195029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3269179336903138864520077 1225942251338677074195029)
                      ·
                        rfl

theorem cell23_2387514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_2387514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387514 prefixEnd_2387514 := by exact prefixLift 2387514
  have htrace : WordTrace (prefixWord ++ tailWord_2387514) baseStart_2387514 baseEnd_2387514 := by
    simpa [prefixWord, tailWord_2387514, baseEnd_2387514] using wordTrace_append hprefix tailTrace_2387514
  have hstable : (prefixWord ++ tailWord_2387514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387514).length < 2 ^ (prefixWord ++ tailWord_2387514).sum := by decide
  have hdescent : baseEnd_2387514 < baseStart_2387514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387574 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2387574 : Nat := 118140960795 + 2387574 * 2 ^ 59
def prefixEnd_2387574 : Nat := 4983230072969 + 3 ^ 40 * 2387574 * 2
def baseEnd_2387574 : Nat := 1225973060177946839444753

theorem tailTrace_2387574 : CollatzResearch.WordTrace tailWord_2387574 prefixEnd_2387574 1225973060177946839444753 := by
  unfold tailWord_2387574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442623615764664876279111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58054651901489758680310517 5442623615764664876279111)
  ·
    refine ⟨8163935423646997314418667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5442623615764664876279111 8163935423646997314418667)
    ·
      refine ⟨12245903135470495971628001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8163935423646997314418667 12245903135470495971628001)
      ·
        refine ⟨9184427351602871978721001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12245903135470495971628001 9184427351602871978721001)
        ·
          refine ⟨6888320513702153984040751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9184427351602871978721001 6888320513702153984040751)
          ·
            refine ⟨10332480770553230976061127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6888320513702153984040751 10332480770553230976061127)
            ·
              refine ⟨15498721155829846464091691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10332480770553230976061127 15498721155829846464091691)
              ·
                refine ⟨23248081733744769696137537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15498721155829846464091691 23248081733744769696137537)
                ·
                  refine ⟨17436061300308577272103153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23248081733744769696137537 17436061300308577272103153)
                  ·
                    refine ⟨13077045975231432954077365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17436061300308577272103153 13077045975231432954077365)
                    ·
                      refine ⟨1225973060177946839444753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13077045975231432954077365 1225973060177946839444753)
                      ·
                        rfl

theorem cell23_2387574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2387574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387574 prefixEnd_2387574 := by exact prefixLift 2387574
  have htrace : WordTrace (prefixWord ++ tailWord_2387574) baseStart_2387574 baseEnd_2387574 := by
    simpa [prefixWord, tailWord_2387574, baseEnd_2387574] using wordTrace_append hprefix tailTrace_2387574
  have hstable : (prefixWord ++ tailWord_2387574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387574).length < 2 ^ (prefixWord ++ tailWord_2387574).sum := by decide
  have hdescent : baseEnd_2387574 < baseStart_2387574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387584 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 3, 4, 2]
def baseStart_2387584 : Nat := 118140960795 + 2387584 * 2 ^ 59
def prefixEnd_2387584 : Nat := 4983230072969 + 3 ^ 40 * 2387584 * 2
def baseEnd_2387584 : Nat := 1225978194984491800319707

theorem tailTrace_2387584 : CollatzResearch.WordTrace tailWord_2387584 prefixEnd_2387584 1225978194984491800319707 := by
  unfold tailWord_2387584
  simp only [CollatzResearch.WordTrace]
  refine ⟨43541171291099204864164903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58054895054798939818886537 43541171291099204864164903)
  ·
    refine ⟨65311756936648807296247355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43541171291099204864164903 65311756936648807296247355)
    ·
      refine ⟨97967635404973210944371033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65311756936648807296247355 97967635404973210944371033)
      ·
        refine ⟨73475726553729908208278275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97967635404973210944371033 73475726553729908208278275)
        ·
          refine ⟨110213589830594862312417413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73475726553729908208278275 110213589830594862312417413)
          ·
            refine ⟨20665048093236536683578265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110213589830594862312417413 20665048093236536683578265)
            ·
              refine ⟨15498786069927402512683699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20665048093236536683578265 15498786069927402512683699)
              ·
                refine ⟨23248179104891103769025549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15498786069927402512683699 23248179104891103769025549)
                ·
                  refine ⟨8718067164334163913384581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23248179104891103769025549 8718067164334163913384581)
                  ·
                    refine ⟨1634637593312655733759609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8718067164334163913384581 1634637593312655733759609)
                    ·
                      refine ⟨1225978194984491800319707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634637593312655733759609 1225978194984491800319707)
                      ·
                        rfl

theorem cell23_2387584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_2387584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387584 prefixEnd_2387584 := by exact prefixLift 2387584
  have htrace : WordTrace (prefixWord ++ tailWord_2387584) baseStart_2387584 baseEnd_2387584 := by
    simpa [prefixWord, tailWord_2387584, baseEnd_2387584] using wordTrace_append hprefix tailTrace_2387584
  have hstable : (prefixWord ++ tailWord_2387584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387584).length < 2 ^ (prefixWord ++ tailWord_2387584).sum := by decide
  have hdescent : baseEnd_2387584 < baseStart_2387584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387587 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 3]
def baseStart_2387587 : Nat := 118140960795 + 2387587 * 2 ^ 59
def prefixEnd_2387587 : Nat := 4983230072969 + 3 ^ 40 * 2387587 * 2
def baseEnd_2387587 : Nat := 1225979735426455288582193

theorem tailTrace_2387587 : CollatzResearch.WordTrace tailWord_2387587 prefixEnd_2387587 1225979735426455288582193 := by
  unfold tailWord_2387587
  simp only [CollatzResearch.WordTrace]
  refine ⟨87082452001187541240689015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58054968000791694160459343 87082452001187541240689015)
  ·
    refine ⟨130623678001781311861033523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87082452001187541240689015 130623678001781311861033523)
    ·
      refine ⟨195935517002671967791550285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130623678001781311861033523 195935517002671967791550285)
      ·
        refine ⟨73475818876001987921831357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195935517002671967791550285 73475818876001987921831357)
        ·
          refine ⟨27553432078500745470686759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73475818876001987921831357 27553432078500745470686759)
          ·
            refine ⟨41330148117751118206030139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27553432078500745470686759 41330148117751118206030139)
            ·
              refine ⟨61995222176626677309045209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41330148117751118206030139 61995222176626677309045209)
              ·
                refine ⟨46496416632470007981783907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61995222176626677309045209 46496416632470007981783907)
                ·
                  refine ⟨69744624948705011972675861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46496416632470007981783907 69744624948705011972675861)
                  ·
                    refine ⟨3269279294470547436219181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69744624948705011972675861 3269279294470547436219181)
                    ·
                      refine ⟨1225979735426455288582193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3269279294470547436219181 1225979735426455288582193)
                      ·
                        rfl

theorem cell23_2387587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_2387587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387587 prefixEnd_2387587 := by exact prefixLift 2387587
  have htrace : WordTrace (prefixWord ++ tailWord_2387587) baseStart_2387587 baseEnd_2387587 := by
    simpa [prefixWord, tailWord_2387587, baseEnd_2387587] using wordTrace_append hprefix tailTrace_2387587
  have hstable : (prefixWord ++ tailWord_2387587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387587).length < 2 ^ (prefixWord ++ tailWord_2387587).sum := by decide
  have hdescent : baseEnd_2387587 < baseStart_2387587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387612 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_2387612 : Nat := 118140960795 + 2387612 * 2 ^ 59
def prefixEnd_2387612 : Nat := 4983230072969 + 3 ^ 40 * 2387612 * 2
def baseEnd_2387612 : Nat := 1225992572442817690769579

theorem tailTrace_2387612 : CollatzResearch.WordTrace tailWord_2387612 prefixEnd_2387612 1225992572442817690769579 := by
  unfold tailWord_2387612
  simp only [CollatzResearch.WordTrace]
  refine ⟨43541681913048485255174545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58055575884064647006899393 43541681913048485255174545)
  ·
    refine ⟨32656261434786363941380909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43541681913048485255174545 32656261434786363941380909)
    ·
      refine ⟨12246098038044886478017841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32656261434786363941380909 12246098038044886478017841)
      ·
        refine ⟨9184573528533664858513381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12246098038044886478017841 9184573528533664858513381)
        ·
          refine ⟨1722107536600062160971259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9184573528533664858513381 1722107536600062160971259)
          ·
            refine ⟨2583161304900093241456889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722107536600062160971259 2583161304900093241456889)
            ·
              refine ⟨1937370978675069931092667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2583161304900093241456889 1937370978675069931092667)
              ·
                refine ⟨2906056468012604896639001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937370978675069931092667 2906056468012604896639001)
                ·
                  refine ⟨2179542351009453672479251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2906056468012604896639001 2179542351009453672479251)
                  ·
                    refine ⟨3269313526514180508718877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2179542351009453672479251 3269313526514180508718877)
                    ·
                      refine ⟨1225992572442817690769579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3269313526514180508718877 1225992572442817690769579)
                      ·
                        rfl

theorem cell23_2387612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_2387612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387612 prefixEnd_2387612 := by exact prefixLift 2387612
  have htrace : WordTrace (prefixWord ++ tailWord_2387612) baseStart_2387612 baseEnd_2387612 := by
    simpa [prefixWord, tailWord_2387612, baseEnd_2387612] using wordTrace_append hprefix tailTrace_2387612
  have hstable : (prefixWord ++ tailWord_2387612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387612).length < 2 ^ (prefixWord ++ tailWord_2387612).sum := by decide
  have hdescent : baseEnd_2387612 < baseStart_2387612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387647 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_2387647 : Nat := 118140960795 + 2387647 * 2 ^ 59
def prefixEnd_2387647 : Nat := 4983230072969 + 3 ^ 40 * 2387647 * 2
def baseEnd_2387647 : Nat := 1226010544265725053831917

theorem tailTrace_2387647 : CollatzResearch.WordTrace tailWord_2387647 prefixEnd_2387647 1226010544265725053831917 := by
  unfold tailWord_2387647
  simp only [CollatzResearch.WordTrace]
  refine ⟨87084640380970171487873195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58056426920646780991915463 87084640380970171487873195)
  ·
    refine ⟨130626960571455257231809793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87084640380970171487873195 130626960571455257231809793)
    ·
      refine ⟨97970220428591442923857345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130626960571455257231809793 97970220428591442923857345)
      ·
        refine ⟨73477665321443582192893009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97970220428591442923857345 73477665321443582192893009)
        ·
          refine ⟨55108248991082686644669757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73477665321443582192893009 55108248991082686644669757)
          ·
            refine ⟨20665593371656007491751159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55108248991082686644669757 20665593371656007491751159)
            ·
              refine ⟨30998390057484011237626739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20665593371656007491751159 30998390057484011237626739)
              ·
                refine ⟨46497585086226016856440109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30998390057484011237626739 46497585086226016856440109)
                ·
                  refine ⟨17436594407334756321165041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46497585086226016856440109 17436594407334756321165041)
                  ·
                    refine ⟨13077445805501067240873781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17436594407334756321165041 13077445805501067240873781)
                    ·
                      refine ⟨1226010544265725053831917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13077445805501067240873781 1226010544265725053831917)
                      ·
                        rfl

theorem cell23_2387647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_2387647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387647 prefixEnd_2387647 := by exact prefixLift 2387647
  have htrace : WordTrace (prefixWord ++ tailWord_2387647) baseStart_2387647 baseEnd_2387647 := by
    simpa [prefixWord, tailWord_2387647, baseEnd_2387647] using wordTrace_append hprefix tailTrace_2387647
  have hstable : (prefixWord ++ tailWord_2387647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387647).length < 2 ^ (prefixWord ++ tailWord_2387647).sum := by decide
  have hdescent : baseEnd_2387647 < baseStart_2387647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387727 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 2, 9]
def baseStart_2387727 : Nat := 118140960795 + 2387727 * 2 ^ 59
def prefixEnd_2387727 : Nat := 4983230072969 + 3 ^ 40 * 2387727 * 2
def baseEnd_2387727 : Nat := 408683874239361580277183

theorem tailTrace_2387727 : CollatzResearch.WordTrace tailWord_2387727 prefixEnd_2387727 408683874239361580277183 := by
  unfold tailWord_2387727
  simp only [CollatzResearch.WordTrace]
  refine ⟨87087558220680345150785435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58058372147120230100523623 87087558220680345150785435)
  ·
    refine ⟨130631337331020517726178153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87087558220680345150785435 130631337331020517726178153)
    ·
      refine ⟨97973502998265388294633615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130631337331020517726178153 97973502998265388294633615)
      ·
        refine ⟨146960254497398082441950423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97973502998265388294633615 146960254497398082441950423)
        ·
          refine ⟨220440381746097123662925635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146960254497398082441950423 220440381746097123662925635)
          ·
            refine ⟨330660572619145685494388453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220440381746097123662925635 330660572619145685494388453)
            ·
              refine ⟨61998857366089816030197835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 330660572619145685494388453 61998857366089816030197835)
              ·
                refine ⟨92998286049134724045296753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61998857366089816030197835 92998286049134724045296753)
                ·
                  refine ⟨69748714536851043033972565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92998286049134724045296753 69748714536851043033972565)
                  ·
                    refine ⟨408683874239361580277183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 69748714536851043033972565 408683874239361580277183)
                    ·
                      rfl

theorem cell23_2387727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_2387727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387727 prefixEnd_2387727 := by exact prefixLift 2387727
  have htrace : WordTrace (prefixWord ++ tailWord_2387727) baseStart_2387727 baseEnd_2387727 := by
    simpa [prefixWord, tailWord_2387727, baseEnd_2387727] using wordTrace_append hprefix tailTrace_2387727
  have hstable : (prefixWord ++ tailWord_2387727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387727).length < 2 ^ (prefixWord ++ tailWord_2387727).sum := by decide
  have hdescent : baseEnd_2387727 < baseStart_2387727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387761 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 1, 5]
def baseStart_2387761 : Nat := 118140960795 + 2387761 * 2 ^ 59
def prefixEnd_2387761 : Nat := 4983230072969 + 3 ^ 40 * 2387761 * 2
def baseEnd_2387761 : Nat := 408689693686779202602131

theorem tailTrace_2387761 : CollatzResearch.WordTrace tailWord_2387761 prefixEnd_2387761 408689693686779202602131 := by
  unfold tailWord_2387761
  simp only [CollatzResearch.WordTrace]
  refine ⟨87088798302557168957523137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58059198868371445971682091 87088798302557168957523137)
  ·
    refine ⟨65316598726917876718142353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87088798302557168957523137 65316598726917876718142353)
    ·
      refine ⟨48987449045188407538606765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65316598726917876718142353 48987449045188407538606765)
      ·
        refine ⟨18370293391945652826977537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48987449045188407538606765 18370293391945652826977537)
        ·
          refine ⟨13777720043959239620233153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18370293391945652826977537 13777720043959239620233153)
          ·
            refine ⟨10333290032969429715174865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13777720043959239620233153 10333290032969429715174865)
            ·
              refine ⟨7749967524727072286381149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10333290032969429715174865 7749967524727072286381149)
              ·
                refine ⟨2906237821772652107392931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7749967524727072286381149 2906237821772652107392931)
                ·
                  refine ⟨4359356732658978161089397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906237821772652107392931 4359356732658978161089397)
                  ·
                    refine ⟨408689693686779202602131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4359356732658978161089397 408689693686779202602131)
                    ·
                      rfl

theorem cell23_2387761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_2387761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387761 prefixEnd_2387761 := by exact prefixLift 2387761
  have htrace : WordTrace (prefixWord ++ tailWord_2387761) baseStart_2387761 baseEnd_2387761 := by
    simpa [prefixWord, tailWord_2387761, baseEnd_2387761] using wordTrace_append hprefix tailTrace_2387761
  have hstable : (prefixWord ++ tailWord_2387761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387761).length < 2 ^ (prefixWord ++ tailWord_2387761).sum := by decide
  have hdescent : baseEnd_2387761 < baseStart_2387761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387768 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 2, 3, 2]
def baseStart_2387768 : Nat := 118140960795 + 2387768 * 2 ^ 59
def prefixEnd_2387768 : Nat := 4983230072969 + 3 ^ 40 * 2387768 * 2
def baseEnd_2387768 : Nat := 1226072675424919080418861

theorem tailTrace_2387768 : CollatzResearch.WordTrace tailWord_2387768 prefixEnd_2387768 1226072675424919080418861 := by
  unfold tailWord_2387768
  simp only [CollatzResearch.WordTrace]
  refine ⟨43544526806765904576513979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58059369075687872768685305 43544526806765904576513979)
  ·
    refine ⟨65316790210148856864770969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43544526806765904576513979 65316790210148856864770969)
    ·
      refine ⟨48987592657611642648578227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65316790210148856864770969 48987592657611642648578227)
      ·
        refine ⟨73481388986417463972867341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48987592657611642648578227 73481388986417463972867341)
        ·
          refine ⟨27555520869906548989825253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73481388986417463972867341 27555520869906548989825253)
          ·
            refine ⟨5166660163107477935592235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27555520869906548989825253 5166660163107477935592235)
            ·
              refine ⟨7749990244661216903388353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166660163107477935592235 7749990244661216903388353)
              ·
                refine ⟨5812492683495912677541265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7749990244661216903388353 5812492683495912677541265)
                ·
                  refine ⟨4359369512621934508155949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5812492683495912677541265 4359369512621934508155949)
                  ·
                    refine ⟨1634763567233225440558481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4359369512621934508155949 1634763567233225440558481)
                    ·
                      refine ⟨1226072675424919080418861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634763567233225440558481 1226072675424919080418861)
                      ·
                        rfl

theorem cell23_2387768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_2387768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387768 prefixEnd_2387768 := by exact prefixLift 2387768
  have htrace : WordTrace (prefixWord ++ tailWord_2387768) baseStart_2387768 baseEnd_2387768 := by
    simpa [prefixWord, tailWord_2387768, baseEnd_2387768] using wordTrace_append hprefix tailTrace_2387768
  have hstable : (prefixWord ++ tailWord_2387768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387768).length < 2 ^ (prefixWord ++ tailWord_2387768).sum := by decide
  have hdescent : baseEnd_2387768 < baseStart_2387768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387775 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 3]
def baseStart_2387775 : Nat := 118140960795 + 2387775 * 2 ^ 59
def prefixEnd_2387775 : Nat := 4983230072969 + 3 ^ 40 * 2387775 * 2
def baseEnd_2387775 : Nat := 1226076269789500553031329

theorem tailTrace_2387775 : CollatzResearch.WordTrace tailWord_2387775 prefixEnd_2387775 1226076269789500553031329 := by
  unfold tailWord_2387775
  simp only [CollatzResearch.WordTrace]
  refine ⟨87089308924506449348532779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58059539283004299565688519 87089308924506449348532779)
  ·
    refine ⟨130633963386759674022799169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87089308924506449348532779 130633963386759674022799169)
    ·
      refine ⟨97975472540069755517099377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130633963386759674022799169 97975472540069755517099377)
      ·
        refine ⟨73481604405052316637824533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97975472540069755517099377 73481604405052316637824533)
        ·
          refine ⟨3444450206486827342398025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73481604405052316637824533 3444450206486827342398025)
          ·
            refine ⟨2583337654865120506798519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3444450206486827342398025 2583337654865120506798519)
            ·
              refine ⟨3875006482297680760197779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583337654865120506798519 3875006482297680760197779)
              ·
                refine ⟨5812509723446521140296669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875006482297680760197779 5812509723446521140296669)
                ·
                  refine ⟨2179691146292445427611251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5812509723446521140296669 2179691146292445427611251)
                  ·
                    refine ⟨3269536719438668141416877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2179691146292445427611251 3269536719438668141416877)
                    ·
                      refine ⟨1226076269789500553031329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3269536719438668141416877 1226076269789500553031329)
                      ·
                        rfl

theorem cell23_2387775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_2387775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387775 prefixEnd_2387775 := by exact prefixLift 2387775
  have htrace : WordTrace (prefixWord ++ tailWord_2387775) baseStart_2387775 baseEnd_2387775 := by
    simpa [prefixWord, tailWord_2387775, baseEnd_2387775] using wordTrace_append hprefix tailTrace_2387775
  have hstable : (prefixWord ++ tailWord_2387775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387775).length < 2 ^ (prefixWord ++ tailWord_2387775).sum := by decide
  have hdescent : baseEnd_2387775 < baseStart_2387775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387782 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2387782 : Nat := 118140960795 + 2387782 * 2 ^ 59
def prefixEnd_2387782 : Nat := 4983230072969 + 3 ^ 40 * 2387782 * 2
def baseEnd_2387782 : Nat := 136231096017120225071533

theorem tailTrace_2387782 : CollatzResearch.WordTrace tailWord_2387782 prefixEnd_2387782 136231096017120225071533 := by
  unfold tailWord_2387782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2721548882358784048251175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58059709490320726362691733 2721548882358784048251175)
  ·
    refine ⟨4082323323538176072376763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2721548882358784048251175 4082323323538176072376763)
    ·
      refine ⟨6123484985307264108565145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4082323323538176072376763 6123484985307264108565145)
      ·
        refine ⟨4592613738980448081423859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6123484985307264108565145 4592613738980448081423859)
        ·
          refine ⟨6888920608470672122135789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4592613738980448081423859 6888920608470672122135789)
          ·
            refine ⟨2583345228176502045800921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6888920608470672122135789 2583345228176502045800921)
            ·
              refine ⟨1937508921132376534350691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2583345228176502045800921 1937508921132376534350691)
              ·
                refine ⟨2906263381698564801526037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937508921132376534350691 2906263381698564801526037)
                ·
                  refine ⟨136231096017120225071533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2906263381698564801526037 136231096017120225071533)
                  ·
                    rfl

theorem cell23_2387782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2387782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387782 prefixEnd_2387782 := by exact prefixLift 2387782
  have htrace : WordTrace (prefixWord ++ tailWord_2387782) baseStart_2387782 baseEnd_2387782 := by
    simpa [prefixWord, tailWord_2387782, baseEnd_2387782] using wordTrace_append hprefix tailTrace_2387782
  have hstable : (prefixWord ++ tailWord_2387782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387782).length < 2 ^ (prefixWord ++ tailWord_2387782).sum := by decide
  have hdescent : baseEnd_2387782 < baseStart_2387782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387801 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 3]
def baseStart_2387801 : Nat := 118140960795 + 2387801 * 2 ^ 59
def prefixEnd_2387801 : Nat := 4983230072969 + 3 ^ 40 * 2387801 * 2
def baseEnd_2387801 : Nat := 1226089620286517451306209

theorem tailTrace_2387801 : CollatzResearch.WordTrace tailWord_2387801 prefixEnd_2387801 1226089620286517451306209 := by
  unfold tailWord_2387801
  simp only [CollatzResearch.WordTrace]
  refine ⟨87090257222412255788979257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58060171481608170525986171 87090257222412255788979257)
  ·
    refine ⟨65317692916809191841734443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87090257222412255788979257 65317692916809191841734443)
    ·
      refine ⟨97976539375213787762601665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65317692916809191841734443 97976539375213787762601665)
      ·
        refine ⟨73482404531410340821951249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97976539375213787762601665 73482404531410340821951249)
        ·
          refine ⟨55111803398557755616463437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73482404531410340821951249 55111803398557755616463437)
          ·
            refine ⟨20666926274459158356173789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55111803398557755616463437 20666926274459158356173789)
            ·
              refine ⟨7750097352922184383565171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20666926274459158356173789 7750097352922184383565171)
              ·
                refine ⟨11625146029383276575347757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7750097352922184383565171 11625146029383276575347757)
                ·
                  refine ⟨4359429761018728715755409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11625146029383276575347757 4359429761018728715755409)
                  ·
                    refine ⟨3269572320764046536816557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4359429761018728715755409 3269572320764046536816557)
                    ·
                      refine ⟨1226089620286517451306209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3269572320764046536816557 1226089620286517451306209)
                      ·
                        rfl

theorem cell23_2387801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_2387801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387801 prefixEnd_2387801 := by exact prefixLift 2387801
  have htrace : WordTrace (prefixWord ++ tailWord_2387801) baseStart_2387801 baseEnd_2387801 := by
    simpa [prefixWord, tailWord_2387801, baseEnd_2387801] using wordTrace_append hprefix tailTrace_2387801
  have hstable : (prefixWord ++ tailWord_2387801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387801).length < 2 ^ (prefixWord ++ tailWord_2387801).sum := by decide
  have hdescent : baseEnd_2387801 < baseStart_2387801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387834 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_2387834 : Nat := 118140960795 + 2387834 * 2 ^ 59
def prefixEnd_2387834 : Nat := 4983230072969 + 3 ^ 40 * 2387834 * 2
def baseEnd_2387834 : Nat := 408702188382705274064519

theorem tailTrace_2387834 : CollatzResearch.WordTrace tailWord_2387834 prefixEnd_2387834 408702188382705274064519 := by
  unfold tailWord_2387834
  simp only [CollatzResearch.WordTrace]
  refine ⟨21772865207823175606232639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58060973887528468283287037 21772865207823175606232639)
  ·
    refine ⟨32659297811734763409348959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21772865207823175606232639 32659297811734763409348959)
    ·
      refine ⟨48988946717602145114023439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32659297811734763409348959 48988946717602145114023439)
      ·
        refine ⟨73483420076403217671035159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48988946717602145114023439 73483420076403217671035159)
        ·
          refine ⟨110225130114604826506552739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73483420076403217671035159 110225130114604826506552739)
          ·
            refine ⟨165337695171907239759829109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110225130114604826506552739 165337695171907239759829109)
            ·
              refine ⟨15500408922366303727483979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165337695171907239759829109 15500408922366303727483979)
              ·
                refine ⟨23250613383549455591225969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15500408922366303727483979 23250613383549455591225969)
                ·
                  refine ⟨17437960037662091693419477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23250613383549455591225969 17437960037662091693419477)
                  ·
                    refine ⟨408702188382705274064519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17437960037662091693419477 408702188382705274064519)
                    ·
                      rfl

theorem cell23_2387834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_2387834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387834 prefixEnd_2387834 := by exact prefixLift 2387834
  have htrace : WordTrace (prefixWord ++ tailWord_2387834) baseStart_2387834 baseEnd_2387834 := by
    simpa [prefixWord, tailWord_2387834, baseEnd_2387834] using wordTrace_append hprefix tailTrace_2387834
  have hstable : (prefixWord ++ tailWord_2387834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387834).length < 2 ^ (prefixWord ++ tailWord_2387834).sum := by decide
  have hdescent : baseEnd_2387834 < baseStart_2387834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387838 : List Nat := [4, 2, 3, 1, 1, 1, 3, 8]
def baseStart_2387838 : Nat := 118140960795 + 2387838 * 2 ^ 59
def prefixEnd_2387838 : Nat := 4983230072969 + 3 ^ 40 * 2387838 * 2
def baseEnd_2387838 : Nat := 45411430335953103946057

theorem tailTrace_2387838 : CollatzResearch.WordTrace tailWord_2387838 prefixEnd_2387838 45411430335953103946057 := by
  unfold tailWord_2387838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10886450840409776388509521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58061071148852140738717445 10886450840409776388509521)
  ·
    refine ⟨8164838130307332291382141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10886450840409776388509521 8164838130307332291382141)
    ·
      refine ⟨3061814298865249609268303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8164838130307332291382141 3061814298865249609268303)
      ·
        refine ⟨4592721448297874413902455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3061814298865249609268303 4592721448297874413902455)
        ·
          refine ⟨6889082172446811620853683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4592721448297874413902455 6889082172446811620853683)
          ·
            refine ⟨10333623258670217431280525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6889082172446811620853683 10333623258670217431280525)
            ·
              refine ⟨3875108722001331536730197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10333623258670217431280525 3875108722001331536730197)
              ·
                refine ⟨45411430335953103946057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3875108722001331536730197 45411430335953103946057)
                ·
                  rfl

theorem cell23_2387838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_2387838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387838 prefixEnd_2387838 := by exact prefixLift 2387838
  have htrace : WordTrace (prefixWord ++ tailWord_2387838) baseStart_2387838 baseEnd_2387838 := by
    simpa [prefixWord, tailWord_2387838, baseEnd_2387838] using wordTrace_append hprefix tailTrace_2387838
  have hstable : (prefixWord ++ tailWord_2387838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387838).length < 2 ^ (prefixWord ++ tailWord_2387838).sum := by decide
  have hdescent : baseEnd_2387838 < baseStart_2387838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387884 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_2387884 : Nat := 118140960795 + 2387884 * 2 ^ 59
def prefixEnd_2387884 : Nat := 4983230072969 + 3 ^ 40 * 2387884 * 2
def baseEnd_2387884 : Nat := 1226132239180840626568327

theorem tailTrace_2387884 : CollatzResearch.WordTrace tailWord_2387884 prefixEnd_2387884 1226132239180840626568327 := by
  unfold tailWord_2387884
  simp only [CollatzResearch.WordTrace]
  refine ⟨43546642240555780482125353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58062189654074373976167137 43546642240555780482125353)
  ·
    refine ⟨32659981680416835361594015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43546642240555780482125353 32659981680416835361594015)
    ·
      refine ⟨48989972520625253042391023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32659981680416835361594015 48989972520625253042391023)
      ·
        refine ⟨73484958780937879563586535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48989972520625253042391023 73484958780937879563586535)
        ·
          refine ⟨110227438171406819345379803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73484958780937879563586535 110227438171406819345379803)
          ·
            refine ⟨165341157257110229018069705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110227438171406819345379803 165341157257110229018069705)
            ·
              refine ⟨124005867942832671763552279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165341157257110229018069705 124005867942832671763552279)
              ·
                refine ⟨186008801914249007645328419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124005867942832671763552279 186008801914249007645328419)
                ·
                  refine ⟨279013202871373511467992629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186008801914249007645328419 279013202871373511467992629)
                  ·
                    refine ⟨26157487769191266700124309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 279013202871373511467992629 26157487769191266700124309)
                    ·
                      refine ⟨1226132239180840626568327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26157487769191266700124309 1226132239180840626568327)
                      ·
                        rfl

theorem cell23_2387884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_2387884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387884 prefixEnd_2387884 := by exact prefixLift 2387884
  have htrace : WordTrace (prefixWord ++ tailWord_2387884) baseStart_2387884 baseEnd_2387884 := by
    simpa [prefixWord, tailWord_2387884, baseEnd_2387884] using wordTrace_append hprefix tailTrace_2387884
  have hstable : (prefixWord ++ tailWord_2387884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387884).length < 2 ^ (prefixWord ++ tailWord_2387884).sum := by decide
  have hdescent : baseEnd_2387884 < baseStart_2387884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387921 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_2387921 : Nat := 118140960795 + 2387921 * 2 ^ 59
def prefixEnd_2387921 : Nat := 4983230072969 + 3 ^ 40 * 2387921 * 2
def baseEnd_2387921 : Nat := 1226151237965056981805657

theorem tailTrace_2387921 : CollatzResearch.WordTrace tailWord_2387921 prefixEnd_2387921 1226151237965056981805657 := by
  unfold tailWord_2387921
  simp only [CollatzResearch.WordTrace]
  refine ⟨87094633981977516283347617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58063089321318344188898411 87094633981977516283347617)
  ·
    refine ⟨65320975486483137212510713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87094633981977516283347617 65320975486483137212510713)
    ·
      refine ⟨48990731614862352909383035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65320975486483137212510713 48990731614862352909383035)
      ·
        refine ⟨73486097422293529364074553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48990731614862352909383035 73486097422293529364074553)
        ·
          refine ⟨55114573066720147023055915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73486097422293529364074553 55114573066720147023055915)
          ·
            refine ⟨82671859600080220534583873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55114573066720147023055915 82671859600080220534583873)
            ·
              refine ⟨62003894700060165400937905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82671859600080220534583873 62003894700060165400937905)
              ·
                refine ⟨46502921025045124050703429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62003894700060165400937905 46502921025045124050703429)
                ·
                  refine ⟨8719297692195960759506893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46502921025045124050703429 8719297692195960759506893)
                  ·
                    refine ⟨3269736634573485284815085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8719297692195960759506893 3269736634573485284815085)
                    ·
                      refine ⟨1226151237965056981805657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3269736634573485284815085 1226151237965056981805657)
                      ·
                        rfl

theorem cell23_2387921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_2387921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387921 prefixEnd_2387921 := by exact prefixLift 2387921
  have htrace : WordTrace (prefixWord ++ tailWord_2387921) baseStart_2387921 baseEnd_2387921 := by
    simpa [prefixWord, tailWord_2387921, baseEnd_2387921] using wordTrace_append hprefix tailTrace_2387921
  have hstable : (prefixWord ++ tailWord_2387921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387921).length < 2 ^ (prefixWord ++ tailWord_2387921).sum := by decide
  have hdescent : baseEnd_2387921 < baseStart_2387921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387951 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_2387951 : Nat := 118140960795 + 2387951 * 2 ^ 59
def prefixEnd_2387951 : Nat := 4983230072969 + 3 ^ 40 * 2387951 * 2
def baseEnd_2387951 : Nat := 1226166642384691864430519

theorem tailTrace_2387951 : CollatzResearch.WordTrace tailWord_2387951 prefixEnd_2387951 1226166642384691864430519 := by
  unfold tailWord_2387951
  simp only [CollatzResearch.WordTrace]
  refine ⟨87095728171868831406939707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58063818781245887604626471 87095728171868831406939707)
  ·
    refine ⟨130643592257803247110409561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87095728171868831406939707 130643592257803247110409561)
    ·
      refine ⟨97982694193352435332807171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130643592257803247110409561 97982694193352435332807171)
      ·
        refine ⟨146974041290028652999210757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97982694193352435332807171 146974041290028652999210757)
        ·
          refine ⟨27557632741880372437352017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146974041290028652999210757 27557632741880372437352017)
          ·
            refine ⟨20668224556410279328014013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27557632741880372437352017 20668224556410279328014013)
            ·
              refine ⟨7750584208653854748005255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20668224556410279328014013 7750584208653854748005255)
              ·
                refine ⟨11625876312980782122007883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7750584208653854748005255 11625876312980782122007883)
                ·
                  refine ⟨17438814469471173183011825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11625876312980782122007883 17438814469471173183011825)
                  ·
                    refine ⟨13079110852103379887258869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17438814469471173183011825 13079110852103379887258869)
                    ·
                      refine ⟨1226166642384691864430519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13079110852103379887258869 1226166642384691864430519)
                      ·
                        rfl

theorem cell23_2387951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_2387951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2387951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2387951 prefixEnd_2387951 := by exact prefixLift 2387951
  have htrace : WordTrace (prefixWord ++ tailWord_2387951) baseStart_2387951 baseEnd_2387951 := by
    simpa [prefixWord, tailWord_2387951, baseEnd_2387951] using wordTrace_append hprefix tailTrace_2387951
  have hstable : (prefixWord ++ tailWord_2387951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387951).length < 2 ^ (prefixWord ++ tailWord_2387951).sum := by decide
  have hdescent : baseEnd_2387951 < baseStart_2387951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388018 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 6]
def baseStart_2388018 : Nat := 118140960795 + 2388018 * 2 ^ 59
def prefixEnd_2388018 : Nat := 4983230072969 + 3 ^ 40 * 2388018 * 2
def baseEnd_2388018 : Nat := 136244560620949233588079

theorem tailTrace_2388018 : CollatzResearch.WordTrace tailWord_2388018 prefixEnd_2388018 136244560620949233588079 := by
  unfold tailWord_2388018
  simp only [CollatzResearch.WordTrace]
  refine ⟨21774542965656525462407177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58065447908417401233085805 21774542965656525462407177)
  ·
    refine ⟨16330907224242394096805383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21774542965656525462407177 16330907224242394096805383)
    ·
      refine ⟨24496360836363591145208075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16330907224242394096805383 24496360836363591145208075)
      ·
        refine ⟨36744541254545386717812113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24496360836363591145208075 36744541254545386717812113)
        ·
          refine ⟨27558405940909040038359085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36744541254545386717812113 27558405940909040038359085)
          ·
            refine ⟨10334402227840890014384657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27558405940909040038359085 10334402227840890014384657)
            ·
              refine ⟨7750801670880667510788493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10334402227840890014384657 7750801670880667510788493)
              ·
                refine ⟨2906550626580250316545685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7750801670880667510788493 2906550626580250316545685)
                ·
                  refine ⟨136244560620949233588079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2906550626580250316545685 136244560620949233588079)
                  ·
                    rfl

theorem cell23_2388018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_2388018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388018 prefixEnd_2388018 := by exact prefixLift 2388018
  have htrace : WordTrace (prefixWord ++ tailWord_2388018) baseStart_2388018 baseEnd_2388018 := by
    simpa [prefixWord, tailWord_2388018, baseEnd_2388018] using wordTrace_append hprefix tailTrace_2388018
  have hstable : (prefixWord ++ tailWord_2388018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388018).length < 2 ^ (prefixWord ++ tailWord_2388018).sum := by decide
  have hdescent : baseEnd_2388018 < baseStart_2388018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388051 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 4]
def baseStart_2388051 : Nat := 118140960795 + 2388051 * 2 ^ 59
def prefixEnd_2388051 : Nat := 4983230072969 + 3 ^ 40 * 2388051 * 2
def baseEnd_2388051 : Nat := 1226217990450141473180059

theorem tailTrace_2388051 : CollatzResearch.WordTrace tailWord_2388051 prefixEnd_2388051 1226217990450141473180059 := by
  unfold tailWord_2388051
  simp only [CollatzResearch.WordTrace]
  refine ⟨87099375471506548485580007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58066250314337698990386671 87099375471506548485580007)
  ·
    refine ⟨130649063207259822728370011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87099375471506548485580007 130649063207259822728370011)
    ·
      refine ⟨195973594810889734092555017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130649063207259822728370011 195973594810889734092555017)
      ·
        refine ⟨146980196108167300569416263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195973594810889734092555017 146980196108167300569416263)
        ·
          refine ⟨220470294162250950854124395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146980196108167300569416263 220470294162250950854124395)
          ·
            refine ⟨330705441243376426281186593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220470294162250950854124395 330705441243376426281186593)
            ·
              refine ⟨248029080932532319710889945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330705441243376426281186593 248029080932532319710889945)
              ·
                refine ⟨186021810699399239783167459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248029080932532319710889945 186021810699399239783167459)
                ·
                  refine ⟨279032716049098859674751189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186021810699399239783167459 279032716049098859674751189)
                  ·
                    refine ⟨6539829282400754523626981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 279032716049098859674751189 6539829282400754523626981)
                    ·
                      refine ⟨1226217990450141473180059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6539829282400754523626981 1226217990450141473180059)
                      ·
                        rfl

theorem cell23_2388051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_2388051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388051 prefixEnd_2388051 := by exact prefixLift 2388051
  have htrace : WordTrace (prefixWord ++ tailWord_2388051) baseStart_2388051 baseEnd_2388051 := by
    simpa [prefixWord, tailWord_2388051, baseEnd_2388051] using wordTrace_append hprefix tailTrace_2388051
  have hstable : (prefixWord ++ tailWord_2388051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388051).length < 2 ^ (prefixWord ++ tailWord_2388051).sum := by decide
  have hdescent : baseEnd_2388051 < baseStart_2388051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388055 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 2, 3, 2]
def baseStart_2388055 : Nat := 118140960795 + 2388055 * 2 ^ 59
def prefixEnd_2388055 : Nat := 4983230072969 + 3 ^ 40 * 2388055 * 2
def baseEnd_2388055 : Nat := 1226220044372759457530041

theorem tailTrace_2388055 : CollatzResearch.WordTrace tailWord_2388055 prefixEnd_2388055 1226220044372759457530041 := by
  unfold tailWord_2388055
  simp only [CollatzResearch.WordTrace]
  refine ⟨87099521363492057168725619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58066347575661371445817079 87099521363492057168725619)
  ·
    refine ⟨130649282045238085753088429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87099521363492057168725619 130649282045238085753088429)
    ·
      refine ⟨48993480766964282157408161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130649282045238085753088429 48993480766964282157408161)
      ·
        refine ⟨36745110575223211618056121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48993480766964282157408161 36745110575223211618056121)
        ·
          refine ⟨27558832931417408713542091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36745110575223211618056121 27558832931417408713542091)
          ·
            refine ⟨41338249397126113070313137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27558832931417408713542091 41338249397126113070313137)
            ·
              refine ⟨31003687047844584802734853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41338249397126113070313137 31003687047844584802734853)
              ·
                refine ⟨5813191321470859650512785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31003687047844584802734853 5813191321470859650512785)
                ·
                  refine ⟨4359893491103144737884589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5813191321470859650512785 4359893491103144737884589)
                  ·
                    refine ⟨1634960059163679276706721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4359893491103144737884589 1634960059163679276706721)
                    ·
                      refine ⟨1226220044372759457530041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1634960059163679276706721 1226220044372759457530041)
                      ·
                        rfl

theorem cell23_2388055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_2388055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388055 prefixEnd_2388055 := by exact prefixLift 2388055
  have htrace : WordTrace (prefixWord ++ tailWord_2388055) baseStart_2388055 baseEnd_2388055 := by
    simpa [prefixWord, tailWord_2388055, baseEnd_2388055] using wordTrace_append hprefix tailTrace_2388055
  have hstable : (prefixWord ++ tailWord_2388055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388055).length < 2 ^ (prefixWord ++ tailWord_2388055).sum := by decide
  have hdescent : baseEnd_2388055 < baseStart_2388055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388068 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_2388068 : Nat := 118140960795 + 2388068 * 2 ^ 59
def prefixEnd_2388068 : Nat := 4983230072969 + 3 ^ 40 * 2388068 * 2
def baseEnd_2388068 : Nat := 1226226719621267906667481

theorem tailTrace_2388068 : CollatzResearch.WordTrace tailWord_2388068 prefixEnd_2388068 1226226719621267906667481 := by
  unfold tailWord_2388068
  simp only [CollatzResearch.WordTrace]
  refine ⟨43549997756222480194474429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58066663674963306925965905 43549997756222480194474429)
  ·
    refine ⟨16331249158583430072927911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43549997756222480194474429 16331249158583430072927911)
    ·
      refine ⟨24496873737875145109391867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16331249158583430072927911 24496873737875145109391867)
      ·
        refine ⟨36745310606812717664087801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24496873737875145109391867 36745310606812717664087801)
        ·
          refine ⟨27558982955109538248065851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36745310606812717664087801 27558982955109538248065851)
          ·
            refine ⟨41338474432664307372098777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27558982955109538248065851 41338474432664307372098777)
            ·
              refine ⟨31003855824498230529074083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41338474432664307372098777 31003855824498230529074083)
              ·
                refine ⟨46505783736747345793611125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31003855824498230529074083 46505783736747345793611125)
                ·
                  refine ⟨4359917225320063668151043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46505783736747345793611125 4359917225320063668151043)
                  ·
                    refine ⟨6539875837980095502226565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4359917225320063668151043 6539875837980095502226565)
                    ·
                      refine ⟨1226226719621267906667481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6539875837980095502226565 1226226719621267906667481)
                      ·
                        rfl

theorem cell23_2388068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_2388068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388068 prefixEnd_2388068 := by exact prefixLift 2388068
  have htrace : WordTrace (prefixWord ++ tailWord_2388068) baseStart_2388068 baseEnd_2388068 := by
    simpa [prefixWord, tailWord_2388068, baseEnd_2388068] using wordTrace_append hprefix tailTrace_2388068
  have hstable : (prefixWord ++ tailWord_2388068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388068).length < 2 ^ (prefixWord ++ tailWord_2388068).sum := by decide
  have hdescent : baseEnd_2388068 < baseStart_2388068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388105 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 3]
def baseStart_2388105 : Nat := 118140960795 + 2388105 * 2 ^ 59
def prefixEnd_2388105 : Nat := 4983230072969 + 3 ^ 40 * 2388105 * 2
def baseEnd_2388105 : Nat := 1226245718405484261904811

theorem tailTrace_2388105 : CollatzResearch.WordTrace tailWord_2388105 prefixEnd_2388105 1226245718405484261904811 := by
  unfold tailWord_2388105
  simp only [CollatzResearch.WordTrace]
  refine ⟨87101345013310915708045769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58067563342207277138697179 87101345013310915708045769)
  ·
    refine ⟨65326008759983186781034327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87101345013310915708045769 65326008759983186781034327)
    ·
      refine ⟨97989013139974780171551491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65326008759983186781034327 97989013139974780171551491)
      ·
        refine ⟨146983519709962170257327237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97989013139974780171551491 146983519709962170257327237)
        ·
          refine ⟨27559409945617906923248857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146983519709962170257327237 27559409945617906923248857)
          ·
            refine ⟨20669557459213430192436643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27559409945617906923248857 20669557459213430192436643)
            ·
              refine ⟨31004336188820145288654965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20669557459213430192436643 31004336188820145288654965)
              ·
                refine ⟨2906656517701888620811403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31004336188820145288654965 2906656517701888620811403)
                ·
                  refine ⟨4359984776552832931217105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906656517701888620811403 4359984776552832931217105)
                  ·
                    refine ⟨3269988582414624698412829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4359984776552832931217105 3269988582414624698412829)
                    ·
                      refine ⟨1226245718405484261904811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3269988582414624698412829 1226245718405484261904811)
                      ·
                        rfl

theorem cell23_2388105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 3].length) (baseStart_2388105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388105 prefixEnd_2388105 := by exact prefixLift 2388105
  have htrace : WordTrace (prefixWord ++ tailWord_2388105) baseStart_2388105 baseEnd_2388105 := by
    simpa [prefixWord, tailWord_2388105, baseEnd_2388105] using wordTrace_append hprefix tailTrace_2388105
  have hstable : (prefixWord ++ tailWord_2388105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388105).length < 2 ^ (prefixWord ++ tailWord_2388105).sum := by decide
  have hdescent : baseEnd_2388105 < baseStart_2388105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388129 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 2, 4]
def baseStart_2388129 : Nat := 118140960795 + 2388129 * 2 ^ 59
def prefixEnd_2388129 : Nat := 4983230072969 + 3 ^ 40 * 2388129 * 2
def baseEnd_2388129 : Nat := 408752680647064056001567

theorem tailTrace_2388129 : CollatzResearch.WordTrace tailWord_2388129 prefixEnd_2388129 408752680647064056001567 := by
  unfold tailWord_2388129
  simp only [CollatzResearch.WordTrace]
  refine ⟨87102220365223967806919441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58068146910149311871279627 87102220365223967806919441)
  ·
    refine ⟨65326665273917975855189581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87102220365223967806919441 65326665273917975855189581)
    ·
      refine ⟨24497499477719240945696093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65326665273917975855189581 24497499477719240945696093)
      ·
        refine ⟨9186562304144715354636035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24497499477719240945696093 9186562304144715354636035)
        ·
          refine ⟨13779843456217073031954053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9186562304144715354636035 13779843456217073031954053)
          ·
            refine ⟨2583720648040701193491385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13779843456217073031954053 2583720648040701193491385)
            ·
              refine ⟨1937790486030525895118539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2583720648040701193491385 1937790486030525895118539)
              ·
                refine ⟨2906685729045788842677809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937790486030525895118539 2906685729045788842677809)
                ·
                  refine ⟨2180014296784341632008357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2906685729045788842677809 2180014296784341632008357)
                  ·
                    refine ⟨408752680647064056001567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2180014296784341632008357 408752680647064056001567)
                    ·
                      rfl

theorem cell23_2388129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_2388129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388129 prefixEnd_2388129 := by exact prefixLift 2388129
  have htrace : WordTrace (prefixWord ++ tailWord_2388129) baseStart_2388129 baseEnd_2388129 := by
    simpa [prefixWord, tailWord_2388129, baseEnd_2388129] using wordTrace_append hprefix tailTrace_2388129
  have hstable : (prefixWord ++ tailWord_2388129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388129).length < 2 ^ (prefixWord ++ tailWord_2388129).sum := by decide
  have hdescent : baseEnd_2388129 < baseStart_2388129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388168 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 2, 6]
def baseStart_2388168 : Nat := 118140960795 + 2388168 * 2 ^ 59
def prefixEnd_2388168 : Nat := 4983230072969 + 3 ^ 40 * 2388168 * 2
def baseEnd_2388168 : Nat := 408759355895572505139007

theorem tailTrace_2388168 : CollatzResearch.WordTrace tailWord_2388168 prefixEnd_2388168 408759355895572505139007 := by
  unfold tailWord_2388168
  simp only [CollatzResearch.WordTrace]
  refine ⟨43551821406041338733794579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58069095208055118311726105 43551821406041338733794579)
  ·
    refine ⟨65327732109062008100691869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43551821406041338733794579 65327732109062008100691869)
    ·
      refine ⟨24497899540898253037759451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65327732109062008100691869 24497899540898253037759451)
      ·
        refine ⟨36746849311347379556639177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24497899540898253037759451 36746849311347379556639177)
        ·
          refine ⟨27560136983510534667479383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36746849311347379556639177 27560136983510534667479383)
          ·
            refine ⟨41340205475265802001219075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27560136983510534667479383 41340205475265802001219075)
            ·
              refine ⟨62010308212898703001828613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41340205475265802001219075 62010308212898703001828613)
              ·
                refine ⟨11626932789918506812842865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62010308212898703001828613 11626932789918506812842865)
                ·
                  refine ⟨8720199592438880109632149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11626932789918506812842865 8720199592438880109632149)
                  ·
                    refine ⟨408759355895572505139007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8720199592438880109632149 408759355895572505139007)
                    ·
                      rfl

theorem cell23_2388168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_2388168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388168 prefixEnd_2388168 := by exact prefixLift 2388168
  have htrace : WordTrace (prefixWord ++ tailWord_2388168) baseStart_2388168 baseEnd_2388168 := by
    simpa [prefixWord, tailWord_2388168, baseEnd_2388168] using wordTrace_append hprefix tailTrace_2388168
  have hstable : (prefixWord ++ tailWord_2388168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388168).length < 2 ^ (prefixWord ++ tailWord_2388168).sum := by decide
  have hdescent : baseEnd_2388168 < baseStart_2388168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388175 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 3, 4, 2]
def baseStart_2388175 : Nat := 118140960795 + 2388175 * 2 ^ 59
def prefixEnd_2388175 : Nat := 4983230072969 + 3 ^ 40 * 2388175 * 2
def baseEnd_2388175 : Nat := 1226281662051298988029489

theorem tailTrace_2388175 : CollatzResearch.WordTrace tailWord_2388175 prefixEnd_2388175 1226281662051298988029489 := by
  unfold tailWord_2388175
  simp only [CollatzResearch.WordTrace]
  refine ⟨87103898123057317663093979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58069265415371545108729319 87103898123057317663093979)
  ·
    refine ⟨130655847184585976494640969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87103898123057317663093979 130655847184585976494640969)
    ·
      refine ⟨97991885388439482370980727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130655847184585976494640969 97991885388439482370980727)
      ·
        refine ⟨146987828082659223556471091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97991885388439482370980727 146987828082659223556471091)
        ·
          refine ⟨220481742123988835334706637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146987828082659223556471091 220481742123988835334706637)
          ·
            refine ⟨82680653296495813250514989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220481742123988835334706637 82680653296495813250514989)
            ·
              refine ⟨31005244986185929968943121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82680653296495813250514989 31005244986185929968943121)
              ·
                refine ⟨23253933739639447476707341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31005244986185929968943121 23253933739639447476707341)
                ·
                  refine ⟨8720225152364792803765253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23253933739639447476707341 8720225152364792803765253)
                  ·
                    refine ⟨1635042216068398650705985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8720225152364792803765253 1635042216068398650705985)
                    ·
                      refine ⟨1226281662051298988029489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635042216068398650705985 1226281662051298988029489)
                      ·
                        rfl

theorem cell23_2388175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 4, 2].length) (baseStart_2388175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388175 prefixEnd_2388175 := by exact prefixLift 2388175
  have htrace : WordTrace (prefixWord ++ tailWord_2388175) baseStart_2388175 baseEnd_2388175 := by
    simpa [prefixWord, tailWord_2388175, baseEnd_2388175] using wordTrace_append hprefix tailTrace_2388175
  have hstable : (prefixWord ++ tailWord_2388175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388175).length < 2 ^ (prefixWord ++ tailWord_2388175).sum := by decide
  have hdescent : baseEnd_2388175 < baseStart_2388175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388192 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 1, 4, 2]
def baseStart_2388192 : Nat := 118140960795 + 2388192 * 2 ^ 59
def prefixEnd_2388192 : Nat := 4983230072969 + 3 ^ 40 * 2388192 * 2
def baseEnd_2388192 : Nat := 1226290391222425421516911

theorem tailTrace_2388192 : CollatzResearch.WordTrace tailWord_2388192 prefixEnd_2388192 1226290391222425421516911 := by
  unfold tailWord_2388192
  simp only [CollatzResearch.WordTrace]
  refine ⟨43552259081997864783231415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58069678775997153044308553 43552259081997864783231415)
  ·
    refine ⟨65328388622996797174847123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43552259081997864783231415 65328388622996797174847123)
    ·
      refine ⟨97992582934495195762270685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65328388622996797174847123 97992582934495195762270685)
      ·
        refine ⟨36747218600435698410851507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97992582934495195762270685 36747218600435698410851507)
        ·
          refine ⟨55120827900653547616277261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36747218600435698410851507 55120827900653547616277261)
          ·
            refine ⟨20670310462745080356103973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55120827900653547616277261 20670310462745080356103973)
            ·
              refine ⟨3875683211764702566769495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20670310462745080356103973 3875683211764702566769495)
              ·
                refine ⟨5813524817647053850154243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875683211764702566769495 5813524817647053850154243)
                ·
                  refine ⟨8720287226470580775231365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5813524817647053850154243 8720287226470580775231365)
                  ·
                    refine ⟨1635053854963233895355881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8720287226470580775231365 1635053854963233895355881)
                    ·
                      refine ⟨1226290391222425421516911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635053854963233895355881 1226290391222425421516911)
                      ·
                        rfl

theorem cell23_2388192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_2388192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388192 prefixEnd_2388192 := by exact prefixLift 2388192
  have htrace : WordTrace (prefixWord ++ tailWord_2388192) baseStart_2388192 baseEnd_2388192 := by
    simpa [prefixWord, tailWord_2388192, baseEnd_2388192] using wordTrace_append hprefix tailTrace_2388192
  have hstable : (prefixWord ++ tailWord_2388192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388192).length < 2 ^ (prefixWord ++ tailWord_2388192).sum := by decide
  have hdescent : baseEnd_2388192 < baseStart_2388192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388225 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_2388225 : Nat := 118140960795 + 2388225 * 2 ^ 59
def prefixEnd_2388225 : Nat := 4983230072969 + 3 ^ 40 * 2388225 * 2
def baseEnd_2388225 : Nat := 1226307336084023792404259

theorem tailTrace_2388225 : CollatzResearch.WordTrace tailWord_2388225 prefixEnd_2388225 1226307336084023792404259 := by
  unfold tailWord_2388225
  simp only [CollatzResearch.WordTrace]
  refine ⟨87105721772876176202414129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58070481181917450801609419 87105721772876176202414129)
  ·
    refine ⟨65329291329657132151810597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87105721772876176202414129 65329291329657132151810597)
    ·
      refine ⟨12249242124310712278464487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65329291329657132151810597 12249242124310712278464487)
      ·
        refine ⟨18373863186466068417696731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12249242124310712278464487 18373863186466068417696731)
        ·
          refine ⟨27560794779699102626545097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18373863186466068417696731 27560794779699102626545097)
          ·
            refine ⟨20670596084774326969908823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27560794779699102626545097 20670596084774326969908823)
            ·
              refine ⟨31005894127161490454863235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20670596084774326969908823 31005894127161490454863235)
              ·
                refine ⟨46508841190742235682294853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31005894127161490454863235 46508841190742235682294853)
                ·
                  refine ⟨8720407723264169190430285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46508841190742235682294853 8720407723264169190430285)
                  ·
                    refine ⟨3270152896224063446411357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8720407723264169190430285 3270152896224063446411357)
                    ·
                      refine ⟨1226307336084023792404259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3270152896224063446411357 1226307336084023792404259)
                      ·
                        rfl

theorem cell23_2388225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_2388225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388225 prefixEnd_2388225 := by exact prefixLift 2388225
  have htrace : WordTrace (prefixWord ++ tailWord_2388225) baseStart_2388225 baseEnd_2388225 := by
    simpa [prefixWord, tailWord_2388225, baseEnd_2388225] using wordTrace_append hprefix tailTrace_2388225
  have hstable : (prefixWord ++ tailWord_2388225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388225).length < 2 ^ (prefixWord ++ tailWord_2388225).sum := by decide
  have hdescent : baseEnd_2388225 < baseStart_2388225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388226 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_2388226 : Nat := 118140960795 + 2388226 * 2 ^ 59
def prefixEnd_2388226 : Nat := 4983230072969 + 3 ^ 40 * 2388226 * 2
def baseEnd_2388226 : Nat := 1226307849564678288491755

theorem tailTrace_2388226 : CollatzResearch.WordTrace tailWord_2388226 prefixEnd_2388226 1226307849564678288491755 := by
  unfold tailWord_2388226
  simp only [CollatzResearch.WordTrace]
  refine ⟨21776439561468138343300133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58070505497248368915467021 21776439561468138343300133)
  ·
    refine ⟨4083082417775275939368775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21776439561468138343300133 4083082417775275939368775)
    ·
      refine ⟨6124623626662913909053163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4083082417775275939368775 6124623626662913909053163)
      ·
        refine ⟨9186935439994370863579745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6124623626662913909053163 9186935439994370863579745)
        ·
          refine ⟨6890201579995778147684809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9186935439994370863579745 6890201579995778147684809)
          ·
            refine ⟨5167651184996833610763607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6890201579995778147684809 5167651184996833610763607)
            ·
              refine ⟨7751476777495250416145411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167651184996833610763607 7751476777495250416145411)
              ·
                refine ⟨11627215166242875624218117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7751476777495250416145411 11627215166242875624218117)
                ·
                  refine ⟨2180102843670539179540897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11627215166242875624218117 2180102843670539179540897)
                  ·
                    refine ⟨1635077132752904384655673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2180102843670539179540897 1635077132752904384655673)
                    ·
                      refine ⟨1226307849564678288491755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635077132752904384655673 1226307849564678288491755)
                      ·
                        rfl

theorem cell23_2388226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_2388226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388226 prefixEnd_2388226 := by exact prefixLift 2388226
  have htrace : WordTrace (prefixWord ++ tailWord_2388226) baseStart_2388226 baseEnd_2388226 := by
    simpa [prefixWord, tailWord_2388226, baseEnd_2388226] using wordTrace_append hprefix tailTrace_2388226
  have hstable : (prefixWord ++ tailWord_2388226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388226).length < 2 ^ (prefixWord ++ tailWord_2388226).sum := by decide
  have hdescent : baseEnd_2388226 < baseStart_2388226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388232 : List Nat := [2, 1, 3, 2, 3, 1, 2, 4, 5]
def baseStart_2388232 : Nat := 118140960795 + 2388232 * 2 ^ 59
def prefixEnd_2388232 : Nat := 4983230072969 + 3 ^ 40 * 2388232 * 2
def baseEnd_2388232 : Nat := 136256770049845029446303

theorem tailTrace_2388232 : CollatzResearch.WordTrace tailWord_2388232 prefixEnd_2388232 136256770049845029446303 := by
  unfold tailWord_2388232
  simp only [CollatzResearch.WordTrace]
  refine ⟨43552988541925408198959475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58070651389233877598612633 43552988541925408198959475)
  ·
    refine ⟨65329482812888112298439213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43552988541925408198959475 65329482812888112298439213)
    ·
      refine ⟨24498556054833042111914705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65329482812888112298439213 24498556054833042111914705)
      ·
        refine ⟨18373917041124781583936029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24498556054833042111914705 18373917041124781583936029)
        ·
          refine ⟨6890218890421793093976011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18373917041124781583936029 6890218890421793093976011)
          ·
            refine ⟨10335328335632689640964017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6890218890421793093976011 10335328335632689640964017)
            ·
              refine ⟨7751496251724517230723013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10335328335632689640964017 7751496251724517230723013)
              ·
                refine ⟨1453405547198346980760565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7751496251724517230723013 1453405547198346980760565)
                ·
                  refine ⟨136256770049845029446303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1453405547198346980760565 136256770049845029446303)
                  ·
                    rfl

theorem cell23_2388232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 5].length) (baseStart_2388232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388232 prefixEnd_2388232 := by exact prefixLift 2388232
  have htrace : WordTrace (prefixWord ++ tailWord_2388232) baseStart_2388232 baseEnd_2388232 := by
    simpa [prefixWord, tailWord_2388232, baseEnd_2388232] using wordTrace_append hprefix tailTrace_2388232
  have hstable : (prefixWord ++ tailWord_2388232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388232).length < 2 ^ (prefixWord ++ tailWord_2388232).sum := by decide
  have hdescent : baseEnd_2388232 < baseStart_2388232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388266 : List Nat := [3, 1, 4, 2, 2, 2, 1, 3, 5]
def baseStart_2388266 : Nat := 118140960795 + 2388266 * 2 ^ 59
def prefixEnd_2388266 : Nat := 4983230072969 + 3 ^ 40 * 2388266 * 2
def baseEnd_2388266 : Nat := 136258709865650903554619

theorem tailTrace_2388266 : CollatzResearch.WordTrace tailWord_2388266 prefixEnd_2388266 136258709865650903554619 := by
  unfold tailWord_2388266
  simp only [CollatzResearch.WordTrace]
  refine ⟨21776804291431910051164163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58071478110485093469771101 21776804291431910051164163)
  ·
    refine ⟨32665206437147865076746245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21776804291431910051164163 32665206437147865076746245)
    ·
      refine ⟨6124726206965224701889921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32665206437147865076746245 6124726206965224701889921)
      ·
        refine ⟨4593544655223918526417441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6124726206965224701889921 4593544655223918526417441)
        ·
          refine ⟨3445158491417938894813081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4593544655223918526417441 3445158491417938894813081)
          ·
            refine ⟨2583868868563454171109811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3445158491417938894813081 2583868868563454171109811)
            ·
              refine ⟨3875803302845181256664717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583868868563454171109811 3875803302845181256664717)
              ·
                refine ⟨1453426238566942971249269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3875803302845181256664717 1453426238566942971249269)
                ·
                  refine ⟨136258709865650903554619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1453426238566942971249269 136258709865650903554619)
                  ·
                    rfl

theorem cell23_2388266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_2388266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388266 prefixEnd_2388266 := by exact prefixLift 2388266
  have htrace : WordTrace (prefixWord ++ tailWord_2388266) baseStart_2388266 baseEnd_2388266 := by
    simpa [prefixWord, tailWord_2388266, baseEnd_2388266] using wordTrace_append hprefix tailTrace_2388266
  have hstable : (prefixWord ++ tailWord_2388266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388266).length < 2 ^ (prefixWord ++ tailWord_2388266).sum := by decide
  have hdescent : baseEnd_2388266 < baseStart_2388266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388282 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_2388282 : Nat := 118140960795 + 2388282 * 2 ^ 59
def prefixEnd_2388282 : Nat := 4983230072969 + 3 ^ 40 * 2388282 * 2
def baseEnd_2388282 : Nat := 1226336604481330069391497

theorem tailTrace_2388282 : CollatzResearch.WordTrace tailWord_2388282 prefixEnd_2388282 1226336604481330069391497 := by
  unfold tailWord_2388282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21776950183417418734309775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58071867155779783291492733 21776950183417418734309775)
  ·
    refine ⟨32665425275126128101464663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21776950183417418734309775 32665425275126128101464663)
    ·
      refine ⟨48998137912689192152196995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32665425275126128101464663 48998137912689192152196995)
      ·
        refine ⟨73497206869033788228295493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48998137912689192152196995 73497206869033788228295493)
        ·
          refine ⟨13780726287943835292805405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73497206869033788228295493 13780726287943835292805405)
          ·
            refine ⟨5167772357978938234802027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13780726287943835292805405 5167772357978938234802027)
            ·
              refine ⟨7751658536968407352203041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167772357978938234802027 7751658536968407352203041)
              ·
                refine ⟨5813743902726305514152281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7751658536968407352203041 5813743902726305514152281)
                ·
                  refine ⟨4360307927044729135614211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5813743902726305514152281 4360307927044729135614211)
                  ·
                    refine ⟨6540461890567093703421317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4360307927044729135614211 6540461890567093703421317)
                    ·
                      refine ⟨1226336604481330069391497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6540461890567093703421317 1226336604481330069391497)
                      ·
                        rfl

theorem cell23_2388282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_2388282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388282 prefixEnd_2388282 := by exact prefixLift 2388282
  have htrace : WordTrace (prefixWord ++ tailWord_2388282) baseStart_2388282 baseEnd_2388282 := by
    simpa [prefixWord, tailWord_2388282, baseEnd_2388282] using wordTrace_append hprefix tailTrace_2388282
  have hstable : (prefixWord ++ tailWord_2388282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388282).length < 2 ^ (prefixWord ++ tailWord_2388282).sum := by decide
  have hdescent : baseEnd_2388282 < baseStart_2388282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388316 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2388316 : Nat := 118140960795 + 2388316 * 2 ^ 59
def prefixEnd_2388316 : Nat := 4983230072969 + 3 ^ 40 * 2388316 * 2
def baseEnd_2388316 : Nat := 1226354062823582936366341

theorem tailTrace_2388316 : CollatzResearch.WordTrace tailWord_2388316 prefixEnd_2388316 1226354062823582936366341 := by
  unfold tailWord_2388316
  simp only [CollatzResearch.WordTrace]
  refine ⟨43554520407773249371988401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58072693877030999162651201 43554520407773249371988401)
  ·
    refine ⟨32665890305829937028991301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43554520407773249371988401 32665890305829937028991301)
    ·
      refine ⟨6124854432343113192935869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32665890305829937028991301 6124854432343113192935869)
      ·
        refine ⟨2296820412128667447350951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6124854432343113192935869 2296820412128667447350951)
        ·
          refine ⟨3445230618193001171026427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296820412128667447350951 3445230618193001171026427)
          ·
            refine ⟨5167845927289501756539641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445230618193001171026427 5167845927289501756539641)
            ·
              refine ⟨3875884445467126317404731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5167845927289501756539641 3875884445467126317404731)
              ·
                refine ⟨5813826668200689476107097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875884445467126317404731 5813826668200689476107097)
                ·
                  refine ⟨4360370001150517107080323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5813826668200689476107097 4360370001150517107080323)
                  ·
                    refine ⟨6540555001725775660620485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4360370001150517107080323 6540555001725775660620485)
                    ·
                      refine ⟨1226354062823582936366341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6540555001725775660620485 1226354062823582936366341)
                      ·
                        rfl

theorem cell23_2388316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2388316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388316 prefixEnd_2388316 := by exact prefixLift 2388316
  have htrace : WordTrace (prefixWord ++ tailWord_2388316) baseStart_2388316 baseEnd_2388316 := by
    simpa [prefixWord, tailWord_2388316, baseEnd_2388316] using wordTrace_append hprefix tailTrace_2388316
  have hstable : (prefixWord ++ tailWord_2388316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388316).length < 2 ^ (prefixWord ++ tailWord_2388316).sum := by decide
  have hdescent : baseEnd_2388316 < baseStart_2388316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388366 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2388366 : Nat := 118140960795 + 2388366 * 2 ^ 59
def prefixEnd_2388366 : Nat := 4983230072969 + 3 ^ 40 * 2388366 * 2
def baseEnd_2388366 : Nat := 1226379736856307740741111

theorem tailTrace_2388366 : CollatzResearch.WordTrace tailWord_2388366 prefixEnd_2388366 1226379736856307740741111 := by
  unfold tailWord_2388366
  simp only [CollatzResearch.WordTrace]
  refine ⟨10888858058170669660412119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58073909643576904855531301 10888858058170669660412119)
  ·
    refine ⟨16333287087256004490618179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10888858058170669660412119 16333287087256004490618179)
    ·
      refine ⟨24499930630884006735927269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16333287087256004490618179 24499930630884006735927269)
      ·
        refine ⟨4593736993290751262986363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24499930630884006735927269 4593736993290751262986363)
        ·
          refine ⟨6890605489936126894479545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4593736993290751262986363 6890605489936126894479545)
          ·
            refine ⟨5167954117452095170859659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6890605489936126894479545 5167954117452095170859659)
            ·
              refine ⟨7751931176178142756289489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167954117452095170859659 7751931176178142756289489)
              ·
                refine ⟨5813948382133607067217117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7751931176178142756289489 5813948382133607067217117)
                ·
                  refine ⟨2180230643300102650206419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5813948382133607067217117 2180230643300102650206419)
                  ·
                    refine ⟨3270345964950153975309629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2180230643300102650206419 3270345964950153975309629)
                    ·
                      refine ⟨1226379736856307740741111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3270345964950153975309629 1226379736856307740741111)
                      ·
                        rfl

theorem cell23_2388366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2388366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388366 prefixEnd_2388366 := by exact prefixLift 2388366
  have htrace : WordTrace (prefixWord ++ tailWord_2388366) baseStart_2388366 baseEnd_2388366 := by
    simpa [prefixWord, tailWord_2388366, baseEnd_2388366] using wordTrace_append hprefix tailTrace_2388366
  have hstable : (prefixWord ++ tailWord_2388366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388366).length < 2 ^ (prefixWord ++ tailWord_2388366).sum := by decide
  have hdescent : baseEnd_2388366 < baseStart_2388366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388376 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2388376 : Nat := 118140960795 + 2388376 * 2 ^ 59
def prefixEnd_2388376 : Nat := 4983230072969 + 3 ^ 40 * 2388376 * 2
def baseEnd_2388376 : Nat := 1226384871662852701616065

theorem tailTrace_2388376 : CollatzResearch.WordTrace tailWord_2388376 prefixEnd_2388376 1226384871662852701616065 := by
  unfold tailWord_2388376
  simp only [CollatzResearch.WordTrace]
  refine ⟨43555614597664564495580491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58074152796886085994107321 43555614597664564495580491)
  ·
    refine ⟨65333421896496846743370737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43555614597664564495580491 65333421896496846743370737)
    ·
      refine ⟨49000066422372635057528053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65333421896496846743370737 49000066422372635057528053)
      ·
        refine ⟨4593756227097434536643255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49000066422372635057528053 4593756227097434536643255)
        ·
          refine ⟨6890634340646151804964883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4593756227097434536643255 6890634340646151804964883)
          ·
            refine ⟨10335951510969227707447325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6890634340646151804964883 10335951510969227707447325)
            ·
              refine ⟨3875981816613460390292747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10335951510969227707447325 3875981816613460390292747)
              ·
                refine ⟨5813972724920190585439121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875981816613460390292747 5813972724920190585439121)
                ·
                  refine ⟨4360479543690142939079341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5813972724920190585439121 4360479543690142939079341)
                  ·
                    refine ⟨1635179828883803602154753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4360479543690142939079341 1635179828883803602154753)
                    ·
                      refine ⟨1226384871662852701616065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635179828883803602154753 1226384871662852701616065)
                      ·
                        rfl

theorem cell23_2388376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2388376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388376 prefixEnd_2388376 := by exact prefixLift 2388376
  have htrace : WordTrace (prefixWord ++ tailWord_2388376) baseStart_2388376 baseEnd_2388376 := by
    simpa [prefixWord, tailWord_2388376, baseEnd_2388376] using wordTrace_append hprefix tailTrace_2388376
  have hstable : (prefixWord ++ tailWord_2388376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388376).length < 2 ^ (prefixWord ++ tailWord_2388376).sum := by decide
  have hdescent : baseEnd_2388376 < baseStart_2388376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388389 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 5, 2, 2]
def baseStart_2388389 : Nat := 118140960795 + 2388389 * 2 ^ 59
def prefixEnd_2388389 : Nat := 4983230072969 + 3 ^ 40 * 2388389 * 2
def baseEnd_2388389 : Nat := 1226391546911361150753505

theorem tailTrace_2388389 : CollatzResearch.WordTrace tailWord_2388389 prefixEnd_2388389 1226391546911361150753505 := by
  unfold tailWord_2388389
  simp only [CollatzResearch.WordTrace]
  refine ⟨87111703344282032211384221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58074468896188021474256147 87111703344282032211384221)
  ·
    refine ⟨32666888754105762079269083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87111703344282032211384221 32666888754105762079269083)
    ·
      refine ⟨49000333131158643118903625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32666888754105762079269083 49000333131158643118903625)
      ·
        refine ⟨36750249848368982339177719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49000333131158643118903625 36750249848368982339177719)
        ·
          refine ⟨55125374772553473508766579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36750249848368982339177719 55125374772553473508766579)
          ·
            refine ⟨82688062158830210263149869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55125374772553473508766579 82688062158830210263149869)
            ·
              refine ⟨31008023309561328848681201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82688062158830210263149869 31008023309561328848681201)
              ·
                refine ⟨23256017482170996636510901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31008023309561328848681201 23256017482170996636510901)
                ·
                  refine ⟨2180251638953530934672897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23256017482170996636510901 2180251638953530934672897)
                  ·
                    refine ⟨1635188729215148201004673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2180251638953530934672897 1635188729215148201004673)
                    ·
                      refine ⟨1226391546911361150753505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635188729215148201004673 1226391546911361150753505)
                      ·
                        rfl

theorem cell23_2388389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_2388389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388389 prefixEnd_2388389 := by exact prefixLift 2388389
  have htrace : WordTrace (prefixWord ++ tailWord_2388389) baseStart_2388389 baseEnd_2388389 := by
    simpa [prefixWord, tailWord_2388389, baseEnd_2388389] using wordTrace_append hprefix tailTrace_2388389
  have hstable : (prefixWord ++ tailWord_2388389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388389).length < 2 ^ (prefixWord ++ tailWord_2388389).sum := by decide
  have hdescent : baseEnd_2388389 < baseStart_2388389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388425 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 2, 7]
def baseStart_2388425 : Nat := 118140960795 + 2388425 * 2 ^ 59
def prefixEnd_2388425 : Nat := 4983230072969 + 3 ^ 40 * 2388425 * 2
def baseEnd_2388425 : Nat := 408803344071641003301113

theorem tailTrace_2388425 : CollatzResearch.WordTrace tailWord_2388425 prefixEnd_2388425 408803344071641003301113 := by
  unfold tailWord_2388425
  simp only [CollatzResearch.WordTrace]
  refine ⟨87113016372151610359694729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58075344248101073573129819 87113016372151610359694729)
  ·
    refine ⟨65334762279113707769771047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87113016372151610359694729 65334762279113707769771047)
    ·
      refine ⟨98002143418670561654656571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65334762279113707769771047 98002143418670561654656571)
      ·
        refine ⟨147003215128005842481984857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98002143418670561654656571 147003215128005842481984857)
        ·
          refine ⟨110252411346004381861488643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147003215128005842481984857 110252411346004381861488643)
          ·
            refine ⟨165378617019006572792232965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110252411346004381861488643 165378617019006572792232965)
            ·
              refine ⟨31008490691063732398543681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165378617019006572792232965 31008490691063732398543681)
              ·
                refine ⟨23256368018297799298907761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31008490691063732398543681 23256368018297799298907761)
                ·
                  refine ⟨17442276013723349474180821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23256368018297799298907761 17442276013723349474180821)
                  ·
                    refine ⟨408803344071641003301113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17442276013723349474180821 408803344071641003301113)
                    ·
                      rfl

theorem cell23_2388425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_2388425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388425 prefixEnd_2388425 := by exact prefixLift 2388425
  have htrace : WordTrace (prefixWord ++ tailWord_2388425) baseStart_2388425 baseEnd_2388425 := by
    simpa [prefixWord, tailWord_2388425, baseEnd_2388425] using wordTrace_append hprefix tailTrace_2388425
  have hstable : (prefixWord ++ tailWord_2388425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388425).length < 2 ^ (prefixWord ++ tailWord_2388425).sum := by decide
  have hdescent : baseEnd_2388425 < baseStart_2388425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388479 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 1, 4, 2]
def baseStart_2388479 : Nat := 118140960795 + 2388479 * 2 ^ 59
def prefixEnd_2388479 : Nat := 4983230072969 + 3 ^ 40 * 2388479 * 2
def baseEnd_2388479 : Nat := 1226437760170265798628091

theorem tailTrace_2388479 : CollatzResearch.WordTrace tailWord_2388479 prefixEnd_2388479 1226437760170265798628091 := by
  unfold tailWord_2388479
  simp only [CollatzResearch.WordTrace]
  refine ⟨87114985913955977582160491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58076657275970651721440327 87114985913955977582160491)
  ·
    refine ⟨130672478870933966373240737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87114985913955977582160491 130672478870933966373240737)
    ·
      refine ⟨98004359153200474779930553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130672478870933966373240737 98004359153200474779930553)
      ·
        refine ⟨73503269364900356084947915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98004359153200474779930553 73503269364900356084947915)
        ·
          refine ⟨110254904047350534127421873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73503269364900356084947915 110254904047350534127421873)
          ·
            refine ⟨82691178035512900595566405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110254904047350534127421873 82691178035512900595566405)
            ·
              refine ⟨15504595881658668861668701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82691178035512900595566405 15504595881658668861668701)
              ·
                refine ⟨5814223455622000823125763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15504595881658668861668701 5814223455622000823125763)
                ·
                  refine ⟨8721335183433001234688645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5814223455622000823125763 8721335183433001234688645)
                  ·
                    refine ⟨1635250346893687731504121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8721335183433001234688645 1635250346893687731504121)
                    ·
                      refine ⟨1226437760170265798628091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635250346893687731504121 1226437760170265798628091)
                      ·
                        rfl

theorem cell23_2388479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_2388479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388479 prefixEnd_2388479 := by exact prefixLift 2388479
  have htrace : WordTrace (prefixWord ++ tailWord_2388479) baseStart_2388479 baseEnd_2388479 := by
    simpa [prefixWord, tailWord_2388479, baseEnd_2388479] using wordTrace_append hprefix tailTrace_2388479
  have hstable : (prefixWord ++ tailWord_2388479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388479).length < 2 ^ (prefixWord ++ tailWord_2388479).sum := by decide
  have hdescent : baseEnd_2388479 < baseStart_2388479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388513 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_2388513 : Nat := 118140960795 + 2388513 * 2 ^ 59
def prefixEnd_2388513 : Nat := 4983230072969 + 3 ^ 40 * 2388513 * 2
def baseEnd_2388513 : Nat := 1226455218512518665602935

theorem tailTrace_2388513 : CollatzResearch.WordTrace tailWord_2388513 prefixEnd_2388513 1226455218512518665602935 := by
  unfold tailWord_2388513
  simp only [CollatzResearch.WordTrace]
  refine ⟨87116225995832801388898193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58077483997221867592598795 87116225995832801388898193)
  ·
    refine ⟨65337169496874601041673645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87116225995832801388898193 65337169496874601041673645)
    ·
      refine ⟨24501438561327975390627617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65337169496874601041673645 24501438561327975390627617)
      ·
        refine ⟨18376078920995981542970713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24501438561327975390627617 18376078920995981542970713)
        ·
          refine ⟨13782059190746986157228035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18376078920995981542970713 13782059190746986157228035)
          ·
            refine ⟨20673088786120479235842053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13782059190746986157228035 20673088786120479235842053)
            ·
              refine ⟨3876204147397589856720385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20673088786120479235842053 3876204147397589856720385)
              ·
                refine ⟨2907153110548192392540289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3876204147397589856720385 2907153110548192392540289)
                ·
                  refine ⟨2180364832911144294405217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2907153110548192392540289 2180364832911144294405217)
                  ·
                    refine ⟨1635273624683358220803913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2180364832911144294405217 1635273624683358220803913)
                    ·
                      refine ⟨1226455218512518665602935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635273624683358220803913 1226455218512518665602935)
                      ·
                        rfl

theorem cell23_2388513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_2388513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388513 prefixEnd_2388513 := by exact prefixLift 2388513
  have htrace : WordTrace (prefixWord ++ tailWord_2388513) baseStart_2388513 baseEnd_2388513 := by
    simpa [prefixWord, tailWord_2388513, baseEnd_2388513] using wordTrace_append hprefix tailTrace_2388513
  have hstable : (prefixWord ++ tailWord_2388513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388513).length < 2 ^ (prefixWord ++ tailWord_2388513).sum := by decide
  have hdescent : baseEnd_2388513 < baseStart_2388513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388526 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2388526 : Nat := 118140960795 + 2388526 * 2 ^ 59
def prefixEnd_2388526 : Nat := 4983230072969 + 3 ^ 40 * 2388526 * 2
def baseEnd_2388526 : Nat := 1226461893761027114740375

theorem tailTrace_2388526 : CollatzResearch.WordTrace tailWord_2388526 prefixEnd_2388526 1226461893761027114740375 := by
  unfold tailWord_2388526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10889587518098213076140179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58077800096523803072747621 10889587518098213076140179)
  ·
    refine ⟨16334381277147319614210269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10889587518098213076140179 16334381277147319614210269)
    ·
      refine ⟨6125392978930244855328851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16334381277147319614210269 6125392978930244855328851)
      ·
        refine ⟨9188089468395367282993277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6125392978930244855328851 9188089468395367282993277)
        ·
          refine ⟨3445533550648262731122479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9188089468395367282993277 3445533550648262731122479)
          ·
            refine ⟨5168300325972394096683719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445533550648262731122479 5168300325972394096683719)
            ·
              refine ⟨7752450488958591145025579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5168300325972394096683719 7752450488958591145025579)
              ·
                refine ⟨11628675733437886717538369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7752450488958591145025579 11628675733437886717538369)
                ·
                  refine ⟨8721506800078415038153777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11628675733437886717538369 8721506800078415038153777)
                  ·
                    refine ⟨6541130100058811278615333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8721506800078415038153777 6541130100058811278615333)
                    ·
                      refine ⟨1226461893761027114740375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6541130100058811278615333 1226461893761027114740375)
                      ·
                        rfl

theorem cell23_2388526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2388526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388526 prefixEnd_2388526 := by exact prefixLift 2388526
  have htrace : WordTrace (prefixWord ++ tailWord_2388526) baseStart_2388526 baseEnd_2388526 := by
    simpa [prefixWord, tailWord_2388526, baseEnd_2388526] using wordTrace_append hprefix tailTrace_2388526
  have hstable : (prefixWord ++ tailWord_2388526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388526).length < 2 ^ (prefixWord ++ tailWord_2388526).sum := by decide
  have hdescent : baseEnd_2388526 < baseStart_2388526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388549 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_2388549 : Nat := 118140960795 + 2388549 * 2 ^ 59
def prefixEnd_2388549 : Nat := 4983230072969 + 3 ^ 40 * 2388549 * 2
def baseEnd_2388549 : Nat := 408824567938693508250923

theorem tailTrace_2388549 : CollatzResearch.WordTrace tailWord_2388549 prefixEnd_2388549 408824567938693508250923 := by
  unfold tailWord_2388549
  simp only [CollatzResearch.WordTrace]
  refine ⟨87117539023702379537208701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58078359349134919691472467 87117539023702379537208701)
  ·
    refine ⟨32669077133888392326453263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87117539023702379537208701 32669077133888392326453263)
    ·
      refine ⟨49003615700832588489679895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32669077133888392326453263 49003615700832588489679895)
      ·
        refine ⟨73505423551248882734519843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49003615700832588489679895 73505423551248882734519843)
        ·
          refine ⟨110258135326873324101779765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73505423551248882734519843 110258135326873324101779765)
          ·
            refine ⟨10336700186894374134541853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110258135326873324101779765 10336700186894374134541853)
            ·
              refine ⟨3876262570085390300453195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10336700186894374134541853 3876262570085390300453195)
              ·
                refine ⟨5814393855128085450679793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3876262570085390300453195 5814393855128085450679793)
                ·
                  refine ⟨4360795391346064088009845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5814393855128085450679793 4360795391346064088009845)
                  ·
                    refine ⟨408824567938693508250923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4360795391346064088009845 408824567938693508250923)
                    ·
                      rfl

theorem cell23_2388549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_2388549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388549 prefixEnd_2388549 := by exact prefixLift 2388549
  have htrace : WordTrace (prefixWord ++ tailWord_2388549) baseStart_2388549 baseEnd_2388549 := by
    simpa [prefixWord, tailWord_2388549, baseEnd_2388549] using wordTrace_append hprefix tailTrace_2388549
  have hstable : (prefixWord ++ tailWord_2388549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388549).length < 2 ^ (prefixWord ++ tailWord_2388549).sum := by decide
  have hdescent : baseEnd_2388549 < baseStart_2388549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388586 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_2388586 : Nat := 118140960795 + 2388586 * 2 ^ 59
def prefixEnd_2388586 : Nat := 4983230072969 + 3 ^ 40 * 2388586 * 2
def baseEnd_2388586 : Nat := 1226492702600296879990099

theorem tailTrace_2388586 : CollatzResearch.WordTrace tailWord_2388586 prefixEnd_2388586 1226492702600296879990099 := by
  unfold tailWord_2388586
  simp only [CollatzResearch.WordTrace]
  refine ⟨21779722131142083714076403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58079259016378889904203741 21779722131142083714076403)
  ·
    refine ⟨32669583196713125571114605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21779722131142083714076403 32669583196713125571114605)
    ·
      refine ⟨12251093698767422089167977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32669583196713125571114605 12251093698767422089167977)
      ·
        refine ⟨9188320274075566566875983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12251093698767422089167977 9188320274075566566875983)
        ·
          refine ⟨13782480411113349850313975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9188320274075566566875983 13782480411113349850313975)
          ·
            refine ⟨20673720616670024775470963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13782480411113349850313975 20673720616670024775470963)
            ·
              refine ⟨31010580925005037163206445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20673720616670024775470963 31010580925005037163206445)
              ·
                refine ⟨11628967846876888936202417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31010580925005037163206445 11628967846876888936202417)
                ·
                  refine ⟨8721725885157666702151813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11628967846876888936202417 8721725885157666702151813)
                  ·
                    refine ⟨1635323603467062506653465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8721725885157666702151813 1635323603467062506653465)
                    ·
                      refine ⟨1226492702600296879990099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635323603467062506653465 1226492702600296879990099)
                      ·
                        rfl

theorem cell23_2388586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_2388586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388586 prefixEnd_2388586 := by exact prefixLift 2388586
  have htrace : WordTrace (prefixWord ++ tailWord_2388586) baseStart_2388586 baseEnd_2388586 := by
    simpa [prefixWord, tailWord_2388586, baseEnd_2388586] using wordTrace_append hprefix tailTrace_2388586
  have hstable : (prefixWord ++ tailWord_2388586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388586).length < 2 ^ (prefixWord ++ tailWord_2388586).sum := by decide
  have hdescent : baseEnd_2388586 < baseStart_2388586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388613 : List Nat := [1, 3, 1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_2388613 : Nat := 118140960795 + 2388613 * 2 ^ 59
def prefixEnd_2388613 : Nat := 4983230072969 + 3 ^ 40 * 2388613 * 2
def baseEnd_2388613 : Nat := 408835522192656091450825

theorem tailTrace_2388613 : CollatzResearch.WordTrace tailWord_2388613 prefixEnd_2388613 408835522192656091450825 := by
  unfold tailWord_2388613
  simp only [CollatzResearch.WordTrace]
  refine ⟨87119873295470518467538493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58079915530313678978358995 87119873295470518467538493)
  ·
    refine ⟨32669952485801444425326935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87119873295470518467538493 32669952485801444425326935)
    ·
      refine ⟨49004928728702166637990403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32669952485801444425326935 49004928728702166637990403)
      ·
        refine ⟨73507393093053249956985605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49004928728702166637990403 73507393093053249956985605)
        ·
          refine ⟨13782636204947484366934801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73507393093053249956985605 13782636204947484366934801)
          ·
            refine ⟨10336977153710613275201101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13782636204947484366934801 10336977153710613275201101)
            ·
              refine ⟨3876366432641479978200413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10336977153710613275201101 3876366432641479978200413)
              ·
                refine ⟨1453637412240554991825155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3876366432641479978200413 1453637412240554991825155)
                ·
                  refine ⟨2180456118360832487737733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453637412240554991825155 2180456118360832487737733)
                  ·
                    refine ⟨408835522192656091450825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2180456118360832487737733 408835522192656091450825)
                    ·
                      rfl

theorem cell23_2388613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_2388613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388613 prefixEnd_2388613 := by exact prefixLift 2388613
  have htrace : WordTrace (prefixWord ++ tailWord_2388613) baseStart_2388613 baseEnd_2388613 := by
    simpa [prefixWord, tailWord_2388613, baseEnd_2388613] using wordTrace_append hprefix tailTrace_2388613
  have hstable : (prefixWord ++ tailWord_2388613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388613).length < 2 ^ (prefixWord ++ tailWord_2388613).sum := by decide
  have hdescent : baseEnd_2388613 < baseStart_2388613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388669 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_2388669 : Nat := 118140960795 + 2388669 * 2 ^ 59
def prefixEnd_2388669 : Nat := 4983230072969 + 3 ^ 40 * 2388669 * 2
def baseEnd_2388669 : Nat := 408845107164873351750739

theorem tailTrace_2388669 : CollatzResearch.WordTrace tailWord_2388669 prefixEnd_2388669 408845107164873351750739 := by
  unfold tailWord_2388669
  simp only [CollatzResearch.WordTrace]
  refine ⟨87121915783267640031577061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58081277188845093354384707 87121915783267640031577061)
  ·
    refine ⟨16335359209362682505920699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87121915783267640031577061 16335359209362682505920699)
    ·
      refine ⟨24503038814044023758881049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16335359209362682505920699 24503038814044023758881049)
      ·
        refine ⟨18377279110533017819160787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24503038814044023758881049 18377279110533017819160787)
        ·
          refine ⟨27565918665799526728741181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18377279110533017819160787 27565918665799526728741181)
          ·
            refine ⟨10337219499674822523277943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27565918665799526728741181 10337219499674822523277943)
            ·
              refine ⟨15505829249512233784916915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10337219499674822523277943 15505829249512233784916915)
              ·
                refine ⟨23258743874268350677375373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15505829249512233784916915 23258743874268350677375373)
                ·
                  refine ⟨8722028952850631504015765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23258743874268350677375373 8722028952850631504015765)
                  ·
                    refine ⟨408845107164873351750739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8722028952850631504015765 408845107164873351750739)
                    ·
                      rfl

theorem cell23_2388669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_2388669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388669 prefixEnd_2388669 := by exact prefixLift 2388669
  have htrace : WordTrace (prefixWord ++ tailWord_2388669) baseStart_2388669 baseEnd_2388669 := by
    simpa [prefixWord, tailWord_2388669, baseEnd_2388669] using wordTrace_append hprefix tailTrace_2388669
  have hstable : (prefixWord ++ tailWord_2388669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388669).length < 2 ^ (prefixWord ++ tailWord_2388669).sum := by decide
  have hdescent : baseEnd_2388669 < baseStart_2388669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388670 : List Nat := [4, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_2388670 : Nat := 118140960795 + 2388670 * 2 ^ 59
def prefixEnd_2388670 : Nat := 4983230072969 + 3 ^ 40 * 2388670 * 2
def baseEnd_2388670 : Nat := 1226535834975274551339713

theorem tailTrace_2388670 : CollatzResearch.WordTrace tailWord_2388670 prefixEnd_2388670 1226535834975274551339713 := by
  unfold tailWord_2388670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10890244032033002150295433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58081301504176011468242309 10890244032033002150295433)
  ·
    refine ⟨8167683024024751612721575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10890244032033002150295433 8167683024024751612721575)
    ·
      refine ⟨12251524536037127419082363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8167683024024751612721575 12251524536037127419082363)
      ·
        refine ⟨18377286804055691128623545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12251524536037127419082363 18377286804055691128623545)
        ·
          refine ⟨13782965103041768346467659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18377286804055691128623545 13782965103041768346467659)
          ·
            refine ⟨20674447654562652519701489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13782965103041768346467659 20674447654562652519701489)
            ·
              refine ⟨15505835740921989389776117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20674447654562652519701489 15505835740921989389776117)
              ·
                refine ⟨1453672100711436505291511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15505835740921989389776117 1453672100711436505291511)
                ·
                  refine ⟨2180508151067154757937267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453672100711436505291511 2180508151067154757937267)
                  ·
                    refine ⟨3270762226600732136905901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2180508151067154757937267 3270762226600732136905901)
                    ·
                      refine ⟨1226535834975274551339713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3270762226600732136905901 1226535834975274551339713)
                      ·
                        rfl

theorem cell23_2388670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_2388670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388670 prefixEnd_2388670 := by exact prefixLift 2388670
  have htrace : WordTrace (prefixWord ++ tailWord_2388670) baseStart_2388670 baseEnd_2388670 := by
    simpa [prefixWord, tailWord_2388670, baseEnd_2388670] using wordTrace_append hprefix tailTrace_2388670
  have hstable : (prefixWord ++ tailWord_2388670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388670).length < 2 ^ (prefixWord ++ tailWord_2388670).sum := by decide
  have hdescent : baseEnd_2388670 < baseStart_2388670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388679 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_2388679 : Nat := 118140960795 + 2388679 * 2 ^ 59
def prefixEnd_2388679 : Nat := 4983230072969 + 3 ^ 40 * 2388679 * 2
def baseEnd_2388679 : Nat := 1226540456301165016127171

theorem tailTrace_2388679 : CollatzResearch.WordTrace tailWord_2388679 prefixEnd_2388679 1226540456301165016127171 := by
  unfold tailWord_2388679
  simp only [CollatzResearch.WordTrace]
  refine ⟨87122280513231411739441091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58081520342154274492960727 87122280513231411739441091)
  ·
    refine ⟨130683420769847117609161637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87122280513231411739441091 130683420769847117609161637)
    ·
      refine ⟨24503141394346334551717807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130683420769847117609161637 24503141394346334551717807)
      ·
        refine ⟨36754712091519501827576711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24503141394346334551717807 36754712091519501827576711)
        ·
          refine ⟨55132068137279252741365067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36754712091519501827576711 55132068137279252741365067)
          ·
            refine ⟨82698102205918879112047601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55132068137279252741365067 82698102205918879112047601)
            ·
              refine ⟨62023576654439159334035701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82698102205918879112047601 62023576654439159334035701)
              ·
                refine ⟨5814710311353671187565847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62023576654439159334035701 5814710311353671187565847)
                ·
                  refine ⟨8722065467030506781348771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5814710311353671187565847 8722065467030506781348771)
                  ·
                    refine ⟨13083098200545760172023157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8722065467030506781348771 13083098200545760172023157)
                    ·
                      refine ⟨1226540456301165016127171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13083098200545760172023157 1226540456301165016127171)
                      ·
                        rfl

theorem cell23_2388679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_2388679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388679 prefixEnd_2388679 := by exact prefixLift 2388679
  have htrace : WordTrace (prefixWord ++ tailWord_2388679) baseStart_2388679 baseEnd_2388679 := by
    simpa [prefixWord, tailWord_2388679, baseEnd_2388679] using wordTrace_append hprefix tailTrace_2388679
  have hstable : (prefixWord ++ tailWord_2388679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388679).length < 2 ^ (prefixWord ++ tailWord_2388679).sum := by decide
  have hdescent : baseEnd_2388679 < baseStart_2388679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388689 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_2388689 : Nat := 118140960795 + 2388689 * 2 ^ 59
def prefixEnd_2388689 : Nat := 4983230072969 + 3 ^ 40 * 2388689 * 2
def baseEnd_2388689 : Nat := 1226545591107709977002125

theorem tailTrace_2388689 : CollatzResearch.WordTrace tailWord_2388689 prefixEnd_2388689 1226545591107709977002125 := by
  unfold tailWord_2388689
  simp only [CollatzResearch.WordTrace]
  refine ⟨87122645243195183447305121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58081763495463455631536747 87122645243195183447305121)
  ·
    refine ⟨65341983932396387585478841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87122645243195183447305121 65341983932396387585478841)
    ·
      refine ⟨49006487949297290689109131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65341983932396387585478841 49006487949297290689109131)
      ·
        refine ⟨73509731923945936033663697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49006487949297290689109131 73509731923945936033663697)
        ·
          refine ⟨55132298942959452025247773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73509731923945936033663697 55132298942959452025247773)
          ·
            refine ⟨20674612103609794509467915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55132298942959452025247773 20674612103609794509467915)
            ·
              refine ⟨31011918155414691764201873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20674612103609794509467915 31011918155414691764201873)
              ·
                refine ⟨23258938616561018823151405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31011918155414691764201873 23258938616561018823151405)
                ·
                  refine ⟨8722101981210382058681777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23258938616561018823151405 8722101981210382058681777)
                  ·
                    refine ⟨6541576485907786544011333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8722101981210382058681777 6541576485907786544011333)
                    ·
                      refine ⟨1226545591107709977002125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6541576485907786544011333 1226545591107709977002125)
                      ·
                        rfl

theorem cell23_2388689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_2388689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388689 prefixEnd_2388689 := by exact prefixLift 2388689
  have htrace : WordTrace (prefixWord ++ tailWord_2388689) baseStart_2388689 baseEnd_2388689 := by
    simpa [prefixWord, tailWord_2388689, baseEnd_2388689] using wordTrace_append hprefix tailTrace_2388689
  have hstable : (prefixWord ++ tailWord_2388689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388689).length < 2 ^ (prefixWord ++ tailWord_2388689).sum := by decide
  have hdescent : baseEnd_2388689 < baseStart_2388689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388696 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_2388696 : Nat := 118140960795 + 2388696 * 2 ^ 59
def prefixEnd_2388696 : Nat := 4983230072969 + 3 ^ 40 * 2388696 * 2
def baseEnd_2388696 : Nat := 1226549185472291449614593

theorem tailTrace_2388696 : CollatzResearch.WordTrace tailWord_2388696 prefixEnd_2388696 1226549185472291449614593 := by
  unfold tailWord_2388696
  simp only [CollatzResearch.WordTrace]
  refine ⟨43561450277084911821404971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58081933702779882428539961 43561450277084911821404971)
  ·
    refine ⟨65342175415627367732107457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43561450277084911821404971 65342175415627367732107457)
    ·
      refine ⟨49006631561720525799080593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65342175415627367732107457 49006631561720525799080593)
      ·
        refine ⟨36754973671290394349310445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49006631561720525799080593 36754973671290394349310445)
        ·
          refine ⟨13783115126733897880991417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36754973671290394349310445 13783115126733897880991417)
          ·
            refine ⟨10337336345050423410743563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13783115126733897880991417 10337336345050423410743563)
            ·
              refine ⟨15506004517575635116115345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10337336345050423410743563 15506004517575635116115345)
              ·
                refine ⟨11629503388181726337086509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15506004517575635116115345 11629503388181726337086509)
                ·
                  refine ⟨4361063770568147376407441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11629503388181726337086509 4361063770568147376407441)
                  ·
                    refine ⟨3270797827926110532305581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4361063770568147376407441 3270797827926110532305581)
                    ·
                      refine ⟨1226549185472291449614593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3270797827926110532305581 1226549185472291449614593)
                      ·
                        rfl

theorem cell23_2388696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_2388696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388696 prefixEnd_2388696 := by exact prefixLift 2388696
  have htrace : WordTrace (prefixWord ++ tailWord_2388696) baseStart_2388696 baseEnd_2388696 := by
    simpa [prefixWord, tailWord_2388696, baseEnd_2388696] using wordTrace_append hprefix tailTrace_2388696
  have hstable : (prefixWord ++ tailWord_2388696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388696).length < 2 ^ (prefixWord ++ tailWord_2388696).sum := by decide
  have hdescent : baseEnd_2388696 < baseStart_2388696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388724 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2388724 : Nat := 118140960795 + 2388724 * 2 ^ 59
def prefixEnd_2388724 : Nat := 4983230072969 + 3 ^ 40 * 2388724 * 2
def baseEnd_2388724 : Nat := 408854520976872446688155

theorem tailTrace_2388724 : CollatzResearch.WordTrace tailWord_2388724 prefixEnd_2388724 408854520976872446688155 := by
  unfold tailWord_2388724
  simp only [CollatzResearch.WordTrace]
  refine ⟨43561960899034192212414613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58082614532045589616552817 43561960899034192212414613)
  ·
    refine ⟨2041966917142227759956935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43561960899034192212414613 2041966917142227759956935)
    ·
      refine ⟨3062950375713341639935403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041966917142227759956935 3062950375713341639935403)
      ·
        refine ⟨4594425563570012459903105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3062950375713341639935403 4594425563570012459903105)
        ·
          refine ⟨3445819172677509344927329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4594425563570012459903105 3445819172677509344927329)
          ·
            refine ⟨2584364379508132008695497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3445819172677509344927329 2584364379508132008695497)
            ·
              refine ⟨1938273284631099006521623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2584364379508132008695497 1938273284631099006521623)
              ·
                refine ⟨2907409926946648509782435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938273284631099006521623 2907409926946648509782435)
                ·
                  refine ⟨4361114890419972764673653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907409926946648509782435 4361114890419972764673653)
                  ·
                    refine ⟨408854520976872446688155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4361114890419972764673653 408854520976872446688155)
                    ·
                      rfl

theorem cell23_2388724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2388724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388724 prefixEnd_2388724 := by exact prefixLift 2388724
  have htrace : WordTrace (prefixWord ++ tailWord_2388724) baseStart_2388724 baseEnd_2388724 := by
    simpa [prefixWord, tailWord_2388724, baseEnd_2388724] using wordTrace_append hprefix tailTrace_2388724
  have hstable : (prefixWord ++ tailWord_2388724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388724).length < 2 ^ (prefixWord ++ tailWord_2388724).sum := by decide
  have hdescent : baseEnd_2388724 < baseStart_2388724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388770 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_2388770 : Nat := 118140960795 + 2388770 * 2 ^ 59
def prefixEnd_2388770 : Nat := 4983230072969 + 3 ^ 40 * 2388770 * 2
def baseEnd_2388770 : Nat := 1226587183040724160089253

theorem tailTrace_2388770 : CollatzResearch.WordTrace tailWord_2388770 prefixEnd_2388770 1226587183040724160089253 := by
  unfold tailWord_2388770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21781399888975433570250941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58083733037267822854002509 21781399888975433570250941)
  ·
    refine ⟨8168024958365787588844103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21781399888975433570250941 8168024958365787588844103)
    ·
      refine ⟨12252037437548681383266155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8168024958365787588844103 12252037437548681383266155)
      ·
        refine ⟨18378056156323022074899233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12252037437548681383266155 18378056156323022074899233)
        ·
          refine ⟨13783542117242266556174425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18378056156323022074899233 13783542117242266556174425)
          ·
            refine ⟨10337656587931699917130819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13783542117242266556174425 10337656587931699917130819)
            ·
              refine ⟨15506484881897549875696229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10337656587931699917130819 15506484881897549875696229)
              ·
                refine ⟨2907465915355790601693043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15506484881897549875696229 2907465915355790601693043)
                ·
                  refine ⟨4361198873033685902539565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907465915355790601693043 4361198873033685902539565)
                  ·
                    refine ⟨1635449577387632213452337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4361198873033685902539565 1635449577387632213452337)
                    ·
                      refine ⟨1226587183040724160089253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635449577387632213452337 1226587183040724160089253)
                      ·
                        rfl

theorem cell23_2388770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_2388770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388770 prefixEnd_2388770 := by exact prefixLift 2388770
  have htrace : WordTrace (prefixWord ++ tailWord_2388770) baseStart_2388770 baseEnd_2388770 := by
    simpa [prefixWord, tailWord_2388770, baseEnd_2388770] using wordTrace_append hprefix tailTrace_2388770
  have hstable : (prefixWord ++ tailWord_2388770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388770).length < 2 ^ (prefixWord ++ tailWord_2388770).sum := by decide
  have hdescent : baseEnd_2388770 < baseStart_2388770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388778 : List Nat := [3, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2388778 : Nat := 118140960795 + 2388778 * 2 ^ 59
def prefixEnd_2388778 : Nat := 4983230072969 + 3 ^ 40 * 2388778 * 2
def baseEnd_2388778 : Nat := 1226591290885960128789217

theorem tailTrace_2388778 : CollatzResearch.WordTrace tailWord_2388778 prefixEnd_2388778 1226591290885960128789217 := by
  unfold tailWord_2388778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21781472834968187911823747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58083927559915167764863325 21781472834968187911823747)
  ·
    refine ⟨32672209252452281867735621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21781472834968187911823747 32672209252452281867735621)
    ·
      refine ⟨6126039234834802850200429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32672209252452281867735621 6126039234834802850200429)
      ·
        refine ⟨2297264713063051068825161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6126039234834802850200429 2297264713063051068825161)
        ·
          refine ⟨1722948534797288301618871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2297264713063051068825161 1722948534797288301618871)
          ·
            refine ⟨2584422802195932452428307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722948534797288301618871 2584422802195932452428307)
            ·
              refine ⟨3876634203293898678642461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2584422802195932452428307 3876634203293898678642461)
              ·
                refine ⟨1453737826235212004490923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3876634203293898678642461 1453737826235212004490923)
                ·
                  refine ⟨2180606739352818006736385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453737826235212004490923 2180606739352818006736385)
                  ·
                    refine ⟨1635455054514613505052289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2180606739352818006736385 1635455054514613505052289)
                    ·
                      refine ⟨1226591290885960128789217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635455054514613505052289 1226591290885960128789217)
                      ·
                        rfl

theorem cell23_2388778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2388778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388778 prefixEnd_2388778 := by exact prefixLift 2388778
  have htrace : WordTrace (prefixWord ++ tailWord_2388778) baseStart_2388778 baseEnd_2388778 := by
    simpa [prefixWord, tailWord_2388778, baseEnd_2388778] using wordTrace_append hprefix tailTrace_2388778
  have hstable : (prefixWord ++ tailWord_2388778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388778).length < 2 ^ (prefixWord ++ tailWord_2388778).sum := by decide
  have hdescent : baseEnd_2388778 < baseStart_2388778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388779 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 4]
def baseStart_2388779 : Nat := 118140960795 + 2388779 * 2 ^ 59
def prefixEnd_2388779 : Nat := 4983230072969 + 3 ^ 40 * 2388779 * 2
def baseEnd_2388779 : Nat := 1226591804366614624876711

theorem tailTrace_2388779 : CollatzResearch.WordTrace tailWord_2388779 prefixEnd_2388779 1226591804366614624876711 := by
  unfold tailWord_2388779
  simp only [CollatzResearch.WordTrace]
  refine ⟨87125927812869128818081391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58083951875246085878720927 87125927812869128818081391)
  ·
    refine ⟨130688891719303693227122087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87125927812869128818081391 130688891719303693227122087)
    ·
      refine ⟨196033337578955539840683131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130688891719303693227122087 196033337578955539840683131)
      ·
        refine ⟨294050006368433309761024697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196033337578955539840683131 294050006368433309761024697)
        ·
          refine ⟨220537504776324982320768523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294050006368433309761024697 220537504776324982320768523)
          ·
            refine ⟨330806257164487473481152785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220537504776324982320768523 330806257164487473481152785)
            ·
              refine ⟨248104692873365605110864589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330806257164487473481152785 248104692873365605110864589)
              ·
                refine ⟨93039259827512101916574221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248104692873365605110864589 93039259827512101916574221)
                ·
                  refine ⟨34889722435317038218715333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93039259827512101916574221 34889722435317038218715333)
                  ·
                    refine ⟨6541822956621944666009125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34889722435317038218715333 6541822956621944666009125)
                    ·
                      refine ⟨1226591804366614624876711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6541822956621944666009125 1226591804366614624876711)
                      ·
                        rfl

theorem cell23_2388779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 4].length) (baseStart_2388779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388779 prefixEnd_2388779 := by exact prefixLift 2388779
  have htrace : WordTrace (prefixWord ++ tailWord_2388779) baseStart_2388779 baseEnd_2388779 := by
    simpa [prefixWord, tailWord_2388779, baseEnd_2388779] using wordTrace_append hprefix tailTrace_2388779
  have hstable : (prefixWord ++ tailWord_2388779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388779).length < 2 ^ (prefixWord ++ tailWord_2388779).sum := by decide
  have hdescent : baseEnd_2388779 < baseStart_2388779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388786 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2388786 : Nat := 118140960795 + 2388786 * 2 ^ 59
def prefixEnd_2388786 : Nat := 4983230072969 + 3 ^ 40 * 2388786 * 2
def baseEnd_2388786 : Nat := 1226595398731196097489179

theorem tailTrace_2388786 : CollatzResearch.WordTrace tailWord_2388786 prefixEnd_2388786 1226595398731196097489179 := by
  unfold tailWord_2388786
  simp only [CollatzResearch.WordTrace]
  refine ⟨21781545780960942253396553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58084122082562512675724141 21781545780960942253396553)
  ·
    refine ⟨16336159335720706690047415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21781545780960942253396553 16336159335720706690047415)
    ·
      refine ⟨24504239003581060035071123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16336159335720706690047415 24504239003581060035071123)
      ·
        refine ⟨36756358505371590052606685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24504239003581060035071123 36756358505371590052606685)
        ·
          refine ⟨13783634439514346269727507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36756358505371590052606685 13783634439514346269727507)
          ·
            refine ⟨20675451659271519404591261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13783634439514346269727507 20675451659271519404591261)
            ·
              refine ⟨7753294372226819776721723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20675451659271519404591261 7753294372226819776721723)
              ·
                refine ⟨11629941558340229665082585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7753294372226819776721723 11629941558340229665082585)
                ·
                  refine ⟨8722456168755172248811939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11629941558340229665082585 8722456168755172248811939)
                  ·
                    refine ⟨13083684253132758373217909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8722456168755172248811939 13083684253132758373217909)
                    ·
                      refine ⟨1226595398731196097489179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13083684253132758373217909 1226595398731196097489179)
                      ·
                        rfl

theorem cell23_2388786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2388786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388786 prefixEnd_2388786 := by exact prefixLift 2388786
  have htrace : WordTrace (prefixWord ++ tailWord_2388786) baseStart_2388786 baseEnd_2388786 := by
    simpa [prefixWord, tailWord_2388786, baseEnd_2388786] using wordTrace_append hprefix tailTrace_2388786
  have hstable : (prefixWord ++ tailWord_2388786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388786).length < 2 ^ (prefixWord ++ tailWord_2388786).sum := by decide
  have hdescent : baseEnd_2388786 < baseStart_2388786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388816 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 3]
def baseStart_2388816 : Nat := 118140960795 + 2388816 * 2 ^ 59
def prefixEnd_2388816 : Nat := 4983230072969 + 3 ^ 40 * 2388816 * 2
def baseEnd_2388816 : Nat := 1226610803150830980114041

theorem tailTrace_2388816 : CollatzResearch.WordTrace tailWord_2388816 prefixEnd_2388816 1226610803150830980114041 := by
  unfold tailWord_2388816
  simp only [CollatzResearch.WordTrace]
  refine ⟨43563638656867542068589151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58084851542490056091452201 43563638656867542068589151)
  ·
    refine ⟨65345457985301313102883727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43563638656867542068589151 65345457985301313102883727)
    ·
      refine ⟨98018186977951969654325591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65345457985301313102883727 98018186977951969654325591)
      ·
        refine ⟨147027280466927954481488387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98018186977951969654325591 147027280466927954481488387)
        ·
          refine ⟨220540920700391931722232581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147027280466927954481488387 220540920700391931722232581)
          ·
            refine ⟨41351422631323487197918609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220540920700391931722232581 41351422631323487197918609)
            ·
              refine ⟨31013566973492615398438957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41351422631323487197918609 31013566973492615398438957)
              ·
                refine ⟨11630087615059730774414609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31013566973492615398438957 11630087615059730774414609)
                ·
                  refine ⟨8722565711294798080810957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11630087615059730774414609 8722565711294798080810957)
                  ·
                    refine ⟨3270962141735549280304109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8722565711294798080810957 3270962141735549280304109)
                    ·
                      refine ⟨1226610803150830980114041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3270962141735549280304109 1226610803150830980114041)
                      ·
                        rfl

theorem cell23_2388816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_2388816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388816 prefixEnd_2388816 := by exact prefixLift 2388816
  have htrace : WordTrace (prefixWord ++ tailWord_2388816) baseStart_2388816 baseEnd_2388816 := by
    simpa [prefixWord, tailWord_2388816, baseEnd_2388816] using wordTrace_append hprefix tailTrace_2388816
  have hstable : (prefixWord ++ tailWord_2388816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388816).length < 2 ^ (prefixWord ++ tailWord_2388816).sum := by decide
  have hdescent : baseEnd_2388816 < baseStart_2388816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388817 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 2, 2, 2]
def baseStart_2388817 : Nat := 118140960795 + 2388817 * 2 ^ 59
def prefixEnd_2388817 : Nat := 4983230072969 + 3 ^ 40 * 2388817 * 2
def baseEnd_2388817 : Nat := 1226611316631485476201537

theorem tailTrace_2388817 : CollatzResearch.WordTrace tailWord_2388817 prefixEnd_2388817 1226611316631485476201537 := by
  unfold tailWord_2388817
  simp only [CollatzResearch.WordTrace]
  refine ⟨87127313786731461307964705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58084875857820974205309803 87127313786731461307964705)
  ·
    refine ⟨65345485340048595980973529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87127313786731461307964705 65345485340048595980973529)
    ·
      refine ⟨49009114005036446985730147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65345485340048595980973529 49009114005036446985730147)
      ·
        refine ⟨73513671007554670478595221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49009114005036446985730147 73513671007554670478595221)
        ·
          refine ⟨3445953328479125178684151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73513671007554670478595221 3445953328479125178684151)
          ·
            refine ⟨5168929992718687768026227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445953328479125178684151 5168929992718687768026227)
            ·
              refine ⟨7753394989078031652039341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5168929992718687768026227 7753394989078031652039341)
              ·
                refine ⟨2907523120904261869514753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7753394989078031652039341 2907523120904261869514753)
                ·
                  refine ⟨2180642340678196402136065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2907523120904261869514753 2180642340678196402136065)
                  ·
                    refine ⟨1635481755508647301602049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2180642340678196402136065 1635481755508647301602049)
                    ·
                      refine ⟨1226611316631485476201537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635481755508647301602049 1226611316631485476201537)
                      ·
                        rfl

theorem cell23_2388817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_2388817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388817 prefixEnd_2388817 := by exact prefixLift 2388817
  have htrace : WordTrace (prefixWord ++ tailWord_2388817) baseStart_2388817 baseEnd_2388817 := by
    simpa [prefixWord, tailWord_2388817, baseEnd_2388817] using wordTrace_append hprefix tailTrace_2388817
  have hstable : (prefixWord ++ tailWord_2388817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388817).length < 2 ^ (prefixWord ++ tailWord_2388817).sum := by decide
  have hdescent : baseEnd_2388817 < baseStart_2388817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388819 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 3, 7]
def baseStart_2388819 : Nat := 118140960795 + 2388819 * 2 ^ 59
def prefixEnd_2388819 : Nat := 4983230072969 + 3 ^ 40 * 2388819 * 2
def baseEnd_2388819 : Nat := 408870781197598156125509

theorem tailTrace_2388819 : CollatzResearch.WordTrace tailWord_2388819 prefixEnd_2388819 408870781197598156125509 := by
  unfold tailWord_2388819
  simp only [CollatzResearch.WordTrace]
  refine ⟨87127386732724215649537511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58084924488482810433025007 87127386732724215649537511)
  ·
    refine ⟨130691080099086323474306267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87127386732724215649537511 130691080099086323474306267)
    ·
      refine ⟨196036620148629485211459401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130691080099086323474306267 196036620148629485211459401)
      ·
        refine ⟨147027465111472113908594551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196036620148629485211459401 147027465111472113908594551)
        ·
          refine ⟨220541197667208170862891827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147027465111472113908594551 220541197667208170862891827)
          ·
            refine ⟨330811796500812256294337741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220541197667208170862891827 330811796500812256294337741)
            ·
              refine ⟨124054423687804596110376653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 330811796500812256294337741 124054423687804596110376653)
              ·
                refine ⟨46520408882926723541391245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124054423687804596110376653 46520408882926723541391245)
                ·
                  refine ⟨17445153331097521328021717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46520408882926723541391245 17445153331097521328021717)
                  ·
                    refine ⟨408870781197598156125509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17445153331097521328021717 408870781197598156125509)
                    ·
                      rfl

theorem cell23_2388819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 7].length) (baseStart_2388819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388819 prefixEnd_2388819 := by exact prefixLift 2388819
  have htrace : WordTrace (prefixWord ++ tailWord_2388819) baseStart_2388819 baseEnd_2388819 := by
    simpa [prefixWord, tailWord_2388819, baseEnd_2388819] using wordTrace_append hprefix tailTrace_2388819
  have hstable : (prefixWord ++ tailWord_2388819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388819).length < 2 ^ (prefixWord ++ tailWord_2388819).sum := by decide
  have hdescent : baseEnd_2388819 < baseStart_2388819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388853 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2388853 : Nat := 118140960795 + 2388853 * 2 ^ 59
def prefixEnd_2388853 : Nat := 4983230072969 + 3 ^ 40 * 2388853 * 2
def baseEnd_2388853 : Nat := 408876600645015778450457

theorem tailTrace_2388853 : CollatzResearch.WordTrace tailWord_2388853 prefixEnd_2388853 408876600645015778450457 := by
  unfold tailWord_2388853
  simp only [CollatzResearch.WordTrace]
  refine ⟨87128626814601039456275213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58085751209734026304183475 87128626814601039456275213)
  ·
    refine ⟨32673235055475389796103205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87128626814601039456275213 32673235055475389796103205)
    ·
      refine ⟨6126231572901635586769351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32673235055475389796103205 6126231572901635586769351)
      ·
        refine ⟨9189347359352453380154027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6126231572901635586769351 9189347359352453380154027)
        ·
          refine ⟨13784021039028680070231041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9189347359352453380154027 13784021039028680070231041)
          ·
            refine ⟨10338015779271510052673281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13784021039028680070231041 10338015779271510052673281)
            ·
              refine ⟨7753511834453632539504961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10338015779271510052673281 7753511834453632539504961)
              ·
                refine ⟨5815133875840224404628721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7753511834453632539504961 5815133875840224404628721)
                ·
                  refine ⟨4361350406880168303471541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5815133875840224404628721 4361350406880168303471541)
                  ·
                    refine ⟨408876600645015778450457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4361350406880168303471541 408876600645015778450457)
                    ·
                      rfl

theorem cell23_2388853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2388853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388853 prefixEnd_2388853 := by exact prefixLift 2388853
  have htrace : WordTrace (prefixWord ++ tailWord_2388853) baseStart_2388853 baseEnd_2388853 := by
    simpa [prefixWord, tailWord_2388853, baseEnd_2388853] using wordTrace_append hprefix tailTrace_2388853
  have hstable : (prefixWord ++ tailWord_2388853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388853).length < 2 ^ (prefixWord ++ tailWord_2388853).sum := by decide
  have hdescent : baseEnd_2388853 < baseStart_2388853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388856 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_2388856 : Nat := 118140960795 + 2388856 * 2 ^ 59
def prefixEnd_2388856 : Nat := 4983230072969 + 3 ^ 40 * 2388856 * 2
def baseEnd_2388856 : Nat := 1226631342377010823613857

theorem tailTrace_2388856 : CollatzResearch.WordTrace tailWord_2388856 prefixEnd_2388856 1226631342377010823613857 := by
  unfold tailWord_2388856
  simp only [CollatzResearch.WordTrace]
  refine ⟨43564368116795085484317211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58085824155726780645756281 43564368116795085484317211)
  ·
    refine ⟨65346552175192628226475817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43564368116795085484317211 65346552175192628226475817)
    ·
      refine ⟨49009914131394471169856863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65346552175192628226475817 49009914131394471169856863)
      ·
        refine ⟨73514871197091706754785295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49009914131394471169856863 73514871197091706754785295)
        ·
          refine ⟨110272306795637560132177943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73514871197091706754785295 110272306795637560132177943)
          ·
            refine ⟨165408460193456340198266915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110272306795637560132177943 165408460193456340198266915)
            ·
              refine ⟨248112690290184510297400373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165408460193456340198266915 248112690290184510297400373)
              ·
                refine ⟨23260564714704797840381285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 248112690290184510297400373 23260564714704797840381285)
                ·
                  refine ⟨4361355884007149595071491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23260564714704797840381285 4361355884007149595071491)
                  ·
                    refine ⟨6542033826010724392607237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4361355884007149595071491 6542033826010724392607237)
                    ·
                      refine ⟨1226631342377010823613857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6542033826010724392607237 1226631342377010823613857)
                      ·
                        rfl

theorem cell23_2388856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_2388856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388856 prefixEnd_2388856 := by exact prefixLift 2388856
  have htrace : WordTrace (prefixWord ++ tailWord_2388856) baseStart_2388856 baseEnd_2388856 := by
    simpa [prefixWord, tailWord_2388856, baseEnd_2388856] using wordTrace_append hprefix tailTrace_2388856
  have hstable : (prefixWord ++ tailWord_2388856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388856).length < 2 ^ (prefixWord ++ tailWord_2388856).sum := by decide
  have hdescent : baseEnd_2388856 < baseStart_2388856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388873 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 1, 6, 2]
def baseStart_2388873 : Nat := 118140960795 + 2388873 * 2 ^ 59
def prefixEnd_2388873 : Nat := 4983230072969 + 3 ^ 40 * 2388873 * 2
def baseEnd_2388873 : Nat := 1226640071548137257101279

theorem tailTrace_2388873 : CollatzResearch.WordTrace tailWord_2388873 prefixEnd_2388873 1226640071548137257101279 := by
  unfold tailWord_2388873
  simp only [CollatzResearch.WordTrace]
  refine ⟨87129356274528582872003273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58086237516352388581335515 87129356274528582872003273)
  ·
    refine ⟨65347017205896437154002455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87129356274528582872003273 65347017205896437154002455)
    ·
      refine ⟨98020525808844655731003683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65347017205896437154002455 98020525808844655731003683)
      ·
        refine ⟨147030788713266983596505525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98020525808844655731003683 147030788713266983596505525)
        ·
          refine ⟨13784136441868779712172393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147030788713266983596505525 13784136441868779712172393)
          ·
            refine ⟨10338102331401584784129295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13784136441868779712172393 10338102331401584784129295)
            ·
              refine ⟨15507153497102377176193943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10338102331401584784129295 15507153497102377176193943)
              ·
                refine ⟨23260730245653565764290915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15507153497102377176193943 23260730245653565764290915)
                ·
                  refine ⟨34891095368480348646436373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23260730245653565764290915 34891095368480348646436373)
                  ·
                    refine ⟨1635520095397516342801705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34891095368480348646436373 1635520095397516342801705)
                    ·
                      refine ⟨1226640071548137257101279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635520095397516342801705 1226640071548137257101279)
                      ·
                        rfl

theorem cell23_2388873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 6, 2].length) (baseStart_2388873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388873 prefixEnd_2388873 := by exact prefixLift 2388873
  have htrace : WordTrace (prefixWord ++ tailWord_2388873) baseStart_2388873 baseEnd_2388873 := by
    simpa [prefixWord, tailWord_2388873, baseEnd_2388873] using wordTrace_append hprefix tailTrace_2388873
  have hstable : (prefixWord ++ tailWord_2388873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388873).length < 2 ^ (prefixWord ++ tailWord_2388873).sum := by decide
  have hdescent : baseEnd_2388873 < baseStart_2388873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388893 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_2388893 : Nat := 118140960795 + 2388893 * 2 ^ 59
def prefixEnd_2388893 : Nat := 4983230072969 + 3 ^ 40 * 2388893 * 2
def baseEnd_2388893 : Nat := 1226650341161227178851187

theorem tailTrace_2388893 : CollatzResearch.WordTrace tailWord_2388893 prefixEnd_2388893 1226650341161227178851187 := by
  unfold tailWord_2388893
  simp only [CollatzResearch.WordTrace]
  refine ⟨87130085734456126287731333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58086723822970750858487555 87130085734456126287731333)
  ·
    refine ⟨16336891075210523678949625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87130085734456126287731333 16336891075210523678949625)
    ·
      refine ⟨12252668306407892759212219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16336891075210523678949625 12252668306407892759212219)
      ·
        refine ⟨18379002459611839138818329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12252668306407892759212219 18379002459611839138818329)
        ·
          refine ⟨13784251844708879354113747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18379002459611839138818329 13784251844708879354113747)
          ·
            refine ⟨20676377767063319031170621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13784251844708879354113747 20676377767063319031170621)
            ·
              refine ⟨7753641662648744636688983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20676377767063319031170621 7753641662648744636688983)
              ·
                refine ⟨11630462493973116955033475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7753641662648744636688983 11630462493973116955033475)
                ·
                  refine ⟨17445693740959675432550213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11630462493973116955033475 17445693740959675432550213)
                  ·
                    refine ⟨3271067576429939143603165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17445693740959675432550213 3271067576429939143603165)
                    ·
                      refine ⟨1226650341161227178851187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3271067576429939143603165 1226650341161227178851187)
                      ·
                        rfl

theorem cell23_2388893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_2388893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388893 prefixEnd_2388893 := by exact prefixLift 2388893
  have htrace : WordTrace (prefixWord ++ tailWord_2388893) baseStart_2388893 baseEnd_2388893 := by
    simpa [prefixWord, tailWord_2388893, baseEnd_2388893] using wordTrace_append hprefix tailTrace_2388893
  have hstable : (prefixWord ++ tailWord_2388893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388893).length < 2 ^ (prefixWord ++ tailWord_2388893).sum := by decide
  have hdescent : baseEnd_2388893 < baseStart_2388893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388913 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 8]
def baseStart_2388913 : Nat := 118140960795 + 2388913 * 2 ^ 59
def prefixEnd_2388913 : Nat := 4983230072969 + 3 ^ 40 * 2388913 * 2
def baseEnd_2388913 : Nat := 136295623419368566733455

theorem tailTrace_2388913 : CollatzResearch.WordTrace tailWord_2388913 prefixEnd_2388913 136295623419368566733455 := by
  unfold tailWord_2388913
  simp only [CollatzResearch.WordTrace]
  refine ⟨87130815194383669703459393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58087210129589113135639595 87130815194383669703459393)
  ·
    refine ⟨65348111395787752277594545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87130815194383669703459393 65348111395787752277594545)
    ·
      refine ⟨49011083546840814208195909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65348111395787752277594545 49011083546840814208195909)
      ·
        refine ⟨9189578165032652664036733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49011083546840814208195909 9189578165032652664036733)
        ·
          refine ⟨3446091811887244749013775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9189578165032652664036733 3446091811887244749013775)
          ·
            refine ⟨5169137717830867123520663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3446091811887244749013775 5169137717830867123520663)
            ·
              refine ⟨7753706576746300685280995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169137717830867123520663 7753706576746300685280995)
              ·
                refine ⟨11630559865119451027921493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7753706576746300685280995 11630559865119451027921493)
                ·
                  refine ⟨136295623419368566733455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11630559865119451027921493 136295623419368566733455)
                  ·
                    rfl

theorem cell23_2388913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 8].length) (baseStart_2388913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388913 prefixEnd_2388913 := by exact prefixLift 2388913
  have htrace : WordTrace (prefixWord ++ tailWord_2388913) baseStart_2388913 baseEnd_2388913 := by
    simpa [prefixWord, tailWord_2388913, baseEnd_2388913] using wordTrace_append hprefix tailTrace_2388913
  have hstable : (prefixWord ++ tailWord_2388913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388913).length < 2 ^ (prefixWord ++ tailWord_2388913).sum := by decide
  have hdescent : baseEnd_2388913 < baseStart_2388913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388940 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2388940 : Nat := 118140960795 + 2388940 * 2 ^ 59
def prefixEnd_2388940 : Nat := 4983230072969 + 3 ^ 40 * 2388940 * 2
def baseEnd_2388940 : Nat := 1226674474751988494963471

theorem tailTrace_2388940 : CollatzResearch.WordTrace tailWord_2388940 prefixEnd_2388940 1226674474751988494963471 := by
  unfold tailWord_2388940
  simp only [CollatzResearch.WordTrace]
  refine ⟨43565899982642926657346137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58087866643523902209794849 43565899982642926657346137)
  ·
    refine ⟨32674424986982194993009603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43565899982642926657346137 32674424986982194993009603)
    ·
      refine ⟨49011637480473292489514405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32674424986982194993009603 49011637480473292489514405)
      ·
        refine ⟨9189682027588742341783951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49011637480473292489514405 9189682027588742341783951)
        ·
          refine ⟨13784523041383113512675927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9189682027588742341783951 13784523041383113512675927)
          ·
            refine ⟨20676784562074670269013891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13784523041383113512675927 20676784562074670269013891)
            ·
              refine ⟨31015176843112005403520837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20676784562074670269013891 31015176843112005403520837)
              ·
                refine ⟨5815345658083501013160157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31015176843112005403520837 5815345658083501013160157)
                ·
                  refine ⟨2180754621781312879935059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5815345658083501013160157 2180754621781312879935059)
                  ·
                    refine ⟨3271131932671969319902589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2180754621781312879935059 3271131932671969319902589)
                    ·
                      refine ⟨1226674474751988494963471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3271131932671969319902589 1226674474751988494963471)
                      ·
                        rfl

theorem cell23_2388940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2388940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388940 prefixEnd_2388940 := by exact prefixLift 2388940
  have htrace : WordTrace (prefixWord ++ tailWord_2388940) baseStart_2388940 baseEnd_2388940 := by
    simpa [prefixWord, tailWord_2388940, baseEnd_2388940] using wordTrace_append hprefix tailTrace_2388940
  have hstable : (prefixWord ++ tailWord_2388940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388940).length < 2 ^ (prefixWord ++ tailWord_2388940).sum := by decide
  have hdescent : baseEnd_2388940 < baseStart_2388940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388943 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 1, 5]
def baseStart_2388943 : Nat := 118140960795 + 2388943 * 2 ^ 59
def prefixEnd_2388943 : Nat := 4983230072969 + 3 ^ 40 * 2388943 * 2
def baseEnd_2388943 : Nat := 408892005064650661075319

theorem tailTrace_2388943 : CollatzResearch.WordTrace tailWord_2388943 prefixEnd_2388943 408892005064650661075319 := by
  unfold tailWord_2388943
  simp only [CollatzResearch.WordTrace]
  refine ⟨87131909384274984827051483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58087939589516656551367655 87131909384274984827051483)
  ·
    refine ⟨130697864076412477240577225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87131909384274984827051483 130697864076412477240577225)
    ·
      refine ⟨98023398057309357930432919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130697864076412477240577225 98023398057309357930432919)
      ·
        refine ⟨147035097085964036895649379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98023398057309357930432919 147035097085964036895649379)
        ·
          refine ⟨220552645628946055343474069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147035097085964036895649379 220552645628946055343474069)
          ·
            refine ⟨10338405263856846344225347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 220552645628946055343474069 10338405263856846344225347)
            ·
              refine ⟨15507607895785269516338021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10338405263856846344225347 15507607895785269516338021)
              ·
                refine ⟨2907676480459738034313379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15507607895785269516338021 2907676480459738034313379)
                ·
                  refine ⟨4361514720689607051470069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907676480459738034313379 4361514720689607051470069)
                  ·
                    refine ⟨408892005064650661075319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4361514720689607051470069 408892005064650661075319)
                    ·
                      rfl

theorem cell23_2388943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 5].length) (baseStart_2388943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388943 prefixEnd_2388943 := by exact prefixLift 2388943
  have htrace : WordTrace (prefixWord ++ tailWord_2388943) baseStart_2388943 baseEnd_2388943 := by
    simpa [prefixWord, tailWord_2388943, baseEnd_2388943] using wordTrace_append hprefix tailTrace_2388943
  have hstable : (prefixWord ++ tailWord_2388943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388943).length < 2 ^ (prefixWord ++ tailWord_2388943).sum := by decide
  have hdescent : baseEnd_2388943 < baseStart_2388943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388967 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_2388967 : Nat := 118140960795 + 2388967 * 2 ^ 59
def prefixEnd_2388967 : Nat := 4983230072969 + 3 ^ 40 * 2388967 * 2
def baseEnd_2388967 : Nat := 1226688338729659889325847

theorem tailTrace_2388967 : CollatzResearch.WordTrace tailWord_2388967 prefixEnd_2388967 1226688338729659889325847 := by
  unfold tailWord_2388967
  simp only [CollatzResearch.WordTrace]
  refine ⟨87132784736188036925925155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58088523157458691283950103 87132784736188036925925155)
  ·
    refine ⟨130699177104282055388887733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87132784736188036925925155 130699177104282055388887733)
    ·
      refine ⟨12253047853526442692708225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130699177104282055388887733 12253047853526442692708225)
      ·
        refine ⟨9189785890144832019531169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12253047853526442692708225 9189785890144832019531169)
        ·
          refine ⟨6892339417608624014648377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9189785890144832019531169 6892339417608624014648377)
          ·
            refine ⟨5169254563206468010986283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6892339417608624014648377 5169254563206468010986283)
            ·
              refine ⟨7753881844809702016479425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169254563206468010986283 7753881844809702016479425)
              ·
                refine ⟨5815411383607276512359569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7753881844809702016479425 5815411383607276512359569)
                ·
                  refine ⟨4361558537705457384269677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5815411383607276512359569 4361558537705457384269677)
                  ·
                    refine ⟨1635584451639546519101129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4361558537705457384269677 1635584451639546519101129)
                    ·
                      refine ⟨1226688338729659889325847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1635584451639546519101129 1226688338729659889325847)
                      ·
                        rfl

theorem cell23_2388967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_2388967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388967 prefixEnd_2388967 := by exact prefixLift 2388967
  have htrace : WordTrace (prefixWord ++ tailWord_2388967) baseStart_2388967 baseEnd_2388967 := by
    simpa [prefixWord, tailWord_2388967, baseEnd_2388967] using wordTrace_append hprefix tailTrace_2388967
  have hstable : (prefixWord ++ tailWord_2388967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388967).length < 2 ^ (prefixWord ++ tailWord_2388967).sum := by decide
  have hdescent : baseEnd_2388967 < baseStart_2388967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388974 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_2388974 : Nat := 118140960795 + 2388974 * 2 ^ 59
def prefixEnd_2388974 : Nat := 4983230072969 + 3 ^ 40 * 2388974 * 2
def baseEnd_2388974 : Nat := 1226691933094241361938315

theorem tailTrace_2388974 : CollatzResearch.WordTrace tailWord_2388974 prefixEnd_2388974 1226691933094241361938315 := by
  unfold tailWord_2388974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891630005895334640178747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58088693364775118080953317 10891630005895334640178747)
  ·
    refine ⟨16337445008843001960268121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10891630005895334640178747 16337445008843001960268121)
    ·
      refine ⟨12253083756632251470201091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16337445008843001960268121 12253083756632251470201091)
      ·
        refine ⟨18379625634948377205301637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12253083756632251470201091 18379625634948377205301637)
        ·
          refine ⟨3446179806552820725994057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18379625634948377205301637 3446179806552820725994057)
          ·
            refine ⟨2584634854914615544495543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3446179806552820725994057 2584634854914615544495543)
            ·
              refine ⟨3876952282371923316743315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2584634854914615544495543 3876952282371923316743315)
              ·
                refine ⟨5815428423557884975114973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3876952282371923316743315 5815428423557884975114973)
                ·
                  refine ⟨2180785658834206865668115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5815428423557884975114973 2180785658834206865668115)
                  ·
                    refine ⟨3271178488251310298502173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2180785658834206865668115 3271178488251310298502173)
                    ·
                      refine ⟨1226691933094241361938315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3271178488251310298502173 1226691933094241361938315)
                      ·
                        rfl

theorem cell23_2388974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_2388974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2388974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2388974 prefixEnd_2388974 := by exact prefixLift 2388974
  have htrace : WordTrace (prefixWord ++ tailWord_2388974) baseStart_2388974 baseEnd_2388974 := by
    simpa [prefixWord, tailWord_2388974, baseEnd_2388974] using wordTrace_append hprefix tailTrace_2388974
  have hstable : (prefixWord ++ tailWord_2388974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388974).length < 2 ^ (prefixWord ++ tailWord_2388974).sum := by decide
  have hdescent : baseEnd_2388974 < baseStart_2388974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
