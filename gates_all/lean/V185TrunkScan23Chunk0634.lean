import V185TrunkScan23Chunk0633

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3748900 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_3748900 : Nat := 118140960795 + 3748900 * 2 ^ 59
def prefixEnd_3748900 : Nat := 4983230072969 + 3 ^ 40 * 3748900 * 2
def baseEnd_3748900 : Nat := 641662541880162548403043

theorem tailTrace_3748900 : CollatzResearch.WordTrace tailWord_3748900 prefixEnd_3748900 641662541880162548403043 := by
  unfold tailWord_3748900
  simp only [CollatzResearch.WordTrace]
  refine ⟨68366808059191517995658077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91155744078922023994210769 68366808059191517995658077)
  ·
    refine ⟨25637553022196819248371779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68366808059191517995658077 25637553022196819248371779)
    ·
      refine ⟨38456329533295228872557669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25637553022196819248371779 38456329533295228872557669)
      ·
        refine ⟨7210561787492855413604563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38456329533295228872557669 7210561787492855413604563)
        ·
          refine ⟨10815842681239283120406845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7210561787492855413604563 10815842681239283120406845)
          ·
            refine ⟨4055941005464731170152567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10815842681239283120406845 4055941005464731170152567)
            ·
              refine ⟨6083911508197096755228851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055941005464731170152567 6083911508197096755228851)
              ·
                refine ⟨9125867262295645132843277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083911508197096755228851 9125867262295645132843277)
                ·
                  refine ⟨3422200223360866924816229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9125867262295645132843277 3422200223360866924816229)
                  ·
                    refine ⟨641662541880162548403043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3422200223360866924816229 641662541880162548403043)
                    ·
                      rfl

theorem cell23_3748900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_3748900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748900 prefixEnd_3748900 := by exact prefixLift 3748900
  have htrace : WordTrace (prefixWord ++ tailWord_3748900) baseStart_3748900 baseEnd_3748900 := by
    simpa [prefixWord, tailWord_3748900, baseEnd_3748900] using wordTrace_append hprefix tailTrace_3748900
  have hstable : (prefixWord ++ tailWord_3748900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748900).length < 2 ^ (prefixWord ++ tailWord_3748900).sum := by decide
  have hdescent : baseEnd_3748900 < baseStart_3748900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748933 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 2, 3, 2]
def baseStart_3748933 : Nat := 118140960795 + 3748933 * 2 ^ 59
def prefixEnd_3748933 : Nat := 4983230072969 + 3 ^ 40 * 3748933 * 2
def baseEnd_3748933 : Nat := 1925004570502086016096477

theorem tailTrace_3748933 : CollatzResearch.WordTrace tailWord_3748933 prefixEnd_3748933 1925004570502086016096477 := by
  unfold tailWord_3748933
  simp only [CollatzResearch.WordTrace]
  refine ⟨136734819727263482627267453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91156546484842321751511635 136734819727263482627267453)
  ·
    refine ⟨51275557397723805985225295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136734819727263482627267453 51275557397723805985225295)
    ·
      refine ⟨76913336096585708977837943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51275557397723805985225295 76913336096585708977837943)
      ·
        refine ⟨115370004144878563466756915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76913336096585708977837943 115370004144878563466756915)
        ·
          refine ⟨173055006217317845200135373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115370004144878563466756915 173055006217317845200135373)
          ·
            refine ⟨64895627331494191950050765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173055006217317845200135373 64895627331494191950050765)
            ·
              refine ⟨24335860249310321981269037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64895627331494191950050765 24335860249310321981269037)
              ·
                refine ⟨9125947593491370742975889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24335860249310321981269037 9125947593491370742975889)
                ·
                  refine ⟨6844460695118528057231917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9125947593491370742975889 6844460695118528057231917)
                  ·
                    refine ⟨2566672760669448021461969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6844460695118528057231917 2566672760669448021461969)
                    ·
                      refine ⟨1925004570502086016096477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566672760669448021461969 1925004570502086016096477)
                      ·
                        rfl

theorem cell23_3748933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_3748933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748933 prefixEnd_3748933 := by exact prefixLift 3748933
  have htrace : WordTrace (prefixWord ++ tailWord_3748933) baseStart_3748933 baseEnd_3748933 := by
    simpa [prefixWord, tailWord_3748933, baseEnd_3748933] using wordTrace_append hprefix tailTrace_3748933
  have hstable : (prefixWord ++ tailWord_3748933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748933).length < 2 ^ (prefixWord ++ tailWord_3748933).sum := by decide
  have hdescent : baseEnd_3748933 < baseStart_3748933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748940 : List Nat := [2, 2, 1, 3, 1, 1, 1, 7, 1, 1, 3]
def baseStart_3748940 : Nat := 118140960795 + 3748940 * 2 ^ 59
def prefixEnd_3748940 : Nat := 4983230072969 + 3 ^ 40 * 3748940 * 2
def baseEnd_3748940 : Nat := 1925008164866667488708945

theorem tailTrace_3748940 : CollatzResearch.WordTrace tailWord_3748940 prefixEnd_3748940 1925008164866667488708945 := by
  unfold tailWord_3748940
  simp only [CollatzResearch.WordTrace]
  refine ⟨68367537519119061411386137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91156716692158748548514849 68367537519119061411386137)
  ·
    refine ⟨51275653139339296058539603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68367537519119061411386137 51275653139339296058539603)
    ·
      refine ⟨76913479709008944087809405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51275653139339296058539603 76913479709008944087809405)
      ·
        refine ⟨28842554890878354032928527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76913479709008944087809405 28842554890878354032928527)
        ·
          refine ⟨43263832336317531049392791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28842554890878354032928527 43263832336317531049392791)
          ·
            refine ⟨64895748504476296574089187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43263832336317531049392791 64895748504476296574089187)
            ·
              refine ⟨97343622756714444861133781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64895748504476296574089187 97343622756714444861133781)
              ·
                refine ⟨2281491158360494801432823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97343622756714444861133781 2281491158360494801432823)
                ·
                  refine ⟨3422236737540742202149235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281491158360494801432823 3422236737540742202149235)
                  ·
                    refine ⟨5133355106311113303223853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3422236737540742202149235 5133355106311113303223853)
                    ·
                      refine ⟨1925008164866667488708945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5133355106311113303223853 1925008164866667488708945)
                      ·
                        rfl

theorem cell23_3748940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_3748940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748940 prefixEnd_3748940 := by exact prefixLift 3748940
  have htrace : WordTrace (prefixWord ++ tailWord_3748940) baseStart_3748940 baseEnd_3748940 := by
    simpa [prefixWord, tailWord_3748940, baseEnd_3748940] using wordTrace_append hprefix tailTrace_3748940
  have hstable : (prefixWord ++ tailWord_3748940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748940).length < 2 ^ (prefixWord ++ tailWord_3748940).sum := by decide
  have hdescent : baseEnd_3748940 < baseStart_3748940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748956 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3748956 : Nat := 118140960795 + 3748956 * 2 ^ 59
def prefixEnd_3748956 : Nat := 4983230072969 + 3 ^ 40 * 3748956 * 2
def baseEnd_3748956 : Nat := 641672126852379808702957

theorem tailTrace_3748956 : CollatzResearch.WordTrace tailWord_3748956 prefixEnd_3748956 641672126852379808702957 := by
  unfold tailWord_3748956
  simp only [CollatzResearch.WordTrace]
  refine ⟨68367829303090078777677361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91157105737453438370236481 68367829303090078777677361)
  ·
    refine ⟨51275871977317559083258021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68367829303090078777677361 51275871977317559083258021)
    ·
      refine ⟨9614225995747042328110879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51275871977317559083258021 9614225995747042328110879)
      ·
        refine ⟨14421338993620563492166319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9614225995747042328110879 14421338993620563492166319)
        ·
          refine ⟨21632008490430845238249479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14421338993620563492166319 21632008490430845238249479)
          ·
            refine ⟨32448012735646267857374219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21632008490430845238249479 32448012735646267857374219)
            ·
              refine ⟨48672019103469401786061329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32448012735646267857374219 48672019103469401786061329)
              ·
                refine ⟨36504014327602051339545997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48672019103469401786061329 36504014327602051339545997)
                ·
                  refine ⟨13689005372850769252329749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36504014327602051339545997 13689005372850769252329749)
                  ·
                    refine ⟨641672126852379808702957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13689005372850769252329749 641672126852379808702957)
                    ·
                      rfl

theorem cell23_3748956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3748956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748956 prefixEnd_3748956 := by exact prefixLift 3748956
  have htrace : WordTrace (prefixWord ++ tailWord_3748956) baseStart_3748956 baseEnd_3748956 := by
    simpa [prefixWord, tailWord_3748956, baseEnd_3748956] using wordTrace_append hprefix tailTrace_3748956
  have hstable : (prefixWord ++ tailWord_3748956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748956).length < 2 ^ (prefixWord ++ tailWord_3748956).sum := by decide
  have hdescent : baseEnd_3748956 < baseStart_3748956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748973 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_3748973 : Nat := 118140960795 + 3748973 * 2 ^ 59
def prefixEnd_3748973 : Nat := 4983230072969 + 3 ^ 40 * 3748973 * 2
def baseEnd_3748973 : Nat := 641675036576088619865431

theorem tailTrace_3748973 : CollatzResearch.WordTrace tailWord_3748973 prefixEnd_3748973 641675036576088619865431 := by
  unfold tailWord_3748973
  simp only [CollatzResearch.WordTrace]
  refine ⟨136736278647118569458723573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91157519098079046305815715 136736278647118569458723573)
  ·
    refine ⟨12819026123167365886755335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136736278647118569458723573 12819026123167365886755335)
    ·
      refine ⟨19228539184751048830133003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12819026123167365886755335 19228539184751048830133003)
      ·
        refine ⟨28842808777126573245199505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19228539184751048830133003 28842808777126573245199505)
        ·
          refine ⟨21632106582844929933899629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28842808777126573245199505 21632106582844929933899629)
          ·
            refine ⟨8112039968566848725212361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21632106582844929933899629 8112039968566848725212361)
            ·
              refine ⟨6084029976425136543909271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8112039968566848725212361 6084029976425136543909271)
              ·
                refine ⟨9126044964637704815863907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084029976425136543909271 9126044964637704815863907)
                ·
                  refine ⟨13689067446956557223795861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9126044964637704815863907 13689067446956557223795861)
                  ·
                    refine ⟨641675036576088619865431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13689067446956557223795861 641675036576088619865431)
                    ·
                      rfl

theorem cell23_3748973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_3748973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748973 prefixEnd_3748973 := by exact prefixLift 3748973
  have htrace : WordTrace (prefixWord ++ tailWord_3748973) baseStart_3748973 baseEnd_3748973 := by
    simpa [prefixWord, tailWord_3748973, baseEnd_3748973] using wordTrace_append hprefix tailTrace_3748973
  have hstable : (prefixWord ++ tailWord_3748973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748973).length < 2 ^ (prefixWord ++ tailWord_3748973).sum := by decide
  have hdescent : baseEnd_3748973 < baseStart_3748973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748979 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 7]
def baseStart_3748979 : Nat := 118140960795 + 3748979 * 2 ^ 59
def prefixEnd_3748979 : Nat := 4983230072969 + 3 ^ 40 * 3748979 * 2
def baseEnd_3748979 : Nat := 1925028190612192836121265

theorem tailTrace_3748979 : CollatzResearch.WordTrace tailWord_3748979 prefixEnd_3748979 1925028190612192836121265 := by
  unfold tailWord_3748979
  simp only [CollatzResearch.WordTrace]
  refine ⟨136736497485096832483441991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91157664990064554988961327 136736497485096832483441991)
  ·
    refine ⟨205104746227645248725162987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136736497485096832483441991 205104746227645248725162987)
    ·
      refine ⟨307657119341467873087744481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205104746227645248725162987 307657119341467873087744481)
      ·
        refine ⟨230742839506100904815808361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307657119341467873087744481 230742839506100904815808361)
        ·
          refine ⟨173057129629575678611856271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230742839506100904815808361 173057129629575678611856271)
          ·
            refine ⟨259585694444363517917784407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173057129629575678611856271 259585694444363517917784407)
            ·
              refine ⟨389378541666545276876676611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259585694444363517917784407 389378541666545276876676611)
              ·
                refine ⟨584067812499817915315014917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389378541666545276876676611 584067812499817915315014917)
                ·
                  refine ⟨109512714843715859121565297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 584067812499817915315014917 109512714843715859121565297)
                  ·
                    refine ⟨82134536132786894341173973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109512714843715859121565297 82134536132786894341173973)
                    ·
                      refine ⟨1925028190612192836121265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82134536132786894341173973 1925028190612192836121265)
                      ·
                        rfl

theorem cell23_3748979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_3748979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748979 prefixEnd_3748979 := by exact prefixLift 3748979
  have htrace : WordTrace (prefixWord ++ tailWord_3748979) baseStart_3748979 baseEnd_3748979 := by
    simpa [prefixWord, tailWord_3748979, baseEnd_3748979] using wordTrace_append hprefix tailTrace_3748979
  have hstable : (prefixWord ++ tailWord_3748979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748979).length < 2 ^ (prefixWord ++ tailWord_3748979).sum := by decide
  have hdescent : baseEnd_3748979 < baseStart_3748979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748983 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 3]
def baseStart_3748983 : Nat := 118140960795 + 3748983 * 2 ^ 59
def prefixEnd_3748983 : Nat := 4983230072969 + 3 ^ 40 * 3748983 * 2
def baseEnd_3748983 : Nat := 1925030244534810820471247

theorem tailTrace_3748983 : CollatzResearch.WordTrace tailWord_3748983 prefixEnd_3748983 1925030244534810820471247 := by
  unfold tailWord_3748983
  simp only [CollatzResearch.WordTrace]
  refine ⟨136736643377082341166587603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91157762251388227444391735 136736643377082341166587603)
  ·
    refine ⟨205104965065623511749881405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136736643377082341166587603 205104965065623511749881405)
    ·
      refine ⟨76914361899608816906205527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205104965065623511749881405 76914361899608816906205527)
      ·
        refine ⟨115371542849413225359308291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76914361899608816906205527 115371542849413225359308291)
        ·
          refine ⟨173057314274119838038962437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115371542849413225359308291 173057314274119838038962437)
          ·
            refine ⟨32448246426397469632305457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173057314274119838038962437 32448246426397469632305457)
            ·
              refine ⟨24336184819798102224229093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32448246426397469632305457 24336184819798102224229093)
              ·
                refine ⟨4563034653712144167042955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24336184819798102224229093 4563034653712144167042955)
                ·
                  refine ⟨6844551980568216250564433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563034653712144167042955 6844551980568216250564433)
                  ·
                    refine ⟨5133413985426162187923325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6844551980568216250564433 5133413985426162187923325)
                    ·
                      refine ⟨1925030244534810820471247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5133413985426162187923325 1925030244534810820471247)
                      ·
                        rfl

theorem cell23_3748983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_3748983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748983 prefixEnd_3748983 := by exact prefixLift 3748983
  have htrace : WordTrace (prefixWord ++ tailWord_3748983) baseStart_3748983 baseEnd_3748983 := by
    simpa [prefixWord, tailWord_3748983, baseEnd_3748983] using wordTrace_append hprefix tailTrace_3748983
  have hstable : (prefixWord ++ tailWord_3748983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748983).length < 2 ^ (prefixWord ++ tailWord_3748983).sum := by decide
  have hdescent : baseEnd_3748983 < baseStart_3748983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748993 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3748993 : Nat := 118140960795 + 3748993 * 2 ^ 59
def prefixEnd_3748993 : Nat := 4983230072969 + 3 ^ 40 * 3748993 * 2
def baseEnd_3748993 : Nat := 1925035379341355781346201

theorem tailTrace_3748993 : CollatzResearch.WordTrace tailWord_3748993 prefixEnd_3748993 1925035379341355781346201 := by
  unfold tailWord_3748993
  simp only [CollatzResearch.WordTrace]
  refine ⟨136737008107046112874451633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91158005404697408582967755 136737008107046112874451633)
  ·
    refine ⟨102552756080284584655838725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136737008107046112874451633 102552756080284584655838725)
    ·
      refine ⟨19228641765053359622969761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102552756080284584655838725 19228641765053359622969761)
      ·
        refine ⟨14421481323790019717227321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19228641765053359622969761 14421481323790019717227321)
        ·
          refine ⟨10816110992842514787920491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14421481323790019717227321 10816110992842514787920491)
          ·
            refine ⟨16224166489263772181880737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10816110992842514787920491 16224166489263772181880737)
            ·
              refine ⟨12168124866947829136410553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16224166489263772181880737 12168124866947829136410553)
              ·
                refine ⟨9126093650210871852307915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12168124866947829136410553 9126093650210871852307915)
                ·
                  refine ⟨13689140475316307778461873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9126093650210871852307915 13689140475316307778461873)
                  ·
                    refine ⟨10266855356487230833846405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13689140475316307778461873 10266855356487230833846405)
                    ·
                      refine ⟨1925035379341355781346201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10266855356487230833846405 1925035379341355781346201)
                      ·
                        rfl

theorem cell23_3748993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3748993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748993 prefixEnd_3748993 := by exact prefixLift 3748993
  have htrace : WordTrace (prefixWord ++ tailWord_3748993) baseStart_3748993 baseEnd_3748993 := by
    simpa [prefixWord, tailWord_3748993, baseEnd_3748993] using wordTrace_append hprefix tailTrace_3748993
  have hstable : (prefixWord ++ tailWord_3748993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748993).length < 2 ^ (prefixWord ++ tailWord_3748993).sum := by decide
  have hdescent : baseEnd_3748993 < baseStart_3748993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748997 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 1, 1, 4]
def baseStart_3748997 : Nat := 118140960795 + 3748997 * 2 ^ 59
def prefixEnd_3748997 : Nat := 4983230072969 + 3 ^ 40 * 3748997 * 2
def baseEnd_3748997 : Nat := 1925037433263973765696183

theorem tailTrace_3748997 : CollatzResearch.WordTrace tailWord_3748997 prefixEnd_3748997 1925037433263973765696183 := by
  unfold tailWord_3748997
  simp only [CollatzResearch.WordTrace]
  refine ⟨136737153999031621557597245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91158102666021081038398163 136737153999031621557597245)
  ·
    refine ⟨51276432749636858084098967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136737153999031621557597245 51276432749636858084098967)
    ·
      refine ⟨76914649124455287126148451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51276432749636858084098967 76914649124455287126148451)
      ·
        refine ⟨115371973686682930689222677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76914649124455287126148451 115371973686682930689222677)
        ·
          refine ⟨5408061266563262376057313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115371973686682930689222677 5408061266563262376057313)
          ·
            refine ⟨4056045949922446782042985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5408061266563262376057313 4056045949922446782042985)
            ·
              refine ⟨3042034462441835086532239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4056045949922446782042985 3042034462441835086532239)
              ·
                refine ⟨4563051693662752629798359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042034462441835086532239 4563051693662752629798359)
                ·
                  refine ⟨6844577540494128944697539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563051693662752629798359 6844577540494128944697539)
                  ·
                    refine ⟨10266866310741193417046309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6844577540494128944697539 10266866310741193417046309)
                    ·
                      refine ⟨1925037433263973765696183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10266866310741193417046309 1925037433263973765696183)
                      ·
                        rfl

theorem cell23_3748997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_3748997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748997 prefixEnd_3748997 := by exact prefixLift 3748997
  have htrace : WordTrace (prefixWord ++ tailWord_3748997) baseStart_3748997 baseEnd_3748997 := by
    simpa [prefixWord, tailWord_3748997, baseEnd_3748997] using wordTrace_append hprefix tailTrace_3748997
  have hstable : (prefixWord ++ tailWord_3748997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748997).length < 2 ^ (prefixWord ++ tailWord_3748997).sum := by decide
  have hdescent : baseEnd_3748997 < baseStart_3748997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749037 : List Nat := [1, 5, 2, 1, 4, 1, 2, 7]
def baseStart_3749037 : Nat := 118140960795 + 3749037 * 2 ^ 59
def prefixEnd_3749037 : Nat := 4983230072969 + 3 ^ 40 * 3749037 * 2
def baseEnd_3749037 : Nat := 71298443425561244785037

theorem tailTrace_3749037 : CollatzResearch.WordTrace tailWord_3749037 prefixEnd_3749037 71298443425561244785037 := by
  unfold tailWord_3749037
  simp only [CollatzResearch.WordTrace]
  refine ⟨136738612918886708389053365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91159075279257805592702243 136738612918886708389053365)
  ·
    refine ⟨12819244961145628911473753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136738612918886708389053365 12819244961145628911473753)
    ·
      refine ⟨9614433720859221683605315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12819244961145628911473753 9614433720859221683605315)
      ·
        refine ⟨14421650581288832525407973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9614433720859221683605315 14421650581288832525407973)
        ·
          refine ⟨2704059483991656098513995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14421650581288832525407973 2704059483991656098513995)
          ·
            refine ⟨4056089225987484147770993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704059483991656098513995 4056089225987484147770993)
            ·
              refine ⟨3042066919490613110828245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4056089225987484147770993 3042066919490613110828245)
              ·
                refine ⟨71298443425561244785037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3042066919490613110828245 71298443425561244785037)
                ·
                  rfl

theorem cell23_3749037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 7].length) (baseStart_3749037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749037 prefixEnd_3749037 := by exact prefixLift 3749037
  have htrace : WordTrace (prefixWord ++ tailWord_3749037) baseStart_3749037 baseEnd_3749037 := by
    simpa [prefixWord, tailWord_3749037, baseEnd_3749037] using wordTrace_append hprefix tailTrace_3749037
  have hstable : (prefixWord ++ tailWord_3749037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749037).length < 2 ^ (prefixWord ++ tailWord_3749037).sum := by decide
  have hdescent : baseEnd_3749037 < baseStart_3749037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749110 : List Nat := [5, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_3749110 : Nat := 118140960795 + 3749110 * 2 ^ 59
def prefixEnd_3749110 : Nat := 4983230072969 + 3 ^ 40 * 3749110 * 2
def baseEnd_3749110 : Nat := 213899495175325758175907

theorem tailTrace_3749110 : CollatzResearch.WordTrace tailWord_3749110 prefixEnd_3749110 213899495175325758175907 := by
  unfold tailWord_3749110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8546329715476390116028799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91160850298414827904307189 8546329715476390116028799)
  ·
    refine ⟨12819494573214585174043199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8546329715476390116028799 12819494573214585174043199)
    ·
      refine ⟨19229241859821877761064799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12819494573214585174043199 19229241859821877761064799)
      ·
        refine ⟨28843862789732816641597199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19229241859821877761064799 28843862789732816641597199)
        ·
          refine ⟨43265794184599224962395799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28843862789732816641597199 43265794184599224962395799)
          ·
            refine ⟨64898691276898837443593699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43265794184599224962395799 64898691276898837443593699)
            ·
              refine ⟨97348036915348256165390549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64898691276898837443593699 97348036915348256165390549)
              ·
                refine ⟨2281594615203474753876341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97348036915348256165390549 2281594615203474753876341)
                ·
                  refine ⟨213899495175325758175907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2281594615203474753876341 213899495175325758175907)
                  ·
                    rfl

theorem cell23_3749110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_3749110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749110 prefixEnd_3749110 := by exact prefixLift 3749110
  have htrace : WordTrace (prefixWord ++ tailWord_3749110) baseStart_3749110 baseEnd_3749110 := by
    simpa [prefixWord, tailWord_3749110, baseEnd_3749110] using wordTrace_append hprefix tailTrace_3749110
  have hstable : (prefixWord ++ tailWord_3749110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749110).length < 2 ^ (prefixWord ++ tailWord_3749110).sum := by decide
  have hdescent : baseEnd_3749110 < baseStart_3749110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749123 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 2, 5]
def baseStart_3749123 : Nat := 118140960795 + 3749123 * 2 ^ 59
def prefixEnd_3749123 : Nat := 4983230072969 + 3 ^ 40 * 3749123 * 2
def baseEnd_3749123 : Nat := 641700710608813424240201

theorem tailTrace_3749123 : CollatzResearch.WordTrace tailWord_3749123 prefixEnd_3749123 641700710608813424240201 := by
  unfold tailWord_3749123
  simp only [CollatzResearch.WordTrace]
  refine ⟨136741749596575145076684023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91161166397716763384456015 136741749596575145076684023)
  ·
    refine ⟨205112624394862717615026035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136741749596575145076684023 205112624394862717615026035)
    ·
      refine ⟨307668936592294076422539053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205112624394862717615026035 307668936592294076422539053)
      ·
        refine ⟨115375851222110278658452145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307668936592294076422539053 115375851222110278658452145)
        ·
          refine ⟨86531888416582708993839109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115375851222110278658452145 86531888416582708993839109)
          ·
            refine ⟨16224729078109257936344833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86531888416582708993839109 16224729078109257936344833)
            ·
              refine ⟨12168546808581943452258625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16224729078109257936344833 12168546808581943452258625)
              ·
                refine ⟨9126410106436457589193969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12168546808581943452258625 9126410106436457589193969)
                ·
                  refine ⟨6844807579827343191895477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9126410106436457589193969 6844807579827343191895477)
                  ·
                    refine ⟨641700710608813424240201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6844807579827343191895477 641700710608813424240201)
                    ·
                      rfl

theorem cell23_3749123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 5].length) (baseStart_3749123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749123 prefixEnd_3749123 := by exact prefixLift 3749123
  have htrace : WordTrace (prefixWord ++ tailWord_3749123) baseStart_3749123 baseEnd_3749123 := by
    simpa [prefixWord, tailWord_3749123, baseEnd_3749123] using wordTrace_append hprefix tailTrace_3749123
  have hstable : (prefixWord ++ tailWord_3749123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749123).length < 2 ^ (prefixWord ++ tailWord_3749123).sum := by decide
  have hdescent : baseEnd_3749123 < baseStart_3749123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749143 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3749143 : Nat := 118140960795 + 3749143 * 2 ^ 59
def prefixEnd_3749143 : Nat := 4983230072969 + 3 ^ 40 * 3749143 * 2
def baseEnd_3749143 : Nat := 1925112401439530194470511

theorem tailTrace_3749143 : CollatzResearch.WordTrace tailWord_3749143 prefixEnd_3749143 1925112401439530194470511 := by
  unfold tailWord_3749143
  simp only [CollatzResearch.WordTrace]
  refine ⟨136742479056502688492412083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91161652704335125661608055 136742479056502688492412083)
  ·
    refine ⟨205113718584754032738618125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136742479056502688492412083 205113718584754032738618125)
    ·
      refine ⟨76917644469282762276981797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205113718584754032738618125 76917644469282762276981797)
      ·
        refine ⟨14422058337990517926934087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76917644469282762276981797 14422058337990517926934087)
        ·
          refine ⟨21633087506985776890401131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14422058337990517926934087 21633087506985776890401131)
          ·
            refine ⟨32449631260478665335601697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21633087506985776890401131 32449631260478665335601697)
            ·
              refine ⟨24337223445358999001701273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32449631260478665335601697 24337223445358999001701273)
              ·
                refine ⟨18252917584019249251275955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24337223445358999001701273 18252917584019249251275955)
                ·
                  refine ⟨27379376376028873876913933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18252917584019249251275955 27379376376028873876913933)
                  ·
                    refine ⟨10267266141010827703842725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27379376376028873876913933 10267266141010827703842725)
                    ·
                      refine ⟨1925112401439530194470511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10267266141010827703842725 1925112401439530194470511)
                      ·
                        rfl

theorem cell23_3749143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3749143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749143 prefixEnd_3749143 := by exact prefixLift 3749143
  have htrace : WordTrace (prefixWord ++ tailWord_3749143) baseStart_3749143 baseEnd_3749143 := by
    simpa [prefixWord, tailWord_3749143, baseEnd_3749143] using wordTrace_append hprefix tailTrace_3749143
  have hstable : (prefixWord ++ tailWord_3749143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749143).length < 2 ^ (prefixWord ++ tailWord_3749143).sum := by decide
  have hdescent : baseEnd_3749143 < baseStart_3749143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749160 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3749160 : Nat := 118140960795 + 3749160 * 2 ^ 59
def prefixEnd_3749160 : Nat := 4983230072969 + 3 ^ 40 * 3749160 * 2
def baseEnd_3749160 : Nat := 1925121130610656627957933

theorem tailTrace_3749160 : CollatzResearch.WordTrace tailWord_3749160 prefixEnd_3749160 1925121130610656627957933 := by
  unfold tailWord_3749160
  simp only [CollatzResearch.WordTrace]
  refine ⟨68371549548720550197890467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91162066064960733597187289 68371549548720550197890467)
  ·
    refine ⟨102557324323080825296835701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68371549548720550197890467 102557324323080825296835701)
    ·
      refine ⟨9614749155288827371578347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102557324323080825296835701 9614749155288827371578347)
      ·
        refine ⟨14422123732933241057367521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9614749155288827371578347 14422123732933241057367521)
        ·
          refine ⟨10816592799699930793025641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14422123732933241057367521 10816592799699930793025641)
          ·
            refine ⟨8112444599774948094769231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10816592799699930793025641 8112444599774948094769231)
            ·
              refine ⟨12168666899662422142153847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8112444599774948094769231 12168666899662422142153847)
              ·
                refine ⟨18253000349493633213230771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12168666899662422142153847 18253000349493633213230771)
                ·
                  refine ⟨27379500524240449819846157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18253000349493633213230771 27379500524240449819846157)
                  ·
                    refine ⟨10267312696590168682442309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27379500524240449819846157 10267312696590168682442309)
                    ·
                      refine ⟨1925121130610656627957933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10267312696590168682442309 1925121130610656627957933)
                      ·
                        rfl

theorem cell23_3749160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3749160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749160 prefixEnd_3749160 := by exact prefixLift 3749160
  have htrace : WordTrace (prefixWord ++ tailWord_3749160) baseStart_3749160 baseEnd_3749160 := by
    simpa [prefixWord, tailWord_3749160, baseEnd_3749160] using wordTrace_append hprefix tailTrace_3749160
  have hstable : (prefixWord ++ tailWord_3749160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749160).length < 2 ^ (prefixWord ++ tailWord_3749160).sum := by decide
  have hdescent : baseEnd_3749160 < baseStart_3749160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749163 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 3]
def baseStart_3749163 : Nat := 118140960795 + 3749163 * 2 ^ 59
def prefixEnd_3749163 : Nat := 4983230072969 + 3 ^ 40 * 3749163 * 2
def baseEnd_3749163 : Nat := 1925122671052620116220419

theorem tailTrace_3749163 : CollatzResearch.WordTrace tailWord_3749163 prefixEnd_3749163 1925122671052620116220419 := by
  unfold tailWord_3749163
  simp only [CollatzResearch.WordTrace]
  refine ⟨136743208516430231908140143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91162139010953487938760095 136743208516430231908140143)
  ·
    refine ⟨205114812774645347862210215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136743208516430231908140143 205114812774645347862210215)
    ·
      refine ⟨307672219161968021793315323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205114812774645347862210215 307672219161968021793315323)
      ·
        refine ⟨461508328742952032689972985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307672219161968021793315323 461508328742952032689972985)
        ·
          refine ⟨346131246557214024517479739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461508328742952032689972985 346131246557214024517479739)
          ·
            refine ⟨519196869835821036776219609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346131246557214024517479739 519196869835821036776219609)
            ·
              refine ⟨389397652376865777582164707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519196869835821036776219609 389397652376865777582164707)
              ·
                refine ⟨584096478565298666373247061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389397652376865777582164707 584096478565298666373247061)
                ·
                  refine ⟨6844880608187093746561489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 584096478565298666373247061 6844880608187093746561489)
                  ·
                    refine ⟨5133660456140320309921117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6844880608187093746561489 5133660456140320309921117)
                    ·
                      refine ⟨1925122671052620116220419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5133660456140320309921117 1925122671052620116220419)
                      ·
                        rfl

theorem cell23_3749163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 3].length) (baseStart_3749163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749163 prefixEnd_3749163 := by exact prefixLift 3749163
  have htrace : WordTrace (prefixWord ++ tailWord_3749163) baseStart_3749163 baseEnd_3749163 := by
    simpa [prefixWord, tailWord_3749163, baseEnd_3749163] using wordTrace_append hprefix tailTrace_3749163
  have hstable : (prefixWord ++ tailWord_3749163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749163).length < 2 ^ (prefixWord ++ tailWord_3749163).sum := by decide
  have hdescent : baseEnd_3749163 < baseStart_3749163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749173 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3749173 : Nat := 118140960795 + 3749173 * 2 ^ 59
def prefixEnd_3749173 : Nat := 4983230072969 + 3 ^ 40 * 3749173 * 2
def baseEnd_3749173 : Nat := 1925127805859165077095373

theorem tailTrace_3749173 : CollatzResearch.WordTrace tailWord_3749173 prefixEnd_3749173 1925127805859165077095373 := by
  unfold tailWord_3749173
  simp only [CollatzResearch.WordTrace]
  refine ⟨136743573246394003616004173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91162382164262669077336115 136743573246394003616004173)
  ·
    refine ⟨51278839967397751356001565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136743573246394003616004173 51278839967397751356001565)
    ·
      refine ⟨19229564987774156758500587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51278839967397751356001565 19229564987774156758500587)
      ·
        refine ⟨28844347481661235137750881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19229564987774156758500587 28844347481661235137750881)
        ·
          refine ⟨21633260611245926353313161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28844347481661235137750881 21633260611245926353313161)
          ·
            refine ⟨16224945458434444764984871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21633260611245926353313161 16224945458434444764984871)
            ·
              refine ⟨24337418187651667147477307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16224945458434444764984871 24337418187651667147477307)
              ·
                refine ⟨36506127281477500721215961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24337418187651667147477307 36506127281477500721215961)
                ·
                  refine ⟨27379595461108125540911971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36506127281477500721215961 27379595461108125540911971)
                  ·
                    refine ⟨41069393191662188311367957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27379595461108125540911971 41069393191662188311367957)
                    ·
                      refine ⟨1925127805859165077095373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41069393191662188311367957 1925127805859165077095373)
                      ·
                        rfl

theorem cell23_3749173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3749173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749173 prefixEnd_3749173 := by exact prefixLift 3749173
  have htrace : WordTrace (prefixWord ++ tailWord_3749173) baseStart_3749173 baseEnd_3749173 := by
    simpa [prefixWord, tailWord_3749173, baseEnd_3749173] using wordTrace_append hprefix tailTrace_3749173
  have hstable : (prefixWord ++ tailWord_3749173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749173).length < 2 ^ (prefixWord ++ tailWord_3749173).sum := by decide
  have hdescent : baseEnd_3749173 < baseStart_3749173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749183 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 8]
def baseStart_3749183 : Nat := 118140960795 + 3749183 * 2 ^ 59
def prefixEnd_3749183 : Nat := 4983230072969 + 3 ^ 40 * 3749183 * 2
def baseEnd_3749183 : Nat := 213903660073967781996703

theorem tailTrace_3749183 : CollatzResearch.WordTrace tailWord_3749183 prefixEnd_3749183 213903660073967781996703 := by
  unfold tailWord_3749183
  simp only [CollatzResearch.WordTrace]
  refine ⟨136743937976357775323868203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91162625317571850215912135 136743937976357775323868203)
  ·
    refine ⟨205115906964536662985802305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136743937976357775323868203 205115906964536662985802305)
    ·
      refine ⟨153836930223402497239351729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205115906964536662985802305 153836930223402497239351729)
      ·
        refine ⟨115377697667551872929513797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153836930223402497239351729 115377697667551872929513797)
        ·
          refine ⟨21633318312665976174283837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115377697667551872929513797 21633318312665976174283837)
          ·
            refine ⟨8112494367249741065356439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21633318312665976174283837 8112494367249741065356439)
            ·
              refine ⟨12168741550874611598034659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8112494367249741065356439 12168741550874611598034659)
              ·
                refine ⟨18253112326311917397051989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12168741550874611598034659 18253112326311917397051989)
                ·
                  refine ⟨213903660073967781996703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18253112326311917397051989 213903660073967781996703)
                  ·
                    rfl

theorem cell23_3749183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 8].length) (baseStart_3749183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749183 prefixEnd_3749183 := by exact prefixLift 3749183
  have htrace : WordTrace (prefixWord ++ tailWord_3749183) baseStart_3749183 baseEnd_3749183 := by
    simpa [prefixWord, tailWord_3749183, baseEnd_3749183] using wordTrace_append hprefix tailTrace_3749183
  have hstable : (prefixWord ++ tailWord_3749183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749183).length < 2 ^ (prefixWord ++ tailWord_3749183).sum := by decide
  have hdescent : baseEnd_3749183 < baseStart_3749183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749200 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 6]
def baseStart_3749200 : Nat := 118140960795 + 3749200 * 2 ^ 59
def prefixEnd_3749200 : Nat := 4983230072969 + 3 ^ 40 * 3749200 * 2
def baseEnd_3749200 : Nat := 213904629981870719050861

theorem tailTrace_3749200 : CollatzResearch.WordTrace tailWord_3749200 prefixEnd_3749200 213904629981870719050861 := by
  unfold tailWord_3749200
  simp only [CollatzResearch.WordTrace]
  refine ⟨68372279008648093613618527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91163038678197458151491369 68372279008648093613618527)
  ·
    refine ⟨102558418512972140420427791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68372279008648093613618527 102558418512972140420427791)
    ·
      refine ⟨153837627769458210630641687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102558418512972140420427791 153837627769458210630641687)
      ·
        refine ⟨230756441654187315945962531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153837627769458210630641687 230756441654187315945962531)
        ·
          refine ⟨346134662481280973918943797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230756441654187315945962531 346134662481280973918943797)
          ·
            refine ⟨32450124607620091304900981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 346134662481280973918943797 32450124607620091304900981)
            ·
              refine ⟨3042199181964383559834467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32450124607620091304900981 3042199181964383559834467)
              ·
                refine ⟨4563298772946575339751701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042199181964383559834467 4563298772946575339751701)
                ·
                  refine ⟨213904629981870719050861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4563298772946575339751701 213904629981870719050861)
                  ·
                    rfl

theorem cell23_3749200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 6].length) (baseStart_3749200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749200 prefixEnd_3749200 := by exact prefixLift 3749200
  have htrace : WordTrace (prefixWord ++ tailWord_3749200) baseStart_3749200 baseEnd_3749200 := by
    simpa [prefixWord, tailWord_3749200, baseEnd_3749200] using wordTrace_append hprefix tailTrace_3749200
  have hstable : (prefixWord ++ tailWord_3749200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749200).length < 2 ^ (prefixWord ++ tailWord_3749200).sum := by decide
  have hdescent : baseEnd_3749200 < baseStart_3749200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749273 : List Nat := [1, 2, 1, 2, 1, 5, 2, 9]
def baseStart_3749273 : Nat := 118140960795 + 3749273 * 2 ^ 59
def prefixEnd_3749273 : Nat := 4983230072969 + 3 ^ 40 * 3749273 * 2
def baseEnd_3749273 : Nat := 71302931626837580957219

theorem tailTrace_3749273 : CollatzResearch.WordTrace tailWord_3749273 prefixEnd_3749273 71302931626837580957219 := by
  unfold tailWord_3749273
  simp only [CollatzResearch.WordTrace]
  refine ⟨136747220546031720694644473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91164813697354480463096315 136747220546031720694644473)
  ·
    refine ⟨102560415409523790520983355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136747220546031720694644473 102560415409523790520983355)
    ·
      refine ⟨153840623114285685781475033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102560415409523790520983355 153840623114285685781475033)
      ·
        refine ⟨115380467335714264336106275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153840623114285685781475033 115380467335714264336106275)
        ·
          refine ⟨173070701003571396504159413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115380467335714264336106275 173070701003571396504159413)
          ·
            refine ⟨16225378219084818422264945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173070701003571396504159413 16225378219084818422264945)
            ·
              refine ⟨12169033664313613816698709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16225378219084818422264945 12169033664313613816698709)
              ·
                refine ⟨71302931626837580957219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12169033664313613816698709 71302931626837580957219)
                ·
                  rfl

theorem cell23_3749273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 9].length) (baseStart_3749273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749273 prefixEnd_3749273 := by exact prefixLift 3749273
  have htrace : WordTrace (prefixWord ++ tailWord_3749273) baseStart_3749273 baseEnd_3749273 := by
    simpa [prefixWord, tailWord_3749273, baseEnd_3749273] using wordTrace_append hprefix tailTrace_3749273
  have hstable : (prefixWord ++ tailWord_3749273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749273).length < 2 ^ (prefixWord ++ tailWord_3749273).sum := by decide
  have hdescent : baseEnd_3749273 < baseStart_3749273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749280 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_3749280 : Nat := 118140960795 + 3749280 * 2 ^ 59
def prefixEnd_3749280 : Nat := 4983230072969 + 3 ^ 40 * 3749280 * 2
def baseEnd_3749280 : Nat := 1925182748289196158457381

theorem tailTrace_3749280 : CollatzResearch.WordTrace tailWord_3749280 prefixEnd_3749280 1925182748289196158457381 := by
  unfold tailWord_3749280
  simp only [CollatzResearch.WordTrace]
  refine ⟨68373737928503180445074647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91164983904670907260099529 68373737928503180445074647)
  ·
    refine ⟨102560606892754770667611971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68373737928503180445074647 102560606892754770667611971)
    ·
      refine ⟨153840910339132156001417957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102560606892754770667611971 153840910339132156001417957)
      ·
        refine ⟨28845170688587279250265867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153840910339132156001417957 28845170688587279250265867)
        ·
          refine ⟨43267756032880918875398801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28845170688587279250265867 43267756032880918875398801)
          ·
            refine ⟨32450817024660689156549101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43267756032880918875398801 32450817024660689156549101)
            ·
              refine ⟨12169056384247758433705913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32450817024660689156549101 12169056384247758433705913)
              ·
                refine ⟨9126792288185818825279435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12169056384247758433705913 9126792288185818825279435)
                ·
                  refine ⟨13690188432278728237919153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9126792288185818825279435 13690188432278728237919153)
                  ·
                    refine ⟨10267641324209046178439365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13690188432278728237919153 10267641324209046178439365)
                    ·
                      refine ⟨1925182748289196158457381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10267641324209046178439365 1925182748289196158457381)
                      ·
                        rfl

theorem cell23_3749280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_3749280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749280 prefixEnd_3749280 := by exact prefixLift 3749280
  have htrace : WordTrace (prefixWord ++ tailWord_3749280) baseStart_3749280 baseEnd_3749280 := by
    simpa [prefixWord, tailWord_3749280, baseEnd_3749280] using wordTrace_append hprefix tailTrace_3749280
  have hstable : (prefixWord ++ tailWord_3749280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749280).length < 2 ^ (prefixWord ++ tailWord_3749280).sum := by decide
  have hdescent : baseEnd_3749280 < baseStart_3749280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749290 : List Nat := [3, 1, 6, 13]
def baseStart_3749290 : Nat := 118140960795 + 3749290 * 2 ^ 59
def prefixEnd_3749290 : Nat := 4983230072969 + 3 ^ 40 * 3749290 * 2
def baseEnd_3749290 : Nat := 880287097894714732205

theorem tailTrace_3749290 : CollatzResearch.WordTrace tailWord_3749290 prefixEnd_3749290 880287097894714732205 := by
  unfold tailWord_3749290
  simp only [CollatzResearch.WordTrace]
  refine ⟨34186960146742533149503331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91165227057980088398675549 34186960146742533149503331)
  ·
    refine ⟨51280440220113799724254997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34186960146742533149503331 51280440220113799724254997)
    ·
      refine ⟨2403770635317834362074453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51280440220113799724254997 2403770635317834362074453)
      ·
        refine ⟨880287097894714732205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2403770635317834362074453 880287097894714732205)
        ·
          rfl

theorem cell23_3749290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 13].length) (baseStart_3749290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749290 prefixEnd_3749290 := by exact prefixLift 3749290
  have htrace : WordTrace (prefixWord ++ tailWord_3749290) baseStart_3749290 baseEnd_3749290 := by
    simpa [prefixWord, tailWord_3749290, baseEnd_3749290] using wordTrace_append hprefix tailTrace_3749290
  have hstable : (prefixWord ++ tailWord_3749290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749290).length < 2 ^ (prefixWord ++ tailWord_3749290).sum := by decide
  have hdescent : baseEnd_3749290 < baseStart_3749290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749303 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 1, 9]
def baseStart_3749303 : Nat := 118140960795 + 3749303 * 2 ^ 59
def prefixEnd_3749303 : Nat := 4983230072969 + 3 ^ 40 * 3749303 * 2
def baseEnd_3749303 : Nat := 641731519448083189489925

theorem tailTrace_3749303 : CollatzResearch.WordTrace tailWord_3749303 prefixEnd_3749303 641731519448083189489925 := by
  unfold tailWord_3749303
  simp only [CollatzResearch.WordTrace]
  refine ⟨136748314735923035818236563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91165543157282023878824375 136748314735923035818236563)
  ·
    refine ⟨205122472103884553727354845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136748314735923035818236563 205122472103884553727354845)
    ·
      refine ⟨76920927038956707647758067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205122472103884553727354845 76920927038956707647758067)
      ·
        refine ⟨115381390558435061471637101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76920927038956707647758067 115381390558435061471637101)
        ·
          refine ⟨43268021459413148051863913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115381390558435061471637101 43268021459413148051863913)
          ·
            refine ⟨32451016094559861038897935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43268021459413148051863913 32451016094559861038897935)
            ·
              refine ⟨48676524141839791558346903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32451016094559861038897935 48676524141839791558346903)
              ·
                refine ⟨73014786212759687337520355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48676524141839791558346903 73014786212759687337520355)
                ·
                  refine ⟨109522179319139531006280533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73014786212759687337520355 109522179319139531006280533)
                  ·
                    refine ⟨641731519448083189489925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 109522179319139531006280533 641731519448083189489925)
                    ·
                      rfl

theorem cell23_3749303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_3749303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749303 prefixEnd_3749303 := by exact prefixLift 3749303
  have htrace : WordTrace (prefixWord ++ tailWord_3749303) baseStart_3749303 baseEnd_3749303 := by
    simpa [prefixWord, tailWord_3749303, baseEnd_3749303] using wordTrace_append hprefix tailTrace_3749303
  have hstable : (prefixWord ++ tailWord_3749303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749303).length < 2 ^ (prefixWord ++ tailWord_3749303).sum := by decide
  have hdescent : baseEnd_3749303 < baseStart_3749303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749327 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 3, 3, 2]
def baseStart_3749327 : Nat := 118140960795 + 3749327 * 2 ^ 59
def prefixEnd_3749327 : Nat := 4983230072969 + 3 ^ 40 * 3749327 * 2
def baseEnd_3749327 : Nat := 1925206881879957474569665

theorem tailTrace_3749327 : CollatzResearch.WordTrace tailWord_3749327 prefixEnd_3749327 1925206881879957474569665 := by
  unfold tailWord_3749327
  simp only [CollatzResearch.WordTrace]
  refine ⟨136749190087836087917110235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91166126725224058611406823 136749190087836087917110235)
  ·
    refine ⟨205123785131754131875665353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136749190087836087917110235 205123785131754131875665353)
    ·
      refine ⟨153842838848815598906749015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205123785131754131875665353 153842838848815598906749015)
      ·
        refine ⟨230764258273223398360123523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153842838848815598906749015 230764258273223398360123523)
        ·
          refine ⟨346146387409835097540185285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230764258273223398360123523 346146387409835097540185285)
          ·
            refine ⟨64902447639344080788784741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346146387409835097540185285 64902447639344080788784741)
            ·
              refine ⟨12169208932377015147897139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64902447639344080788784741 12169208932377015147897139)
              ·
                refine ⟨18253813398565522721845709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12169208932377015147897139 18253813398565522721845709)
                ·
                  refine ⟨6845180024462071020692141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18253813398565522721845709 6845180024462071020692141)
                  ·
                    refine ⟨2566942509173276632759553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6845180024462071020692141 2566942509173276632759553)
                    ·
                      refine ⟨1925206881879957474569665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566942509173276632759553 1925206881879957474569665)
                      ·
                        rfl

theorem cell23_3749327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 3, 2].length) (baseStart_3749327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749327 prefixEnd_3749327 := by exact prefixLift 3749327
  have htrace : WordTrace (prefixWord ++ tailWord_3749327) baseStart_3749327 baseEnd_3749327 := by
    simpa [prefixWord, tailWord_3749327, baseEnd_3749327] using wordTrace_append hprefix tailTrace_3749327
  have hstable : (prefixWord ++ tailWord_3749327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749327).length < 2 ^ (prefixWord ++ tailWord_3749327).sum := by decide
  have hdescent : baseEnd_3749327 < baseStart_3749327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749334 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3749334 : Nat := 118140960795 + 3749334 * 2 ^ 59
def prefixEnd_3749334 : Nat := 4983230072969 + 3 ^ 40 * 3749334 * 2
def baseEnd_3749334 : Nat := 1925210476244538947182133

theorem tailTrace_3749334 : CollatzResearch.WordTrace tailWord_3749334 prefixEnd_3749334 1925210476244538947182133 := by
  unfold tailWord_3749334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8546840337425670507038441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91166296932540485408410037 8546840337425670507038441)
  ·
    refine ⟨6410130253069252880278831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8546840337425670507038441 6410130253069252880278831)
    ·
      refine ⟨9615195379603879320418247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6410130253069252880278831 9615195379603879320418247)
      ·
        refine ⟨14422793069405818980627371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9615195379603879320418247 14422793069405818980627371)
        ·
          refine ⟨21634189604108728470941057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14422793069405818980627371 21634189604108728470941057)
          ·
            refine ⟨16225642203081546353205793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21634189604108728470941057 16225642203081546353205793)
            ·
              refine ⟨12169231652311159764904345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16225642203081546353205793 12169231652311159764904345)
              ·
                refine ⟨9126923739233369823678259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12169231652311159764904345 9126923739233369823678259)
                ·
                  refine ⟨13690385608850054735517389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9126923739233369823678259 13690385608850054735517389)
                  ·
                    refine ⟨5133894603318770525819021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13690385608850054735517389 5133894603318770525819021)
                    ·
                      refine ⟨1925210476244538947182133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5133894603318770525819021 1925210476244538947182133)
                      ·
                        rfl

theorem cell23_3749334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3749334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749334 prefixEnd_3749334 := by exact prefixLift 3749334
  have htrace : WordTrace (prefixWord ++ tailWord_3749334) baseStart_3749334 baseEnd_3749334 := by
    simpa [prefixWord, tailWord_3749334, baseEnd_3749334] using wordTrace_append hprefix tailTrace_3749334
  have hstable : (prefixWord ++ tailWord_3749334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749334).length < 2 ^ (prefixWord ++ tailWord_3749334).sum := by decide
  have hdescent : baseEnd_3749334 < baseStart_3749334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749351 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3749351 : Nat := 118140960795 + 3749351 * 2 ^ 59
def prefixEnd_3749351 : Nat := 4983230072969 + 3 ^ 40 * 3749351 * 2
def baseEnd_3749351 : Nat := 1925219205415665380669555

theorem tailTrace_3749351 : CollatzResearch.WordTrace tailWord_3749351 prefixEnd_3749351 1925219205415665380669555 := by
  unfold tailWord_3749351
  simp only [CollatzResearch.WordTrace]
  refine ⟨136750065439749140015983907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91166710293166093343989271 136750065439749140015983907)
  ·
    refine ⟨205125098159623710023975861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136750065439749140015983907 205125098159623710023975861)
    ·
      refine ⟨19230477952464722814747737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205125098159623710023975861 19230477952464722814747737)
      ·
        refine ⟨14422858464348542111060803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19230477952464722814747737 14422858464348542111060803)
        ·
          refine ⟨21634287696522813166591205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14422858464348542111060803 21634287696522813166591205)
          ·
            refine ⟨4056428943098027468735851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21634287696522813166591205 4056428943098027468735851)
            ·
              refine ⟨6084643414647041203103777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056428943098027468735851 6084643414647041203103777)
              ·
                refine ⟨4563482560985280902327833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6084643414647041203103777 4563482560985280902327833)
                ·
                  refine ⟨3422611920738960676745875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4563482560985280902327833 3422611920738960676745875)
                  ·
                    refine ⟨5133917881108441015118813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3422611920738960676745875 5133917881108441015118813)
                    ·
                      refine ⟨1925219205415665380669555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5133917881108441015118813 1925219205415665380669555)
                      ·
                        rfl

theorem cell23_3749351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3749351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749351 prefixEnd_3749351 := by exact prefixLift 3749351
  have htrace : WordTrace (prefixWord ++ tailWord_3749351) baseStart_3749351 baseEnd_3749351 := by
    simpa [prefixWord, tailWord_3749351, baseEnd_3749351] using wordTrace_append hprefix tailTrace_3749351
  have hstable : (prefixWord ++ tailWord_3749351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749351).length < 2 ^ (prefixWord ++ tailWord_3749351).sum := by decide
  have hdescent : baseEnd_3749351 < baseStart_3749351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749370 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_3749370 : Nat := 118140960795 + 3749370 * 2 ^ 59
def prefixEnd_3749370 : Nat := 4983230072969 + 3 ^ 40 * 3749370 * 2
def baseEnd_3749370 : Nat := 1925228961548100806331967

theorem tailTrace_3749370 : CollatzResearch.WordTrace tailWord_3749370 prefixEnd_3749370 1925228961548100806331967 := by
  unfold tailWord_3749370
  simp only [CollatzResearch.WordTrace]
  refine ⟨34187689606670076565231391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91167172284453537507283709 34187689606670076565231391)
  ·
    refine ⟨51281534410005114847847087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34187689606670076565231391 51281534410005114847847087)
    ·
      refine ⟨76922301615007672271770631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51281534410005114847847087 76922301615007672271770631)
      ·
        refine ⟨115383452422511508407655947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76922301615007672271770631 115383452422511508407655947)
        ·
          refine ⟨173075178633767262611483921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115383452422511508407655947 173075178633767262611483921)
          ·
            refine ⟨129806383975325446958612941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173075178633767262611483921 129806383975325446958612941)
            ·
              refine ⟨48677393990747042609479853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129806383975325446958612941 48677393990747042609479853)
              ·
                refine ⟨18254022746530140978554945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48677393990747042609479853 18254022746530140978554945)
                ·
                  refine ⟨13690517059897605733916209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18254022746530140978554945 13690517059897605733916209)
                  ·
                    refine ⟨10267887794923204300437157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13690517059897605733916209 10267887794923204300437157)
                    ·
                      refine ⟨1925228961548100806331967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10267887794923204300437157 1925228961548100806331967)
                      ·
                        rfl

theorem cell23_3749370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_3749370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749370 prefixEnd_3749370 := by exact prefixLift 3749370
  have htrace : WordTrace (prefixWord ++ tailWord_3749370) baseStart_3749370 baseEnd_3749370 := by
    simpa [prefixWord, tailWord_3749370, baseEnd_3749370] using wordTrace_append hprefix tailTrace_3749370
  have hstable : (prefixWord ++ tailWord_3749370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749370).length < 2 ^ (prefixWord ++ tailWord_3749370).sum := by decide
  have hdescent : baseEnd_3749370 < baseStart_3749370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749378 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_3749378 : Nat := 118140960795 + 3749378 * 2 ^ 59
def prefixEnd_3749378 : Nat := 4983230072969 + 3 ^ 40 * 3749378 * 2
def baseEnd_3749378 : Nat := 1925233069393336775031931

theorem tailTrace_3749378 : CollatzResearch.WordTrace tailWord_3749378 prefixEnd_3749378 1925233069393336775031931 := by
  unfold tailWord_3749378
  simp only [CollatzResearch.WordTrace]
  refine ⟨34187762552662830906804197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91167366807100882418144525 34187762552662830906804197)
  ·
    refine ⟨6410205478624280795025787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34187762552662830906804197 6410205478624280795025787)
    ·
      refine ⟨9615308217936421192538681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6410205478624280795025787 9615308217936421192538681)
      ·
        refine ⟨7211481163452315894404011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9615308217936421192538681 7211481163452315894404011)
        ·
          refine ⟨10817221745178473841606017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7211481163452315894404011 10817221745178473841606017)
          ·
            refine ⟨8112916308883855381204513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10817221745178473841606017 8112916308883855381204513)
            ·
              refine ⟨6084687231662891535903385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8112916308883855381204513 6084687231662891535903385)
              ·
                refine ⟨4563515423747168651927539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6084687231662891535903385 4563515423747168651927539)
                ·
                  refine ⟨6845273135620752977891309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563515423747168651927539 6845273135620752977891309)
                  ·
                    refine ⟨2566977425857782366709241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6845273135620752977891309 2566977425857782366709241)
                    ·
                      refine ⟨1925233069393336775031931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566977425857782366709241 1925233069393336775031931)
                      ·
                        rfl

theorem cell23_3749378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_3749378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749378 prefixEnd_3749378 := by exact prefixLift 3749378
  have htrace : WordTrace (prefixWord ++ tailWord_3749378) baseStart_3749378 baseEnd_3749378 := by
    simpa [prefixWord, tailWord_3749378, baseEnd_3749378] using wordTrace_append hprefix tailTrace_3749378
  have hstable : (prefixWord ++ tailWord_3749378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749378).length < 2 ^ (prefixWord ++ tailWord_3749378).sum := by decide
  have hdescent : baseEnd_3749378 < baseStart_3749378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749501 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_3749501 : Nat := 118140960795 + 3749501 * 2 ^ 59
def prefixEnd_3749501 : Nat := 4983230072969 + 3 ^ 40 * 3749501 * 2
def baseEnd_3749501 : Nat := 1925296227513839793793865

theorem tailTrace_3749501 : CollatzResearch.WordTrace tailWord_3749501 prefixEnd_3749501 1925296227513839793793865 := by
  unfold tailWord_3749501
  simp only [CollatzResearch.WordTrace]
  refine ⟨136755536389205715633944357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91170357592803810422629571 136755536389205715633944357)
  ·
    refine ⟨25641663072976071681364567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136755536389205715633944357 25641663072976071681364567)
    ·
      refine ⟨38462494609464107522046851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25641663072976071681364567 38462494609464107522046851)
      ·
        refine ⟨57693741914196161283070277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38462494609464107522046851 57693741914196161283070277)
        ·
          refine ⟨10817576608911780240575677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57693741914196161283070277 10817576608911780240575677)
          ·
            refine ⟨4056591228341917590215879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10817576608911780240575677 4056591228341917590215879)
            ·
              refine ⟨6084886842512876385323819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056591228341917590215879 6084886842512876385323819)
              ·
                refine ⟨9127330263769314577985729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084886842512876385323819 9127330263769314577985729)
                ·
                  refine ⟨6845497697826985933489297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9127330263769314577985729 6845497697826985933489297)
                  ·
                    refine ⟨5134123273370239450116973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6845497697826985933489297 5134123273370239450116973)
                    ·
                      refine ⟨1925296227513839793793865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5134123273370239450116973 1925296227513839793793865)
                      ·
                        rfl

theorem cell23_3749501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_3749501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749501 prefixEnd_3749501 := by exact prefixLift 3749501
  have htrace : WordTrace (prefixWord ++ tailWord_3749501) baseStart_3749501 baseEnd_3749501 := by
    simpa [prefixWord, tailWord_3749501, baseEnd_3749501] using wordTrace_append hprefix tailTrace_3749501
  have hstable : (prefixWord ++ tailWord_3749501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749501).length < 2 ^ (prefixWord ++ tailWord_3749501).sum := by decide
  have hdescent : baseEnd_3749501 < baseStart_3749501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749508 : List Nat := [2, 3, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_3749508 : Nat := 118140960795 + 3749508 * 2 ^ 59
def prefixEnd_3749508 : Nat := 4983230072969 + 3 ^ 40 * 3749508 * 2
def baseEnd_3749508 : Nat := 641766607292807088802111

theorem tailTrace_3749508 : CollatzResearch.WordTrace tailWord_3749508 prefixEnd_3749508 641766607292807088802111 := by
  unfold tailWord_3749508
  simp only [CollatzResearch.WordTrace]
  refine ⟨68377895850090177914724589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91170527800120237219632785 68377895850090177914724589)
  ·
    refine ⟨25641710943783816718021721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68377895850090177914724589 25641710943783816718021721)
    ·
      refine ⟨19231283207837862538516291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25641710943783816718021721 19231283207837862538516291)
      ·
        refine ⟨28846924811756793807774437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19231283207837862538516291 28846924811756793807774437)
        ·
          refine ⟨5408798402204398838957707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28846924811756793807774437 5408798402204398838957707)
          ·
            refine ⟨8113197603306598258436561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408798402204398838957707 8113197603306598258436561)
            ·
              refine ⟨6084898202479948693827421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8113197603306598258436561 6084898202479948693827421)
              ·
                refine ⟨2281836825929980760185283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6084898202479948693827421 2281836825929980760185283)
                ·
                  refine ⟨3422755238894971140277925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281836825929980760185283 3422755238894971140277925)
                  ·
                    refine ⟨641766607292807088802111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3422755238894971140277925 641766607292807088802111)
                    ·
                      rfl

theorem cell23_3749508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_3749508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749508 prefixEnd_3749508 := by exact prefixLift 3749508
  have htrace : WordTrace (prefixWord ++ tailWord_3749508) baseStart_3749508 baseEnd_3749508 := by
    simpa [prefixWord, tailWord_3749508, baseEnd_3749508] using wordTrace_append hprefix tailTrace_3749508
  have hstable : (prefixWord ++ tailWord_3749508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749508).length < 2 ^ (prefixWord ++ tailWord_3749508).sum := by decide
  have hdescent : baseEnd_3749508 < baseStart_3749508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749538 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 6]
def baseStart_3749538 : Nat := 118140960795 + 3749538 * 2 ^ 59
def prefixEnd_3749538 : Nat := 4983230072969 + 3 ^ 40 * 3749538 * 2
def baseEnd_3749538 : Nat := 213923914033117349892355

theorem tailTrace_3749538 : CollatzResearch.WordTrace tailWord_3749538 prefixEnd_3749538 213923914033117349892355 := by
  unfold tailWord_3749538
  simp only [CollatzResearch.WordTrace]
  refine ⟨34189221472517917738260317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91171257260047780635360845 34189221472517917738260317)
  ·
    refine ⟨12820958052194219151847619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34189221472517917738260317 12820958052194219151847619)
    ·
      refine ⟨19231437078291328727771429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12820958052194219151847619 19231437078291328727771429)
      ·
        refine ⟨3605894452179624136457143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19231437078291328727771429 3605894452179624136457143)
        ·
          refine ⟨5408841678269436204685715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605894452179624136457143 5408841678269436204685715)
          ·
            refine ⟨8113262517404154307028573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408841678269436204685715 8113262517404154307028573)
            ·
              refine ⟨3042473444026557865135715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8113262517404154307028573 3042473444026557865135715)
              ·
                refine ⟨4563710166039836797703573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042473444026557865135715 4563710166039836797703573)
                ·
                  refine ⟨213923914033117349892355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4563710166039836797703573 213923914033117349892355)
                  ·
                    rfl

theorem cell23_3749538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_3749538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749538 prefixEnd_3749538 := by exact prefixLift 3749538
  have htrace : WordTrace (prefixWord ++ tailWord_3749538) baseStart_3749538 baseEnd_3749538 := by
    simpa [prefixWord, tailWord_3749538, baseEnd_3749538] using wordTrace_append hprefix tailTrace_3749538
  have hstable : (prefixWord ++ tailWord_3749538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749538).length < 2 ^ (prefixWord ++ tailWord_3749538).sum := by decide
  have hdescent : baseEnd_3749538 < baseStart_3749538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749554 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_3749554 : Nat := 118140960795 + 3749554 * 2 ^ 59
def prefixEnd_3749554 : Nat := 4983230072969 + 3 ^ 40 * 3749554 * 2
def baseEnd_3749554 : Nat := 1925323441988528086431121

theorem tailTrace_3749554 : CollatzResearch.WordTrace tailWord_3749554 prefixEnd_3749554 1925323441988528086431121 := by
  unfold tailWord_3749554
  simp only [CollatzResearch.WordTrace]
  refine ⟨34189367364503426421405929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91171646305342470457082477 34189367364503426421405929)
  ·
    refine ⟨25642025523377569816054447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34189367364503426421405929 25642025523377569816054447)
    ·
      refine ⟨38463038285066354724081671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25642025523377569816054447 38463038285066354724081671)
      ·
        refine ⟨57694557427599532086122507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38463038285066354724081671 57694557427599532086122507)
        ·
          refine ⟨86541836141399298129183761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57694557427599532086122507 86541836141399298129183761)
          ·
            refine ⟨64906377106049473596887821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86541836141399298129183761 64906377106049473596887821)
            ·
              refine ⟨24339891414768552598832933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64906377106049473596887821 24339891414768552598832933)
              ·
                refine ⟨4563729640269103612281175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24339891414768552598832933 4563729640269103612281175)
                ·
                  refine ⟨6845594460403655418421763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563729640269103612281175 6845594460403655418421763)
                  ·
                    refine ⟨10268391690605483127632645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6845594460403655418421763 10268391690605483127632645)
                    ·
                      refine ⟨1925323441988528086431121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10268391690605483127632645 1925323441988528086431121)
                      ·
                        rfl

theorem cell23_3749554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_3749554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749554 prefixEnd_3749554 := by exact prefixLift 3749554
  have htrace : WordTrace (prefixWord ++ tailWord_3749554) baseStart_3749554 baseEnd_3749554 := by
    simpa [prefixWord, tailWord_3749554, baseEnd_3749554] using wordTrace_append hprefix tailTrace_3749554
  have hstable : (prefixWord ++ tailWord_3749554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749554).length < 2 ^ (prefixWord ++ tailWord_3749554).sum := by decide
  have hdescent : baseEnd_3749554 < baseStart_3749554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749558 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_3749558 : Nat := 118140960795 + 3749558 * 2 ^ 59
def prefixEnd_3749558 : Nat := 4983230072969 + 3 ^ 40 * 3749558 * 2
def baseEnd_3749558 : Nat := 1925325495911146070781103

theorem tailTrace_3749558 : CollatzResearch.WordTrace tailWord_3749558 prefixEnd_3749558 1925325495911146070781103 := by
  unfold tailWord_3749558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547350959374950898048083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91171743566666142912512885 8547350959374950898048083)
  ·
    refine ⟨12821026439062426347072125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8547350959374950898048083 12821026439062426347072125)
    ·
      refine ⟨4807884914648409880152047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12821026439062426347072125 4807884914648409880152047)
      ·
        refine ⟨7211827371972614820228071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807884914648409880152047 7211827371972614820228071)
        ·
          refine ⟨10817741057958922230342107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7211827371972614820228071 10817741057958922230342107)
          ·
            refine ⟨16226611586938383345513161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10817741057958922230342107 16226611586938383345513161)
            ·
              refine ⟨12169958690203787509134871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16226611586938383345513161 12169958690203787509134871)
              ·
                refine ⟨18254938035305681263702307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12169958690203787509134871 18254938035305681263702307)
                ·
                  refine ⟨27382407052958521895553461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18254938035305681263702307 27382407052958521895553461)
                  ·
                    refine ⟨2567100661214861427708137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27382407052958521895553461 2567100661214861427708137)
                    ·
                      refine ⟨1925325495911146070781103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567100661214861427708137 1925325495911146070781103)
                      ·
                        rfl

theorem cell23_3749558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_3749558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749558 prefixEnd_3749558 := by exact prefixLift 3749558
  have htrace : WordTrace (prefixWord ++ tailWord_3749558) baseStart_3749558 baseEnd_3749558 := by
    simpa [prefixWord, tailWord_3749558, baseEnd_3749558] using wordTrace_append hprefix tailTrace_3749558
  have hstable : (prefixWord ++ tailWord_3749558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749558).length < 2 ^ (prefixWord ++ tailWord_3749558).sum := by decide
  have hdescent : baseEnd_3749558 < baseStart_3749558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749564 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_3749564 : Nat := 118140960795 + 3749564 * 2 ^ 59
def prefixEnd_3749564 : Nat := 4983230072969 + 3 ^ 40 * 3749564 * 2
def baseEnd_3749564 : Nat := 641776192265024349102025

theorem tailTrace_3749564 : CollatzResearch.WordTrace tailWord_3749564 prefixEnd_3749564 641776192265024349102025 := by
  unfold tailWord_3749564
  simp only [CollatzResearch.WordTrace]
  refine ⟨68378917093988738696743873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91171889458651651595658497 68378917093988738696743873)
  ·
    refine ⟨51284187820491554022557905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68378917093988738696743873 51284187820491554022557905)
    ·
      refine ⟨38463140865368665516918429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51284187820491554022557905 38463140865368665516918429)
      ·
        refine ⟨14423677824513249568844411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38463140865368665516918429 14423677824513249568844411)
        ·
          refine ⟨21635516736769874353266617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14423677824513249568844411 21635516736769874353266617)
          ·
            refine ⟨16226637552577405764949963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21635516736769874353266617 16226637552577405764949963)
            ·
              refine ⟨24339956328866108647424945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16226637552577405764949963 24339956328866108647424945)
              ·
                refine ⟨18254967246649581485568709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24339956328866108647424945 18254967246649581485568709)
                ·
                  refine ⟨3422806358746796528544133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18254967246649581485568709 3422806358746796528544133)
                  ·
                    refine ⟨641776192265024349102025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3422806358746796528544133 641776192265024349102025)
                    ·
                      rfl

theorem cell23_3749564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_3749564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749564 prefixEnd_3749564 := by exact prefixLift 3749564
  have htrace : WordTrace (prefixWord ++ tailWord_3749564) baseStart_3749564 baseEnd_3749564 := by
    simpa [prefixWord, tailWord_3749564, baseEnd_3749564] using wordTrace_append hprefix tailTrace_3749564
  have hstable : (prefixWord ++ tailWord_3749564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749564).length < 2 ^ (prefixWord ++ tailWord_3749564).sum := by decide
  have hdescent : baseEnd_3749564 < baseStart_3749564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749567 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_3749567 : Nat := 118140960795 + 3749567 * 2 ^ 59
def prefixEnd_3749567 : Nat := 4983230072969 + 3 ^ 40 * 3749567 * 2
def baseEnd_3749567 : Nat := 1925330117237036535568561

theorem tailTrace_3749567 : CollatzResearch.WordTrace tailWord_3749567 prefixEnd_3749567 1925330117237036535568561 := by
  unfold tailWord_3749567
  simp only [CollatzResearch.WordTrace]
  refine ⟨136757943606966608905846955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91171962404644405937231303 136757943606966608905846955)
  ·
    refine ⟨205136915410449913358770433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136757943606966608905846955 205136915410449913358770433)
    ·
      refine ⟨153852686557837435019077825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205136915410449913358770433 153852686557837435019077825)
      ·
        refine ⟨115389514918378076264308369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153852686557837435019077825 115389514918378076264308369)
        ·
          refine ⟨86542136188783557198231277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115389514918378076264308369 86542136188783557198231277)
          ·
            refine ⟨32453301070793833949336729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86542136188783557198231277 32453301070793833949336729)
            ·
              refine ⟨24339975803095375462002547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32453301070793833949336729 24339975803095375462002547)
              ·
                refine ⟨36509963704643063193003821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24339975803095375462002547 36509963704643063193003821)
                ·
                  refine ⟨13691236389241148697376433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36509963704643063193003821 13691236389241148697376433)
                  ·
                    refine ⟨10268427291930861523032325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13691236389241148697376433 10268427291930861523032325)
                    ·
                      refine ⟨1925330117237036535568561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10268427291930861523032325 1925330117237036535568561)
                      ·
                        rfl

theorem cell23_3749567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_3749567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749567 prefixEnd_3749567 := by exact prefixLift 3749567
  have htrace : WordTrace (prefixWord ++ tailWord_3749567) baseStart_3749567 baseEnd_3749567 := by
    simpa [prefixWord, tailWord_3749567, baseEnd_3749567] using wordTrace_append hprefix tailTrace_3749567
  have hstable : (prefixWord ++ tailWord_3749567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749567).length < 2 ^ (prefixWord ++ tailWord_3749567).sum := by decide
  have hdescent : baseEnd_3749567 < baseStart_3749567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749604 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_3749604 : Nat := 118140960795 + 3749604 * 2 ^ 59
def prefixEnd_3749604 : Nat := 4983230072969 + 3 ^ 40 * 3749604 * 2
def baseEnd_3749604 : Nat := 1925349116021252890805891

theorem tailTrace_3749604 : CollatzResearch.WordTrace tailWord_3749604 prefixEnd_3749604 1925349116021252890805891 := by
  unfold tailWord_3749604
  simp only [CollatzResearch.WordTrace]
  refine ⟨68379646553916282112471933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91172862071888376149962577 68379646553916282112471933)
  ·
    refine ⟨25642367457718605792176975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68379646553916282112471933 25642367457718605792176975)
    ·
      refine ⟨38463551186577908688265463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25642367457718605792176975 38463551186577908688265463)
      ·
        refine ⟨57695326779866863032398195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38463551186577908688265463 57695326779866863032398195)
        ·
          refine ⟨86542990169800294548597293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57695326779866863032398195 86542990169800294548597293)
          ·
            refine ⟨32453621313675110455723985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86542990169800294548597293 32453621313675110455723985)
            ·
              refine ⟨24340215985256332841792989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32453621313675110455723985 24340215985256332841792989)
              ·
                refine ⟨9127580994471124815672371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24340215985256332841792989 9127580994471124815672371)
                ·
                  refine ⟨13691371491706687223508557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9127580994471124815672371 13691371491706687223508557)
                  ·
                    refine ⟨5134264309390007708815709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13691371491706687223508557 5134264309390007708815709)
                    ·
                      refine ⟨1925349116021252890805891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5134264309390007708815709 1925349116021252890805891)
                      ·
                        rfl

theorem cell23_3749604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_3749604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749604 prefixEnd_3749604 := by exact prefixLift 3749604
  have htrace : WordTrace (prefixWord ++ tailWord_3749604) baseStart_3749604 baseEnd_3749604 := by
    simpa [prefixWord, tailWord_3749604, baseEnd_3749604] using wordTrace_append hprefix tailTrace_3749604
  have hstable : (prefixWord ++ tailWord_3749604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749604).length < 2 ^ (prefixWord ++ tailWord_3749604).sum := by decide
  have hdescent : baseEnd_3749604 < baseStart_3749604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749608 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3749608 : Nat := 118140960795 + 3749608 * 2 ^ 59
def prefixEnd_3749608 : Nat := 4983230072969 + 3 ^ 40 * 3749608 * 2
def baseEnd_3749608 : Nat := 1925351169943870875155873

theorem tailTrace_3749608 : CollatzResearch.WordTrace tailWord_3749608 prefixEnd_3749608 1925351169943870875155873 := by
  unfold tailWord_3749608
  simp only [CollatzResearch.WordTrace]
  refine ⟨68379719499909036454044739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91172959333212048605392985 68379719499909036454044739)
  ·
    refine ⟨102569579249863554681067109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68379719499909036454044739 102569579249863554681067109)
    ·
      refine ⟨19231796109349416502700083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102569579249863554681067109 19231796109349416502700083)
      ·
        refine ⟨28847694164024124754050125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19231796109349416502700083 28847694164024124754050125)
        ·
          refine ⟨10817885311509046782768797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28847694164024124754050125 10817885311509046782768797)
          ·
            refine ⟨4056706991815892543538299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10817885311509046782768797 4056706991815892543538299)
            ·
              refine ⟨6085060487723838815307449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056706991815892543538299 6085060487723838815307449)
              ·
                refine ⟨4563795365792879111480587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6085060487723838815307449 4563795365792879111480587)
                ·
                  refine ⟨6845693048689318667220881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563795365792879111480587 6845693048689318667220881)
                  ·
                    refine ⟨5134269786516989000415661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6845693048689318667220881 5134269786516989000415661)
                    ·
                      refine ⟨1925351169943870875155873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5134269786516989000415661 1925351169943870875155873)
                      ·
                        rfl

theorem cell23_3749608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3749608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749608 prefixEnd_3749608 := by exact prefixLift 3749608
  have htrace : WordTrace (prefixWord ++ tailWord_3749608) baseStart_3749608 baseEnd_3749608 := by
    simpa [prefixWord, tailWord_3749608, baseEnd_3749608] using wordTrace_append hprefix tailTrace_3749608
  have hstable : (prefixWord ++ tailWord_3749608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749608).length < 2 ^ (prefixWord ++ tailWord_3749608).sum := by decide
  have hdescent : baseEnd_3749608 < baseStart_3749608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749631 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 1, 3, 2]
def baseStart_3749631 : Nat := 118140960795 + 3749631 * 2 ^ 59
def prefixEnd_3749631 : Nat := 4983230072969 + 3 ^ 40 * 3749631 * 2
def baseEnd_3749631 : Nat := 1925362979998924285168267

theorem tailTrace_3749631 : CollatzResearch.WordTrace tailWord_3749631 prefixEnd_3749631 1925362979998924285168267 := by
  unfold tailWord_3749631
  simp only [CollatzResearch.WordTrace]
  refine ⟨136760277878734747836176747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91173518585823165224117831 136760277878734747836176747)
  ·
    refine ⟨205140416818102121754265121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136760277878734747836176747 205140416818102121754265121)
    ·
      refine ⟨153855312613576591315698841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205140416818102121754265121 153855312613576591315698841)
      ·
        refine ⟨115391484460182443486774131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153855312613576591315698841 115391484460182443486774131)
        ·
          refine ⟨173087226690273665230161197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115391484460182443486774131 173087226690273665230161197)
          ·
            refine ⟨64907710008852624461310449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173087226690273665230161197 64907710008852624461310449)
            ·
              refine ⟨48680782506639468345982837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64907710008852624461310449 48680782506639468345982837)
              ·
                refine ⟨4563823359997450157435891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48680782506639468345982837 4563823359997450157435891)
                ·
                  refine ⟨6845735039996175236153837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563823359997450157435891 6845735039996175236153837)
                  ·
                    refine ⟨2567150639998565713557689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6845735039996175236153837 2567150639998565713557689)
                    ·
                      refine ⟨1925362979998924285168267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567150639998565713557689 1925362979998924285168267)
                      ·
                        rfl

theorem cell23_3749631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_3749631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749631 prefixEnd_3749631 := by exact prefixLift 3749631
  have htrace : WordTrace (prefixWord ++ tailWord_3749631) baseStart_3749631 baseEnd_3749631 := by
    simpa [prefixWord, tailWord_3749631, baseEnd_3749631] using wordTrace_append hprefix tailTrace_3749631
  have hstable : (prefixWord ++ tailWord_3749631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749631).length < 2 ^ (prefixWord ++ tailWord_3749631).sum := by decide
  have hdescent : baseEnd_3749631 < baseStart_3749631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749639 : List Nat := [1, 1, 4, 4, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3749639 : Nat := 118140960795 + 3749639 * 2 ^ 59
def prefixEnd_3749639 : Nat := 4983230072969 + 3 ^ 40 * 3749639 * 2
def baseEnd_3749639 : Nat := 1925367087844160253868231

theorem tailTrace_3749639 : CollatzResearch.WordTrace tailWord_3749639 prefixEnd_3749639 1925367087844160253868231 := by
  unfold tailWord_3749639
  simp only [CollatzResearch.WordTrace]
  refine ⟨136760569662705765202467971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91173713108470510134978647 136760569662705765202467971)
  ·
    refine ⟨205140854494058647803701957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136760569662705765202467971 205140854494058647803701957)
    ·
      refine ⟨38463910217635996463194117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205140854494058647803701957 38463910217635996463194117)
      ·
        refine ⟨7211983165806749336848897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38463910217635996463194117 7211983165806749336848897)
        ·
          refine ⟨5408987374355062002636673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7211983165806749336848897 5408987374355062002636673)
          ·
            refine ⟨4056740530766296501977505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5408987374355062002636673 4056740530766296501977505)
            ·
              refine ⟨3042555398074722376483129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4056740530766296501977505 3042555398074722376483129)
              ·
                refine ⟨2281916548556041782362347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3042555398074722376483129 2281916548556041782362347)
                ·
                  refine ⟨3422874822834062673543521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281916548556041782362347 3422874822834062673543521)
                  ·
                    refine ⟨2567156117125547005157641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3422874822834062673543521 2567156117125547005157641)
                    ·
                      refine ⟨1925367087844160253868231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567156117125547005157641 1925367087844160253868231)
                      ·
                        rfl

theorem cell23_3749639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3749639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749639 prefixEnd_3749639 := by exact prefixLift 3749639
  have htrace : WordTrace (prefixWord ++ tailWord_3749639) baseStart_3749639 baseEnd_3749639 := by
    simpa [prefixWord, tailWord_3749639, baseEnd_3749639] using wordTrace_append hprefix tailTrace_3749639
  have hstable : (prefixWord ++ tailWord_3749639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749639).length < 2 ^ (prefixWord ++ tailWord_3749639).sum := by decide
  have hdescent : baseEnd_3749639 < baseStart_3749639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749647 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_3749647 : Nat := 118140960795 + 3749647 * 2 ^ 59
def prefixEnd_3749647 : Nat := 4983230072969 + 3 ^ 40 * 3749647 * 2
def baseEnd_3749647 : Nat := 1925371195689396222568193

theorem tailTrace_3749647 : CollatzResearch.WordTrace tailWord_3749647 prefixEnd_3749647 1925371195689396222568193 := by
  unfold tailWord_3749647
  simp only [CollatzResearch.WordTrace]
  refine ⟨136760861446676782568759195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91173907631117855045839463 136760861446676782568759195)
  ·
    refine ⟨205141292170015173853138793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136760861446676782568759195 205141292170015173853138793)
    ·
      refine ⟨153855969127511380389854095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205141292170015173853138793 153855969127511380389854095)
      ·
        refine ⟨230783953691267070584781143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153855969127511380389854095 230783953691267070584781143)
        ·
          refine ⟨346175930536900605877171715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230783953691267070584781143 346175930536900605877171715)
          ·
            refine ⟨519263895805350908815757573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346175930536900605877171715 519263895805350908815757573)
            ·
              refine ⟨97361980463503295402954545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 519263895805350908815757573 97361980463503295402954545)
              ·
                refine ⟨73021485347627471552215909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97361980463503295402954545 73021485347627471552215909)
                ·
                  refine ⟨13691528502680150916040483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73021485347627471552215909 13691528502680150916040483)
                  ·
                    refine ⟨20537292754020226374060725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13691528502680150916040483 20537292754020226374060725)
                    ·
                      refine ⟨1925371195689396222568193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20537292754020226374060725 1925371195689396222568193)
                      ·
                        rfl

theorem cell23_3749647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_3749647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749647 prefixEnd_3749647 := by exact prefixLift 3749647
  have htrace : WordTrace (prefixWord ++ tailWord_3749647) baseStart_3749647 baseEnd_3749647 := by
    simpa [prefixWord, tailWord_3749647, baseEnd_3749647] using wordTrace_append hprefix tailTrace_3749647
  have hstable : (prefixWord ++ tailWord_3749647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749647).length < 2 ^ (prefixWord ++ tailWord_3749647).sum := by decide
  have hdescent : baseEnd_3749647 < baseStart_3749647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749664 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3749664 : Nat := 118140960795 + 3749664 * 2 ^ 59
def prefixEnd_3749664 : Nat := 4983230072969 + 3 ^ 40 * 3749664 * 2
def baseEnd_3749664 : Nat := 1925379924860522656055615

theorem tailTrace_3749664 : CollatzResearch.WordTrace tailWord_3749664 prefixEnd_3749664 1925379924860522656055615 := by
  unfold tailWord_3749664
  simp only [CollatzResearch.WordTrace]
  refine ⟨68380740743807597236064023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91174320991743462981418697 68380740743807597236064023)
  ·
    refine ⟨102571111115711395854096035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68380740743807597236064023 102571111115711395854096035)
    ·
      refine ⟨153856666673567093781144053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102571111115711395854096035 153856666673567093781144053)
      ·
        refine ⟨14424062500646915041982255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153856666673567093781144053 14424062500646915041982255)
        ·
          refine ⟨21636093750970372562973383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14424062500646915041982255 21636093750970372562973383)
          ·
            refine ⟨32454140626455558844460075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21636093750970372562973383 32454140626455558844460075)
            ·
              refine ⟨48681210939683338266690113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32454140626455558844460075 48681210939683338266690113)
              ·
                refine ⟨36510908204762503700017585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48681210939683338266690113 36510908204762503700017585)
                ·
                  refine ⟨27383181153571877775013189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36510908204762503700017585 27383181153571877775013189)
                  ·
                    refine ⟨5134346466294727082814973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27383181153571877775013189 5134346466294727082814973)
                    ·
                      refine ⟨1925379924860522656055615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5134346466294727082814973 1925379924860522656055615)
                      ·
                        rfl

theorem cell23_3749664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3749664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749664 prefixEnd_3749664 := by exact prefixLift 3749664
  have htrace : WordTrace (prefixWord ++ tailWord_3749664) baseStart_3749664 baseEnd_3749664 := by
    simpa [prefixWord, tailWord_3749664, baseEnd_3749664] using wordTrace_append hprefix tailTrace_3749664
  have hstable : (prefixWord ++ tailWord_3749664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749664).length < 2 ^ (prefixWord ++ tailWord_3749664).sum := by decide
  have hdescent : baseEnd_3749664 < baseStart_3749664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749667 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 9]
def baseStart_3749667 : Nat := 118140960795 + 3749667 * 2 ^ 59
def prefixEnd_3749667 : Nat := 4983230072969 + 3 ^ 40 * 3749667 * 2
def baseEnd_3749667 : Nat := 213931273922498460479789

theorem tailTrace_3749667 : CollatzResearch.WordTrace tailWord_3749667 prefixEnd_3749667 213931273922498460479789 := by
  unfold tailWord_3749667
  simp only [CollatzResearch.WordTrace]
  refine ⟨136761590906604325984487255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91174393937736217322991503 136761590906604325984487255)
  ·
    refine ⟨205142386359906488976730883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136761590906604325984487255 205142386359906488976730883)
    ·
      refine ⟨307713579539859733465096325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205142386359906488976730883 307713579539859733465096325)
      ·
        refine ⟨57696296163723700024705561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307713579539859733465096325 57696296163723700024705561)
        ·
          refine ⟨43272222122792775018529171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57696296163723700024705561 43272222122792775018529171)
          ·
            refine ⟨64908333184189162527793757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43272222122792775018529171 64908333184189162527793757)
            ·
              refine ⟨24340624944070935947922659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64908333184189162527793757 24340624944070935947922659)
              ·
                refine ⟨36510937416106403921883989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24340624944070935947922659 36510937416106403921883989)
                ·
                  refine ⟨213931273922498460479789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36510937416106403921883989 213931273922498460479789)
                  ·
                    rfl

theorem cell23_3749667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 9].length) (baseStart_3749667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749667 prefixEnd_3749667 := by exact prefixLift 3749667
  have htrace : WordTrace (prefixWord ++ tailWord_3749667) baseStart_3749667 baseEnd_3749667 := by
    simpa [prefixWord, tailWord_3749667, baseEnd_3749667] using wordTrace_append hprefix tailTrace_3749667
  have hstable : (prefixWord ++ tailWord_3749667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749667).length < 2 ^ (prefixWord ++ tailWord_3749667).sum := by decide
  have hdescent : baseEnd_3749667 < baseStart_3749667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749714 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3749714 : Nat := 118140960795 + 3749714 * 2 ^ 59
def prefixEnd_3749714 : Nat := 4983230072969 + 3 ^ 40 * 3749714 * 2
def baseEnd_3749714 : Nat := 641801866297749153476795

theorem tailTrace_3749714 : CollatzResearch.WordTrace tailWord_3749714 prefixEnd_3749714 641801866297749153476795 := by
  unfold tailWord_3749714
  simp only [CollatzResearch.WordTrace]
  refine ⟨34190826284358513252862049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91175536758289368674298797 34190826284358513252862049)
  ·
    refine ⟨25643119713268884939646537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34190826284358513252862049 25643119713268884939646537)
    ·
      refine ⟨19232339784951663704734903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25643119713268884939646537 19232339784951663704734903)
      ·
        refine ⟨28848509677427495557102355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19232339784951663704734903 28848509677427495557102355)
        ·
          refine ⟨43272764516141243335653533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28848509677427495557102355 43272764516141243335653533)
          ·
            refine ⟨16227286693552966250870075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43272764516141243335653533 16227286693552966250870075)
            ·
              refine ⟨24340930040329449376305113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16227286693552966250870075 24340930040329449376305113)
              ·
                refine ⟨18255697530247087032228835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24340930040329449376305113 18255697530247087032228835)
                ·
                  refine ⟨27383546295370630548343253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18255697530247087032228835 27383546295370630548343253)
                  ·
                    refine ⟨641801866297749153476795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27383546295370630548343253 641801866297749153476795)
                    ·
                      rfl

theorem cell23_3749714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3749714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749714 prefixEnd_3749714 := by exact prefixLift 3749714
  have htrace : WordTrace (prefixWord ++ tailWord_3749714) baseStart_3749714 baseEnd_3749714 := by
    simpa [prefixWord, tailWord_3749714, baseEnd_3749714] using wordTrace_append hprefix tailTrace_3749714
  have hstable : (prefixWord ++ tailWord_3749714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749714).length < 2 ^ (prefixWord ++ tailWord_3749714).sum := by decide
  have hdescent : baseEnd_3749714 < baseStart_3749714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749758 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3749758 : Nat := 118140960795 + 3749758 * 2 ^ 59
def prefixEnd_3749758 : Nat := 4983230072969 + 3 ^ 40 * 3749758 * 2
def baseEnd_3749758 : Nat := 1925428192042045288280183

theorem tailTrace_3749758 : CollatzResearch.WordTrace tailWord_3749758 prefixEnd_3749758 1925428192042045288280183 := by
  unfold tailWord_3749758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17095613743659331065756241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91176606632849765684033285 17095613743659331065756241)
  ·
    refine ⟨12821710307744498299317181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17095613743659331065756241 12821710307744498299317181)
    ·
      refine ⟨4808141365404186862243943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12821710307744498299317181 4808141365404186862243943)
      ·
        refine ⟨7212212048106280293365915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808141365404186862243943 7212212048106280293365915)
        ·
          refine ⟨10818318072159420440048873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212212048106280293365915 10818318072159420440048873)
          ·
            refine ⟨8113738554119565330036655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10818318072159420440048873 8113738554119565330036655)
            ·
              refine ⟨12170607831179347995054983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8113738554119565330036655 12170607831179347995054983)
              ·
                refine ⟨18255911746769021992582475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12170607831179347995054983 18255911746769021992582475)
                ·
                  refine ⟨27383867620153532988873713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18255911746769021992582475 27383867620153532988873713)
                  ·
                    refine ⟨20537900715115149741655285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27383867620153532988873713 20537900715115149741655285)
                    ·
                      refine ⟨1925428192042045288280183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20537900715115149741655285 1925428192042045288280183)
                      ·
                        rfl

theorem cell23_3749758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3749758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749758 prefixEnd_3749758 := by exact prefixLift 3749758
  have htrace : WordTrace (prefixWord ++ tailWord_3749758) baseStart_3749758 baseEnd_3749758 := by
    simpa [prefixWord, tailWord_3749758, baseEnd_3749758] using wordTrace_append hprefix tailTrace_3749758
  have hstable : (prefixWord ++ tailWord_3749758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749758).length < 2 ^ (prefixWord ++ tailWord_3749758).sum := by decide
  have hdescent : baseEnd_3749758 < baseStart_3749758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749764 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3749764 : Nat := 118140960795 + 3749764 * 2 ^ 59
def prefixEnd_3749764 : Nat := 4983230072969 + 3 ^ 40 * 3749764 * 2
def baseEnd_3749764 : Nat := 1925431272925972264805155

theorem tailTrace_3749764 : CollatzResearch.WordTrace tailWord_3749764 prefixEnd_3749764 1925431272925972264805155 := by
  unfold tailWord_3749764
  simp only [CollatzResearch.WordTrace]
  refine ⟨68382564393626455775384173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91176752524835274367178897 68382564393626455775384173)
  ·
    refine ⟨25643461647609920915769065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68382564393626455775384173 25643461647609920915769065)
    ·
      refine ⟨19232596235707440686826799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25643461647609920915769065 19232596235707440686826799)
      ·
        refine ⟨28848894353561161030240199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19232596235707440686826799 28848894353561161030240199)
        ·
          refine ⟨43273341530341741545360299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28848894353561161030240199 43273341530341741545360299)
          ·
            refine ⟨64910012295512612318040449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43273341530341741545360299 64910012295512612318040449)
            ·
              refine ⟨48682509221634459238530337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64910012295512612318040449 48682509221634459238530337)
              ·
                refine ⟨36511881916225844428897753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48682509221634459238530337 36511881916225844428897753)
                ·
                  refine ⟨27383911437169383321673315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36511881916225844428897753 27383911437169383321673315)
                  ·
                    refine ⟨41075867155754074982509973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27383911437169383321673315 41075867155754074982509973)
                    ·
                      refine ⟨1925431272925972264805155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41075867155754074982509973 1925431272925972264805155)
                      ·
                        rfl

theorem cell23_3749764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3749764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749764 prefixEnd_3749764 := by exact prefixLift 3749764
  have htrace : WordTrace (prefixWord ++ tailWord_3749764) baseStart_3749764 baseEnd_3749764 := by
    simpa [prefixWord, tailWord_3749764, baseEnd_3749764] using wordTrace_append hprefix tailTrace_3749764
  have hstable : (prefixWord ++ tailWord_3749764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749764).length < 2 ^ (prefixWord ++ tailWord_3749764).sum := by decide
  have hdescent : baseEnd_3749764 < baseStart_3749764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749782 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3749782 : Nat := 118140960795 + 3749782 * 2 ^ 59
def prefixEnd_3749782 : Nat := 4983230072969 + 3 ^ 40 * 3749782 * 2
def baseEnd_3749782 : Nat := 641813505192584398126691

theorem tailTrace_3749782 : CollatzResearch.WordTrace tailWord_3749782 prefixEnd_3749782 641813505192584398126691 := by
  unfold tailWord_3749782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547861581324231289057725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91177190200791800416615733 8547861581324231289057725)
  ·
    refine ⟨3205448092996586733396647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8547861581324231289057725 3205448092996586733396647)
    ·
      refine ⟨4808172139494880100094971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205448092996586733396647 4808172139494880100094971)
      ·
        refine ⟨7212258209242320150142457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808172139494880100094971 7212258209242320150142457)
        ·
          refine ⟨5409193656931740112606843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7212258209242320150142457 5409193656931740112606843)
          ·
            refine ⟨8113790485397610168910265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5409193656931740112606843 8113790485397610168910265)
            ·
              refine ⟨6085342864048207626682699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8113790485397610168910265 6085342864048207626682699)
              ·
                refine ⟨9128014296072311440024049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6085342864048207626682699 9128014296072311440024049)
                ·
                  refine ⟨6846010722054233580018037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9128014296072311440024049 6846010722054233580018037)
                  ·
                    refine ⟨641813505192584398126691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6846010722054233580018037 641813505192584398126691)
                    ·
                      rfl

theorem cell23_3749782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3749782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749782 prefixEnd_3749782 := by exact prefixLift 3749782
  have htrace : WordTrace (prefixWord ++ tailWord_3749782) baseStart_3749782 baseEnd_3749782 := by
    simpa [prefixWord, tailWord_3749782, baseEnd_3749782] using wordTrace_append hprefix tailTrace_3749782
  have hstable : (prefixWord ++ tailWord_3749782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749782).length < 2 ^ (prefixWord ++ tailWord_3749782).sum := by decide
  have hdescent : baseEnd_3749782 < baseStart_3749782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749788 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3749788 : Nat := 118140960795 + 3749788 * 2 ^ 59
def prefixEnd_3749788 : Nat := 4983230072969 + 3 ^ 40 * 3749788 * 2
def baseEnd_3749788 : Nat := 1925443596461680170905045

theorem tailTrace_3749788 : CollatzResearch.WordTrace tailWord_3749788 prefixEnd_3749788 1925443596461680170905045 := by
  unfold tailWord_3749788
  simp only [CollatzResearch.WordTrace]
  refine ⟨68383002069582981824821009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91177336092777309099761345 68383002069582981824821009)
  ·
    refine ⟨51287251552187236368615757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68383002069582981824821009 51287251552187236368615757)
    ·
      refine ⟨19232719332070213638230909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51287251552187236368615757 19232719332070213638230909)
      ·
        refine ⟨7212269749526330114336591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19232719332070213638230909 7212269749526330114336591)
        ·
          refine ⟨10818404624289495171504887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212269749526330114336591 10818404624289495171504887)
          ·
            refine ⟨16227606936434242757257331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818404624289495171504887 16227606936434242757257331)
            ·
              refine ⟨24341410404651364135885997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16227606936434242757257331 24341410404651364135885997)
              ·
                refine ⟨9128028901744261550957249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24341410404651364135885997 9128028901744261550957249)
                ·
                  refine ⟨6846021676308196163217937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9128028901744261550957249 6846021676308196163217937)
                  ·
                    refine ⟨5134516257231147122413453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6846021676308196163217937 5134516257231147122413453)
                    ·
                      refine ⟨1925443596461680170905045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5134516257231147122413453 1925443596461680170905045)
                      ·
                        rfl

theorem cell23_3749788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3749788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749788 prefixEnd_3749788 := by exact prefixLift 3749788
  have htrace : WordTrace (prefixWord ++ tailWord_3749788) baseStart_3749788 baseEnd_3749788 := by
    simpa [prefixWord, tailWord_3749788, baseEnd_3749788] using wordTrace_append hprefix tailTrace_3749788
  have hstable : (prefixWord ++ tailWord_3749788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749788).length < 2 ^ (prefixWord ++ tailWord_3749788).sum := by decide
  have hdescent : baseEnd_3749788 < baseStart_3749788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749801 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 3]
def baseStart_3749801 : Nat := 118140960795 + 3749801 * 2 ^ 59
def prefixEnd_3749801 : Nat := 4983230072969 + 3 ^ 40 * 3749801 * 2
def baseEnd_3749801 : Nat := 1925450271710188620042485

theorem tailTrace_3749801 : CollatzResearch.WordTrace tailWord_3749801 prefixEnd_3749801 1925450271710188620042485 := by
  unfold tailWord_3749801
  simp only [CollatzResearch.WordTrace]
  refine ⟨136766478288118866869865257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91177652192079244579910171 136766478288118866869865257)
  ·
    refine ⟨102574858716089150152398943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136766478288118866869865257 102574858716089150152398943)
    ·
      refine ⟨153862288074133725228598415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102574858716089150152398943 153862288074133725228598415)
      ·
        refine ⟨230793432111200587842897623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153862288074133725228598415 230793432111200587842897623)
        ·
          refine ⟨346190148166800881764346435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230793432111200587842897623 346190148166800881764346435)
          ·
            refine ⟨519285222250201322646519653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346190148166800881764346435 519285222250201322646519653)
            ·
              refine ⟨97365979171912747996222435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 519285222250201322646519653 97365979171912747996222435)
              ·
                refine ⟨146048968757869121994333653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97365979171912747996222435 146048968757869121994333653)
                ·
                  refine ⟨3423022705262557546742195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 146048968757869121994333653 3423022705262557546742195)
                  ·
                    refine ⟨5134534057893836320113293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3423022705262557546742195 5134534057893836320113293)
                    ·
                      refine ⟨1925450271710188620042485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5134534057893836320113293 1925450271710188620042485)
                      ·
                        rfl

theorem cell23_3749801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 3].length) (baseStart_3749801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749801 prefixEnd_3749801 := by exact prefixLift 3749801
  have htrace : WordTrace (prefixWord ++ tailWord_3749801) baseStart_3749801 baseEnd_3749801 := by
    simpa [prefixWord, tailWord_3749801, baseEnd_3749801] using wordTrace_append hprefix tailTrace_3749801
  have hstable : (prefixWord ++ tailWord_3749801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749801).length < 2 ^ (prefixWord ++ tailWord_3749801).sum := by decide
  have hdescent : baseEnd_3749801 < baseStart_3749801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749804 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_3749804 : Nat := 118140960795 + 3749804 * 2 ^ 59
def prefixEnd_3749804 : Nat := 4983230072969 + 3 ^ 40 * 3749804 * 2
def baseEnd_3749804 : Nat := 641817270717384036101657

theorem tailTrace_3749804 : CollatzResearch.WordTrace tailWord_3749804 prefixEnd_3749804 641817270717384036101657 := by
  unfold tailWord_3749804
  simp only [CollatzResearch.WordTrace]
  refine ⟨68383293853553999191112233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91177725138071998921482977 68383293853553999191112233)
  ·
    refine ⟨51287470390165499393334175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68383293853553999191112233 51287470390165499393334175)
    ·
      refine ⟨76931205585248249090001263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51287470390165499393334175 76931205585248249090001263)
      ·
        refine ⟨115396808377872373635001895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76931205585248249090001263 115396808377872373635001895)
        ·
          refine ⟨173095212566808560452502843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115396808377872373635001895 173095212566808560452502843)
          ·
            refine ⟨259642818850212840678754265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173095212566808560452502843 259642818850212840678754265)
            ·
              refine ⟨194732114137659630509065699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259642818850212840678754265 194732114137659630509065699)
              ·
                refine ⟨292098171206489445763598549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194732114137659630509065699 292098171206489445763598549)
                ·
                  refine ⟨6846050887652096385084341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 292098171206489445763598549 6846050887652096385084341)
                  ·
                    refine ⟨641817270717384036101657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6846050887652096385084341 641817270717384036101657)
                    ·
                      rfl

theorem cell23_3749804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_3749804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749804 prefixEnd_3749804 := by exact prefixLift 3749804
  have htrace : WordTrace (prefixWord ++ tailWord_3749804) baseStart_3749804 baseEnd_3749804 := by
    simpa [prefixWord, tailWord_3749804, baseEnd_3749804] using wordTrace_append hprefix tailTrace_3749804
  have hstable : (prefixWord ++ tailWord_3749804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749804).length < 2 ^ (prefixWord ++ tailWord_3749804).sum := by decide
  have hdescent : baseEnd_3749804 < baseStart_3749804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749821 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_3749821 : Nat := 118140960795 + 3749821 * 2 ^ 59
def prefixEnd_3749821 : Nat := 4983230072969 + 3 ^ 40 * 3749821 * 2
def baseEnd_3749821 : Nat := 641820180441092847264131

theorem tailTrace_3749821 : CollatzResearch.WordTrace tailWord_3749821 prefixEnd_3749821 641820180441092847264131 := by
  unfold tailWord_3749821
  simp only [CollatzResearch.WordTrace]
  refine ⟨136767207748046410285593317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91178138498697606857062211 136767207748046410285593317)
  ·
    refine ⟨25643851452758701928548747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136767207748046410285593317 25643851452758701928548747)
    ·
      refine ⟨38465777179138052892823121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25643851452758701928548747 38465777179138052892823121)
      ·
        refine ⟨28849332884353539669617341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38465777179138052892823121 28849332884353539669617341)
        ·
          refine ⟨10818499831632577376106503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28849332884353539669617341 10818499831632577376106503)
          ·
            refine ⟨16227749747448866064159755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818499831632577376106503 16227749747448866064159755)
            ·
              refine ⟨24341624621173299096239633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16227749747448866064159755 24341624621173299096239633)
              ·
                refine ⟨18256218465879974322179725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24341624621173299096239633 18256218465879974322179725)
                ·
                  refine ⟨6846081924704990370817397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18256218465879974322179725 6846081924704990370817397)
                  ·
                    refine ⟨641820180441092847264131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6846081924704990370817397 641820180441092847264131)
                    ·
                      rfl

theorem cell23_3749821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_3749821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749821 prefixEnd_3749821 := by exact prefixLift 3749821
  have htrace : WordTrace (prefixWord ++ tailWord_3749821) baseStart_3749821 baseEnd_3749821 := by
    simpa [prefixWord, tailWord_3749821, baseEnd_3749821] using wordTrace_append hprefix tailTrace_3749821
  have hstable : (prefixWord ++ tailWord_3749821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749821).length < 2 ^ (prefixWord ++ tailWord_3749821).sum := by decide
  have hdescent : baseEnd_3749821 < baseStart_3749821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749841 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 1, 8, 2]
def baseStart_3749841 : Nat := 118140960795 + 3749841 * 2 ^ 59
def prefixEnd_3749841 : Nat := 4983230072969 + 3 ^ 40 * 3749841 * 2
def baseEnd_3749841 : Nat := 1925470810936368463542301

theorem tailTrace_3749841 : CollatzResearch.WordTrace tailWord_3749841 prefixEnd_3749841 1925470810936368463542301 := by
  unfold tailWord_3749841
  simp only [CollatzResearch.WordTrace]
  refine ⟨136767937207973953701321377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91178624805315969134214251 136767937207973953701321377)
  ·
    refine ⟨102575952905980465275991033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136767937207973953701321377 102575952905980465275991033)
    ·
      refine ⟨76931964679485348956993275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102575952905980465275991033 76931964679485348956993275)
      ·
        refine ⟨115397947019228023435489913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76931964679485348956993275 115397947019228023435489913)
        ·
          refine ⟨86548460264421017576617435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115397947019228023435489913 86548460264421017576617435)
          ·
            refine ⟨129822690396631526364926153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86548460264421017576617435 129822690396631526364926153)
            ·
              refine ⟨97367017797473644773694615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129822690396631526364926153 97367017797473644773694615)
              ·
                refine ⟨146050526696210467160541923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97367017797473644773694615 146050526696210467160541923)
                ·
                  refine ⟨219075790044315700740812885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146050526696210467160541923 219075790044315700740812885)
                  ·
                    refine ⟨2567294414581824618056401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 219075790044315700740812885 2567294414581824618056401)
                    ·
                      refine ⟨1925470810936368463542301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567294414581824618056401 1925470810936368463542301)
                      ·
                        rfl

theorem cell23_3749841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_3749841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749841 prefixEnd_3749841 := by exact prefixLift 3749841
  have htrace : WordTrace (prefixWord ++ tailWord_3749841) baseStart_3749841 baseEnd_3749841 := by
    simpa [prefixWord, tailWord_3749841, baseEnd_3749841] using wordTrace_append hprefix tailTrace_3749841
  have hstable : (prefixWord ++ tailWord_3749841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749841).length < 2 ^ (prefixWord ++ tailWord_3749841).sum := by decide
  have hdescent : baseEnd_3749841 < baseStart_3749841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749845 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_3749845 : Nat := 118140960795 + 3749845 * 2 ^ 59
def prefixEnd_3749845 : Nat := 4983230072969 + 3 ^ 40 * 3749845 * 2
def baseEnd_3749845 : Nat := 1925472864858986447892283

theorem tailTrace_3749845 : CollatzResearch.WordTrace tailWord_3749845 prefixEnd_3749845 1925472864858986447892283 := by
  unfold tailWord_3749845
  simp only [CollatzResearch.WordTrace]
  refine ⟨136768083099959462384466989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91178722066639641589644659 136768083099959462384466989)
  ·
    refine ⟨51288031162484798394175121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136768083099959462384466989 51288031162484798394175121)
    ·
      refine ⟨38466023371863598795631341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51288031162484798394175121 38466023371863598795631341)
      ·
        refine ⟨14424758764448849548361753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38466023371863598795631341 14424758764448849548361753)
        ·
          refine ⟨10818569073336637161271315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14424758764448849548361753 10818569073336637161271315)
          ·
            refine ⟨16227853610004955741906973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818569073336637161271315 16227853610004955741906973)
            ·
              refine ⟨6085445103751858403215115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16227853610004955741906973 6085445103751858403215115)
              ·
                refine ⟨9128167655627787604822673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6085445103751858403215115 9128167655627787604822673)
                ·
                  refine ⟨6846125741720840703617005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9128167655627787604822673 6846125741720840703617005)
                  ·
                    refine ⟨2567297153145315263856377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6846125741720840703617005 2567297153145315263856377)
                    ·
                      refine ⟨1925472864858986447892283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567297153145315263856377 1925472864858986447892283)
                      ·
                        rfl

theorem cell23_3749845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_3749845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749845 prefixEnd_3749845 := by exact prefixLift 3749845
  have htrace : WordTrace (prefixWord ++ tailWord_3749845) baseStart_3749845 baseEnd_3749845 := by
    simpa [prefixWord, tailWord_3749845, baseEnd_3749845] using wordTrace_append hprefix tailTrace_3749845
  have hstable : (prefixWord ++ tailWord_3749845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749845).length < 2 ^ (prefixWord ++ tailWord_3749845).sum := by decide
  have hdescent : baseEnd_3749845 < baseStart_3749845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749855 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 1, 5]
def baseStart_3749855 : Nat := 118140960795 + 3749855 * 2 ^ 59
def prefixEnd_3749855 : Nat := 4983230072969 + 3 ^ 40 * 3749855 * 2
def baseEnd_3749855 : Nat := 641825999888510469589079

theorem tailTrace_3749855 : CollatzResearch.WordTrace tailWord_3749855 prefixEnd_3749855 641825999888510469589079 := by
  unfold tailWord_3749855
  simp only [CollatzResearch.WordTrace]
  refine ⟨136768447829923234092331019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91178965219948822728220679 136768447829923234092331019)
  ·
    refine ⟨205152671744884851138496529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136768447829923234092331019 205152671744884851138496529)
    ·
      refine ⟨153864503808663638353872397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205152671744884851138496529 153864503808663638353872397)
      ·
        refine ⟨57699188928248864382702149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153864503808663638353872397 57699188928248864382702149)
        ·
          refine ⟨10818597924046662071756653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57699188928248864382702149 10818597924046662071756653)
          ·
            refine ⟨4056974221517498276908745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10818597924046662071756653 4056974221517498276908745)
            ·
              refine ⟨3042730666138123707681559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4056974221517498276908745 3042730666138123707681559)
              ·
                refine ⟨4564095999207185561522339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042730666138123707681559 4564095999207185561522339)
                ·
                  refine ⟨6846143998810778342283509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564095999207185561522339 6846143998810778342283509)
                  ·
                    refine ⟨641825999888510469589079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6846143998810778342283509 641825999888510469589079)
                    ·
                      rfl

theorem cell23_3749855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 5].length) (baseStart_3749855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749855 prefixEnd_3749855 := by exact prefixLift 3749855
  have htrace : WordTrace (prefixWord ++ tailWord_3749855) baseStart_3749855 baseEnd_3749855 := by
    simpa [prefixWord, tailWord_3749855, baseEnd_3749855] using wordTrace_append hprefix tailTrace_3749855
  have hstable : (prefixWord ++ tailWord_3749855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749855).length < 2 ^ (prefixWord ++ tailWord_3749855).sum := by decide
  have hdescent : baseEnd_3749855 < baseStart_3749855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749892 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3749892 : Nat := 118140960795 + 3749892 * 2 ^ 59
def prefixEnd_3749892 : Nat := 4983230072969 + 3 ^ 40 * 3749892 * 2
def baseEnd_3749892 : Nat := 1925496998449747764004567

theorem tailTrace_3749892 : CollatzResearch.WordTrace tailWord_3749892 prefixEnd_3749892 1925496998449747764004567 := by
  unfold tailWord_3749892
  simp only [CollatzResearch.WordTrace]
  refine ⟨68384898665394594705713965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91179864887192792940951953 68384898665394594705713965)
  ·
    refine ⟨25644336999522973014642737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68384898665394594705713965 25644336999522973014642737)
    ·
      refine ⟨19233252749642229760982053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25644336999522973014642737 19233252749642229760982053)
      ·
        refine ⟨3606234890557918080184135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19233252749642229760982053 3606234890557918080184135)
        ·
          refine ⟨5409352335836877120276203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606234890557918080184135 5409352335836877120276203)
          ·
            refine ⟨8114028503755315680414305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5409352335836877120276203 8114028503755315680414305)
            ·
              refine ⟨6085521377816486760310729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8114028503755315680414305 6085521377816486760310729)
              ·
                refine ⟨4564141033362365070233047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6085521377816486760310729 4564141033362365070233047)
                ·
                  refine ⟨6846211550043547605349571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564141033362365070233047 6846211550043547605349571)
                  ·
                    refine ⟨10269317325065321408024357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6846211550043547605349571 10269317325065321408024357)
                    ·
                      refine ⟨1925496998449747764004567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10269317325065321408024357 1925496998449747764004567)
                      ·
                        rfl

theorem cell23_3749892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3749892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749892 prefixEnd_3749892 := by exact prefixLift 3749892
  have htrace : WordTrace (prefixWord ++ tailWord_3749892) baseStart_3749892 baseEnd_3749892 := by
    simpa [prefixWord, tailWord_3749892, baseEnd_3749892] using wordTrace_append hprefix tailTrace_3749892
  have hstable : (prefixWord ++ tailWord_3749892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749892).length < 2 ^ (prefixWord ++ tailWord_3749892).sum := by decide
  have hdescent : baseEnd_3749892 < baseStart_3749892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749895 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3749895 : Nat := 118140960795 + 3749895 * 2 ^ 59
def prefixEnd_3749895 : Nat := 4983230072969 + 3 ^ 40 * 3749895 * 2
def baseEnd_3749895 : Nat := 1925498538891711252267053

theorem tailTrace_3749895 : CollatzResearch.WordTrace tailWord_3749895 prefixEnd_3749895 1925498538891711252267053 := by
  unfold tailWord_3749895
  simp only [CollatzResearch.WordTrace]
  refine ⟨136769906749778320923787139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91179937833185547282524759 136769906749778320923787139)
  ·
    refine ⟨205154860124667481385680709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136769906749778320923787139 205154860124667481385680709)
    ·
      refine ⟨38466536273375152759815133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205154860124667481385680709 38466536273375152759815133)
      ·
        refine ⟨14424951102515682284930675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38466536273375152759815133 14424951102515682284930675)
        ·
          refine ⟨21637426653773523427396013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14424951102515682284930675 21637426653773523427396013)
          ·
            refine ⟨8114034995165071285273505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21637426653773523427396013 8114034995165071285273505)
            ·
              refine ⟨6085526246373803463955129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8114034995165071285273505 6085526246373803463955129)
              ·
                refine ⟨4564144684780352597966347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6085526246373803463955129 4564144684780352597966347)
                ·
                  refine ⟨6846217027170528896949521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564144684780352597966347 6846217027170528896949521)
                  ·
                    refine ⟨5134662770377896672712141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6846217027170528896949521 5134662770377896672712141)
                    ·
                      refine ⟨1925498538891711252267053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5134662770377896672712141 1925498538891711252267053)
                      ·
                        rfl

theorem cell23_3749895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3749895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749895 prefixEnd_3749895 := by exact prefixLift 3749895
  have htrace : WordTrace (prefixWord ++ tailWord_3749895) baseStart_3749895 baseEnd_3749895 := by
    simpa [prefixWord, tailWord_3749895, baseEnd_3749895] using wordTrace_append hprefix tailTrace_3749895
  have hstable : (prefixWord ++ tailWord_3749895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749895).length < 2 ^ (prefixWord ++ tailWord_3749895).sum := by decide
  have hdescent : baseEnd_3749895 < baseStart_3749895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749941 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3749941 : Nat := 118140960795 + 3749941 * 2 ^ 59
def prefixEnd_3749941 : Nat := 4983230072969 + 3 ^ 40 * 3749941 * 2
def baseEnd_3749941 : Nat := 641840719667272690763947

theorem tailTrace_3749941 : CollatzResearch.WordTrace tailWord_3749941 prefixEnd_3749941 641840719667272690763947 := by
  unfold tailWord_3749941
  simp only [CollatzResearch.WordTrace]
  refine ⟨136771584507611670779961677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91181056338407780519974451 136771584507611670779961677)
  ·
    refine ⟨51289344190354376542485629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136771584507611670779961677 51289344190354376542485629)
    ·
      refine ⟨19233504071382891203432111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51289344190354376542485629 19233504071382891203432111)
      ·
        refine ⟨28850256107074336805148167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19233504071382891203432111 28850256107074336805148167)
        ·
          refine ⟨43275384160611505207722251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28850256107074336805148167 43275384160611505207722251)
          ·
            refine ⟨64913076240917257811583377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43275384160611505207722251 64913076240917257811583377)
            ·
              refine ⟨48684807180687943358687533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64913076240917257811583377 48684807180687943358687533)
              ·
                refine ⟨18256802692757978759507825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48684807180687943358687533 18256802692757978759507825)
                ·
                  refine ⟨13692602019568484069630869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18256802692757978759507825 13692602019568484069630869)
                  ·
                    refine ⟨641840719667272690763947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13692602019568484069630869 641840719667272690763947)
                    ·
                      rfl

theorem cell23_3749941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3749941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749941 prefixEnd_3749941 := by exact prefixLift 3749941
  have htrace : WordTrace (prefixWord ++ tailWord_3749941) baseStart_3749941 baseEnd_3749941 := by
    simpa [prefixWord, tailWord_3749941, baseEnd_3749941] using wordTrace_append hprefix tailTrace_3749941
  have hstable : (prefixWord ++ tailWord_3749941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749941).length < 2 ^ (prefixWord ++ tailWord_3749941).sum := by decide
  have hdescent : baseEnd_3749941 < baseStart_3749941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749942 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_3749942 : Nat := 118140960795 + 3749942 * 2 ^ 59
def prefixEnd_3749942 : Nat := 4983230072969 + 3 ^ 40 * 3749942 * 2
def baseEnd_3749942 : Nat := 1925522672482472568379337

theorem tailTrace_3749942 : CollatzResearch.WordTrace tailWord_3749942 prefixEnd_3749942 1925522672482472568379337 := by
  unfold tailWord_3749942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548226311288002996921755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91181080653738698633832053 8548226311288002996921755)
  ·
    refine ⟨12822339466932004495382633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8548226311288002996921755 12822339466932004495382633)
    ·
      refine ⟨9616754600199003371536975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12822339466932004495382633 9616754600199003371536975)
      ·
        refine ⟨14425131900298505057305463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9616754600199003371536975 14425131900298505057305463)
        ·
          refine ⟨21637697850447757585958195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14425131900298505057305463 21637697850447757585958195)
          ·
            refine ⟨32456546775671636378937293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21637697850447757585958195 32456546775671636378937293)
            ·
              refine ⟨12171205040876863642101485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32456546775671636378937293 12171205040876863642101485)
              ·
                refine ⟨4564201890328823865788057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12171205040876863642101485 4564201890328823865788057)
                ·
                  refine ⟨3423151417746617899341043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4564201890328823865788057 3423151417746617899341043)
                  ·
                    refine ⟨5134727126619926849011565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3423151417746617899341043 5134727126619926849011565)
                    ·
                      refine ⟨1925522672482472568379337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5134727126619926849011565 1925522672482472568379337)
                      ·
                        rfl

theorem cell23_3749942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_3749942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749942 prefixEnd_3749942 := by exact prefixLift 3749942
  have htrace : WordTrace (prefixWord ++ tailWord_3749942) baseStart_3749942 baseEnd_3749942 := by
    simpa [prefixWord, tailWord_3749942, baseEnd_3749942] using wordTrace_append hprefix tailTrace_3749942
  have hstable : (prefixWord ++ tailWord_3749942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749942).length < 2 ^ (prefixWord ++ tailWord_3749942).sum := by decide
  have hdescent : baseEnd_3749942 < baseStart_3749942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749951 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_3749951 : Nat := 118140960795 + 3749951 * 2 ^ 59
def prefixEnd_3749951 : Nat := 4983230072969 + 3 ^ 40 * 3749951 * 2
def baseEnd_3749951 : Nat := 1925527293808363033166795

theorem tailTrace_3749951 : CollatzResearch.WordTrace tailWord_3749951 prefixEnd_3749951 1925527293808363033166795 := by
  unfold tailWord_3749951
  simp only [CollatzResearch.WordTrace]
  refine ⟨136771949237575442487825707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91181299491716961658550471 136771949237575442487825707)
  ·
    refine ⟨205157923856363163731738561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136771949237575442487825707 205157923856363163731738561)
    ·
      refine ⟨153868442892272372798803921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205157923856363163731738561 153868442892272372798803921)
      ·
        refine ⟨115401332169204279599102941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153868442892272372798803921 115401332169204279599102941)
        ·
          refine ⟨43275499563451604849663603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115401332169204279599102941 43275499563451604849663603)
          ·
            refine ⟨64913249345177407274495405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43275499563451604849663603 64913249345177407274495405)
            ·
              refine ⟨24342468504441527727935777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64913249345177407274495405 24342468504441527727935777)
              ·
                refine ⟨18256851378331145795951833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24342468504441527727935777 18256851378331145795951833)
                ·
                  refine ⟨13692638533748359346963875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18256851378331145795951833 13692638533748359346963875)
                  ·
                    refine ⟨20538957800622539020445813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13692638533748359346963875 20538957800622539020445813)
                    ·
                      refine ⟨1925527293808363033166795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20538957800622539020445813 1925527293808363033166795)
                      ·
                        rfl

theorem cell23_3749951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_3749951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749951 prefixEnd_3749951 := by exact prefixLift 3749951
  have htrace : WordTrace (prefixWord ++ tailWord_3749951) baseStart_3749951 baseEnd_3749951 := by
    simpa [prefixWord, tailWord_3749951, baseEnd_3749951] using wordTrace_append hprefix tailTrace_3749951
  have hstable : (prefixWord ++ tailWord_3749951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749951).length < 2 ^ (prefixWord ++ tailWord_3749951).sum := by decide
  have hdescent : baseEnd_3749951 < baseStart_3749951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3749952 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 1, 3, 2]
def baseStart_3749952 : Nat := 118140960795 + 3749952 * 2 ^ 59
def prefixEnd_3749952 : Nat := 4983230072969 + 3 ^ 40 * 3749952 * 2
def baseEnd_3749952 : Nat := 1925527807289017529254291

theorem tailTrace_3749952 : CollatzResearch.WordTrace tailWord_3749952 prefixEnd_3749952 1925527807289017529254291 := by
  unfold tailWord_3749952
  simp only [CollatzResearch.WordTrace]
  refine ⟨68385992855285909829306055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91181323807047879772408073 68385992855285909829306055)
  ·
    refine ⟨102578989282928864743959083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68385992855285909829306055 102578989282928864743959083)
    ·
      refine ⟨153868483924393297115938625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102578989282928864743959083 153868483924393297115938625)
      ·
        refine ⟨115401362943294972836953969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153868483924393297115938625 115401362943294972836953969)
        ·
          refine ⟨86551022207471229627715477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115401362943294972836953969 86551022207471229627715477)
          ·
            refine ⟨4057079165975213888799163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86551022207471229627715477 4057079165975213888799163)
            ·
              refine ⟨6085618748962820833198745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057079165975213888799163 6085618748962820833198745)
              ·
                refine ⟨4564214061722115624899059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6085618748962820833198745 4564214061722115624899059)
                ·
                  refine ⟨6846321092583173437348589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564214061722115624899059 6846321092583173437348589)
                  ·
                    refine ⟨2567370409718690039005721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6846321092583173437348589 2567370409718690039005721)
                    ·
                      refine ⟨1925527807289017529254291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567370409718690039005721 1925527807289017529254291)
                      ·
                        rfl

theorem cell23_3749952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_3749952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3749952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3749952 prefixEnd_3749952 := by exact prefixLift 3749952
  have htrace : WordTrace (prefixWord ++ tailWord_3749952) baseStart_3749952 baseEnd_3749952 := by
    simpa [prefixWord, tailWord_3749952, baseEnd_3749952] using wordTrace_append hprefix tailTrace_3749952
  have hstable : (prefixWord ++ tailWord_3749952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3749952).length < 2 ^ (prefixWord ++ tailWord_3749952).sum := by decide
  have hdescent : baseEnd_3749952 < baseStart_3749952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3749952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750001 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 1, 7]
def baseStart_3750001 : Nat := 118140960795 + 3750001 * 2 ^ 59
def prefixEnd_3750001 : Nat := 4983230072969 + 3 ^ 40 * 3750001 * 2
def baseEnd_3750001 : Nat := 641850989280362612513855

theorem tailTrace_3750001 : CollatzResearch.WordTrace tailWord_3750001 prefixEnd_3750001 641850989280362612513855 := by
  unfold tailWord_3750001
  simp only [CollatzResearch.WordTrace]
  refine ⟨136773772887394301027145857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91182515258262867351430571 136773772887394301027145857)
  ·
    refine ⟨102580329665545725770359393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136773772887394301027145857 102580329665545725770359393)
    ·
      refine ⟨76935247249159294327769545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102580329665545725770359393 76935247249159294327769545)
      ·
        refine ⟨57701435436869470745827159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76935247249159294327769545 57701435436869470745827159)
        ·
          refine ⟨86552153155304206118740739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57701435436869470745827159 86552153155304206118740739)
          ·
            refine ⟨129828229732956309178111109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86552153155304206118740739 129828229732956309178111109)
            ·
              refine ⟨24342793074929307970895833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129828229732956309178111109 24342793074929307970895833)
              ·
                refine ⟨18257094806196980978171875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24342793074929307970895833 18257094806196980978171875)
                ·
                  refine ⟨27385642209295471467257813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18257094806196980978171875 27385642209295471467257813)
                  ·
                    refine ⟨641850989280362612513855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27385642209295471467257813 641850989280362612513855)
                    ·
                      rfl

theorem cell23_3750001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_3750001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750001 prefixEnd_3750001 := by exact prefixLift 3750001
  have htrace : WordTrace (prefixWord ++ tailWord_3750001) baseStart_3750001 baseEnd_3750001 := by
    simpa [prefixWord, tailWord_3750001, baseEnd_3750001] using wordTrace_append hprefix tailTrace_3750001
  have hstable : (prefixWord ++ tailWord_3750001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750001).length < 2 ^ (prefixWord ++ tailWord_3750001).sum := by decide
  have hdescent : baseEnd_3750001 < baseStart_3750001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750008 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 4, 5, 2]
def baseStart_3750008 : Nat := 118140960795 + 3750008 * 2 ^ 59
def prefixEnd_3750008 : Nat := 4983230072969 + 3 ^ 40 * 3750008 * 2
def baseEnd_3750008 : Nat := 1925556562205669310154033

theorem tailTrace_3750008 : CollatzResearch.WordTrace tailWord_3750008 prefixEnd_3750008 1925556562205669310154033 := by
  unfold tailWord_3750008
  simp only [CollatzResearch.WordTrace]
  refine ⟨68387014099184470611325339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91182685465579294148433785 68387014099184470611325339)
  ·
    refine ⟨102580521148776705916988009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68387014099184470611325339 102580521148776705916988009)
    ·
      refine ⟨76935390861582529437741007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102580521148776705916988009 76935390861582529437741007)
      ·
        refine ⟨115403086292373794156611511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76935390861582529437741007 115403086292373794156611511)
        ·
          refine ⟨173104629438560691234917267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115403086292373794156611511 173104629438560691234917267)
          ·
            refine ⟨259656944157841036852375901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173104629438560691234917267 259656944157841036852375901)
            ·
              refine ⟨97371354059190388819640963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259656944157841036852375901 97371354059190388819640963)
              ·
                refine ⟨146057031088785583229461445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97371354059190388819640963 146057031088785583229461445)
                ·
                  refine ⟨27385693329147296855524021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146057031088785583229461445 27385693329147296855524021)
                  ·
                    refine ⟨2567408749607559080205377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27385693329147296855524021 2567408749607559080205377)
                    ·
                      refine ⟨1925556562205669310154033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567408749607559080205377 1925556562205669310154033)
                      ·
                        rfl

theorem cell23_3750008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_3750008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750008 prefixEnd_3750008 := by exact prefixLift 3750008
  have htrace : WordTrace (prefixWord ++ tailWord_3750008) baseStart_3750008 baseEnd_3750008 := by
    simpa [prefixWord, tailWord_3750008, baseEnd_3750008] using wordTrace_append hprefix tailTrace_3750008
  have hstable : (prefixWord ++ tailWord_3750008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750008).length < 2 ^ (prefixWord ++ tailWord_3750008).sum := by decide
  have hdescent : baseEnd_3750008 < baseStart_3750008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750041 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_3750041 : Nat := 118140960795 + 3750041 * 2 ^ 59
def prefixEnd_3750041 : Nat := 4983230072969 + 3 ^ 40 * 3750041 * 2
def baseEnd_3750041 : Nat := 1925573507067267681041381

theorem tailTrace_3750041 : CollatzResearch.WordTrace tailWord_3750041 prefixEnd_3750041 1925573507067267681041381 := by
  unfold tailWord_3750041
  simp only [CollatzResearch.WordTrace]
  refine ⟨136775231807249387858601977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91183487871499591905734651 136775231807249387858601977)
  ·
    refine ⟨102581423855437040893951483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136775231807249387858601977 102581423855437040893951483)
    ·
      refine ⟨153872135783155561340927225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102581423855437040893951483 153872135783155561340927225)
      ·
        refine ⟨115404101837366671005695419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153872135783155561340927225 115404101837366671005695419)
        ·
          refine ⟨173106152756050006508543129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115404101837366671005695419 173106152756050006508543129)
          ·
            refine ⟨129829614567037504881407347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173106152756050006508543129 129829614567037504881407347)
            ·
              refine ⟨194744421850556257322111021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129829614567037504881407347 194744421850556257322111021)
              ·
                refine ⟨73029158193958596495791633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194744421850556257322111021 73029158193958596495791633)
                ·
                  refine ⟨54771868645468947371843725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73029158193958596495791633 54771868645468947371843725)
                  ·
                    refine ⟨20539450742050855264441397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54771868645468947371843725 20539450742050855264441397)
                    ·
                      refine ⟨1925573507067267681041381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20539450742050855264441397 1925573507067267681041381)
                      ·
                        rfl

theorem cell23_3750041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_3750041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750041 prefixEnd_3750041 := by exact prefixLift 3750041
  have htrace : WordTrace (prefixWord ++ tailWord_3750041) baseStart_3750041 baseEnd_3750041 := by
    simpa [prefixWord, tailWord_3750041, baseEnd_3750041] using wordTrace_append hprefix tailTrace_3750041
  have hstable : (prefixWord ++ tailWord_3750041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750041).length < 2 ^ (prefixWord ++ tailWord_3750041).sum := by decide
  have hdescent : baseEnd_3750041 < baseStart_3750041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750138 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_3750138 : Nat := 118140960795 + 3750138 * 2 ^ 59
def prefixEnd_3750138 : Nat := 4983230072969 + 3 ^ 40 * 3750138 * 2
def baseEnd_3750138 : Nat := 641874438230251267176145

theorem tailTrace_3750138 : CollatzResearch.WordTrace tailWord_3750138 prefixEnd_3750138 641874438230251267176145 := by
  unfold tailWord_3750138
  simp only [CollatzResearch.WordTrace]
  refine ⟨34194692421974493356220767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91185846458598648949922045 34194692421974493356220767)
  ·
    refine ⟨51292038632961740034331151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34194692421974493356220767 51292038632961740034331151)
    ·
      refine ⟨76938057949442610051496727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51292038632961740034331151 76938057949442610051496727)
      ·
        refine ⟨115407086924163915077245091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76938057949442610051496727 115407086924163915077245091)
        ·
          refine ⟨173110630386245872615867637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115407086924163915077245091 173110630386245872615867637)
          ·
            refine ⟨16229121598710550557737591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173110630386245872615867637 16229121598710550557737591)
            ·
              refine ⟨24343682398065825836606387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16229121598710550557737591 24343682398065825836606387)
              ·
                refine ⟨36515523597098738754909581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24343682398065825836606387 36515523597098738754909581)
                ·
                  refine ⟨13693321348912027033091093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36515523597098738754909581 13693321348912027033091093)
                  ·
                    refine ⟨641874438230251267176145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13693321348912027033091093 641874438230251267176145)
                    ·
                      rfl

theorem cell23_3750138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_3750138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750138 prefixEnd_3750138 := by exact prefixLift 3750138
  have htrace : WordTrace (prefixWord ++ tailWord_3750138) baseStart_3750138 baseEnd_3750138 := by
    simpa [prefixWord, tailWord_3750138, baseEnd_3750138] using wordTrace_append hprefix tailTrace_3750138
  have hstable : (prefixWord ++ tailWord_3750138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750138).length < 2 ^ (prefixWord ++ tailWord_3750138).sum := by decide
  have hdescent : baseEnd_3750138 < baseStart_3750138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750165 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_3750165 : Nat := 118140960795 + 3750165 * 2 ^ 59
def prefixEnd_3750165 : Nat := 4983230072969 + 3 ^ 40 * 3750165 * 2
def baseEnd_3750165 : Nat := 1925637178668425195890811

theorem tailTrace_3750165 : CollatzResearch.WordTrace tailWord_3750165 prefixEnd_3750165 1925637178668425195890811 := by
  unfold tailWord_3750165
  simp only [CollatzResearch.WordTrace]
  refine ⟨136779754458800157036115949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91186502972533438024077299 136779754458800157036115949)
  ·
    refine ⟨51292407922050058888543481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136779754458800157036115949 51292407922050058888543481)
    ·
      refine ⟨38469305941537544166407611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51292407922050058888543481 38469305941537544166407611)
      ·
        refine ⟨57703958912306316249611417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38469305941537544166407611 57703958912306316249611417)
        ·
          refine ⟨43277969184229737187208563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57703958912306316249611417 43277969184229737187208563)
          ·
            refine ⟨64916953776344605780812845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43277969184229737187208563 64916953776344605780812845)
            ·
              refine ⟨24343857666129227167804817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64916953776344605780812845 24343857666129227167804817)
              ·
                refine ⟨18257893249596920375853613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24343857666129227167804817 18257893249596920375853613)
                ·
                  refine ⟨6846709968598845140945105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18257893249596920375853613 6846709968598845140945105)
                  ·
                    refine ⟨5135032476449133855708829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6846709968598845140945105 5135032476449133855708829)
                    ·
                      refine ⟨1925637178668425195890811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5135032476449133855708829 1925637178668425195890811)
                      ·
                        rfl

theorem cell23_3750165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_3750165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750165 prefixEnd_3750165 := by exact prefixLift 3750165
  have htrace : WordTrace (prefixWord ++ tailWord_3750165) baseStart_3750165 baseEnd_3750165 := by
    simpa [prefixWord, tailWord_3750165, baseEnd_3750165] using wordTrace_append hprefix tailTrace_3750165
  have hstable : (prefixWord ++ tailWord_3750165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750165).length < 2 ^ (prefixWord ++ tailWord_3750165).sum := by decide
  have hdescent : baseEnd_3750165 < baseStart_3750165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750175 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_3750175 : Nat := 118140960795 + 3750175 * 2 ^ 59
def prefixEnd_3750175 : Nat := 4983230072969 + 3 ^ 40 * 3750175 * 2
def baseEnd_3750175 : Nat := 1925642313474970156765765

theorem tailTrace_3750175 : CollatzResearch.WordTrace tailWord_3750175 prefixEnd_3750175 1925642313474970156765765 := by
  unfold tailWord_3750175
  simp only [CollatzResearch.WordTrace]
  refine ⟨136780119188763928743979979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91186746125842619162653319 136780119188763928743979979)
  ·
    refine ⟨205170178783145893115969969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136780119188763928743979979 205170178783145893115969969)
    ·
      refine ⟨153877634087359419836977477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205170178783145893115969969 153877634087359419836977477)
      ·
        refine ⟨28852056391379891219433277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153877634087359419836977477 28852056391379891219433277)
        ·
          refine ⟨10819521146767459207287479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28852056391379891219433277 10819521146767459207287479)
          ·
            refine ⟨16229281720151188810931219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819521146767459207287479 16229281720151188810931219)
            ·
              refine ⟨24343922580226783216396829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16229281720151188810931219 24343922580226783216396829)
              ·
                refine ⟨9128970967585043706148811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24343922580226783216396829 9128970967585043706148811)
                ·
                  refine ⟨13693456451377565559223217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9128970967585043706148811 13693456451377565559223217)
                  ·
                    refine ⟨10270092338533174169417413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13693456451377565559223217 10270092338533174169417413)
                    ·
                      refine ⟨1925642313474970156765765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10270092338533174169417413 1925642313474970156765765)
                      ·
                        rfl

theorem cell23_3750175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_3750175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750175 prefixEnd_3750175 := by exact prefixLift 3750175
  have htrace : WordTrace (prefixWord ++ tailWord_3750175) baseStart_3750175 baseEnd_3750175 := by
    simpa [prefixWord, tailWord_3750175, baseEnd_3750175] using wordTrace_append hprefix tailTrace_3750175
  have hstable : (prefixWord ++ tailWord_3750175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750175).length < 2 ^ (prefixWord ++ tailWord_3750175).sum := by decide
  have hdescent : baseEnd_3750175 < baseStart_3750175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750195 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 3]
def baseStart_3750195 : Nat := 118140960795 + 3750195 * 2 ^ 59
def prefixEnd_3750195 : Nat := 4983230072969 + 3 ^ 40 * 3750195 * 2
def baseEnd_3750195 : Nat := 1925652583088060078515673

theorem tailTrace_3750195 : CollatzResearch.WordTrace tailWord_3750195 prefixEnd_3750195 1925652583088060078515673 := by
  unfold tailWord_3750195
  simp only [CollatzResearch.WordTrace]
  refine ⟨136780848648691472159708039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91187232432460981439805359 136780848648691472159708039)
  ·
    refine ⟨205171272973037208239562059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136780848648691472159708039 205171272973037208239562059)
    ·
      refine ⟨307756909459555812359343089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205171272973037208239562059 307756909459555812359343089)
      ·
        refine ⟨230817682094666859269507317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307756909459555812359343089 230817682094666859269507317)
        ·
          refine ⟨21639157696375018056516311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230817682094666859269507317 21639157696375018056516311)
          ·
            refine ⟨32458736544562527084774467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21639157696375018056516311 32458736544562527084774467)
            ·
              refine ⟨48688104816843790627161701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32458736544562527084774467 48688104816843790627161701)
              ·
                refine ⟨9129019653158210742592819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48688104816843790627161701 9129019653158210742592819)
                ·
                  refine ⟨13693529479737316113889229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9129019653158210742592819 13693529479737316113889229)
                  ·
                    refine ⟨5135073554901493542708461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13693529479737316113889229 5135073554901493542708461)
                    ·
                      refine ⟨1925652583088060078515673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5135073554901493542708461 1925652583088060078515673)
                      ·
                        rfl

theorem cell23_3750195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_3750195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750195 prefixEnd_3750195 := by exact prefixLift 3750195
  have htrace : WordTrace (prefixWord ++ tailWord_3750195) baseStart_3750195 baseEnd_3750195 := by
    simpa [prefixWord, tailWord_3750195, baseEnd_3750195] using wordTrace_append hprefix tailTrace_3750195
  have hstable : (prefixWord ++ tailWord_3750195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750195).length < 2 ^ (prefixWord ++ tailWord_3750195).sum := by decide
  have hdescent : baseEnd_3750195 < baseStart_3750195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750196 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_3750196 : Nat := 118140960795 + 3750196 * 2 ^ 59
def prefixEnd_3750196 : Nat := 4983230072969 + 3 ^ 40 * 3750196 * 2
def baseEnd_3750196 : Nat := 1925653096568714574603169

theorem tailTrace_3750196 : CollatzResearch.WordTrace tailWord_3750196 prefixEnd_3750196 1925653096568714574603169 := by
  unfold tailWord_3750196
  simp only [CollatzResearch.WordTrace]
  refine ⟨68390442560843924665247221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91187256747791899553662961 68390442560843924665247221)
  ·
    refine ⟨6411603990079117937366927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68390442560843924665247221 6411603990079117937366927)
    ·
      refine ⟨9617405985118676906050391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6411603990079117937366927 9617405985118676906050391)
      ·
        refine ⟨14426108977678015359075587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9617405985118676906050391 14426108977678015359075587)
        ·
          refine ⟨21639163466517023038613381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14426108977678015359075587 21639163466517023038613381)
          ·
            refine ⟨4057343149971941819740009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21639163466517023038613381 4057343149971941819740009)
            ·
              refine ⟨3043007362478956364805007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4057343149971941819740009 3043007362478956364805007)
              ·
                refine ⟨4564511043718434547207511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043007362478956364805007 4564511043718434547207511)
                ·
                  refine ⟨6846766565577651820811267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564511043718434547207511 6846766565577651820811267)
                  ·
                    refine ⟨10270149848366477731216901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6846766565577651820811267 10270149848366477731216901)
                    ·
                      refine ⟨1925653096568714574603169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10270149848366477731216901 1925653096568714574603169)
                      ·
                        rfl

theorem cell23_3750196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_3750196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750196 prefixEnd_3750196 := by exact prefixLift 3750196
  have htrace : WordTrace (prefixWord ++ tailWord_3750196) baseStart_3750196 baseEnd_3750196 := by
    simpa [prefixWord, tailWord_3750196, baseEnd_3750196] using wordTrace_append hprefix tailTrace_3750196
  have hstable : (prefixWord ++ tailWord_3750196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750196).length < 2 ^ (prefixWord ++ tailWord_3750196).sum := by decide
  have hdescent : baseEnd_3750196 < baseStart_3750196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750208 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_3750208 : Nat := 118140960795 + 3750208 * 2 ^ 59
def prefixEnd_3750208 : Nat := 4983230072969 + 3 ^ 40 * 3750208 * 2
def baseEnd_3750208 : Nat := 1925659258336568527653113

theorem tailTrace_3750208 : CollatzResearch.WordTrace tailWord_3750208 prefixEnd_3750208 1925659258336568527653113 := by
  unfold tailWord_3750208
  simp only [CollatzResearch.WordTrace]
  refine ⟨68390661398822187689965639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91187548531762916919954185 68390661398822187689965639)
  ·
    refine ⟨102585992098233281534948459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68390661398822187689965639 102585992098233281534948459)
    ·
      refine ⟨153878988147349922302422689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102585992098233281534948459 153878988147349922302422689)
      ·
        refine ⟨115409241110512441726817017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153878988147349922302422689 115409241110512441726817017)
        ·
          refine ⟨86556930832884331295112763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115409241110512441726817017 86556930832884331295112763)
          ·
            refine ⟨129835396249326496942669145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86556930832884331295112763 129835396249326496942669145)
            ·
              refine ⟨97376547186994872707001859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129835396249326496942669145 97376547186994872707001859)
              ·
                refine ⟨146064820780492309060502789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97376547186994872707001859 146064820780492309060502789)
                ·
                  refine ⟨27387153896342307948844273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146064820780492309060502789 27387153896342307948844273)
                  ·
                    refine ⟨20540365422256730961633205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27387153896342307948844273 20540365422256730961633205)
                    ·
                      refine ⟨1925659258336568527653113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20540365422256730961633205 1925659258336568527653113)
                      ·
                        rfl

theorem cell23_3750208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_3750208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750208 prefixEnd_3750208 := by exact prefixLift 3750208
  have htrace : WordTrace (prefixWord ++ tailWord_3750208) baseStart_3750208 baseEnd_3750208 := by
    simpa [prefixWord, tailWord_3750208, baseEnd_3750208] using wordTrace_append hprefix tailTrace_3750208
  have hstable : (prefixWord ++ tailWord_3750208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750208).length < 2 ^ (prefixWord ++ tailWord_3750208).sum := by decide
  have hdescent : baseEnd_3750208 < baseStart_3750208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750222 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_3750222 : Nat := 118140960795 + 3750222 * 2 ^ 59
def prefixEnd_3750222 : Nat := 4983230072969 + 3 ^ 40 * 3750222 * 2
def baseEnd_3750222 : Nat := 1925666447065731472878049

theorem tailTrace_3750222 : CollatzResearch.WordTrace tailWord_3750222 prefixEnd_3750222 1925666447065731472878049 := by
  unfold tailWord_3750222
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097729177449206971367615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91187888946395770513960613 17097729177449206971367615)
  ·
    refine ⟨25646593766173810457051423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17097729177449206971367615 25646593766173810457051423)
    ·
      refine ⟨38469890649260715685577135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25646593766173810457051423 38469890649260715685577135)
      ·
        refine ⟨57704835973891073528365703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38469890649260715685577135 57704835973891073528365703)
        ·
          refine ⟨86557253960836610292548555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57704835973891073528365703 86557253960836610292548555)
          ·
            refine ⟨129835880941254915438822833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86557253960836610292548555 129835880941254915438822833)
            ·
              refine ⟨97376910705941186579117125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129835880941254915438822833 97376910705941186579117125)
              ·
                refine ⟨18258170757363972483584461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97376910705941186579117125 18258170757363972483584461)
                ·
                  refine ⟨6846814034011489681344173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18258170757363972483584461 6846814034011489681344173)
                  ·
                    refine ⟨2567555262754308630504065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6846814034011489681344173 2567555262754308630504065)
                    ·
                      refine ⟨1925666447065731472878049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567555262754308630504065 1925666447065731472878049)
                      ·
                        rfl

theorem cell23_3750222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_3750222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750222 prefixEnd_3750222 := by exact prefixLift 3750222
  have htrace : WordTrace (prefixWord ++ tailWord_3750222) baseStart_3750222 baseEnd_3750222 := by
    simpa [prefixWord, tailWord_3750222, baseEnd_3750222] using wordTrace_append hprefix tailTrace_3750222
  have hstable : (prefixWord ++ tailWord_3750222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750222).length < 2 ^ (prefixWord ++ tailWord_3750222).sum := by decide
  have hdescent : baseEnd_3750222 < baseStart_3750222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750229 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3750229 : Nat := 118140960795 + 3750229 * 2 ^ 59
def prefixEnd_3750229 : Nat := 4983230072969 + 3 ^ 40 * 3750229 * 2
def baseEnd_3750229 : Nat := 1925670041430312945490517

theorem tailTrace_3750229 : CollatzResearch.WordTrace tailWord_3750229 prefixEnd_3750229 1925670041430312945490517 := by
  unfold tailWord_3750229
  simp only [CollatzResearch.WordTrace]
  refine ⟨136782088730568295966445741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91188059153712197310963827 136782088730568295966445741)
  ·
    refine ⟨51293283273963110987417153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136782088730568295966445741 51293283273963110987417153)
    ·
      refine ⟨38469962455472333240562865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51293283273963110987417153 38469962455472333240562865)
      ·
        refine ⟨28852471841604249930422149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38469962455472333240562865 28852471841604249930422149)
        ·
          refine ⟨5409838470300796861954153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28852471841604249930422149 5409838470300796861954153)
          ·
            refine ⟨4057378852725597646465615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5409838470300796861954153 4057378852725597646465615)
            ·
              refine ⟨6086068279088396469698423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057378852725597646465615 6086068279088396469698423)
              ·
                refine ⟨9129102418632594704547635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086068279088396469698423 9129102418632594704547635)
                ·
                  refine ⟨13693653627948892056821453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9129102418632594704547635 13693653627948892056821453)
                  ·
                    refine ⟨5135120110480834521308045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13693653627948892056821453 5135120110480834521308045)
                    ·
                      refine ⟨1925670041430312945490517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5135120110480834521308045 1925670041430312945490517)
                      ·
                        rfl

theorem cell23_3750229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3750229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750229 prefixEnd_3750229 := by exact prefixLift 3750229
  have htrace : WordTrace (prefixWord ++ tailWord_3750229) baseStart_3750229 baseEnd_3750229 := by
    simpa [prefixWord, tailWord_3750229, baseEnd_3750229] using wordTrace_append hprefix tailTrace_3750229
  have hstable : (prefixWord ++ tailWord_3750229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750229).length < 2 ^ (prefixWord ++ tailWord_3750229).sum := by decide
  have hdescent : baseEnd_3750229 < baseStart_3750229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750236 : List Nat := [2, 2, 4, 3, 2, 1, 2, 7]
def baseStart_3750236 : Nat := 118140960795 + 3750236 * 2 ^ 59
def prefixEnd_3750236 : Nat := 4983230072969 + 3 ^ 40 * 3750236 * 2
def baseEnd_3750236 : Nat := 71321245770181274744555

theorem tailTrace_3750236 : CollatzResearch.WordTrace tailWord_3750236 prefixEnd_3750236 71321245770181274744555 := by
  unfold tailWord_3750236
  simp only [CollatzResearch.WordTrace]
  refine ⟨68391172020771468080975281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91188229361028624107967041 68391172020771468080975281)
  ·
    refine ⟨51293379015578601060731461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68391172020771468080975281 51293379015578601060731461)
    ·
      refine ⟨9617508565420987698887149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51293379015578601060731461 9617508565420987698887149)
      ·
        refine ⟨3606565712032870387082681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9617508565420987698887149 3606565712032870387082681)
        ·
          refine ⟨2704924284024652790312011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3606565712032870387082681 2704924284024652790312011)
          ·
            refine ⟨4057386426036979185468017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704924284024652790312011 4057386426036979185468017)
            ·
              refine ⟨3043039819527734389101013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4057386426036979185468017 3043039819527734389101013)
              ·
                refine ⟨71321245770181274744555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3043039819527734389101013 71321245770181274744555)
                ·
                  rfl

theorem cell23_3750236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 7].length) (baseStart_3750236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750236 prefixEnd_3750236 := by exact prefixLift 3750236
  have htrace : WordTrace (prefixWord ++ tailWord_3750236) baseStart_3750236 baseEnd_3750236 := by
    simpa [prefixWord, tailWord_3750236, baseEnd_3750236] using wordTrace_append hprefix tailTrace_3750236
  have hstable : (prefixWord ++ tailWord_3750236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750236).length < 2 ^ (prefixWord ++ tailWord_3750236).sum := by decide
  have hdescent : baseEnd_3750236 < baseStart_3750236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750269 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_3750269 : Nat := 118140960795 + 3750269 * 2 ^ 59
def prefixEnd_3750269 : Nat := 4983230072969 + 3 ^ 40 * 3750269 * 2
def baseEnd_3750269 : Nat := 1925690580656492788990333

theorem tailTrace_3750269 : CollatzResearch.WordTrace tailWord_3750269 prefixEnd_3750269 1925690580656492788990333 := by
  unfold tailWord_3750269
  simp only [CollatzResearch.WordTrace]
  refine ⟨136783547650423382797901861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91189031766948921865267907 136783547650423382797901861)
  ·
    refine ⟨25646915184454384274606599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136783547650423382797901861 25646915184454384274606599)
    ·
      refine ⟨38470372776681576411909899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25646915184454384274606599 38470372776681576411909899)
      ·
        refine ⟨57705559165022364617864849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38470372776681576411909899 57705559165022364617864849)
        ·
          refine ⟨43279169373766773463398637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57705559165022364617864849 43279169373766773463398637)
          ·
            refine ⟨16229688515162540048774489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43279169373766773463398637 16229688515162540048774489)
            ·
              refine ⟨12172266386371905036580867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16229688515162540048774489 12172266386371905036580867)
              ·
                refine ⟨18258399579557857554871301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12172266386371905036580867 18258399579557857554871301)
                ·
                  refine ⟨3423449921167098291538369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18258399579557857554871301 3423449921167098291538369)
                  ·
                    refine ⟨2567587440875323718653777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3423449921167098291538369 2567587440875323718653777)
                    ·
                      refine ⟨1925690580656492788990333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567587440875323718653777 1925690580656492788990333)
                      ·
                        rfl

theorem cell23_3750269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_3750269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750269 prefixEnd_3750269 := by exact prefixLift 3750269
  have htrace : WordTrace (prefixWord ++ tailWord_3750269) baseStart_3750269 baseEnd_3750269 := by
    simpa [prefixWord, tailWord_3750269, baseEnd_3750269] using wordTrace_append hprefix tailTrace_3750269
  have hstable : (prefixWord ++ tailWord_3750269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750269).length < 2 ^ (prefixWord ++ tailWord_3750269).sum := by decide
  have hdescent : baseEnd_3750269 < baseStart_3750269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750332 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3750332 : Nat := 118140960795 + 3750332 * 2 ^ 59
def prefixEnd_3750332 : Nat := 4983230072969 + 3 ^ 40 * 3750332 * 2
def baseEnd_3750332 : Nat := 1925722929937726042502543

theorem tailTrace_3750332 : CollatzResearch.WordTrace tailWord_3750332 prefixEnd_3750332 1925722929937726042502543 := by
  unfold tailWord_3750332
  simp only [CollatzResearch.WordTrace]
  refine ⟨68392922724597572278722625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91190563632796763038296833 68392922724597572278722625)
  ·
    refine ⟨51294692043448179209041969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68392922724597572278722625 51294692043448179209041969)
    ·
      refine ⟨38471019032586134406781477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51294692043448179209041969 38471019032586134406781477)
      ·
        refine ⟨7213316068609900201271527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38471019032586134406781477 7213316068609900201271527)
        ·
          refine ⟨10819974102914850301907291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7213316068609900201271527 10819974102914850301907291)
          ·
            refine ⟨16229961154372275452860937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819974102914850301907291 16229961154372275452860937)
            ·
              refine ⟨12172470865779206589645703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16229961154372275452860937 12172470865779206589645703)
              ·
                refine ⟨18258706298668809884468555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12172470865779206589645703 18258706298668809884468555)
                ·
                  refine ⟨27388059448003214826702833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18258706298668809884468555 27388059448003214826702833)
                  ·
                    refine ⟨20541044586002411120027125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27388059448003214826702833 20541044586002411120027125)
                    ·
                      refine ⟨1925722929937726042502543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20541044586002411120027125 1925722929937726042502543)
                      ·
                        rfl

theorem cell23_3750332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3750332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750332 prefixEnd_3750332 := by exact prefixLift 3750332
  have htrace : WordTrace (prefixWord ++ tailWord_3750332) baseStart_3750332 baseEnd_3750332 := by
    simpa [prefixWord, tailWord_3750332, baseEnd_3750332] using wordTrace_append hprefix tailTrace_3750332
  have hstable : (prefixWord ++ tailWord_3750332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750332).length < 2 ^ (prefixWord ++ tailWord_3750332).sum := by decide
  have hdescent : baseEnd_3750332 < baseStart_3750332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750362 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_3750362 : Nat := 118140960795 + 3750362 * 2 ^ 59
def prefixEnd_3750362 : Nat := 4983230072969 + 3 ^ 40 * 3750362 * 2
def baseEnd_3750362 : Nat := 1925738334357360925127405

theorem tailTrace_3750362 : CollatzResearch.WordTrace tailWord_3750362 prefixEnd_3750362 1925738334357360925127405 := by
  unfold tailWord_3750362
  simp only [CollatzResearch.WordTrace]
  refine ⟨34196734909771614920259335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91191293092724306454024893 34196734909771614920259335)
  ·
    refine ⟨51295102364657422380389003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34196734909771614920259335 51295102364657422380389003)
    ·
      refine ⟨76942653546986133570583505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51295102364657422380389003 76942653546986133570583505)
      ·
        refine ⟨57706990160239600177937629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76942653546986133570583505 57706990160239600177937629)
        ·
          refine ⟨21640121310089850066726611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57706990160239600177937629 21640121310089850066726611)
          ·
            refine ⟨32460181965134775100089917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21640121310089850066726611 32460181965134775100089917)
            ·
              refine ⟨12172568236925540662533719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32460181965134775100089917 12172568236925540662533719)
              ·
                refine ⟨18258852355388310993800579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12172568236925540662533719 18258852355388310993800579)
                ·
                  refine ⟨27388278533082466490700869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18258852355388310993800579 27388278533082466490700869)
                  ·
                    refine ⟨5135302224952962467006413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27388278533082466490700869 5135302224952962467006413)
                    ·
                      refine ⟨1925738334357360925127405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5135302224952962467006413 1925738334357360925127405)
                      ·
                        rfl

theorem cell23_3750362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_3750362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750362 prefixEnd_3750362 := by exact prefixLift 3750362
  have htrace : WordTrace (prefixWord ++ tailWord_3750362) baseStart_3750362 baseEnd_3750362 := by
    simpa [prefixWord, tailWord_3750362, baseEnd_3750362] using wordTrace_append hprefix tailTrace_3750362
  have hstable : (prefixWord ++ tailWord_3750362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750362).length < 2 ^ (prefixWord ++ tailWord_3750362).sum := by decide
  have hdescent : baseEnd_3750362 < baseStart_3750362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750382 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_3750382 : Nat := 118140960795 + 3750382 * 2 ^ 59
def prefixEnd_3750382 : Nat := 4983230072969 + 3 ^ 40 * 3750382 * 2
def baseEnd_3750382 : Nat := 213972067107827871875257

theorem tailTrace_3750382 : CollatzResearch.WordTrace tailWord_3750382 prefixEnd_3750382 213972067107827871875257 := by
  unfold tailWord_3750382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17098458637376750387095675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91191779399342668731176933 17098458637376750387095675)
  ·
    refine ⟨25647687956065125580643513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17098458637376750387095675 25647687956065125580643513)
    ·
      refine ⟨19235765967048844185482635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25647687956065125580643513 19235765967048844185482635)
      ·
        refine ⟨28853648950573266278223953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19235765967048844185482635 28853648950573266278223953)
        ·
          refine ⟨21640236712929949708667965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28853648950573266278223953 21640236712929949708667965)
          ·
            refine ⟨8115088767348731140750487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21640236712929949708667965 8115088767348731140750487)
            ·
              refine ⟨12172633151023096711125731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115088767348731140750487 12172633151023096711125731)
              ·
                refine ⟨18258949726534645066688597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12172633151023096711125731 18258949726534645066688597)
                ·
                  refine ⟨213972067107827871875257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18258949726534645066688597 213972067107827871875257)
                  ·
                    rfl

theorem cell23_3750382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_3750382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750382 prefixEnd_3750382 := by exact prefixLift 3750382
  have htrace : WordTrace (prefixWord ++ tailWord_3750382) baseStart_3750382 baseEnd_3750382 := by
    simpa [prefixWord, tailWord_3750382, baseEnd_3750382] using wordTrace_append hprefix tailTrace_3750382
  have hstable : (prefixWord ++ tailWord_3750382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750382).length < 2 ^ (prefixWord ++ tailWord_3750382).sum := by decide
  have hdescent : baseEnd_3750382 < baseStart_3750382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750385 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_3750385 : Nat := 118140960795 + 3750385 * 2 ^ 59
def prefixEnd_3750385 : Nat := 4983230072969 + 3 ^ 40 * 3750385 * 2
def baseEnd_3750385 : Nat := 1925750144412414335139799

theorem tailTrace_3750385 : CollatzResearch.WordTrace tailWord_3750385 prefixEnd_3750385 1925750144412414335139799 := by
  unfold tailWord_3750385
  simp only [CollatzResearch.WordTrace]
  refine ⟨136787778518003134609124609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91191852345335423072749739 136787778518003134609124609)
  ·
    refine ⟨102590833888502350956843457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136787778518003134609124609 102590833888502350956843457)
    ·
      refine ⟨76943125416376763217632593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102590833888502350956843457 76943125416376763217632593)
      ·
        refine ⟨57707344062282572413224445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76943125416376763217632593 57707344062282572413224445)
        ·
          refine ⟨21640254023355964654959167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57707344062282572413224445 21640254023355964654959167)
          ·
            refine ⟨32460381035033946982438751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21640254023355964654959167 32460381035033946982438751)
            ·
              refine ⟨48690571552550920473658127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32460381035033946982438751 48690571552550920473658127)
              ·
                refine ⟨73035857328826380710487191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48690571552550920473658127 73035857328826380710487191)
                ·
                  refine ⟨109553785993239571065730787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73035857328826380710487191 109553785993239571065730787)
                  ·
                    refine ⟨164330678989859356598596181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109553785993239571065730787 164330678989859356598596181)
                    ·
                      refine ⟨1925750144412414335139799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 164330678989859356598596181 1925750144412414335139799)
                      ·
                        rfl

theorem cell23_3750385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_3750385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750385 prefixEnd_3750385 := by exact prefixLift 3750385
  have htrace : WordTrace (prefixWord ++ tailWord_3750385) baseStart_3750385 baseEnd_3750385 := by
    simpa [prefixWord, tailWord_3750385, baseEnd_3750385] using wordTrace_append hprefix tailTrace_3750385
  have hstable : (prefixWord ++ tailWord_3750385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750385).length < 2 ^ (prefixWord ++ tailWord_3750385).sum := by decide
  have hdescent : baseEnd_3750385 < baseStart_3750385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750386 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_3750386 : Nat := 118140960795 + 3750386 * 2 ^ 59
def prefixEnd_3750386 : Nat := 4983230072969 + 3 ^ 40 * 3750386 * 2
def baseEnd_3750386 : Nat := 641916885964356277075765

theorem tailTrace_3750386 : CollatzResearch.WordTrace tailWord_3750386 prefixEnd_3750386 641916885964356277075765 := by
  unfold tailWord_3750386
  simp only [CollatzResearch.WordTrace]
  refine ⟨34196953747749877944977753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91191876660666341186607341 34196953747749877944977753)
  ·
    refine ⟨25647715310812408458733315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34196953747749877944977753 25647715310812408458733315)
    ·
      refine ⟨38471572966218612688099973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25647715310812408458733315 38471572966218612688099973)
      ·
        refine ⟨7213419931165989879018745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38471572966218612688099973 7213419931165989879018745)
        ·
          refine ⟨5410064948374492409264059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7213419931165989879018745 5410064948374492409264059)
          ·
            refine ⟨8115097422561738613896089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410064948374492409264059 8115097422561738613896089)
            ·
              refine ⟨6086323066921303960422067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8115097422561738613896089 6086323066921303960422067)
              ·
                refine ⟨9129484600381955940633101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086323066921303960422067 9129484600381955940633101)
                ·
                  refine ⟨3423556725143233477737413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9129484600381955940633101 3423556725143233477737413)
                  ·
                    refine ⟨641916885964356277075765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3423556725143233477737413 641916885964356277075765)
                    ·
                      rfl

theorem cell23_3750386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_3750386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750386 prefixEnd_3750386 := by exact prefixLift 3750386
  have htrace : WordTrace (prefixWord ++ tailWord_3750386) baseStart_3750386 baseEnd_3750386 := by
    simpa [prefixWord, tailWord_3750386, baseEnd_3750386] using wordTrace_append hprefix tailTrace_3750386
  have hstable : (prefixWord ++ tailWord_3750386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750386).length < 2 ^ (prefixWord ++ tailWord_3750386).sum := by decide
  have hdescent : baseEnd_3750386 < baseStart_3750386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750405 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_3750405 : Nat := 118140960795 + 3750405 * 2 ^ 59
def prefixEnd_3750405 : Nat := 4983230072969 + 3 ^ 40 * 3750405 * 2
def baseEnd_3750405 : Nat := 1925760414025504256889707

theorem tailTrace_3750405 : CollatzResearch.WordTrace tailWord_3750405 prefixEnd_3750405 1925760414025504256889707 := by
  unfold tailWord_3750405
  simp only [CollatzResearch.WordTrace]
  refine ⟨136788507977930678024852669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91192338651953785349901779 136788507977930678024852669)
  ·
    refine ⟨51295690491724004259319751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136788507977930678024852669 51295690491724004259319751)
    ·
      refine ⟨76943535737586006388979627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51295690491724004259319751 76943535737586006388979627)
      ·
        refine ⟨115415303606379009583469441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76943535737586006388979627 115415303606379009583469441)
        ·
          refine ⟨86561477704784257187602081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115415303606379009583469441 86561477704784257187602081)
          ·
            refine ⟨64921108278588192890701561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86561477704784257187602081 64921108278588192890701561)
            ·
              refine ⟨48690831208941144668026171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64921108278588192890701561 48690831208941144668026171)
              ·
                refine ⟨73036246813411717002039257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48690831208941144668026171 73036246813411717002039257)
                ·
                  refine ⟨54777185110058787751529443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73036246813411717002039257 54777185110058787751529443)
                  ·
                    refine ⟨82165777665088181627294165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54777185110058787751529443 82165777665088181627294165)
                    ·
                      refine ⟨1925760414025504256889707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82165777665088181627294165 1925760414025504256889707)
                      ·
                        rfl

theorem cell23_3750405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_3750405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750405 prefixEnd_3750405 := by exact prefixLift 3750405
  have htrace : WordTrace (prefixWord ++ tailWord_3750405) baseStart_3750405 baseEnd_3750405 := by
    simpa [prefixWord, tailWord_3750405, baseEnd_3750405] using wordTrace_append hprefix tailTrace_3750405
  have hstable : (prefixWord ++ tailWord_3750405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750405).length < 2 ^ (prefixWord ++ tailWord_3750405).sum := by decide
  have hdescent : baseEnd_3750405 < baseStart_3750405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750419 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 2, 3, 2]
def baseStart_3750419 : Nat := 118140960795 + 3750419 * 2 ^ 59
def prefixEnd_3750419 : Nat := 4983230072969 + 3 ^ 40 * 3750419 * 2
def baseEnd_3750419 : Nat := 1925767602754667202114643

theorem tailTrace_3750419 : CollatzResearch.WordTrace tailWord_3750419 prefixEnd_3750419 1925767602754667202114643 := by
  unfold tailWord_3750419
  simp only [CollatzResearch.WordTrace]
  refine ⟨136789018599879958415862311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91192679066586638943908207 136789018599879958415862311)
  ·
    refine ⟨205183527899819937623793467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136789018599879958415862311 205183527899819937623793467)
    ·
      refine ⟨307775291849729906435690201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205183527899819937623793467 307775291849729906435690201)
      ·
        refine ⟨230831468887297429826767651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307775291849729906435690201 230831468887297429826767651)
        ·
          refine ⟨346247203330946144740151477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230831468887297429826767651 346247203330946144740151477)
          ·
            refine ⟨32460675312276201069389201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 346247203330946144740151477 32460675312276201069389201)
            ·
              refine ⟨24345506484207150802041901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32460675312276201069389201 24345506484207150802041901)
              ·
                refine ⟨9129564931577681550765713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24345506484207150802041901 9129564931577681550765713)
                ·
                  refine ⟨6847173698683261163074285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9129564931577681550765713 6847173698683261163074285)
                  ·
                    refine ⟨2567690137006222936152857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6847173698683261163074285 2567690137006222936152857)
                    ·
                      refine ⟨1925767602754667202114643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567690137006222936152857 1925767602754667202114643)
                      ·
                        rfl

theorem cell23_3750419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 3, 2].length) (baseStart_3750419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750419 prefixEnd_3750419 := by exact prefixLift 3750419
  have htrace : WordTrace (prefixWord ++ tailWord_3750419) baseStart_3750419 baseEnd_3750419 := by
    simpa [prefixWord, tailWord_3750419, baseEnd_3750419] using wordTrace_append hprefix tailTrace_3750419
  have hstable : (prefixWord ++ tailWord_3750419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750419).length < 2 ^ (prefixWord ++ tailWord_3750419).sum := by decide
  have hdescent : baseEnd_3750419 < baseStart_3750419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750420 : List Nat := [2, 4, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3750420 : Nat := 118140960795 + 3750420 * 2 ^ 59
def prefixEnd_3750420 : Nat := 4983230072969 + 3 ^ 40 * 3750420 * 2
def baseEnd_3750420 : Nat := 641922705411773899400713

theorem tailTrace_3750420 : CollatzResearch.WordTrace tailWord_3750420 prefixEnd_3750420 641922705411773899400713 := by
  unfold tailWord_3750420
  simp only [CollatzResearch.WordTrace]
  refine ⟨68394527536438167793324357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91192703381917557057765809 68394527536438167793324357)
  ·
    refine ⟨12823973913082156461248317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68394527536438167793324357 12823973913082156461248317)
    ·
      refine ⟨4808990217405808672968119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12823973913082156461248317 4808990217405808672968119)
      ·
        refine ⟨7213485326108713009452179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808990217405808672968119 7213485326108713009452179)
        ·
          refine ⟨10820227989163069514178269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7213485326108713009452179 10820227989163069514178269)
          ·
            refine ⟨4057585495936151067816851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10820227989163069514178269 4057585495936151067816851)
            ·
              refine ⟨6086378243904226601725277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057585495936151067816851 6086378243904226601725277)
              ·
                refine ⟨2282391841464084975646979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6086378243904226601725277 2282391841464084975646979)
                ·
                  refine ⟨3423587762196127463470469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282391841464084975646979 3423587762196127463470469)
                  ·
                    refine ⟨641922705411773899400713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3423587762196127463470469 641922705411773899400713)
                    ·
                      rfl

theorem cell23_3750420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3750420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750420 prefixEnd_3750420 := by exact prefixLift 3750420
  have htrace : WordTrace (prefixWord ++ tailWord_3750420) baseStart_3750420 baseEnd_3750420 := by
    simpa [prefixWord, tailWord_3750420, baseEnd_3750420] using wordTrace_append hprefix tailTrace_3750420
  have hstable : (prefixWord ++ tailWord_3750420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750420).length < 2 ^ (prefixWord ++ tailWord_3750420).sum := by decide
  have hdescent : baseEnd_3750420 < baseStart_3750420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750429 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3750429 : Nat := 118140960795 + 3750429 * 2 ^ 59
def prefixEnd_3750429 : Nat := 4983230072969 + 3 ^ 40 * 3750429 * 2
def baseEnd_3750429 : Nat := 641924245853737387663199

theorem tailTrace_3750429 : CollatzResearch.WordTrace tailWord_3750429 prefixEnd_3750429 641924245853737387663199 := by
  unfold tailWord_3750429
  simp only [CollatzResearch.WordTrace]
  refine ⟨136789383329843730123726341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91192922219895820082484227 136789383329843730123726341)
  ·
    refine ⟨25648009374345699398198689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136789383329843730123726341 25648009374345699398198689)
    ·
      refine ⟨19236007030759274548649017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25648009374345699398198689 19236007030759274548649017)
      ·
        refine ⟨14427005273069455911486763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19236007030759274548649017 14427005273069455911486763)
        ·
          refine ⟨21640507909604183867230145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14427005273069455911486763 21640507909604183867230145)
          ·
            refine ⟨16230380932203137900422609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21640507909604183867230145 16230380932203137900422609)
            ·
              refine ⟨12172785699152353425316957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16230380932203137900422609 12172785699152353425316957)
              ·
                refine ⟨4564794637182132534493859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12172785699152353425316957 4564794637182132534493859)
                ·
                  refine ⟨6847191955773198801740789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564794637182132534493859 6847191955773198801740789)
                  ·
                    refine ⟨641924245853737387663199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6847191955773198801740789 641924245853737387663199)
                    ·
                      rfl

theorem cell23_3750429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3750429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750429 prefixEnd_3750429 := by exact prefixLift 3750429
  have htrace : WordTrace (prefixWord ++ tailWord_3750429) baseStart_3750429 baseEnd_3750429 := by
    simpa [prefixWord, tailWord_3750429, baseEnd_3750429] using wordTrace_append hprefix tailTrace_3750429
  have hstable : (prefixWord ++ tailWord_3750429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750429).length < 2 ^ (prefixWord ++ tailWord_3750429).sum := by decide
  have hdescent : baseEnd_3750429 < baseStart_3750429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750469 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_3750469 : Nat := 118140960795 + 3750469 * 2 ^ 59
def prefixEnd_3750469 : Nat := 4983230072969 + 3 ^ 40 * 3750469 * 2
def baseEnd_3750469 : Nat := 1925793276787392006489413

theorem tailTrace_3750469 : CollatzResearch.WordTrace tailWord_3750469 prefixEnd_3750469 1925793276787392006489413 := by
  unfold tailWord_3750469
  simp only [CollatzResearch.WordTrace]
  refine ⟨136790842249698816955182461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91193894833132544636788307 136790842249698816955182461)
  ·
    refine ⟨51296565843637056358193423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136790842249698816955182461 51296565843637056358193423)
    ·
      refine ⟨76944848765455584537290135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51296565843637056358193423 76944848765455584537290135)
      ·
        refine ⟨115417273148183376805935203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76944848765455584537290135 115417273148183376805935203)
        ·
          refine ⟨173125909722275065208902805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115417273148183376805935203 173125909722275065208902805)
          ·
            refine ⟨8115277018231643681667319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173125909722275065208902805 8115277018231643681667319)
            ·
              refine ⟨12172915527347465522500979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115277018231643681667319 12172915527347465522500979)
              ·
                refine ⟨18259373291021198283751469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12172915527347465522500979 18259373291021198283751469)
                ·
                  refine ⟨6847264984132949356406801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18259373291021198283751469 6847264984132949356406801)
                  ·
                    refine ⟨5135448738099712017305101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6847264984132949356406801 5135448738099712017305101)
                    ·
                      refine ⟨1925793276787392006489413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5135448738099712017305101 1925793276787392006489413)
                      ·
                        rfl

theorem cell23_3750469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_3750469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750469 prefixEnd_3750469 := by exact prefixLift 3750469
  have htrace : WordTrace (prefixWord ++ tailWord_3750469) baseStart_3750469 baseEnd_3750469 := by
    simpa [prefixWord, tailWord_3750469, baseEnd_3750469] using wordTrace_append hprefix tailTrace_3750469
  have hstable : (prefixWord ++ tailWord_3750469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750469).length < 2 ^ (prefixWord ++ tailWord_3750469).sum := by decide
  have hdescent : baseEnd_3750469 < baseStart_3750469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750470 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_3750470 : Nat := 118140960795 + 3750470 * 2 ^ 59
def prefixEnd_3750470 : Nat := 4983230072969 + 3 ^ 40 * 3750470 * 2
def baseEnd_3750470 : Nat := 1925793790268046502576909

theorem tailTrace_3750470 : CollatzResearch.WordTrace tailWord_3750470 prefixEnd_3750470 1925793790268046502576909 := by
  unfold tailWord_3750470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4274714960084224816436527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91193919148463462750645909 4274714960084224816436527)
  ·
    refine ⟨6412072440126337224654791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4274714960084224816436527 6412072440126337224654791)
    ·
      refine ⟨9618108660189505836982187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6412072440126337224654791 9618108660189505836982187)
      ·
        refine ⟨14427162990284258755473281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9618108660189505836982187 14427162990284258755473281)
        ·
          refine ⟨10820372242713194066604961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14427162990284258755473281 10820372242713194066604961)
          ·
            refine ⟨8115279182034895549953721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10820372242713194066604961 8115279182034895549953721)
            ·
              refine ⟨6086459386526171662465291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8115279182034895549953721 6086459386526171662465291)
              ·
                refine ⟨9129689079789257493697937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086459386526171662465291 9129689079789257493697937)
                ·
                  refine ⟨6847266809841943120273453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9129689079789257493697937 6847266809841943120273453)
                  ·
                    refine ⟨2567725053690728670102545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6847266809841943120273453 2567725053690728670102545)
                    ·
                      refine ⟨1925793790268046502576909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567725053690728670102545 1925793790268046502576909)
                      ·
                        rfl

theorem cell23_3750470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_3750470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750470 prefixEnd_3750470 := by exact prefixLift 3750470
  have htrace : WordTrace (prefixWord ++ tailWord_3750470) baseStart_3750470 baseEnd_3750470 := by
    simpa [prefixWord, tailWord_3750470, baseEnd_3750470] using wordTrace_append hprefix tailTrace_3750470
  have hstable : (prefixWord ++ tailWord_3750470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750470).length < 2 ^ (prefixWord ++ tailWord_3750470).sum := by decide
  have hdescent : baseEnd_3750470 < baseStart_3750470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750494 : List Nat := [4, 4, 1, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_3750494 : Nat := 118140960795 + 3750494 * 2 ^ 59
def prefixEnd_3750494 : Nat := 4983230072969 + 3 ^ 40 * 3750494 * 2
def baseEnd_3750494 : Nat := 1925806113803754408676799

theorem tailTrace_3750494 : CollatzResearch.WordTrace tailWord_3750494 prefixEnd_3750494 1925806113803754408676799 := by
  unfold tailWord_3750494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17098969259326030778105317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91194502716405497483228357 17098969259326030778105317)
  ·
    refine ⟨3206056736123630770894747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17098969259326030778105317 3206056736123630770894747)
    ·
      refine ⟨4809085104185446156342121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3206056736123630770894747 4809085104185446156342121)
      ·
        refine ⟨3606813828139084617256591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4809085104185446156342121 3606813828139084617256591)
        ·
          refine ⟨5410220742208626925884887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606813828139084617256591 5410220742208626925884887)
          ·
            refine ⟨8115331113312940388827331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410220742208626925884887 8115331113312940388827331)
            ·
              refine ⟨12172996669969410583240997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115331113312940388827331 12172996669969410583240997)
              ·
                refine ⟨2282436875619264484357687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12172996669969410583240997 2282436875619264484357687)
                ·
                  refine ⟨3423655313428896726536531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282436875619264484357687 3423655313428896726536531)
                  ·
                    refine ⟨5135482970143345089804797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3423655313428896726536531 5135482970143345089804797)
                    ·
                      refine ⟨1925806113803754408676799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5135482970143345089804797 1925806113803754408676799)
                      ·
                        rfl

theorem cell23_3750494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_3750494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750494 prefixEnd_3750494 := by exact prefixLift 3750494
  have htrace : WordTrace (prefixWord ++ tailWord_3750494) baseStart_3750494 baseEnd_3750494 := by
    simpa [prefixWord, tailWord_3750494, baseEnd_3750494] using wordTrace_append hprefix tailTrace_3750494
  have hstable : (prefixWord ++ tailWord_3750494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750494).length < 2 ^ (prefixWord ++ tailWord_3750494).sum := by decide
  have hdescent : baseEnd_3750494 < baseStart_3750494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750539 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 3, 4, 2]
def baseStart_3750539 : Nat := 118140960795 + 3750539 * 2 ^ 59
def prefixEnd_3750539 : Nat := 4983230072969 + 3 ^ 40 * 3750539 * 2
def baseEnd_3750539 : Nat := 1925829220433206732614091

theorem tailTrace_3750539 : CollatzResearch.WordTrace tailWord_3750539 prefixEnd_3750539 1925829220433206732614091 := by
  unfold tailWord_3750539
  simp only [CollatzResearch.WordTrace]
  refine ⟨136793395359445218910230671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91195596906296812606820447 136793395359445218910230671)
  ·
    refine ⟨205190093039167828365346007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136793395359445218910230671 205190093039167828365346007)
    ·
      refine ⟨307785139558751742548019011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205190093039167828365346007 307785139558751742548019011)
      ·
        refine ⟨461677709338127613822028517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307785139558751742548019011 461677709338127613822028517)
        ·
          refine ⟨86564570500898927591630347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 461677709338127613822028517 86564570500898927591630347)
          ·
            refine ⟨129846855751348391387445521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86564570500898927591630347 129846855751348391387445521)
            ·
              refine ⟨97385141813511293540584141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129846855751348391387445521 97385141813511293540584141)
              ·
                refine ⟨36519428180066735077719053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97385141813511293540584141 36519428180066735077719053)
                ·
                  refine ⟨13694785567525025654144645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36519428180066735077719053 13694785567525025654144645)
                  ·
                    refine ⟨2567772293910942310152121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13694785567525025654144645 2567772293910942310152121)
                    ·
                      refine ⟨1925829220433206732614091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567772293910942310152121 1925829220433206732614091)
                      ·
                        rfl

theorem cell23_3750539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 4, 2].length) (baseStart_3750539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750539 prefixEnd_3750539 := by exact prefixLift 3750539
  have htrace : WordTrace (prefixWord ++ tailWord_3750539) baseStart_3750539 baseEnd_3750539 := by
    simpa [prefixWord, tailWord_3750539, baseEnd_3750539] using wordTrace_append hprefix tailTrace_3750539
  have hstable : (prefixWord ++ tailWord_3750539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750539).length < 2 ^ (prefixWord ++ tailWord_3750539).sum := by decide
  have hdescent : baseEnd_3750539 < baseStart_3750539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750567 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_3750567 : Nat := 118140960795 + 3750567 * 2 ^ 59
def prefixEnd_3750567 : Nat := 4983230072969 + 3 ^ 40 * 3750567 * 2
def baseEnd_3750567 : Nat := 1925843597891532623063963

theorem tailTrace_3750567 : CollatzResearch.WordTrace tailWord_3750567 prefixEnd_3750567 1925843597891532623063963 := by
  unfold tailWord_3750567
  simp only [CollatzResearch.WordTrace]
  refine ⟨136794416603343779692249955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91196277735562519794833303 136794416603343779692249955)
  ·
    refine ⟨205191624905015669538374933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136794416603343779692249955 205191624905015669538374933)
    ·
      refine ⟨9618357417422609509611325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205191624905015669538374933 9618357417422609509611325)
      ·
        refine ⟨3606884031533478566104247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9618357417422609509611325 3606884031533478566104247)
        ·
          refine ⟨5410326047300217849156371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606884031533478566104247 5410326047300217849156371)
          ·
            refine ⟨8115489070950326773734557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410326047300217849156371 8115489070950326773734557)
            ·
              refine ⟨3043308401606372540150459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8115489070950326773734557 3043308401606372540150459)
              ·
                refine ⟨4564962602409558810225689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043308401606372540150459 4564962602409558810225689)
                ·
                  refine ⟨3423721951807169107669267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4564962602409558810225689 3423721951807169107669267)
                  ·
                    refine ⟨5135582927710753661503901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3423721951807169107669267 5135582927710753661503901)
                    ·
                      refine ⟨1925843597891532623063963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5135582927710753661503901 1925843597891532623063963)
                      ·
                        rfl

theorem cell23_3750567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_3750567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750567 prefixEnd_3750567 := by exact prefixLift 3750567
  have htrace : WordTrace (prefixWord ++ tailWord_3750567) baseStart_3750567 baseEnd_3750567 := by
    simpa [prefixWord, tailWord_3750567, baseEnd_3750567] using wordTrace_append hprefix tailTrace_3750567
  have hstable : (prefixWord ++ tailWord_3750567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750567).length < 2 ^ (prefixWord ++ tailWord_3750567).sum := by decide
  have hdescent : baseEnd_3750567 < baseStart_3750567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750573 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_3750573 : Nat := 118140960795 + 3750573 * 2 ^ 59
def prefixEnd_3750573 : Nat := 4983230072969 + 3 ^ 40 * 3750573 * 2
def baseEnd_3750573 : Nat := 1925846678775459599588935

theorem tailTrace_3750573 : CollatzResearch.WordTrace tailWord_3750573 prefixEnd_3750573 1925846678775459599588935 := by
  unfold tailWord_3750573
  simp only [CollatzResearch.WordTrace]
  refine ⟨136794635441322042716968373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91196423627548028477978915 136794635441322042716968373)
  ·
    refine ⟨12824497072623941504715785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136794635441322042716968373 12824497072623941504715785)
    ·
      refine ⟨9618372804467956128536839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12824497072623941504715785 9618372804467956128536839)
      ·
        refine ⟨14427559206701934192805259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9618372804467956128536839 14427559206701934192805259)
        ·
          refine ⟨21641338810052901289207889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14427559206701934192805259 21641338810052901289207889)
          ·
            refine ⟨16231004107539675966905917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21641338810052901289207889 16231004107539675966905917)
            ·
              refine ⟨6086626540327378487589719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16231004107539675966905917 6086626540327378487589719)
              ·
                refine ⟨9129939810491067731384579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086626540327378487589719 9129939810491067731384579)
                ·
                  refine ⟨13694909715736601597076869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9129939810491067731384579 13694909715736601597076869)
                  ·
                    refine ⟨2567795571700612799451913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13694909715736601597076869 2567795571700612799451913)
                    ·
                      refine ⟨1925846678775459599588935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567795571700612799451913 1925846678775459599588935)
                      ·
                        rfl

theorem cell23_3750573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_3750573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750573 prefixEnd_3750573 := by exact prefixLift 3750573
  have htrace : WordTrace (prefixWord ++ tailWord_3750573) baseStart_3750573 baseEnd_3750573 := by
    simpa [prefixWord, tailWord_3750573, baseEnd_3750573] using wordTrace_append hprefix tailTrace_3750573
  have hstable : (prefixWord ++ tailWord_3750573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750573).length < 2 ^ (prefixWord ++ tailWord_3750573).sum := by decide
  have hdescent : baseEnd_3750573 < baseStart_3750573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750593 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3750593 : Nat := 118140960795 + 3750593 * 2 ^ 59
def prefixEnd_3750593 : Nat := 4983230072969 + 3 ^ 40 * 3750593 * 2
def baseEnd_3750593 : Nat := 1925856948388549521338843

theorem tailTrace_3750593 : CollatzResearch.WordTrace tailWord_3750593 prefixEnd_3750593 1925856948388549521338843 := by
  unfold tailWord_3750593
  simp only [CollatzResearch.WordTrace]
  refine ⟨136795364901249586132696433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91196909934166390755130955 136795364901249586132696433)
  ·
    refine ⟨102596523675937189599522325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136795364901249586132696433 102596523675937189599522325)
    ·
      refine ⟨4809212047309555762477609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102596523675937189599522325 4809212047309555762477609)
      ·
        refine ⟨3606909035482166821858207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4809212047309555762477609 3606909035482166821858207)
        ·
          refine ⟨5410363553223250232787311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606909035482166821858207 5410363553223250232787311)
          ·
            refine ⟨8115545329834875349180967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410363553223250232787311 8115545329834875349180967)
            ·
              refine ⟨12173317994752313023771451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115545329834875349180967 12173317994752313023771451)
              ·
                refine ⟨18259976992128469535657177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12173317994752313023771451 18259976992128469535657177)
                ·
                  refine ⟨13694982744096352151742883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18259976992128469535657177 13694982744096352151742883)
                  ·
                    refine ⟨20542474116144528227614325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13694982744096352151742883 20542474116144528227614325)
                    ·
                      refine ⟨1925856948388549521338843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20542474116144528227614325 1925856948388549521338843)
                      ·
                        rfl

theorem cell23_3750593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3750593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750593 prefixEnd_3750593 := by exact prefixLift 3750593
  have htrace : WordTrace (prefixWord ++ tailWord_3750593) baseStart_3750593 baseEnd_3750593 := by
    simpa [prefixWord, tailWord_3750593, baseEnd_3750593] using wordTrace_append hprefix tailTrace_3750593
  have hstable : (prefixWord ++ tailWord_3750593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750593).length < 2 ^ (prefixWord ++ tailWord_3750593).sum := by decide
  have hdescent : baseEnd_3750593 < baseStart_3750593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750609 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 2, 5]
def baseStart_3750609 : Nat := 118140960795 + 3750609 * 2 ^ 59
def prefixEnd_3750609 : Nat := 4983230072969 + 3 ^ 40 * 3750609 * 2
def baseEnd_3750609 : Nat := 641955054693007152912923

theorem tailTrace_3750609 : CollatzResearch.WordTrace tailWord_3750609 prefixEnd_3750609 641955054693007152912923 := by
  unfold tailWord_3750609
  simp only [CollatzResearch.WordTrace]
  refine ⟨136795948469191620865278881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91197298979461080576852587 136795948469191620865278881)
  ·
    refine ⟨102596961351893715648959161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136795948469191620865278881 102596961351893715648959161)
    ·
      refine ⟨76947721013920286736719371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102596961351893715648959161 76947721013920286736719371)
      ·
        refine ⟨115421581520880430105079057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76947721013920286736719371 115421581520880430105079057)
        ·
          refine ⟨86566186140660322578809293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115421581520880430105079057 86566186140660322578809293)
          ·
            refine ⟨32462319802747620967053485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86566186140660322578809293 32462319802747620967053485)
            ·
              refine ⟨12173369926030357862645057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32462319802747620967053485 12173369926030357862645057)
              ·
                refine ⟨9130027444522768396983793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12173369926030357862645057 9130027444522768396983793)
                ·
                  refine ⟨6847520583392076297737845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9130027444522768396983793 6847520583392076297737845)
                  ·
                    refine ⟨641955054693007152912923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6847520583392076297737845 641955054693007152912923)
                    ·
                      rfl

theorem cell23_3750609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_3750609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750609 prefixEnd_3750609 := by exact prefixLift 3750609
  have htrace : WordTrace (prefixWord ++ tailWord_3750609) baseStart_3750609 baseEnd_3750609 := by
    simpa [prefixWord, tailWord_3750609, baseEnd_3750609] using wordTrace_append hprefix tailTrace_3750609
  have hstable : (prefixWord ++ tailWord_3750609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750609).length < 2 ^ (prefixWord ++ tailWord_3750609).sum := by decide
  have hdescent : baseEnd_3750609 < baseStart_3750609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750613 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 7]
def baseStart_3750613 : Nat := 118140960795 + 3750613 * 2 ^ 59
def prefixEnd_3750613 : Nat := 4983230072969 + 3 ^ 40 * 3750613 * 2
def baseEnd_3750613 : Nat := 213985246444626604787639

theorem tailTrace_3750613 : CollatzResearch.WordTrace tailWord_3750613 prefixEnd_3750613 213985246444626604787639 := by
  unfold tailWord_3750613
  simp only [CollatzResearch.WordTrace]
  refine ⟨136796094361177129548424493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91197396240784753032282995 136796094361177129548424493)
  ·
    refine ⟨51298535385441423580659185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136796094361177129548424493 51298535385441423580659185)
    ·
      refine ⟨38473901539081067685494389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51298535385441423580659185 38473901539081067685494389)
      ·
        refine ⟨3606928269288850095515099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38473901539081067685494389 3606928269288850095515099)
        ·
          refine ⟨5410392403933275143272649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606928269288850095515099 5410392403933275143272649)
          ·
            refine ⟨4057794302949956357454487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5410392403933275143272649 4057794302949956357454487)
            ·
              refine ⟨6086691454424934536181731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057794302949956357454487 6086691454424934536181731)
              ·
                refine ⟨9130037181637401804272597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086691454424934536181731 9130037181637401804272597)
                ·
                  refine ⟨213985246444626604787639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9130037181637401804272597 213985246444626604787639)
                  ·
                    rfl

theorem cell23_3750613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_3750613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750613 prefixEnd_3750613 := by exact prefixLift 3750613
  have htrace : WordTrace (prefixWord ++ tailWord_3750613) baseStart_3750613 baseEnd_3750613 := by
    simpa [prefixWord, tailWord_3750613, baseEnd_3750613] using wordTrace_append hprefix tailTrace_3750613
  have hstable : (prefixWord ++ tailWord_3750613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750613).length < 2 ^ (prefixWord ++ tailWord_3750613).sum := by decide
  have hdescent : baseEnd_3750613 < baseStart_3750613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750649 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 3]
def baseStart_3750649 : Nat := 118140960795 + 3750649 * 2 ^ 59
def prefixEnd_3750649 : Nat := 4983230072969 + 3 ^ 40 * 3750649 * 2
def baseEnd_3750649 : Nat := 1925885703305201302238585

theorem tailTrace_3750649 : CollatzResearch.WordTrace tailWord_3750649 prefixEnd_3750649 1925885703305201302238585 := by
  unfold tailWord_3750649
  simp only [CollatzResearch.WordTrace]
  refine ⟨136797407389046707696735001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91198271592697805131156667 136797407389046707696735001)
  ·
    refine ⟨102598055541785030772551251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136797407389046707696735001 102598055541785030772551251)
    ·
      refine ⟨153897083312677546158826877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102598055541785030772551251 153897083312677546158826877)
      ·
        refine ⟨57711406242254079809560079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153897083312677546158826877 57711406242254079809560079)
        ·
          refine ⟨86567109363381119714340119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57711406242254079809560079 86567109363381119714340119)
          ·
            refine ⟨129850664045071679571510179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86567109363381119714340119 129850664045071679571510179)
            ·
              refine ⟨194775996067607519357265269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129850664045071679571510179 194775996067607519357265269)
              ·
                refine ⟨18260249631338204939743619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194775996067607519357265269 18260249631338204939743619)
                ·
                  refine ⟨27390374447007307409615429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18260249631338204939743619 27390374447007307409615429)
                  ·
                    refine ⟨5135695208813870139302893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27390374447007307409615429 5135695208813870139302893)
                    ·
                      refine ⟨1925885703305201302238585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5135695208813870139302893 1925885703305201302238585)
                      ·
                        rfl

theorem cell23_3750649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_3750649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750649 prefixEnd_3750649 := by exact prefixLift 3750649
  have htrace : WordTrace (prefixWord ++ tailWord_3750649) baseStart_3750649 baseEnd_3750649 := by
    simpa [prefixWord, tailWord_3750649, baseEnd_3750649] using wordTrace_append hprefix tailTrace_3750649
  have hstable : (prefixWord ++ tailWord_3750649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750649).length < 2 ^ (prefixWord ++ tailWord_3750649).sum := by decide
  have hdescent : baseEnd_3750649 < baseStart_3750649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750666 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_3750666 : Nat := 118140960795 + 3750666 * 2 ^ 59
def prefixEnd_3750666 : Nat := 4983230072969 + 3 ^ 40 * 3750666 * 2
def baseEnd_3750666 : Nat := 1925894432476327735726007

theorem tailTrace_3750666 : CollatzResearch.WordTrace tailWord_3750666 prefixEnd_3750666 1925894432476327735726007 := by
  unfold tailWord_3750666
  simp only [CollatzResearch.WordTrace]
  refine ⟨34199506857496279900025963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91198684953323413066735901 34199506857496279900025963)
  ·
    refine ⟨51299260286244419850038945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34199506857496279900025963 51299260286244419850038945)
    ·
      refine ⟨38474445214683314887529209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51299260286244419850038945 38474445214683314887529209)
      ·
        refine ⟨28855833911012486165646907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38474445214683314887529209 28855833911012486165646907)
        ·
          refine ⟨43283750866518729248470361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28855833911012486165646907 43283750866518729248470361)
          ·
            refine ⟨32462813149889046936352771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43283750866518729248470361 32462813149889046936352771)
            ·
              refine ⟨48694219724833570404529157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32462813149889046936352771 48694219724833570404529157)
              ·
                refine ⟨9130166198406294450849217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48694219724833570404529157 9130166198406294450849217)
                ·
                  refine ⟨6847624648804720838136913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9130166198406294450849217 6847624648804720838136913)
                  ·
                    refine ⟨5135718486603540628602685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6847624648804720838136913 5135718486603540628602685)
                    ·
                      refine ⟨1925894432476327735726007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5135718486603540628602685 1925894432476327735726007)
                      ·
                        rfl

theorem cell23_3750666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_3750666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750666 prefixEnd_3750666 := by exact prefixLift 3750666
  have htrace : WordTrace (prefixWord ++ tailWord_3750666) baseStart_3750666 baseEnd_3750666 := by
    simpa [prefixWord, tailWord_3750666, baseEnd_3750666] using wordTrace_append hprefix tailTrace_3750666
  have hstable : (prefixWord ++ tailWord_3750666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750666).length < 2 ^ (prefixWord ++ tailWord_3750666).sum := by decide
  have hdescent : baseEnd_3750666 < baseStart_3750666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750746 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_3750746 : Nat := 118140960795 + 3750746 * 2 ^ 59
def prefixEnd_3750746 : Nat := 4983230072969 + 3 ^ 40 * 3750746 * 2
def baseEnd_3750746 : Nat := 641978503642895807575213

theorem tailTrace_3750746 : CollatzResearch.WordTrace tailWord_3750746 prefixEnd_3750746 641978503642895807575213 := by
  unfold tailWord_3750746
  simp only [CollatzResearch.WordTrace]
  refine ⟨34200236317423823315754023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91200630179796862175344061 34200236317423823315754023)
  ·
    refine ⟨51300354476135734973631035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34200236317423823315754023 51300354476135734973631035)
    ·
      refine ⟨76950531714203602460446553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51300354476135734973631035 76950531714203602460446553)
      ·
        refine ⟨57712898785652701845334915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76950531714203602460446553 57712898785652701845334915)
        ·
          refine ⟨86569348178479052768002373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57712898785652701845334915 86569348178479052768002373)
          ·
            refine ⟨16231752783464822394000445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86569348178479052768002373 16231752783464822394000445)
            ·
              refine ⟨6086907293799308397750167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16231752783464822394000445 6086907293799308397750167)
              ·
                refine ⟨9130360940698962596625251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086907293799308397750167 9130360940698962596625251)
                ·
                  refine ⟨13695541411048443894937877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9130360940698962596625251 13695541411048443894937877)
                  ·
                    refine ⟨641978503642895807575213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13695541411048443894937877 641978503642895807575213)
                    ·
                      rfl

theorem cell23_3750746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_3750746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750746 prefixEnd_3750746 := by exact prefixLift 3750746
  have htrace : WordTrace (prefixWord ++ tailWord_3750746) baseStart_3750746 baseEnd_3750746 := by
    simpa [prefixWord, tailWord_3750746, baseEnd_3750746] using wordTrace_append hprefix tailTrace_3750746
  have hstable : (prefixWord ++ tailWord_3750746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750746).length < 2 ^ (prefixWord ++ tailWord_3750746).sum := by decide
  have hdescent : baseEnd_3750746 < baseStart_3750746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750753 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_3750753 : Nat := 118140960795 + 3750753 * 2 ^ 59
def prefixEnd_3750753 : Nat := 4983230072969 + 3 ^ 40 * 3750753 * 2
def baseEnd_3750753 : Nat := 1925939105293268895338107

theorem tailTrace_3750753 : CollatzResearch.WordTrace tailWord_3750753 prefixEnd_3750753 1925939105293268895338107 := by
  unfold tailWord_3750753
  simp only [CollatzResearch.WordTrace]
  refine ⟨136801200580669933458520913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91200800387113288972347275 136801200580669933458520913)
  ·
    refine ⟨102600900435502450093890685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136801200580669933458520913 102600900435502450093890685)
    ·
      refine ⟨38475337663313418785209007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102600900435502450093890685 38475337663313418785209007)
      ·
        refine ⟨57713006494970128177813511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38475337663313418785209007 57713006494970128177813511)
        ·
          refine ⟨86569509742455192266720267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57713006494970128177813511 86569509742455192266720267)
          ·
            refine ⟨129854264613682788400080401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86569509742455192266720267 129854264613682788400080401)
            ·
              refine ⟨97390698460262091300060301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129854264613682788400080401 97390698460262091300060301)
              ·
                refine ⟨36521511922598284237522613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97390698460262091300060301 36521511922598284237522613)
                ·
                  refine ⟨3423891742743589147267745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36521511922598284237522613 3423891742743589147267745)
                  ·
                    refine ⟨2567918807057691860450809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3423891742743589147267745 2567918807057691860450809)
                    ·
                      refine ⟨1925939105293268895338107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567918807057691860450809 1925939105293268895338107)
                      ·
                        rfl

theorem cell23_3750753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_3750753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750753 prefixEnd_3750753 := by exact prefixLift 3750753
  have htrace : WordTrace (prefixWord ++ tailWord_3750753) baseStart_3750753 baseEnd_3750753 := by
    simpa [prefixWord, tailWord_3750753, baseEnd_3750753] using wordTrace_append hprefix tailTrace_3750753
  have hstable : (prefixWord ++ tailWord_3750753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750753).length < 2 ^ (prefixWord ++ tailWord_3750753).sum := by decide
  have hdescent : baseEnd_3750753 < baseStart_3750753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750773 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3750773 : Nat := 118140960795 + 3750773 * 2 ^ 59
def prefixEnd_3750773 : Nat := 4983230072969 + 3 ^ 40 * 3750773 * 2
def baseEnd_3750773 : Nat := 1925949374906358817088015

theorem tailTrace_3750773 : CollatzResearch.WordTrace tailWord_3750773 prefixEnd_3750773 1925949374906358817088015 := by
  unfold tailWord_3750773
  simp only [CollatzResearch.WordTrace]
  refine ⟨136801930040597476874248973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91201286693731651249499315 136801930040597476874248973)
  ·
    refine ⟨51300723765224053827843365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136801930040597476874248973 51300723765224053827843365)
    ·
      refine ⟨9618885705979510092720631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51300723765224053827843365 9618885705979510092720631)
      ·
        refine ⟨14428328558969265139080947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9618885705979510092720631 14428328558969265139080947)
        ·
          refine ⟨21642492838453897708621421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14428328558969265139080947 21642492838453897708621421)
          ·
            refine ⟨8115934814420211640733033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21642492838453897708621421 8115934814420211640733033)
            ·
              refine ⟨6086951110815158730549775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8115934814420211640733033 6086951110815158730549775)
              ·
                refine ⟨9130426666222738095824663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086951110815158730549775 9130426666222738095824663)
                ·
                  refine ⟨13695639999334107143736995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9130426666222738095824663 13695639999334107143736995)
                  ·
                    refine ⟨20543459999001160715605493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13695639999334107143736995 20543459999001160715605493)
                    ·
                      refine ⟨1925949374906358817088015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20543459999001160715605493 1925949374906358817088015)
                      ·
                        rfl

theorem cell23_3750773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3750773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750773 prefixEnd_3750773 := by exact prefixLift 3750773
  have htrace : WordTrace (prefixWord ++ tailWord_3750773) baseStart_3750773 baseEnd_3750773 := by
    simpa [prefixWord, tailWord_3750773, baseEnd_3750773] using wordTrace_append hprefix tailTrace_3750773
  have hstable : (prefixWord ++ tailWord_3750773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750773).length < 2 ^ (prefixWord ++ tailWord_3750773).sum := by decide
  have hdescent : baseEnd_3750773 < baseStart_3750773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750809 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_3750809 : Nat := 118140960795 + 3750809 * 2 ^ 59
def prefixEnd_3750809 : Nat := 4983230072969 + 3 ^ 40 * 3750809 * 2
def baseEnd_3750809 : Nat := 1925967860209920676237849

theorem tailTrace_3750809 : CollatzResearch.WordTrace tailWord_3750809 prefixEnd_3750809 1925967860209920676237849 := by
  unfold tailWord_3750809
  simp only [CollatzResearch.WordTrace]
  refine ⟨136803243068467055022559481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91202162045644703348372987 136803243068467055022559481)
  ·
    refine ⟨102602432301350291266919611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136803243068467055022559481 102602432301350291266919611)
    ·
      refine ⟨153903648452025436900379417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102602432301350291266919611 153903648452025436900379417)
      ·
        refine ⟨115427736339019077675284563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153903648452025436900379417 115427736339019077675284563)
        ·
          refine ⟨173141604508528616512926845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115427736339019077675284563 173141604508528616512926845)
          ·
            refine ⟨64928101690698231192347567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173141604508528616512926845 64928101690698231192347567)
            ·
              refine ⟨97392152536047346788521351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64928101690698231192347567 97392152536047346788521351)
              ·
                refine ⟨146088228804071020182782027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97392152536047346788521351 146088228804071020182782027)
                ·
                  refine ⟨219132343206106530274173041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146088228804071020182782027 219132343206106530274173041)
                  ·
                    refine ⟨164349257404579897705629781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219132343206106530274173041 164349257404579897705629781)
                    ·
                      refine ⟨1925967860209920676237849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 164349257404579897705629781 1925967860209920676237849)
                      ·
                        rfl

theorem cell23_3750809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_3750809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750809 prefixEnd_3750809 := by exact prefixLift 3750809
  have htrace : WordTrace (prefixWord ++ tailWord_3750809) baseStart_3750809 baseEnd_3750809 := by
    simpa [prefixWord, tailWord_3750809, baseEnd_3750809] using wordTrace_append hprefix tailTrace_3750809
  have hstable : (prefixWord ++ tailWord_3750809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750809).length < 2 ^ (prefixWord ++ tailWord_3750809).sum := by decide
  have hdescent : baseEnd_3750809 < baseStart_3750809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750860 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 1, 4, 2]
def baseStart_3750860 : Nat := 118140960795 + 3750860 * 2 ^ 59
def prefixEnd_3750860 : Nat := 4983230072969 + 3 ^ 40 * 3750860 * 2
def baseEnd_3750860 : Nat := 1925994047723299976700115

theorem tailTrace_3750860 : CollatzResearch.WordTrace tailWord_3750860 prefixEnd_3750860 1925994047723299976700115 := by
  unfold tailWord_3750860
  simp only [CollatzResearch.WordTrace]
  refine ⟨68402551595641145366333017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91203402127521527155110689 68402551595641145366333017)
  ·
    refine ⟨51301913696730859024749763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68402551595641145366333017 51301913696730859024749763)
    ·
      refine ⟨76952870545096288537124645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51301913696730859024749763 76952870545096288537124645)
      ·
        refine ⟨14428663227205554100710871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76952870545096288537124645 14428663227205554100710871)
        ·
          refine ⟨21642994840808331151066307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14428663227205554100710871 21642994840808331151066307)
          ·
            refine ⟨32464492261212496726599461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21642994840808331151066307 32464492261212496726599461)
            ·
              refine ⟨6087092298977343136237399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32464492261212496726599461 6087092298977343136237399)
              ·
                refine ⟨9130638448466014704356099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087092298977343136237399 9130638448466014704356099)
                ·
                  refine ⟨13695957672699022056534149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9130638448466014704356099 13695957672699022056534149)
                  ·
                    refine ⟨2567992063631066635600153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13695957672699022056534149 2567992063631066635600153)
                    ·
                      refine ⟨1925994047723299976700115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2567992063631066635600153 1925994047723299976700115)
                      ·
                        rfl

theorem cell23_3750860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_3750860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750860 prefixEnd_3750860 := by exact prefixLift 3750860
  have htrace : WordTrace (prefixWord ++ tailWord_3750860) baseStart_3750860 baseEnd_3750860 := by
    simpa [prefixWord, tailWord_3750860, baseEnd_3750860] using wordTrace_append hprefix tailTrace_3750860
  have hstable : (prefixWord ++ tailWord_3750860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750860).length < 2 ^ (prefixWord ++ tailWord_3750860).sum := by decide
  have hdescent : baseEnd_3750860 < baseStart_3750860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750896 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 4, 5]
def baseStart_3750896 : Nat := 118140960795 + 3750896 * 2 ^ 59
def prefixEnd_3750896 : Nat := 4983230072969 + 3 ^ 40 * 3750896 * 2
def baseEnd_3750896 : Nat := 642004177675620611949983

theorem tailTrace_3750896 : CollatzResearch.WordTrace tailWord_3750896 prefixEnd_3750896 642004177675620611949983 := by
  unfold tailWord_3750896
  simp only [CollatzResearch.WordTrace]
  refine ⟨68403208109575934440488271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91204277479434579253984361 68403208109575934440488271)
  ·
    refine ⟨102604812164363901660732407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68403208109575934440488271 102604812164363901660732407)
    ·
      refine ⟨153907218246545852491098611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102604812164363901660732407 153907218246545852491098611)
      ·
        refine ⟨230860827369818778736647917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153907218246545852491098611 230860827369818778736647917)
        ·
          refine ⟨86572810263682042026242969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230860827369818778736647917 86572810263682042026242969)
          ·
            refine ⟨64929607697761531519682227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86572810263682042026242969 64929607697761531519682227)
            ·
              refine ⟨97394411546642297279523341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64929607697761531519682227 97394411546642297279523341)
              ·
                refine ⟨36522904329990861479821253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97394411546642297279523341 36522904329990861479821253)
                ·
                  refine ⟨6848044561873286527466485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36522904329990861479821253 6848044561873286527466485)
                  ·
                    refine ⟨642004177675620611949983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6848044561873286527466485 642004177675620611949983)
                    ·
                      rfl

theorem cell23_3750896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_3750896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750896 prefixEnd_3750896 := by exact prefixLift 3750896
  have htrace : WordTrace (prefixWord ++ tailWord_3750896) baseStart_3750896 baseEnd_3750896 := by
    simpa [prefixWord, tailWord_3750896, baseEnd_3750896] using wordTrace_append hprefix tailTrace_3750896
  have hstable : (prefixWord ++ tailWord_3750896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750896).length < 2 ^ (prefixWord ++ tailWord_3750896).sum := by decide
  have hdescent : baseEnd_3750896 < baseStart_3750896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750906 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_3750906 : Nat := 118140960795 + 3750906 * 2 ^ 59
def prefixEnd_3750906 : Nat := 4983230072969 + 3 ^ 40 * 3750906 * 2
def baseEnd_3750906 : Nat := 1926017667833406796724903

theorem tailTrace_3750906 : CollatzResearch.WordTrace tailWord_3750906 prefixEnd_3750906 1926017667833406796724903 := by
  unfold tailWord_3750906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34201695237278910147210143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91204520632743760392560381 34201695237278910147210143)
  ·
    refine ⟨51302542855918365220815215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34201695237278910147210143 51302542855918365220815215)
    ·
      refine ⟨76953814283877547831222823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51302542855918365220815215 76953814283877547831222823)
      ·
        refine ⟨115430721425816321746834235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76953814283877547831222823 115430721425816321746834235)
        ·
          refine ⟨173146082138724482620251353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115430721425816321746834235 173146082138724482620251353)
          ·
            refine ⟨129859561604043361965188515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173146082138724482620251353 129859561604043361965188515)
            ·
              refine ⟨194789342406065042947782773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129859561604043361965188515 194789342406065042947782773)
              ·
                refine ⟨18261500850568597776354635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194789342406065042947782773 18261500850568597776354635)
                ·
                  refine ⟨27392251275852896664531953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18261500850568597776354635 27392251275852896664531953)
                  ·
                    refine ⟨20544188456889672498398965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27392251275852896664531953 20544188456889672498398965)
                    ·
                      refine ⟨1926017667833406796724903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20544188456889672498398965 1926017667833406796724903)
                      ·
                        rfl

theorem cell23_3750906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_3750906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750906 prefixEnd_3750906 := by exact prefixLift 3750906
  have htrace : WordTrace (prefixWord ++ tailWord_3750906) baseStart_3750906 baseEnd_3750906 := by
    simpa [prefixWord, tailWord_3750906, baseEnd_3750906] using wordTrace_append hprefix tailTrace_3750906
  have hstable : (prefixWord ++ tailWord_3750906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750906).length < 2 ^ (prefixWord ++ tailWord_3750906).sum := by decide
  have hdescent : baseEnd_3750906 < baseStart_3750906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750933 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3750933 : Nat := 118140960795 + 3750933 * 2 ^ 59
def prefixEnd_3750933 : Nat := 4983230072969 + 3 ^ 40 * 3750933 * 2
def baseEnd_3750933 : Nat := 1926031531811078191087279

theorem tailTrace_3750933 : CollatzResearch.WordTrace tailWord_3750933 prefixEnd_3750933 1926031531811078191087279 := by
  unfold tailWord_3750933
  simp only [CollatzResearch.WordTrace]
  refine ⟨136807765720017824200073453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91205177146678549466715635 136807765720017824200073453)
  ·
    refine ⟨51302912145006684075027545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136807765720017824200073453 51302912145006684075027545)
    ·
      refine ⟨38477184108755013056270659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51302912145006684075027545 38477184108755013056270659)
      ·
        refine ⟨57715776163132519584405989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38477184108755013056270659 57715776163132519584405989)
        ·
          refine ⟨10821708030587347422076123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57715776163132519584405989 10821708030587347422076123)
          ·
            refine ⟨16232562045881021133114185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821708030587347422076123 16232562045881021133114185)
            ·
              refine ⟨12174421534410765849835639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16232562045881021133114185 12174421534410765849835639)
              ·
                refine ⟨18261632301616148774753459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12174421534410765849835639 18261632301616148774753459)
                ·
                  refine ⟨27392448452424223162130189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18261632301616148774753459 27392448452424223162130189)
                  ·
                    refine ⟨10272168169659083685798821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27392448452424223162130189 10272168169659083685798821)
                    ·
                      refine ⟨1926031531811078191087279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10272168169659083685798821 1926031531811078191087279)
                      ·
                        rfl

theorem cell23_3750933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3750933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750933 prefixEnd_3750933 := by exact prefixLift 3750933
  have htrace : WordTrace (prefixWord ++ tailWord_3750933) baseStart_3750933 baseEnd_3750933 := by
    simpa [prefixWord, tailWord_3750933, baseEnd_3750933] using wordTrace_append hprefix tailTrace_3750933
  have hstable : (prefixWord ++ tailWord_3750933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750933).length < 2 ^ (prefixWord ++ tailWord_3750933).sum := by decide
  have hdescent : baseEnd_3750933 < baseStart_3750933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3750956 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 8]
def baseStart_3750956 : Nat := 118140960795 + 3750956 * 2 ^ 59
def prefixEnd_3750956 : Nat := 4983230072969 + 3 ^ 40 * 3750956 * 2
def baseEnd_3750956 : Nat := 214004815762903511233297

theorem tailTrace_3750956 : CollatzResearch.WordTrace tailWord_3750956 prefixEnd_3750956 214004815762903511233297 := by
  unfold tailWord_3750956
  simp only [CollatzResearch.WordTrace]
  refine ⟨68404302299467249564080361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91205736399289666085440481 68404302299467249564080361)
  ·
    refine ⟨51303226724600437173060271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68404302299467249564080361 51303226724600437173060271)
    ·
      refine ⟨76954840086900655759590407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51303226724600437173060271 76954840086900655759590407)
      ·
        refine ⟨115432260130350983639385611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76954840086900655759590407 115432260130350983639385611)
        ·
          refine ⟨173148390195526475459078417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115432260130350983639385611 173148390195526475459078417)
          ·
            refine ⟨129861292646644856594308813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173148390195526475459078417 129861292646644856594308813)
            ·
              refine ⟨48697984742491821222865805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129861292646644856594308813 48697984742491821222865805)
              ·
                refine ⟨18261744278434432958574677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48697984742491821222865805 18261744278434432958574677)
                ·
                  refine ⟨214004815762903511233297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18261744278434432958574677 214004815762903511233297)
                  ·
                    rfl

theorem cell23_3750956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_3750956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3750956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3750956 prefixEnd_3750956 := by exact prefixLift 3750956
  have htrace : WordTrace (prefixWord ++ tailWord_3750956) baseStart_3750956 baseEnd_3750956 := by
    simpa [prefixWord, tailWord_3750956, baseEnd_3750956] using wordTrace_append hprefix tailTrace_3750956
  have hstable : (prefixWord ++ tailWord_3750956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3750956).length < 2 ^ (prefixWord ++ tailWord_3750956).sum := by decide
  have hdescent : baseEnd_3750956 < baseStart_3750956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3750956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751023 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_3751023 : Nat := 118140960795 + 3751023 * 2 ^ 59
def prefixEnd_3751023 : Nat := 4983230072969 + 3 ^ 40 * 3751023 * 2
def baseEnd_3751023 : Nat := 1926077745069982838961865

theorem tailTrace_3751023 : CollatzResearch.WordTrace tailWord_3751023 prefixEnd_3751023 1926077745069982838961865 := by
  unfold tailWord_3751023
  simp only [CollatzResearch.WordTrace]
  refine ⟨136811048289691769570849723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91207365526461179713899815 136811048289691769570849723)
  ·
    refine ⟨205216572434537654356274585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136811048289691769570849723 205216572434537654356274585)
    ·
      refine ⟨153912429325903240767205939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205216572434537654356274585 153912429325903240767205939)
      ·
        refine ⟨230868643988854861150808909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153912429325903240767205939 230868643988854861150808909)
        ·
          refine ⟨86575741495820572931553341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230868643988854861150808909 86575741495820572931553341)
          ·
            refine ⟨32465903060932714849332503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86575741495820572931553341 32465903060932714849332503)
            ·
              refine ⟨48698854591399072273998755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32465903060932714849332503 48698854591399072273998755)
              ·
                refine ⟨73048281887098608410998133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48698854591399072273998755 73048281887098608410998133)
                ·
                  refine ⟨6848276426915494538531075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73048281887098608410998133 6848276426915494538531075)
                  ·
                    refine ⟨10272414640373241807796613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6848276426915494538531075 10272414640373241807796613)
                    ·
                      refine ⟨1926077745069982838961865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10272414640373241807796613 1926077745069982838961865)
                      ·
                        rfl

theorem cell23_3751023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_3751023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751023 prefixEnd_3751023 := by exact prefixLift 3751023
  have htrace : WordTrace (prefixWord ++ tailWord_3751023) baseStart_3751023 baseEnd_3751023 := by
    simpa [prefixWord, tailWord_3751023, baseEnd_3751023] using wordTrace_append hprefix tailTrace_3751023
  have hstable : (prefixWord ++ tailWord_3751023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751023).length < 2 ^ (prefixWord ++ tailWord_3751023).sum := by decide
  have hdescent : baseEnd_3751023 < baseStart_3751023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751038 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3751038 : Nat := 118140960795 + 3751038 * 2 ^ 59
def prefixEnd_3751038 : Nat := 4983230072969 + 3 ^ 40 * 3751038 * 2
def baseEnd_3751038 : Nat := 1926085447279800280274297

theorem tailTrace_3751038 : CollatzResearch.WordTrace tailWord_3751038 prefixEnd_3751038 1926085447279800280274297 := by
  unfold tailWord_3751038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17101449423079678391580721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91207730256424951421763845 17101449423079678391580721)
  ·
    refine ⟨12826087067309758793685541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17101449423079678391580721 12826087067309758793685541)
    ·
      refine ⟨2404891325120579773816039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12826087067309758793685541 2404891325120579773816039)
      ·
        refine ⟨3607336987680869660724059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404891325120579773816039 3607336987680869660724059)
        ·
          refine ⟨5411005481521304491086089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607336987680869660724059 5411005481521304491086089)
          ·
            refine ⟨4058254111140978368314567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5411005481521304491086089 4058254111140978368314567)
            ·
              refine ⟨6087381166711467552471851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058254111140978368314567 6087381166711467552471851)
              ·
                refine ⟨9131071750067201328707777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087381166711467552471851 9131071750067201328707777)
                ·
                  refine ⟨6848303812550400996530833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9131071750067201328707777 6848303812550400996530833)
                  ·
                    refine ⟨5136227859412800747398125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6848303812550400996530833 5136227859412800747398125)
                    ·
                      refine ⟨1926085447279800280274297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5136227859412800747398125 1926085447279800280274297)
                      ·
                        rfl

theorem cell23_3751038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3751038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751038 prefixEnd_3751038 := by exact prefixLift 3751038
  have htrace : WordTrace (prefixWord ++ tailWord_3751038) baseStart_3751038 baseEnd_3751038 := by
    simpa [prefixWord, tailWord_3751038, baseEnd_3751038] using wordTrace_append hprefix tailTrace_3751038
  have hstable : (prefixWord ++ tailWord_3751038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751038).length < 2 ^ (prefixWord ++ tailWord_3751038).sum := by decide
  have hdescent : baseEnd_3751038 < baseStart_3751038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751044 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_3751044 : Nat := 118140960795 + 3751044 * 2 ^ 59
def prefixEnd_3751044 : Nat := 4983230072969 + 3 ^ 40 * 3751044 * 2
def baseEnd_3751044 : Nat := 1926088528163727256799269

theorem tailTrace_3751044 : CollatzResearch.WordTrace tailWord_3751044 prefixEnd_3751044 1926088528163727256799269 := by
  unfold tailWord_3751044
  simp only [CollatzResearch.WordTrace]
  refine ⟨68405907111307845078682093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91207876148410460104909457 68405907111307845078682093)
  ·
    refine ⟨25652215166740441904505785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68405907111307845078682093 25652215166740441904505785)
    ·
      refine ⟨19239161375055331428379339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25652215166740441904505785 19239161375055331428379339)
      ·
        refine ⟨28858742062582997142569009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19239161375055331428379339 28858742062582997142569009)
        ·
          refine ⟨21644056546937247856926757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28858742062582997142569009 21644056546937247856926757)
          ·
            refine ⟨4058260602550733973173767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21644056546937247856926757 4058260602550733973173767)
            ·
              refine ⟨6087390903826100959760651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058260602550733973173767 6087390903826100959760651)
              ·
                refine ⟨9131086355739151439640977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087390903826100959760651 9131086355739151439640977)
                ·
                  refine ⟨6848314766804363579730733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9131086355739151439640977 6848314766804363579730733)
                  ·
                    refine ⟨2568118037551636342399025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6848314766804363579730733 2568118037551636342399025)
                    ·
                      refine ⟨1926088528163727256799269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568118037551636342399025 1926088528163727256799269)
                      ·
                        rfl

theorem cell23_3751044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_3751044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751044 prefixEnd_3751044 := by exact prefixLift 3751044
  have htrace : WordTrace (prefixWord ++ tailWord_3751044) baseStart_3751044 baseEnd_3751044 := by
    simpa [prefixWord, tailWord_3751044, baseEnd_3751044] using wordTrace_append hprefix tailTrace_3751044
  have hstable : (prefixWord ++ tailWord_3751044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751044).length < 2 ^ (prefixWord ++ tailWord_3751044).sum := by decide
  have hdescent : baseEnd_3751044 < baseStart_3751044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751050 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_3751050 : Nat := 118140960795 + 3751050 * 2 ^ 59
def prefixEnd_3751050 : Nat := 4983230072969 + 3 ^ 40 * 3751050 * 2
def baseEnd_3751050 : Nat := 642030536349218077774747

theorem tailTrace_3751050 : CollatzResearch.WordTrace tailWord_3751050 prefixEnd_3751050 642030536349218077774747 := by
  unfold tailWord_3751050
  simp only [CollatzResearch.WordTrace]
  refine ⟨34203008265148488295520651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91208022040395968788055069 34203008265148488295520651)
  ·
    refine ⟨51304512397722732443280977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34203008265148488295520651 51304512397722732443280977)
    ·
      refine ⟨38478384298292049332460733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51304512397722732443280977 38478384298292049332460733)
      ·
        refine ⟨14429394111859518499672775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38478384298292049332460733 14429394111859518499672775)
        ·
          refine ⟨21644091167789277749509163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14429394111859518499672775 21644091167789277749509163)
          ·
            refine ⟨32466136751683916624263745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21644091167789277749509163 32466136751683916624263745)
            ·
              refine ⟨24349602563762937468197809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32466136751683916624263745 24349602563762937468197809)
              ·
                refine ⟨18262201922822203101148357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24349602563762937468197809 18262201922822203101148357)
                ·
                  refine ⟨3424162860529163081465317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18262201922822203101148357 3424162860529163081465317)
                  ·
                    refine ⟨642030536349218077774747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3424162860529163081465317 642030536349218077774747)
                    ·
                      rfl

theorem cell23_3751050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_3751050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751050 prefixEnd_3751050 := by exact prefixLift 3751050
  have htrace : WordTrace (prefixWord ++ tailWord_3751050) baseStart_3751050 baseEnd_3751050 := by
    simpa [prefixWord, tailWord_3751050, baseEnd_3751050] using wordTrace_append hprefix tailTrace_3751050
  have hstable : (prefixWord ++ tailWord_3751050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751050).length < 2 ^ (prefixWord ++ tailWord_3751050).sum := by decide
  have hdescent : baseEnd_3751050 < baseStart_3751050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751054 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_3751054 : Nat := 118140960795 + 3751054 * 2 ^ 59
def prefixEnd_3751054 : Nat := 4983230072969 + 3 ^ 40 * 3751054 * 2
def baseEnd_3751054 : Nat := 642031220990090739224741

theorem tailTrace_3751054 : CollatzResearch.WordTrace tailWord_3751054 prefixEnd_3751054 642031220990090739224741 := by
  unfold tailWord_3751054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17101522369072432733153527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91208119301719641243485477 17101522369072432733153527)
  ·
    refine ⟨25652283553608649099730291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17101522369072432733153527 25652283553608649099730291)
    ·
      refine ⟨38478425330412973649595437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25652283553608649099730291 38478425330412973649595437)
      ·
        refine ⟨14429409498904865118598289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38478425330412973649595437 14429409498904865118598289)
        ·
          refine ⟨10822057124178648838948717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14429409498904865118598289 10822057124178648838948717)
          ·
            refine ⟨4058271421566993314605769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10822057124178648838948717 4058271421566993314605769)
            ·
              refine ⟨3043703566175244985954327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058271421566993314605769 3043703566175244985954327)
              ·
                refine ⟨4565555349262867478931491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043703566175244985954327 4565555349262867478931491)
                ·
                  refine ⟨6848333023894301218397237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4565555349262867478931491 6848333023894301218397237)
                  ·
                    refine ⟨642031220990090739224741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6848333023894301218397237 642031220990090739224741)
                    ·
                      rfl

theorem cell23_3751054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_3751054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751054 prefixEnd_3751054 := by exact prefixLift 3751054
  have htrace : WordTrace (prefixWord ++ tailWord_3751054) baseStart_3751054 baseEnd_3751054 := by
    simpa [prefixWord, tailWord_3751054, baseEnd_3751054] using wordTrace_append hprefix tailTrace_3751054
  have hstable : (prefixWord ++ tailWord_3751054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751054).length < 2 ^ (prefixWord ++ tailWord_3751054).sum := by decide
  have hdescent : baseEnd_3751054 < baseStart_3751054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751063 : List Nat := [1, 1, 3, 3, 3, 2, 10]
def baseStart_3751063 : Nat := 118140960795 + 3751063 * 2 ^ 59
def prefixEnd_3751063 : Nat := 4983230072969 + 3 ^ 40 * 3751063 * 2
def baseEnd_3751063 : Nat := 23778991164150156573601

theorem tailTrace_3751063 : CollatzResearch.WordTrace tailWord_3751063 prefixEnd_3751063 23778991164150156573601 := by
  unfold tailWord_3751063
  simp only [CollatzResearch.WordTrace]
  refine ⟨136812507209546856402305843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91208338139697904268203895 136812507209546856402305843)
  ·
    refine ⟨205218760814320284603458765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136812507209546856402305843 205218760814320284603458765)
    ·
      refine ⟨76957035305370106726297037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205218760814320284603458765 76957035305370106726297037)
      ·
        refine ⟨28858888239513790022361389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76957035305370106726297037 28858888239513790022361389)
        ·
          refine ⟨10822083089817671258385521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28858888239513790022361389 10822083089817671258385521)
          ·
            refine ⟨8116562317363253443789141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10822083089817671258385521 8116562317363253443789141)
            ·
              refine ⟨23778991164150156573601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8116562317363253443789141 23778991164150156573601)
              ·
                rfl

theorem cell23_3751063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 10].length) (baseStart_3751063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751063 prefixEnd_3751063 := by exact prefixLift 3751063
  have htrace : WordTrace (prefixWord ++ tailWord_3751063) baseStart_3751063 baseEnd_3751063 := by
    simpa [prefixWord, tailWord_3751063, baseEnd_3751063] using wordTrace_append hprefix tailTrace_3751063
  have hstable : (prefixWord ++ tailWord_3751063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751063).length < 2 ^ (prefixWord ++ tailWord_3751063).sum := by decide
  have hdescent : baseEnd_3751063 < baseStart_3751063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751103 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_3751103 : Nat := 118140960795 + 3751103 * 2 ^ 59
def prefixEnd_3751103 : Nat := 4983230072969 + 3 ^ 40 * 3751103 * 2
def baseEnd_3751103 : Nat := 1926118823522342525961497

theorem tailTrace_3751103 : CollatzResearch.WordTrace tailWord_3751103 prefixEnd_3751103 1926118823522342525961497 := by
  unfold tailWord_3751103
  simp only [CollatzResearch.WordTrace]
  refine ⟨136813966129401943233761963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91209310752934628822507975 136813966129401943233761963)
  ·
    refine ⟨205220949194102914850642945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136813966129401943233761963 205220949194102914850642945)
    ·
      refine ⟨153915711895577186137982209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205220949194102914850642945 153915711895577186137982209)
      ·
        refine ⟨115436783921682889603486657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153915711895577186137982209 115436783921682889603486657)
        ·
          refine ⟨86577587941262167202614993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115436783921682889603486657 86577587941262167202614993)
          ·
            refine ⟨64933190955946625401961245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86577587941262167202614993 64933190955946625401961245)
            ·
              refine ⟨24349946608479984525735467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64933190955946625401961245 24349946608479984525735467)
              ·
                refine ⟨36524919912719976788603201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24349946608479984525735467 36524919912719976788603201)
                ·
                  refine ⟨27393689934539982591452401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36524919912719976788603201 27393689934539982591452401)
                  ·
                    refine ⟨20545267450904986943589301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27393689934539982591452401 20545267450904986943589301)
                    ·
                      refine ⟨1926118823522342525961497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20545267450904986943589301 1926118823522342525961497)
                      ·
                        rfl

theorem cell23_3751103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_3751103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751103 prefixEnd_3751103 := by exact prefixLift 3751103
  have htrace : WordTrace (prefixWord ++ tailWord_3751103) baseStart_3751103 baseEnd_3751103 := by
    simpa [prefixWord, tailWord_3751103, baseEnd_3751103] using wordTrace_append hprefix tailTrace_3751103
  have hstable : (prefixWord ++ tailWord_3751103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751103).length < 2 ^ (prefixWord ++ tailWord_3751103).sum := by decide
  have hdescent : baseEnd_3751103 < baseStart_3751103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751150 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3751150 : Nat := 118140960795 + 3751150 * 2 ^ 59
def prefixEnd_3751150 : Nat := 4983230072969 + 3 ^ 40 * 3751150 * 2
def baseEnd_3751150 : Nat := 1926142957113103842073781

theorem tailTrace_3751150 : CollatzResearch.WordTrace tailWord_3751150 prefixEnd_3751150 1926142957113103842073781 := by
  unfold tailWord_3751150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17101960045028958782590363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91210453573487780173815269 17101960045028958782590363)
  ·
    refine ⟨25652940067543438173885545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17101960045028958782590363 25652940067543438173885545)
    ·
      refine ⟨19239705050657578630414159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25652940067543438173885545 19239705050657578630414159)
      ·
        refine ⟨28859557575986367945621239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19239705050657578630414159 28859557575986367945621239)
        ·
          refine ⟨43289336363979551918431859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28859557575986367945621239 43289336363979551918431859)
          ·
            refine ⟨64934004545969327877647789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43289336363979551918431859 64934004545969327877647789)
            ·
              refine ⟨24350251704738497954117921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64934004545969327877647789 24350251704738497954117921)
              ·
                refine ⟨18262688778553873465588441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24350251704738497954117921 18262688778553873465588441)
                ·
                  refine ⟨13697016583915405099191331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18262688778553873465588441 13697016583915405099191331)
                  ·
                    refine ⟨20545524875873107648786997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13697016583915405099191331 20545524875873107648786997)
                    ·
                      refine ⟨1926142957113103842073781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20545524875873107648786997 1926142957113103842073781)
                      ·
                        rfl

theorem cell23_3751150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3751150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751150 prefixEnd_3751150 := by exact prefixLift 3751150
  have htrace : WordTrace (prefixWord ++ tailWord_3751150) baseStart_3751150 baseEnd_3751150 := by
    simpa [prefixWord, tailWord_3751150, baseEnd_3751150] using wordTrace_append hprefix tailTrace_3751150
  have hstable : (prefixWord ++ tailWord_3751150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751150).length < 2 ^ (prefixWord ++ tailWord_3751150).sum := by decide
  have hdescent : baseEnd_3751150 < baseStart_3751150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751151 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 1, 3, 2]
def baseStart_3751151 : Nat := 118140960795 + 3751151 * 2 ^ 59
def prefixEnd_3751151 : Nat := 4983230072969 + 3 ^ 40 * 3751151 * 2
def baseEnd_3751151 : Nat := 1926143470593758338161277

theorem tailTrace_3751151 : CollatzResearch.WordTrace tailWord_3751151 prefixEnd_3751151 1926143470593758338161277 := by
  unfold tailWord_3751151
  simp only [CollatzResearch.WordTrace]
  refine ⟨136815716833228047431509307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91210477888818698287672871 136815716833228047431509307)
  ·
    refine ⟨205223575249842071147263961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136815716833228047431509307 205223575249842071147263961)
    ·
      refine ⟨153917681437381553360447971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205223575249842071147263961 153917681437381553360447971)
      ·
        refine ⟨230876522156072330040671957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153917681437381553360447971 230876522156072330040671957)
        ·
          refine ⟨5411168488032945235328249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 230876522156072330040671957 5411168488032945235328249)
          ·
            refine ⟨4058376366024708926496187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5411168488032945235328249 4058376366024708926496187)
            ·
              refine ⟨6087564549037063389744281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058376366024708926496187 6087564549037063389744281)
              ·
                refine ⟨4565673411777797542308211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6087564549037063389744281 4565673411777797542308211)
                ·
                  refine ⟨6848510117666696313462317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4565673411777797542308211 6848510117666696313462317)
                  ·
                    refine ⟨2568191294125011117548369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6848510117666696313462317 2568191294125011117548369)
                    ·
                      refine ⟨1926143470593758338161277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568191294125011117548369 1926143470593758338161277)
                      ·
                        rfl

theorem cell23_3751151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 3, 2].length) (baseStart_3751151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751151 prefixEnd_3751151 := by exact prefixLift 3751151
  have htrace : WordTrace (prefixWord ++ tailWord_3751151) baseStart_3751151 baseEnd_3751151 := by
    simpa [prefixWord, tailWord_3751151, baseEnd_3751151] using wordTrace_append hprefix tailTrace_3751151
  have hstable : (prefixWord ++ tailWord_3751151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751151).length < 2 ^ (prefixWord ++ tailWord_3751151).sum := by decide
  have hdescent : baseEnd_3751151 < baseStart_3751151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751153 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 9]
def baseStart_3751153 : Nat := 118140960795 + 3751153 * 2 ^ 59
def prefixEnd_3751153 : Nat := 4983230072969 + 3 ^ 40 * 3751153 * 2
def baseEnd_3751153 : Nat := 214016055283896370037363

theorem tailTrace_3751153 : CollatzResearch.WordTrace tailWord_3751153 prefixEnd_3751153 214016055283896370037363 := by
  unfold tailWord_3751153
  simp only [CollatzResearch.WordTrace]
  refine ⟨136815789779220801773082113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91210526519480534515388075 136815789779220801773082113)
  ·
    refine ⟨102611842334415601329811585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136815789779220801773082113 102611842334415601329811585)
    ·
      refine ⟨76958881750811700997358689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102611842334415601329811585 76958881750811700997358689)
      ·
        refine ⟨57719161313108775748019017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76958881750811700997358689 57719161313108775748019017)
        ·
          refine ⟨43289370984831581811014263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57719161313108775748019017 43289370984831581811014263)
          ·
            refine ⟨64934056477247372716521395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43289370984831581811014263 64934056477247372716521395)
            ·
              refine ⟨97401084715871059074782093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64934056477247372716521395 97401084715871059074782093)
              ·
                refine ⟨36525406768451647153043285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97401084715871059074782093 36525406768451647153043285)
                ·
                  refine ⟨214016055283896370037363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36525406768451647153043285 214016055283896370037363)
                  ·
                    rfl

theorem cell23_3751153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 9].length) (baseStart_3751153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751153 prefixEnd_3751153 := by exact prefixLift 3751153
  have htrace : WordTrace (prefixWord ++ tailWord_3751153) baseStart_3751153 baseEnd_3751153 := by
    simpa [prefixWord, tailWord_3751153, baseEnd_3751153] using wordTrace_append hprefix tailTrace_3751153
  have hstable : (prefixWord ++ tailWord_3751153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751153).length < 2 ^ (prefixWord ++ tailWord_3751153).sum := by decide
  have hdescent : baseEnd_3751153 < baseStart_3751153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751164 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_3751164 : Nat := 118140960795 + 3751164 * 2 ^ 59
def prefixEnd_3751164 : Nat := 4983230072969 + 3 ^ 40 * 3751164 * 2
def baseEnd_3751164 : Nat := 1926150145842266787298717

theorem tailTrace_3751164 : CollatzResearch.WordTrace tailWord_3751164 prefixEnd_3751164 1926150145842266787298717 := by
  unfold tailWord_3751164
  simp only [CollatzResearch.WordTrace]
  refine ⟨68408095491090475325866273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91210793988120633767821697 68408095491090475325866273)
  ·
    refine ⟨51306071618317856494399705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68408095491090475325866273 51306071618317856494399705)
    ·
      refine ⟨38479553713738392370799779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51306071618317856494399705 38479553713738392370799779)
      ·
        refine ⟨57719330570607588556199669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38479553713738392370799779 57719330570607588556199669)
        ·
          refine ⟨5411187240994461427143719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57719330570607588556199669 5411187240994461427143719)
          ·
            refine ⟨8116780861491692140715579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411187240994461427143719 8116780861491692140715579)
            ·
              refine ⟨12175171292237538211073369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8116780861491692140715579 12175171292237538211073369)
              ·
                refine ⟨9131378469178153658305027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12175171292237538211073369 9131378469178153658305027)
                ·
                  refine ⟨13697067703767230487457541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9131378469178153658305027 13697067703767230487457541)
                  ·
                    refine ⟨2568200194456355716398289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13697067703767230487457541 2568200194456355716398289)
                    ·
                      refine ⟨1926150145842266787298717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568200194456355716398289 1926150145842266787298717)
                      ·
                        rfl

theorem cell23_3751164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_3751164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751164 prefixEnd_3751164 := by exact prefixLift 3751164
  have htrace : WordTrace (prefixWord ++ tailWord_3751164) baseStart_3751164 baseEnd_3751164 := by
    simpa [prefixWord, tailWord_3751164, baseEnd_3751164] using wordTrace_append hprefix tailTrace_3751164
  have hstable : (prefixWord ++ tailWord_3751164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751164).length < 2 ^ (prefixWord ++ tailWord_3751164).sum := by decide
  have hdescent : baseEnd_3751164 < baseStart_3751164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751183 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 5, 7]
def baseStart_3751183 : Nat := 118140960795 + 3751183 * 2 ^ 59
def prefixEnd_3751183 : Nat := 4983230072969 + 3 ^ 40 * 3751183 * 2
def baseEnd_3751183 : Nat := 642053300658234070987043

theorem tailTrace_3751183 : CollatzResearch.WordTrace tailWord_3751183 prefixEnd_3751183 642053300658234070987043 := by
  unfold tailWord_3751183
  simp only [CollatzResearch.WordTrace]
  refine ⟨136816883969112116896674203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91211255979408077931116135 136816883969112116896674203)
  ·
    refine ⟨205225325953668175345011305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136816883969112116896674203 205225325953668175345011305)
    ·
      refine ⟨153918994465251131508758479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205225325953668175345011305 153918994465251131508758479)
      ·
        refine ⟨230878491697876697263137719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153918994465251131508758479 230878491697876697263137719)
        ·
          refine ⟨346317737546815045894706579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230878491697876697263137719 346317737546815045894706579)
          ·
            refine ⟨519476606320222568842059869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346317737546815045894706579 519476606320222568842059869)
            ·
              refine ⟨194803727370083463315772451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519476606320222568842059869 194803727370083463315772451)
              ·
                refine ⟨292205591055125194973658677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194803727370083463315772451 292205591055125194973658677)
                ·
                  refine ⟨27394274161417987028780501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292205591055125194973658677 27394274161417987028780501)
                  ·
                    refine ⟨642053300658234070987043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27394274161417987028780501 642053300658234070987043)
                    ·
                      rfl

theorem cell23_3751183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_3751183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751183 prefixEnd_3751183 := by exact prefixLift 3751183
  have htrace : WordTrace (prefixWord ++ tailWord_3751183) baseStart_3751183 baseEnd_3751183 := by
    simpa [prefixWord, tailWord_3751183, baseEnd_3751183] using wordTrace_append hprefix tailTrace_3751183
  have hstable : (prefixWord ++ tailWord_3751183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751183).length < 2 ^ (prefixWord ++ tailWord_3751183).sum := by decide
  have hdescent : baseEnd_3751183 < baseStart_3751183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751197 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3751197 : Nat := 118140960795 + 3751197 * 2 ^ 59
def prefixEnd_3751197 : Nat := 4983230072969 + 3 ^ 40 * 3751197 * 2
def baseEnd_3751197 : Nat := 1926167090703865158186065

theorem tailTrace_3751197 : CollatzResearch.WordTrace tailWord_3751197 prefixEnd_3751197 1926167090703865158186065 := by
  unfold tailWord_3751197
  simp only [CollatzResearch.WordTrace]
  refine ⟨136817394591061397287683845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91211596394040931525122563 136817394591061397287683845)
  ·
    refine ⟨25653261485824011991440721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136817394591061397287683845 25653261485824011991440721)
    ·
      refine ⟨19239946114368008993580541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25653261485824011991440721 19239946114368008993580541)
      ·
        refine ⟨7214979792888003372592703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19239946114368008993580541 7214979792888003372592703)
        ·
          refine ⟨10822469689332005058889055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214979792888003372592703 10822469689332005058889055)
          ·
            refine ⟨16233704533998007588333583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10822469689332005058889055 16233704533998007588333583)
            ·
              refine ⟨24350556800997011382500375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16233704533998007588333583 24350556800997011382500375)
              ·
                refine ⟨36525835201495517073750563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24350556800997011382500375 36525835201495517073750563)
                ·
                  refine ⟨54788752802243275610625845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36525835201495517073750563 54788752802243275610625845)
                  ·
                    refine ⟨5136445575210307088496173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54788752802243275610625845 5136445575210307088496173)
                    ·
                      refine ⟨1926167090703865158186065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5136445575210307088496173 1926167090703865158186065)
                      ·
                        rfl

theorem cell23_3751197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3751197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751197 prefixEnd_3751197 := by exact prefixLift 3751197
  have htrace : WordTrace (prefixWord ++ tailWord_3751197) baseStart_3751197 baseEnd_3751197 := by
    simpa [prefixWord, tailWord_3751197, baseEnd_3751197] using wordTrace_append hprefix tailTrace_3751197
  have hstable : (prefixWord ++ tailWord_3751197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751197).length < 2 ^ (prefixWord ++ tailWord_3751197).sum := by decide
  have hdescent : baseEnd_3751197 < baseStart_3751197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751198 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_3751198 : Nat := 118140960795 + 3751198 * 2 ^ 59
def prefixEnd_3751198 : Nat := 4983230072969 + 3 ^ 40 * 3751198 * 2
def baseEnd_3751198 : Nat := 1926167604184519654273561

theorem tailTrace_3751198 : CollatzResearch.WordTrace tailWord_3751198 prefixEnd_3751198 1926167604184519654273561 := by
  unfold tailWord_3751198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17102178883007221807308781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91211620709371849638980165 17102178883007221807308781)
  ·
    refine ⟨6413317081127708177740793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17102178883007221807308781 6413317081127708177740793)
    ·
      refine ⟨4809987810845781133305595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6413317081127708177740793 4809987810845781133305595)
      ·
        refine ⟨7214981716268671699958393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809987810845781133305595 7214981716268671699958393)
        ·
          refine ⟨5411236287201503774968795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7214981716268671699958393 5411236287201503774968795)
          ·
            refine ⟨8116854430802255662453193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411236287201503774968795 8116854430802255662453193)
            ·
              refine ⟨6087640823101691746839895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8116854430802255662453193 6087640823101691746839895)
              ·
                refine ⟨9131461234652537620259843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087640823101691746839895 9131461234652537620259843)
                ·
                  refine ⟨13697191851978806430389765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9131461234652537620259843 13697191851978806430389765)
                  ·
                    refine ⟨2568223472246026205698081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13697191851978806430389765 2568223472246026205698081)
                    ·
                      refine ⟨1926167604184519654273561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568223472246026205698081 1926167604184519654273561)
                      ·
                        rfl

theorem cell23_3751198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_3751198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751198 prefixEnd_3751198 := by exact prefixLift 3751198
  have htrace : WordTrace (prefixWord ++ tailWord_3751198) baseStart_3751198 baseEnd_3751198 := by
    simpa [prefixWord, tailWord_3751198, baseEnd_3751198] using wordTrace_append hprefix tailTrace_3751198
  have hstable : (prefixWord ++ tailWord_3751198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751198).length < 2 ^ (prefixWord ++ tailWord_3751198).sum := by decide
  have hdescent : baseEnd_3751198 < baseStart_3751198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751217 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 2, 5]
def baseStart_3751217 : Nat := 118140960795 + 3751217 * 2 ^ 59
def prefixEnd_3751217 : Nat := 4983230072969 + 3 ^ 40 * 3751217 * 2
def baseEnd_3751217 : Nat := 642059120105651693311991

theorem tailTrace_3751217 : CollatzResearch.WordTrace tailWord_3751217 prefixEnd_3751217 642059120105651693311991 := by
  unfold tailWord_3751217
  simp only [CollatzResearch.WordTrace]
  refine ⟨136818124050988940703411905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91212082700659293802274603 136818124050988940703411905)
  ·
    refine ⟨102613593038241705527558929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136818124050988940703411905 102613593038241705527558929)
    ·
      refine ⟨76960194778681279145669197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102613593038241705527558929 76960194778681279145669197)
      ·
        refine ⟨28860073042005479679625949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76960194778681279145669197 28860073042005479679625949)
        ·
          refine ⟨10822527390752054879859731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28860073042005479679625949 10822527390752054879859731)
          ·
            refine ⟨16233791086128082319789597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10822527390752054879859731 16233791086128082319789597)
            ·
              refine ⟨6087671657298030869921099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16233791086128082319789597 6087671657298030869921099)
              ·
                refine ⟨9131507485947046304881649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087671657298030869921099 9131507485947046304881649)
                ·
                  refine ⟨6848630614460284728661237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9131507485947046304881649 6848630614460284728661237)
                  ·
                    refine ⟨642059120105651693311991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6848630614460284728661237 642059120105651693311991)
                    ·
                      rfl

theorem cell23_3751217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_3751217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751217 prefixEnd_3751217 := by exact prefixLift 3751217
  have htrace : WordTrace (prefixWord ++ tailWord_3751217) baseStart_3751217 baseEnd_3751217 := by
    simpa [prefixWord, tailWord_3751217, baseEnd_3751217] using wordTrace_append hprefix tailTrace_3751217
  have hstable : (prefixWord ++ tailWord_3751217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751217).length < 2 ^ (prefixWord ++ tailWord_3751217).sum := by decide
  have hdescent : baseEnd_3751217 < baseStart_3751217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751250 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3751250 : Nat := 118140960795 + 3751250 * 2 ^ 59
def prefixEnd_3751250 : Nat := 4983230072969 + 3 ^ 40 * 3751250 * 2
def baseEnd_3751250 : Nat := 1926194305178553450823321

theorem tailTrace_3751250 : CollatzResearch.WordTrace tailWord_3751250 prefixEnd_3751250 1926194305178553450823321 := by
  unfold tailWord_3751250
  simp only [CollatzResearch.WordTrace]
  refine ⟨34204831914967346834840801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91212885106579591559575469 34204831914967346834840801)
  ·
    refine ⟨25653623936225510126130601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34204831914967346834840801 25653623936225510126130601)
    ·
      refine ⟨19240217952169132594597951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25653623936225510126130601 19240217952169132594597951)
      ·
        refine ⟨28860326928253698891896927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19240217952169132594597951 28860326928253698891896927)
        ·
          refine ⟨43290490392380548337845391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28860326928253698891896927 43290490392380548337845391)
          ·
            refine ⟨64935735588570822506768087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43290490392380548337845391 64935735588570822506768087)
            ·
              refine ⟨97403603382856233760152131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64935735588570822506768087 97403603382856233760152131)
              ·
                refine ⟨146105405074284350640228197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97403603382856233760152131 146105405074284350640228197)
                ·
                  refine ⟨27394763451428315745042787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146105405074284350640228197 27394763451428315745042787)
                  ·
                    refine ⟨41092145177142473617564181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27394763451428315745042787 41092145177142473617564181)
                    ·
                      refine ⟨1926194305178553450823321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41092145177142473617564181 1926194305178553450823321)
                      ·
                        rfl

theorem cell23_3751250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3751250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751250 prefixEnd_3751250 := by exact prefixLift 3751250
  have htrace : WordTrace (prefixWord ++ tailWord_3751250) baseStart_3751250 baseEnd_3751250 := by
    simpa [prefixWord, tailWord_3751250, baseEnd_3751250] using wordTrace_append hprefix tailTrace_3751250
  have hstable : (prefixWord ++ tailWord_3751250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751250).length < 2 ^ (prefixWord ++ tailWord_3751250).sum := by decide
  have hdescent : baseEnd_3751250 < baseStart_3751250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751298 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3751298 : Nat := 118140960795 + 3751298 * 2 ^ 59
def prefixEnd_3751298 : Nat := 4983230072969 + 3 ^ 40 * 3751298 * 2
def baseEnd_3751298 : Nat := 642072984083323087674367

theorem tailTrace_3751298 : CollatzResearch.WordTrace tailWord_3751298 prefixEnd_3751298 642072984083323087674367 := by
  unfold tailWord_3751298
  simp only [CollatzResearch.WordTrace]
  refine ⟨34205269590923872884277637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91214052242463661024740365 34205269590923872884277637)
  ·
    refine ⟨6413488048298226165802057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34205269590923872884277637 6413488048298226165802057)
    ·
      refine ⟨4810116036223669624351543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6413488048298226165802057 4810116036223669624351543)
      ·
        refine ⟨7215174054335504436527315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4810116036223669624351543 7215174054335504436527315)
        ·
          refine ⟨10822761081503256654790973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7215174054335504436527315 10822761081503256654790973)
          ·
            refine ⟨4058535405563721245546615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10822761081503256654790973 4058535405563721245546615)
            ·
              refine ⟨6087803108345581868319923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058535405563721245546615 6087803108345581868319923)
              ·
                refine ⟨9131704662518372802479885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087803108345581868319923 9131704662518372802479885)
                ·
                  refine ⟨3424389248444389800929957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9131704662518372802479885 3424389248444389800929957)
                  ·
                    refine ⟨642072984083323087674367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3424389248444389800929957 642072984083323087674367)
                    ·
                      rfl

theorem cell23_3751298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3751298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751298 prefixEnd_3751298 := by exact prefixLift 3751298
  have htrace : WordTrace (prefixWord ++ tailWord_3751298) baseStart_3751298 baseEnd_3751298 := by
    simpa [prefixWord, tailWord_3751298, baseEnd_3751298] using wordTrace_append hprefix tailTrace_3751298
  have hstable : (prefixWord ++ tailWord_3751298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751298).length < 2 ^ (prefixWord ++ tailWord_3751298).sum := by decide
  have hdescent : baseEnd_3751298 < baseStart_3751298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751344 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 7, 2, 2]
def baseStart_3751344 : Nat := 118140960795 + 3751344 * 2 ^ 59
def prefixEnd_3751344 : Nat := 4983230072969 + 3 ^ 40 * 3751344 * 2
def baseEnd_3751344 : Nat := 1926242572360076083047889

theorem tailTrace_3751344 : CollatzResearch.WordTrace tailWord_3751344 prefixEnd_3751344 1926242572360076083047889 := by
  unfold tailWord_3751344
  simp only [CollatzResearch.WordTrace]
  refine ⟨68411378060764420696642543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91215170747685894262190057 68411378060764420696642543)
  ·
    refine ⟨102617067091146631044963815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68411378060764420696642543 102617067091146631044963815)
    ·
      refine ⟨153925600636719946567445723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102617067091146631044963815 153925600636719946567445723)
      ·
        refine ⟨230888400955079919851168585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153925600636719946567445723 230888400955079919851168585)
        ·
          refine ⟨173166300716309939888376439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230888400955079919851168585 173166300716309939888376439)
          ·
            refine ⟨259749451074464909832564659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173166300716309939888376439 259749451074464909832564659)
            ·
              refine ⟨389624176611697364748846989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259749451074464909832564659 389624176611697364748846989)
              ·
                refine ⟨146109066229386511780817621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389624176611697364748846989 146109066229386511780817621)
                ·
                  refine ⟨3424431239751246369862913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 146109066229386511780817621 3424431239751246369862913)
                  ·
                    refine ⟨2568323429813434777397185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3424431239751246369862913 2568323429813434777397185)
                    ·
                      refine ⟨1926242572360076083047889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568323429813434777397185 1926242572360076083047889)
                      ·
                        rfl

theorem cell23_3751344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7, 2, 2].length) (baseStart_3751344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751344 prefixEnd_3751344 := by exact prefixLift 3751344
  have htrace : WordTrace (prefixWord ++ tailWord_3751344) baseStart_3751344 baseEnd_3751344 := by
    simpa [prefixWord, tailWord_3751344, baseEnd_3751344] using wordTrace_append hprefix tailTrace_3751344
  have hstable : (prefixWord ++ tailWord_3751344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751344).length < 2 ^ (prefixWord ++ tailWord_3751344).sum := by decide
  have hdescent : baseEnd_3751344 < baseStart_3751344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751357 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3751357 : Nat := 118140960795 + 3751357 * 2 ^ 59
def prefixEnd_3751357 : Nat := 4983230072969 + 3 ^ 40 * 3751357 * 2
def baseEnd_3751357 : Nat := 1926249247608584532185329

theorem tailTrace_3751357 : CollatzResearch.WordTrace tailWord_3751357 prefixEnd_3751357 1926249247608584532185329 := by
  unfold tailWord_3751357
  simp only [CollatzResearch.WordTrace]
  refine ⟨136823230270481744613508325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91215486846987829742338883 136823230270481744613508325)
  ·
    refine ⟨25654355675715327115032811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136823230270481744613508325 25654355675715327115032811)
    ·
      refine ⟨38481533513572990672549217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25654355675715327115032811 38481533513572990672549217)
      ·
        refine ⟨28861150135179743004411913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38481533513572990672549217 28861150135179743004411913)
        ·
          refine ⟨21645862601384807253308935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28861150135179743004411913 21645862601384807253308935)
          ·
            refine ⟨32468793902077210879963403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21645862601384807253308935 32468793902077210879963403)
            ·
              refine ⟨48703190853115816319945105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32468793902077210879963403 48703190853115816319945105)
              ·
                refine ⟨36527393139836862239958829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48703190853115816319945105 36527393139836862239958829)
                ·
                  refine ⟨13697772427438823339984561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36527393139836862239958829 13697772427438823339984561)
                  ·
                    refine ⟨10273329320579117504988421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13697772427438823339984561 10273329320579117504988421)
                    ·
                      refine ⟨1926249247608584532185329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10273329320579117504988421 1926249247608584532185329)
                      ·
                        rfl

theorem cell23_3751357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3751357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751357 prefixEnd_3751357 := by exact prefixLift 3751357
  have htrace : WordTrace (prefixWord ++ tailWord_3751357) baseStart_3751357 baseEnd_3751357 := by
    simpa [prefixWord, tailWord_3751357, baseEnd_3751357] using wordTrace_append hprefix tailTrace_3751357
  have hstable : (prefixWord ++ tailWord_3751357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751357).length < 2 ^ (prefixWord ++ tailWord_3751357).sum := by decide
  have hdescent : baseEnd_3751357 < baseStart_3751357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751395 : List Nat := [1, 1, 1, 6, 2, 2, 2, 3, 1, 2, 2]
def baseStart_3751395 : Nat := 118140960795 + 3751395 * 2 ^ 59
def prefixEnd_3751395 : Nat := 4983230072969 + 3 ^ 40 * 3751395 * 2
def baseEnd_3751395 : Nat := 1926268759873455383510155

theorem tailTrace_3751395 : CollatzResearch.WordTrace tailWord_3751395 prefixEnd_3751395 1926268759873455383510155 := by
  unfold tailWord_3751395
  simp only [CollatzResearch.WordTrace]
  refine ⟨136824616244344077103391639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91216410829562718068927759 136824616244344077103391639)
  ·
    refine ⟨205236924366516115655087459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136824616244344077103391639 205236924366516115655087459)
    ·
      refine ⟨307855386549774173482631189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205236924366516115655087459 307855386549774173482631189)
      ·
        refine ⟨14430721244520664381998337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 307855386549774173482631189 14430721244520664381998337)
        ·
          refine ⟨10823040933390498286498753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14430721244520664381998337 10823040933390498286498753)
          ·
            refine ⟨8117280700042873714874065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10823040933390498286498753 8117280700042873714874065)
            ·
              refine ⟨6087960525032155286155549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8117280700042873714874065 6087960525032155286155549)
              ·
                refine ⟨2282985196887058232308331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6087960525032155286155549 2282985196887058232308331)
                ·
                  refine ⟨3424477795330587348462497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282985196887058232308331 3424477795330587348462497)
                  ·
                    refine ⟨2568358346497940511346873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3424477795330587348462497 2568358346497940511346873)
                    ·
                      refine ⟨1926268759873455383510155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568358346497940511346873 1926268759873455383510155)
                      ·
                        rfl

theorem cell23_3751395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_3751395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751395 prefixEnd_3751395 := by exact prefixLift 3751395
  have htrace : WordTrace (prefixWord ++ tailWord_3751395) baseStart_3751395 baseEnd_3751395 := by
    simpa [prefixWord, tailWord_3751395, baseEnd_3751395] using wordTrace_append hprefix tailTrace_3751395
  have hstable : (prefixWord ++ tailWord_3751395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751395).length < 2 ^ (prefixWord ++ tailWord_3751395).sum := by decide
  have hdescent : baseEnd_3751395 < baseStart_3751395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751404 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 5, 3, 2]
def baseStart_3751404 : Nat := 118140960795 + 3751404 * 2 ^ 59
def prefixEnd_3751404 : Nat := 4983230072969 + 3 ^ 40 * 3751404 * 2
def baseEnd_3751404 : Nat := 1926273381199345848297613

theorem tailTrace_3751404 : CollatzResearch.WordTrace tailWord_3751404 prefixEnd_3751404 1926273381199345848297613 := by
  unfold tailWord_3751404
  simp only [CollatzResearch.WordTrace]
  refine ⟨68412472250655735820234633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91216629667540981093646177 68412472250655735820234633)
  ·
    refine ⟨51309354187991801865175975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68412472250655735820234633 51309354187991801865175975)
    ·
      refine ⟨76964031281987702797763963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51309354187991801865175975 76964031281987702797763963)
      ·
        refine ⟨115446046922981554196645945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76964031281987702797763963 115446046922981554196645945)
        ·
          refine ⟨86584535192236165647484459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115446046922981554196645945 86584535192236165647484459)
          ·
            refine ⟨129876802788354248471226689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86584535192236165647484459 129876802788354248471226689)
            ·
              refine ⟨97407602091265686353420017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129876802788354248471226689 97407602091265686353420017)
              ·
                refine ⟨73055701568449264765065013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97407602091265686353420017 73055701568449264765065013)
                ·
                  refine ⟨6848972022042118571724845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73055701568449264765065013 6848972022042118571724845)
                  ·
                    refine ⟨2568364508265794464396817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6848972022042118571724845 2568364508265794464396817)
                    ·
                      refine ⟨1926273381199345848297613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568364508265794464396817 1926273381199345848297613)
                      ·
                        rfl

theorem cell23_3751404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_3751404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751404 prefixEnd_3751404 := by exact prefixLift 3751404
  have htrace : WordTrace (prefixWord ++ tailWord_3751404) baseStart_3751404 baseEnd_3751404 := by
    simpa [prefixWord, tailWord_3751404, baseEnd_3751404] using wordTrace_append hprefix tailTrace_3751404
  have hstable : (prefixWord ++ tailWord_3751404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751404).length < 2 ^ (prefixWord ++ tailWord_3751404).sum := by decide
  have hdescent : baseEnd_3751404 < baseStart_3751404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751405 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_3751405 : Nat := 118140960795 + 3751405 * 2 ^ 59
def prefixEnd_3751405 : Nat := 4983230072969 + 3 ^ 40 * 3751405 * 2
def baseEnd_3751405 : Nat := 642091298226666781461703

theorem tailTrace_3751405 : CollatzResearch.WordTrace tailWord_3751405 prefixEnd_3751405 642091298226666781461703 := by
  unfold tailWord_3751405
  simp only [CollatzResearch.WordTrace]
  refine ⟨136824980974307848811255669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91216653982871899207503779 136824980974307848811255669)
  ·
    refine ⟨12827341966341360826055219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136824980974307848811255669 12827341966341360826055219)
    ·
      refine ⟨19241012949512041239082829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12827341966341360826055219 19241012949512041239082829)
      ·
        refine ⟨7215379856067015464656061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19241012949512041239082829 7215379856067015464656061)
        ·
          refine ⟨2705767446025130799246023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7215379856067015464656061 2705767446025130799246023)
          ·
            refine ⟨4058651169037696198869035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705767446025130799246023 4058651169037696198869035)
            ·
              refine ⟨6087976753556544298303553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058651169037696198869035 6087976753556544298303553)
              ·
                refine ⟨4565982565167408223727665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6087976753556544298303553 4565982565167408223727665)
                ·
                  refine ⟨3424486923875556167795749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4565982565167408223727665 3424486923875556167795749)
                  ·
                    refine ⟨642091298226666781461703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3424486923875556167795749 642091298226666781461703)
                    ·
                      rfl

theorem cell23_3751405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_3751405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751405 prefixEnd_3751405 := by exact prefixLift 3751405
  have htrace : WordTrace (prefixWord ++ tailWord_3751405) baseStart_3751405 baseEnd_3751405 := by
    simpa [prefixWord, tailWord_3751405, baseEnd_3751405] using wordTrace_append hprefix tailTrace_3751405
  have hstable : (prefixWord ++ tailWord_3751405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751405).length < 2 ^ (prefixWord ++ tailWord_3751405).sum := by decide
  have hdescent : baseEnd_3751405 < baseStart_3751405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751428 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3751428 : Nat := 118140960795 + 3751428 * 2 ^ 59
def prefixEnd_3751428 : Nat := 4983230072969 + 3 ^ 40 * 3751428 * 2
def baseEnd_3751428 : Nat := 1926285704735053754397503

theorem tailTrace_3751428 : CollatzResearch.WordTrace tailWord_3751428 prefixEnd_3751428 1926285704735053754397503 := by
  unfold tailWord_3751428
  simp only [CollatzResearch.WordTrace]
  refine ⟨68412909926612261869671469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91217213235483015826228625 68412909926612261869671469)
  ·
    refine ⟨25654841222479598201126801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68412909926612261869671469 25654841222479598201126801)
    ·
      refine ⟨19241130916859698650845101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25654841222479598201126801 19241130916859698650845101)
      ·
        refine ⟨7215424093822386994066913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19241130916859698650845101 7215424093822386994066913)
        ·
          refine ⟨5411568070366790245550185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7215424093822386994066913 5411568070366790245550185)
          ·
            refine ⟨4058676052775092684162639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5411568070366790245550185 4058676052775092684162639)
            ·
              refine ⟨6088014079162639026243959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058676052775092684162639 6088014079162639026243959)
              ·
                refine ⟨9132021118743958539365939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6088014079162639026243959 9132021118743958539365939)
                ·
                  refine ⟨13698031678115937809048909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9132021118743958539365939 13698031678115937809048909)
                  ·
                    refine ⟨5136761879293476678393341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13698031678115937809048909 5136761879293476678393341)
                    ·
                      refine ⟨1926285704735053754397503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5136761879293476678393341 1926285704735053754397503)
                      ·
                        rfl

theorem cell23_3751428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3751428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751428 prefixEnd_3751428 := by exact prefixLift 3751428
  have htrace : WordTrace (prefixWord ++ tailWord_3751428) baseStart_3751428 baseEnd_3751428 := by
    simpa [prefixWord, tailWord_3751428, baseEnd_3751428] using wordTrace_append hprefix tailTrace_3751428
  have hstable : (prefixWord ++ tailWord_3751428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751428).length < 2 ^ (prefixWord ++ tailWord_3751428).sum := by decide
  have hdescent : baseEnd_3751428 < baseStart_3751428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751485 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_3751485 : Nat := 118140960795 + 3751485 * 2 ^ 59
def prefixEnd_3751485 : Nat := 4983230072969 + 3 ^ 40 * 3751485 * 2
def baseEnd_3751485 : Nat := 1926314973132360031384741

theorem tailTrace_3751485 : CollatzResearch.WordTrace tailWord_3751485 prefixEnd_3751485 1926314973132360031384741 := by
  unfold tailWord_3751485
  simp only [CollatzResearch.WordTrace]
  refine ⟨136827898814018022474167909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91218599209345348316111939 136827898814018022474167909)
  ·
    refine ⟨25655231027628379213906483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136827898814018022474167909 25655231027628379213906483)
    ·
      refine ⟨38482846541442568820859725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25655231027628379213906483 38482846541442568820859725)
      ·
        refine ⟨14431067453040963307822397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38482846541442568820859725 14431067453040963307822397)
        ·
          refine ⟨5411650294890361240433399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14431067453040963307822397 5411650294890361240433399)
          ·
            refine ⟨8117475442335541860650099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411650294890361240433399 8117475442335541860650099)
            ·
              refine ⟨12176213163503312790975149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8117475442335541860650099 12176213163503312790975149)
              ·
                refine ⟨4566079936313742296615681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12176213163503312790975149 4566079936313742296615681)
                ·
                  refine ⟨3424559952235306722461761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4566079936313742296615681 3424559952235306722461761)
                  ·
                    refine ⟨2568419964176480041846321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3424559952235306722461761 2568419964176480041846321)
                    ·
                      refine ⟨1926314973132360031384741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568419964176480041846321 1926314973132360031384741)
                      ·
                        rfl

theorem cell23_3751485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_3751485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751485 prefixEnd_3751485 := by exact prefixLift 3751485
  have htrace : WordTrace (prefixWord ++ tailWord_3751485) baseStart_3751485 baseEnd_3751485 := by
    simpa [prefixWord, tailWord_3751485, baseEnd_3751485] using wordTrace_append hprefix tailTrace_3751485
  have hstable : (prefixWord ++ tailWord_3751485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751485).length < 2 ^ (prefixWord ++ tailWord_3751485).sum := by decide
  have hdescent : baseEnd_3751485 < baseStart_3751485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751504 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 2, 5]
def baseStart_3751504 : Nat := 118140960795 + 3751504 * 2 ^ 59
def prefixEnd_3751504 : Nat := 4983230072969 + 3 ^ 40 * 3751504 * 2
def baseEnd_3751504 : Nat := 642108243088265152349051

theorem tailTrace_3751504 : CollatzResearch.WordTrace tailWord_3751504 prefixEnd_3751504 642108243088265152349051 := by
  unfold tailWord_3751504
  simp only [CollatzResearch.WordTrace]
  refine ⟨68414295900474594359554783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91219061200632792479406377 68414295900474594359554783)
  ·
    refine ⟨102621443850711891539332175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68414295900474594359554783 102621443850711891539332175)
    ·
      refine ⟨153932165776067837308998263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102621443850711891539332175 153932165776067837308998263)
      ·
        refine ⟨230898248664101755963497395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153932165776067837308998263 230898248664101755963497395)
        ·
          refine ⟨346347372996152633945246093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230898248664101755963497395 346347372996152633945246093)
          ·
            refine ⟨129880264873557237729467285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346347372996152633945246093 129880264873557237729467285)
            ·
              refine ⟨6088137415947995518568779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129880264873557237729467285 6088137415947995518568779)
              ·
                refine ⟨9132206123921993277853169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6088137415947995518568779 9132206123921993277853169)
                ·
                  refine ⟨6849154592941494958389877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9132206123921993277853169 6849154592941494958389877)
                  ·
                    refine ⟨642108243088265152349051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6849154592941494958389877 642108243088265152349051)
                    ·
                      rfl

theorem cell23_3751504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_3751504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751504 prefixEnd_3751504 := by exact prefixLift 3751504
  have htrace : WordTrace (prefixWord ++ tailWord_3751504) baseStart_3751504 baseEnd_3751504 := by
    simpa [prefixWord, tailWord_3751504, baseEnd_3751504] using wordTrace_append hprefix tailTrace_3751504
  have hstable : (prefixWord ++ tailWord_3751504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751504).length < 2 ^ (prefixWord ++ tailWord_3751504).sum := by decide
  have hdescent : baseEnd_3751504 < baseStart_3751504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751561 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 3]
def baseStart_3751561 : Nat := 118140960795 + 3751561 * 2 ^ 59
def prefixEnd_3751561 : Nat := 4983230072969 + 3 ^ 40 * 3751561 * 2
def baseEnd_3751561 : Nat := 1926353997662101734034391

theorem tailTrace_3751561 : CollatzResearch.WordTrace tailWord_3751561 prefixEnd_3751561 1926353997662101734034391 := by
  unfold tailWord_3751561
  simp only [CollatzResearch.WordTrace]
  refine ⟨136830670761742687453934537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91220447174495124969289691 136830670761742687453934537)
  ·
    refine ⟨102623003071307015590450903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136830670761742687453934537 102623003071307015590450903)
    ·
      refine ⟨153934504606960523385676355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102623003071307015590450903 153934504606960523385676355)
      ·
        refine ⟨230901756910440785078514533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153934504606960523385676355 230901756910440785078514533)
        ·
          refine ⟨43294079420707647202221475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230901756910440785078514533 43294079420707647202221475)
          ·
            refine ⟨64941119131061470803332213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43294079420707647202221475 64941119131061470803332213)
            ·
              refine ⟨6088229918537012887812395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64941119131061470803332213 6088229918537012887812395)
              ·
                refine ⟨9132344877805519331718593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6088229918537012887812395 9132344877805519331718593)
                ·
                  refine ⟨6849258658354139498788945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9132344877805519331718593 6849258658354139498788945)
                  ·
                    refine ⟨5136943993765604624091709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6849258658354139498788945 5136943993765604624091709)
                    ·
                      refine ⟨1926353997662101734034391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5136943993765604624091709 1926353997662101734034391)
                      ·
                        rfl

theorem cell23_3751561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_3751561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751561 prefixEnd_3751561 := by exact prefixLift 3751561
  have htrace : WordTrace (prefixWord ++ tailWord_3751561) baseStart_3751561 baseEnd_3751561 := by
    simpa [prefixWord, tailWord_3751561, baseEnd_3751561] using wordTrace_append hprefix tailTrace_3751561
  have hstable : (prefixWord ++ tailWord_3751561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751561).length < 2 ^ (prefixWord ++ tailWord_3751561).sum := by decide
  have hdescent : baseEnd_3751561 < baseStart_3751561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751567 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_3751567 : Nat := 118140960795 + 3751567 * 2 ^ 59
def prefixEnd_3751567 : Nat := 4983230072969 + 3 ^ 40 * 3751567 * 2
def baseEnd_3751567 : Nat := 1926357078546028710559363

theorem tailTrace_3751567 : CollatzResearch.WordTrace tailWord_3751567 prefixEnd_3751567 1926357078546028710559363 := by
  unfold tailWord_3751567
  simp only [CollatzResearch.WordTrace]
  refine ⟨136830889599720950478652955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91220593066480633652435303 136830889599720950478652955)
  ·
    refine ⟨205246334399581425717979433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136830889599720950478652955 205246334399581425717979433)
    ·
      refine ⟨153934750799686069288484575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205246334399581425717979433 153934750799686069288484575)
      ·
        refine ⟨230902126199529103932726863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153934750799686069288484575 230902126199529103932726863)
        ·
          refine ⟨346353189299293655899090295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230902126199529103932726863 346353189299293655899090295)
          ·
            refine ⟨519529783948940483848635443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346353189299293655899090295 519529783948940483848635443)
            ·
              refine ⟨779294675923410725772953165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519529783948940483848635443 779294675923410725772953165)
              ·
                refine ⟨292235503471279022164857437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 779294675923410725772953165 292235503471279022164857437)
                ·
                  refine ⟨109588313801729633311821539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292235503471279022164857437 109588313801729633311821539)
                  ·
                    refine ⟨164382470702594449967732309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109588313801729633311821539 164382470702594449967732309)
                    ·
                      refine ⟨1926357078546028710559363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 164382470702594449967732309 1926357078546028710559363)
                      ·
                        rfl

theorem cell23_3751567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_3751567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751567 prefixEnd_3751567 := by exact prefixLift 3751567
  have htrace : WordTrace (prefixWord ++ tailWord_3751567) baseStart_3751567 baseEnd_3751567 := by
    simpa [prefixWord, tailWord_3751567, baseEnd_3751567] using wordTrace_append hprefix tailTrace_3751567
  have hstable : (prefixWord ++ tailWord_3751567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751567).length < 2 ^ (prefixWord ++ tailWord_3751567).sum := by decide
  have hdescent : baseEnd_3751567 < baseStart_3751567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751584 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_3751584 : Nat := 118140960795 + 3751584 * 2 ^ 59
def prefixEnd_3751584 : Nat := 4983230072969 + 3 ^ 40 * 3751584 * 2
def baseEnd_3751584 : Nat := 1926365807717155144046785

theorem tailTrace_3751584 : CollatzResearch.WordTrace tailWord_3751584 prefixEnd_3751584 1926365807717155144046785 := by
  unfold tailWord_3751584
  simp only [CollatzResearch.WordTrace]
  refine ⟨68415754820329681191010903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91221006427106241588014537 68415754820329681191010903)
  ·
    refine ⟨102623632230494521786516355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68415754820329681191010903 102623632230494521786516355)
    ·
      refine ⟨153935448345741782679774533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102623632230494521786516355 153935448345741782679774533)
      ·
        refine ⟨28862896564826584252457725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153935448345741782679774533 28862896564826584252457725)
        ·
          refine ⟨10823586211809969094671647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28862896564826584252457725 10823586211809969094671647)
          ·
            refine ⟨16235379317714953642007471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10823586211809969094671647 16235379317714953642007471)
            ·
              refine ⟨24353068976572430463011207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16235379317714953642007471 24353068976572430463011207)
              ·
                refine ⟨36529603464858645694516811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24353068976572430463011207 36529603464858645694516811)
                ·
                  refine ⟨54794405197287968541775217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36529603464858645694516811 54794405197287968541775217)
                  ·
                    refine ⟨41095803897965976406331413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54794405197287968541775217 41095803897965976406331413)
                    ·
                      refine ⟨1926365807717155144046785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41095803897965976406331413 1926365807717155144046785)
                      ·
                        rfl

theorem cell23_3751584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_3751584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751584 prefixEnd_3751584 := by exact prefixLift 3751584
  have htrace : WordTrace (prefixWord ++ tailWord_3751584) baseStart_3751584 baseEnd_3751584 := by
    simpa [prefixWord, tailWord_3751584, baseEnd_3751584] using wordTrace_append hprefix tailTrace_3751584
  have hstable : (prefixWord ++ tailWord_3751584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751584).length < 2 ^ (prefixWord ++ tailWord_3751584).sum := by decide
  have hdescent : baseEnd_3751584 < baseStart_3751584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751624 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 3, 6]
def baseStart_3751624 : Nat := 118140960795 + 3751624 * 2 ^ 59
def prefixEnd_3751624 : Nat := 4983230072969 + 3 ^ 40 * 3751624 * 2
def baseEnd_3751624 : Nat := 642128782314444995848867

theorem tailTrace_3751624 : CollatzResearch.WordTrace tailWord_3751624 prefixEnd_3751624 642128782314444995848867 := by
  unfold tailWord_3751624
  simp only [CollatzResearch.WordTrace]
  refine ⟨68416484280257224606738963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91221979040342966142318617 68416484280257224606738963)
  ·
    refine ⟨102624726420385836910108445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68416484280257224606738963 102624726420385836910108445)
    ·
      refine ⟨38484272407644688841290667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102624726420385836910108445 38484272407644688841290667)
      ·
        refine ⟨57726408611467033261936001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38484272407644688841290667 57726408611467033261936001)
        ·
          refine ⟨43294806458600274946452001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57726408611467033261936001 43294806458600274946452001)
          ·
            refine ⟨32471104843950206209839001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43294806458600274946452001 32471104843950206209839001)
            ·
              refine ⟨24353328632962654657379251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32471104843950206209839001 24353328632962654657379251)
              ·
                refine ⟨36529992949443981986068877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24353328632962654657379251 36529992949443981986068877)
                ·
                  refine ⟨13698747356041493244775829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36529992949443981986068877 13698747356041493244775829)
                  ·
                    refine ⟨642128782314444995848867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13698747356041493244775829 642128782314444995848867)
                    ·
                      rfl

theorem cell23_3751624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_3751624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751624 prefixEnd_3751624 := by exact prefixLift 3751624
  have htrace : WordTrace (prefixWord ++ tailWord_3751624) baseStart_3751624 baseEnd_3751624 := by
    simpa [prefixWord, tailWord_3751624, baseEnd_3751624] using wordTrace_append hprefix tailTrace_3751624
  have hstable : (prefixWord ++ tailWord_3751624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751624).length < 2 ^ (prefixWord ++ tailWord_3751624).sum := by decide
  have hdescent : baseEnd_3751624 < baseStart_3751624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751641 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 4, 4]
def baseStart_3751641 : Nat := 118140960795 + 3751641 * 2 ^ 59
def prefixEnd_3751641 : Nat := 4983230072969 + 3 ^ 40 * 3751641 * 2
def baseEnd_3751641 : Nat := 642131692038153807011341

theorem tailTrace_3751641 : CollatzResearch.WordTrace tailWord_3751641 prefixEnd_3751641 642131692038153807011341 := by
  unfold tailWord_3751641
  simp only [CollatzResearch.WordTrace]
  refine ⟨136833588601452861116846777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91222392400968574077897851 136833588601452861116846777)
  ·
    refine ⟨102625191451089645837635083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136833588601452861116846777 102625191451089645837635083)
    ·
      refine ⟨153937787176634468756452625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102625191451089645837635083 153937787176634468756452625)
      ·
        refine ⟨115453340382475851567339469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153937787176634468756452625 115453340382475851567339469)
        ·
          refine ⟨43295002643428444337752301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115453340382475851567339469 43295002643428444337752301)
          ·
            refine ⟨16235625991285666626657113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43295002643428444337752301 16235625991285666626657113)
            ·
              refine ⟨12176719493464249969992835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16235625991285666626657113 12176719493464249969992835)
              ·
                refine ⟨18265079240196374954989253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12176719493464249969992835 18265079240196374954989253)
                ·
                  refine ⟨3424702357536820304060485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18265079240196374954989253 3424702357536820304060485)
                  ·
                    refine ⟨642131692038153807011341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3424702357536820304060485 642131692038153807011341)
                    ·
                      rfl

theorem cell23_3751641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 4].length) (baseStart_3751641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751641 prefixEnd_3751641 := by exact prefixLift 3751641
  have htrace : WordTrace (prefixWord ++ tailWord_3751641) baseStart_3751641 baseEnd_3751641 := by
    simpa [prefixWord, tailWord_3751641, baseEnd_3751641] using wordTrace_append hprefix tailTrace_3751641
  have hstable : (prefixWord ++ tailWord_3751641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751641).length < 2 ^ (prefixWord ++ tailWord_3751641).sum := by decide
  have hdescent : baseEnd_3751641 < baseStart_3751641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751642 : List Nat := [3, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3]
def baseStart_3751642 : Nat := 118140960795 + 3751642 * 2 ^ 59
def prefixEnd_3751642 : Nat := 4983230072969 + 3 ^ 40 * 3751642 * 2
def baseEnd_3751642 : Nat := 1926395589595115917121519

theorem tailTrace_3751642 : CollatzResearch.WordTrace tailWord_3751642 prefixEnd_3751642 1926395589595115917121519 := by
  unfold tailWord_3751642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34208406268612309571908295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91222416716299492191755453 34208406268612309571908295)
  ·
    refine ⟨51312609402918464357862443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34208406268612309571908295 51312609402918464357862443)
    ·
      refine ⟨76968914104377696536793665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51312609402918464357862443 76968914104377696536793665)
      ·
        refine ⟨57726685578283272402595249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76968914104377696536793665 57726685578283272402595249)
        ·
          refine ⟨43295014183712454301946437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57726685578283272402595249 43295014183712454301946437)
          ·
            refine ⟨8117815159446085181614957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43295014183712454301946437 8117815159446085181614957)
            ·
              refine ⟨3044180684792281943105609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8117815159446085181614957 3044180684792281943105609)
              ·
                refine ⟨2283135513594211457329207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3044180684792281943105609 2283135513594211457329207)
                ·
                  refine ⟨3424703270391317185993811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283135513594211457329207 3424703270391317185993811)
                  ·
                    refine ⟨5137054905586975778990717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3424703270391317185993811 5137054905586975778990717)
                    ·
                      refine ⟨1926395589595115917121519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5137054905586975778990717 1926395589595115917121519)
                      ·
                        rfl

theorem cell23_3751642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_3751642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751642 prefixEnd_3751642 := by exact prefixLift 3751642
  have htrace : WordTrace (prefixWord ++ tailWord_3751642) baseStart_3751642 baseEnd_3751642 := by
    simpa [prefixWord, tailWord_3751642, baseEnd_3751642] using wordTrace_append hprefix tailTrace_3751642
  have hstable : (prefixWord ++ tailWord_3751642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751642).length < 2 ^ (prefixWord ++ tailWord_3751642).sum := by decide
  have hdescent : baseEnd_3751642 < baseStart_3751642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751661 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3751661 : Nat := 118140960795 + 3751661 * 2 ^ 59
def prefixEnd_3751661 : Nat := 4983230072969 + 3 ^ 40 * 3751661 * 2
def baseEnd_3751661 : Nat := 1926405345727551342783931

theorem tailTrace_3751661 : CollatzResearch.WordTrace tailWord_3751661 prefixEnd_3751661 1926405345727551342783931 := by
  unfold tailWord_3751661
  simp only [CollatzResearch.WordTrace]
  refine ⟨136834318061380404532574837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91222878707586936355049891 136834318061380404532574837)
  ·
    refine ⟨12828217318254412924928891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136834318061380404532574837 12828217318254412924928891)
    ·
      refine ⟨19242325977381619387393337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12828217318254412924928891 19242325977381619387393337)
      ·
        refine ⟨14431744483036214540545003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19242325977381619387393337 14431744483036214540545003)
        ·
          refine ⟨21647616724554321810817505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14431744483036214540545003 21647616724554321810817505)
          ·
            refine ⟨16235712543415741358113129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21647616724554321810817505 16235712543415741358113129)
            ·
              refine ⟨12176784407561806018584847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16235712543415741358113129 12176784407561806018584847)
              ·
                refine ⟨18265176611342709027877271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12176784407561806018584847 18265176611342709027877271)
                ·
                  refine ⟨27397764917014063541815907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18265176611342709027877271 27397764917014063541815907)
                  ·
                    refine ⟨41096647375521095312723861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27397764917014063541815907 41096647375521095312723861)
                    ·
                      refine ⟨1926405345727551342783931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41096647375521095312723861 1926405345727551342783931)
                      ·
                        rfl

theorem cell23_3751661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3751661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751661 prefixEnd_3751661 := by exact prefixLift 3751661
  have htrace : WordTrace (prefixWord ++ tailWord_3751661) baseStart_3751661 baseEnd_3751661 := by
    simpa [prefixWord, tailWord_3751661, baseEnd_3751661] using wordTrace_append hprefix tailTrace_3751661
  have hstable : (prefixWord ++ tailWord_3751661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751661).length < 2 ^ (prefixWord ++ tailWord_3751661).sum := by decide
  have hdescent : baseEnd_3751661 < baseStart_3751661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751681 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_3751681 : Nat := 118140960795 + 3751681 * 2 ^ 59
def prefixEnd_3751681 : Nat := 4983230072969 + 3 ^ 40 * 3751681 * 2
def baseEnd_3751681 : Nat := 1926415615340641264533839

theorem tailTrace_3751681 : CollatzResearch.WordTrace tailWord_3751681 prefixEnd_3751681 1926415615340641264533839 := by
  unfold tailWord_3751681
  simp only [CollatzResearch.WordTrace]
  refine ⟨136835047521307947948302897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91223365014205298632201931 136835047521307947948302897)
  ·
    refine ⟨102626285640980960961227173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136835047521307947948302897 102626285640980960961227173)
    ·
      refine ⟨19242428557683930180230095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102626285640980960961227173 19242428557683930180230095)
      ·
        refine ⟨28863642836525895270345143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19242428557683930180230095 28863642836525895270345143)
        ·
          refine ⟨43295464254788842905517715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28863642836525895270345143 43295464254788842905517715)
          ·
            refine ⟨64943196382183264358276573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43295464254788842905517715 64943196382183264358276573)
            ·
              refine ⟨24353698643318724134353715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64943196382183264358276573 24353698643318724134353715)
              ·
                refine ⟨36530547964978086201530573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24353698643318724134353715 36530547964978086201530573)
                ·
                  refine ⟨13698955486866782325573965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36530547964978086201530573 13698955486866782325573965)
                  ·
                    refine ⟨5137108307575043372090237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13698955486866782325573965 5137108307575043372090237)
                    ·
                      refine ⟨1926415615340641264533839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5137108307575043372090237 1926415615340641264533839)
                      ·
                        rfl

theorem cell23_3751681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_3751681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751681 prefixEnd_3751681 := by exact prefixLift 3751681
  have htrace : WordTrace (prefixWord ++ tailWord_3751681) baseStart_3751681 baseEnd_3751681 := by
    simpa [prefixWord, tailWord_3751681, baseEnd_3751681] using wordTrace_append hprefix tailTrace_3751681
  have hstable : (prefixWord ++ tailWord_3751681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751681).length < 2 ^ (prefixWord ++ tailWord_3751681).sum := by decide
  have hdescent : baseEnd_3751681 < baseStart_3751681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751693 : List Nat := [1, 7, 2, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_3751693 : Nat := 118140960795 + 3751693 * 2 ^ 59
def prefixEnd_3751693 : Nat := 4983230072969 + 3 ^ 40 * 3751693 * 2
def baseEnd_3751693 : Nat := 1926421777108495217583785

theorem tailTrace_3751693 : CollatzResearch.WordTrace tailWord_3751693 prefixEnd_3751693 1926421777108495217583785 := by
  unfold tailWord_3751693
  simp only [CollatzResearch.WordTrace]
  refine ⟨136835485197264473997739733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91223656798176315998493155 136835485197264473997739733)
  ·
    refine ⟨3207081684310886109322025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 136835485197264473997739733 3207081684310886109322025)
    ·
      refine ⟨2405311263233164581991519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3207081684310886109322025 2405311263233164581991519)
      ·
        refine ⟨3607966894849746872987279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405311263233164581991519 3607966894849746872987279)
        ·
          refine ⟨5411950342274620309480919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607966894849746872987279 5411950342274620309480919)
          ·
            refine ⟨8117925513411930464221379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411950342274620309480919 8117925513411930464221379)
            ·
              refine ⟨12176888270117895696332069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8117925513411930464221379 12176888270117895696332069)
              ·
                refine ⟨2283166550647105443062263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12176888270117895696332069 2283166550647105443062263)
                ·
                  refine ⟨3424749825970658164593395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283166550647105443062263 3424749825970658164593395)
                  ·
                    refine ⟨5137124738955987246890093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3424749825970658164593395 5137124738955987246890093)
                    ·
                      refine ⟨1926421777108495217583785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5137124738955987246890093 1926421777108495217583785)
                      ·
                        rfl

theorem cell23_3751693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_3751693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751693 prefixEnd_3751693 := by exact prefixLift 3751693
  have htrace : WordTrace (prefixWord ++ tailWord_3751693) baseStart_3751693 baseEnd_3751693 := by
    simpa [prefixWord, tailWord_3751693, baseEnd_3751693] using wordTrace_append hprefix tailTrace_3751693
  have hstable : (prefixWord ++ tailWord_3751693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751693).length < 2 ^ (prefixWord ++ tailWord_3751693).sum := by decide
  have hdescent : baseEnd_3751693 < baseStart_3751693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751708 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_3751708 : Nat := 118140960795 + 3751708 * 2 ^ 59
def prefixEnd_3751708 : Nat := 4983230072969 + 3 ^ 40 * 3751708 * 2
def baseEnd_3751708 : Nat := 1926429479318312658896215

theorem tailTrace_3751708 : CollatzResearch.WordTrace tailWord_3751708 prefixEnd_3751708 1926429479318312658896215 := by
  unfold tailWord_3751708
  simp only [CollatzResearch.WordTrace]
  refine ⟨68418016146105065779767889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91224021528140087706357185 68418016146105065779767889)
  ·
    refine ⟨51313512109578799334825917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68418016146105065779767889 51313512109578799334825917)
    ·
      refine ⟨19242567041092049750559719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51313512109578799334825917 19242567041092049750559719)
      ·
        refine ⟨28863850561638074625839579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19242567041092049750559719 28863850561638074625839579)
        ·
          refine ⟨43295775842457111938759369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28863850561638074625839579 43295775842457111938759369)
          ·
            refine ⟨32471831881842833954069527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43295775842457111938759369 32471831881842833954069527)
            ·
              refine ⟨48707747822764250931104291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32471831881842833954069527 48707747822764250931104291)
              ·
                refine ⟨73061621734146376396656437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48707747822764250931104291 73061621734146376396656437)
                ·
                  refine ⟨6849527037576222787186541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73061621734146376396656437 6849527037576222787186541)
                  ·
                    refine ⟨2568572639091083545194953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6849527037576222787186541 2568572639091083545194953)
                    ·
                      refine ⟨1926429479318312658896215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568572639091083545194953 1926429479318312658896215)
                      ·
                        rfl

theorem cell23_3751708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_3751708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751708 prefixEnd_3751708 := by exact prefixLift 3751708
  have htrace : WordTrace (prefixWord ++ tailWord_3751708) baseStart_3751708 baseEnd_3751708 := by
    simpa [prefixWord, tailWord_3751708, baseEnd_3751708] using wordTrace_append hprefix tailTrace_3751708
  have hstable : (prefixWord ++ tailWord_3751708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751708).length < 2 ^ (prefixWord ++ tailWord_3751708).sum := by decide
  have hdescent : baseEnd_3751708 < baseStart_3751708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751742 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_3751742 : Nat := 118140960795 + 3751742 * 2 ^ 59
def prefixEnd_3751742 : Nat := 4983230072969 + 3 ^ 40 * 3751742 * 2
def baseEnd_3751742 : Nat := 1926446937660565525871059

theorem tailTrace_3751742 : CollatzResearch.WordTrace tailWord_3751742 prefixEnd_3751742 1926446937660565525871059 := by
  unfold tailWord_3751742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17104659046760869420784185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91224848249391303577515653 17104659046760869420784185)
  ·
    refine ⟨12828494285070652065588139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17104659046760869420784185 12828494285070652065588139)
    ·
      refine ⟨19242741427605978098382209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12828494285070652065588139 19242741427605978098382209)
      ·
        refine ⟨14432056070704483573786657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19242741427605978098382209 14432056070704483573786657)
        ·
          refine ⟨10824042053028362680339993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14432056070704483573786657 10824042053028362680339993)
          ·
            refine ⟨8118031539771272010254995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10824042053028362680339993 8118031539771272010254995)
            ·
              refine ⟨12177047309656908015382493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8118031539771272010254995 12177047309656908015382493)
              ·
                refine ⟨4566392741121340505768435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12177047309656908015382493 4566392741121340505768435)
                ·
                  refine ⟨6849589111682010758652653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566392741121340505768435 6849589111682010758652653)
                  ·
                    refine ⟨2568595916880754034494745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6849589111682010758652653 2568595916880754034494745)
                    ·
                      refine ⟨1926446937660565525871059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568595916880754034494745 1926446937660565525871059)
                      ·
                        rfl

theorem cell23_3751742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_3751742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751742 prefixEnd_3751742 := by exact prefixLift 3751742
  have htrace : WordTrace (prefixWord ++ tailWord_3751742) baseStart_3751742 baseEnd_3751742 := by
    simpa [prefixWord, tailWord_3751742, baseEnd_3751742] using wordTrace_append hprefix tailTrace_3751742
  have hstable : (prefixWord ++ tailWord_3751742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751742).length < 2 ^ (prefixWord ++ tailWord_3751742).sum := by decide
  have hdescent : baseEnd_3751742 < baseStart_3751742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751751 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_3751751 : Nat := 118140960795 + 3751751 * 2 ^ 59
def prefixEnd_3751751 : Nat := 4983230072969 + 3 ^ 40 * 3751751 * 2
def baseEnd_3751751 : Nat := 1926451558986455990658517

theorem tailTrace_3751751 : CollatzResearch.WordTrace tailWord_3751751 prefixEnd_3751751 1926451558986455990658517 := by
  unfold tailWord_3751751
  simp only [CollatzResearch.WordTrace]
  refine ⟨136837600631054349903351107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91225067087369566602234071 136837600631054349903351107)
  ·
    refine ⟨205256400946581524855026661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136837600631054349903351107 205256400946581524855026661)
    ·
      refine ⟨38485575177484035910317499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205256400946581524855026661 38485575177484035910317499)
      ·
        refine ⟨57728362766226053865476249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38485575177484035910317499 57728362766226053865476249)
        ·
          refine ⟨43296272074669540399107187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57728362766226053865476249 43296272074669540399107187)
          ·
            refine ⟨64944408112004310598660781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43296272074669540399107187 64944408112004310598660781)
            ·
              refine ⟨24354153042001616474497793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64944408112004310598660781 24354153042001616474497793)
              ·
                refine ⟨18265614781501212355873345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24354153042001616474497793 18265614781501212355873345)
                ·
                  refine ⟨13699211086125909266905009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18265614781501212355873345 13699211086125909266905009)
                  ·
                    refine ⟨10274408314594431950178757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13699211086125909266905009 10274408314594431950178757)
                    ·
                      refine ⟨1926451558986455990658517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10274408314594431950178757 1926451558986455990658517)
                      ·
                        rfl

theorem cell23_3751751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_3751751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751751 prefixEnd_3751751 := by exact prefixLift 3751751
  have htrace : WordTrace (prefixWord ++ tailWord_3751751) baseStart_3751751 baseEnd_3751751 := by
    simpa [prefixWord, tailWord_3751751, baseEnd_3751751] using wordTrace_append hprefix tailTrace_3751751
  have hstable : (prefixWord ++ tailWord_3751751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751751).length < 2 ^ (prefixWord ++ tailWord_3751751).sum := by decide
  have hdescent : baseEnd_3751751 < baseStart_3751751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751761 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 7]
def baseStart_3751761 : Nat := 118140960795 + 3751761 * 2 ^ 59
def prefixEnd_3751761 : Nat := 4983230072969 + 3 ^ 40 * 3751761 * 2
def baseEnd_3751761 : Nat := 214050743754777883503719

theorem tailTrace_3751761 : CollatzResearch.WordTrace tailWord_3751761 prefixEnd_3751761 214050743754777883503719 := by
  unfold tailWord_3751761
  simp only [CollatzResearch.WordTrace]
  refine ⟨136837965361018121611215137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91225310240678747740810091 136837965361018121611215137)
  ·
    refine ⟨102628474020763591208411353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136837965361018121611215137 102628474020763591208411353)
    ·
      refine ⟨76971355515572693406308515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102628474020763591208411353 76971355515572693406308515)
      ·
        refine ⟨115457033273359040109462773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76971355515572693406308515 115457033273359040109462773)
        ·
          refine ⟨10824096869377410010262135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115457033273359040109462773 10824096869377410010262135)
          ·
            refine ⟨16236145304066115015393203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10824096869377410010262135 16236145304066115015393203)
            ·
              refine ⟨24354217956099172523089805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16236145304066115015393203 24354217956099172523089805)
              ·
                refine ⟨9132831733537189696158677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24354217956099172523089805 9132831733537189696158677)
                ·
                  refine ⟨214050743754777883503719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9132831733537189696158677 214050743754777883503719)
                  ·
                    rfl

theorem cell23_3751761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 7].length) (baseStart_3751761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751761 prefixEnd_3751761 := by exact prefixLift 3751761
  have htrace : WordTrace (prefixWord ++ tailWord_3751761) baseStart_3751761 baseEnd_3751761 := by
    simpa [prefixWord, tailWord_3751761, baseEnd_3751761] using wordTrace_append hprefix tailTrace_3751761
  have hstable : (prefixWord ++ tailWord_3751761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751761).length < 2 ^ (prefixWord ++ tailWord_3751761).sum := by decide
  have hdescent : baseEnd_3751761 < baseStart_3751761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751778 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 7]
def baseStart_3751778 : Nat := 118140960795 + 3751778 * 2 ^ 59
def prefixEnd_3751778 : Nat := 4983230072969 + 3 ^ 40 * 3751778 * 2
def baseEnd_3751778 : Nat := 214051713662680820557877

theorem tailTrace_3751778 : CollatzResearch.WordTrace tailWord_3751778 prefixEnd_3751778 214051713662680820557877 := by
  unfold tailWord_3751778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34209646350489133378645997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91225723601304355676389325 34209646350489133378645997)
  ·
    refine ⟨12828617381433425016992249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34209646350489133378645997 12828617381433425016992249)
    ·
      refine ⟨9621463036075068762744187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12828617381433425016992249 9621463036075068762744187)
      ·
        refine ⟨14432194554112603144116281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9621463036075068762744187 14432194554112603144116281)
        ·
          refine ⟨10824145915584452358087211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14432194554112603144116281 10824145915584452358087211)
          ·
            refine ⟨16236218873376678537130817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10824145915584452358087211 16236218873376678537130817)
            ·
              refine ⟨12177164155032508902848113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16236218873376678537130817 12177164155032508902848113)
              ·
                refine ⟨9132873116274381677136085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12177164155032508902848113 9132873116274381677136085)
                ·
                  refine ⟨214051713662680820557877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9132873116274381677136085 214051713662680820557877)
                  ·
                    rfl

theorem cell23_3751778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_3751778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751778 prefixEnd_3751778 := by exact prefixLift 3751778
  have htrace : WordTrace (prefixWord ++ tailWord_3751778) baseStart_3751778 baseEnd_3751778 := by
    simpa [prefixWord, tailWord_3751778, baseEnd_3751778] using wordTrace_append hprefix tailTrace_3751778
  have hstable : (prefixWord ++ tailWord_3751778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751778).length < 2 ^ (prefixWord ++ tailWord_3751778).sum := by decide
  have hdescent : baseEnd_3751778 < baseStart_3751778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751801 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_3751801 : Nat := 118140960795 + 3751801 * 2 ^ 59
def prefixEnd_3751801 : Nat := 4983230072969 + 3 ^ 40 * 3751801 * 2
def baseEnd_3751801 : Nat := 1926477233019180795033287

theorem tailTrace_3751801 : CollatzResearch.WordTrace tailWord_3751801 prefixEnd_3751801 1926477233019180795033287 := by
  unfold tailWord_3751801
  simp only [CollatzResearch.WordTrace]
  refine ⟨136839424280873208442671257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91226282853915472295114171 136839424280873208442671257)
  ·
    refine ⟨102629568210654906332003443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136839424280873208442671257 102629568210654906332003443)
    ·
      refine ⟨153944352315982359498005165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102629568210654906332003443 153944352315982359498005165)
      ·
        refine ⟨57729132118493384811751937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153944352315982359498005165 57729132118493384811751937)
        ·
          refine ⟨43296849088870038608813953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57729132118493384811751937 43296849088870038608813953)
          ·
            refine ⟨32472636816652528956610465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43296849088870038608813953 32472636816652528956610465)
            ·
              refine ⟨24354477612489396717457849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32472636816652528956610465 24354477612489396717457849)
              ·
                refine ⟨18265858209367047538093387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24354477612489396717457849 18265858209367047538093387)
                ·
                  refine ⟨27398787314050571307140081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18265858209367047538093387 27398787314050571307140081)
                  ·
                    refine ⟨20549090485537928480355061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27398787314050571307140081 20549090485537928480355061)
                    ·
                      refine ⟨1926477233019180795033287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20549090485537928480355061 1926477233019180795033287)
                      ·
                        rfl

theorem cell23_3751801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_3751801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751801 prefixEnd_3751801 := by exact prefixLift 3751801
  have htrace : WordTrace (prefixWord ++ tailWord_3751801) baseStart_3751801 baseEnd_3751801 := by
    simpa [prefixWord, tailWord_3751801, baseEnd_3751801] using wordTrace_append hprefix tailTrace_3751801
  have hstable : (prefixWord ++ tailWord_3751801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751801).length < 2 ^ (prefixWord ++ tailWord_3751801).sum := by decide
  have hdescent : baseEnd_3751801 < baseStart_3751801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751855 : List Nat := [1, 1, 2, 1, 2, 2, 4, 5, 1, 4]
def baseStart_3751855 : Nat := 118140960795 + 3751855 * 2 ^ 59
def prefixEnd_3751855 : Nat := 4983230072969 + 3 ^ 40 * 3751855 * 2
def baseEnd_3751855 : Nat := 642168320324841194586013

theorem tailTrace_3751855 : CollatzResearch.WordTrace tailWord_3751855 prefixEnd_3751855 642168320324841194586013 := by
  unfold tailWord_3751855
  simp only [CollatzResearch.WordTrace]
  refine ⟨136841393822677575665137019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91227595881785050443424679 136841393822677575665137019)
  ·
    refine ⟨205262090734016363497705529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136841393822677575665137019 205262090734016363497705529)
    ·
      refine ⟨153946568050512272623279147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205262090734016363497705529 153946568050512272623279147)
      ·
        refine ⟨230919852075768408934918721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153946568050512272623279147 230919852075768408934918721)
        ·
          refine ⟨173189889056826306701189041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230919852075768408934918721 173189889056826306701189041)
          ·
            refine ⟨129892416792619730025891781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173189889056826306701189041 129892416792619730025891781)
            ·
              refine ⟨24354828148616199379854709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129892416792619730025891781 24354828148616199379854709)
              ·
                refine ⟨2283265138932768691861379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24354828148616199379854709 2283265138932768691861379)
                ·
                  refine ⟨3424897708399153037792069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283265138932768691861379 3424897708399153037792069)
                  ·
                    refine ⟨642168320324841194586013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3424897708399153037792069 642168320324841194586013)
                    ·
                      rfl

theorem cell23_3751855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 4].length) (baseStart_3751855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751855 prefixEnd_3751855 := by exact prefixLift 3751855
  have htrace : WordTrace (prefixWord ++ tailWord_3751855) baseStart_3751855 baseEnd_3751855 := by
    simpa [prefixWord, tailWord_3751855, baseEnd_3751855] using wordTrace_append hprefix tailTrace_3751855
  have hstable : (prefixWord ++ tailWord_3751855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751855).length < 2 ^ (prefixWord ++ tailWord_3751855).sum := by decide
  have hdescent : baseEnd_3751855 < baseStart_3751855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751871 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_3751871 : Nat := 118140960795 + 3751871 * 2 ^ 59
def prefixEnd_3751871 : Nat := 4983230072969 + 3 ^ 40 * 3751871 * 2
def baseEnd_3751871 : Nat := 1926513176664995521157965

theorem tailTrace_3751871 : CollatzResearch.WordTrace tailWord_3751871 prefixEnd_3751871 1926513176664995521157965 := by
  unfold tailWord_3751871
  simp only [CollatzResearch.WordTrace]
  refine ⟨136841977390619610397719467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91227984927079740265146311 136841977390619610397719467)
  ·
    refine ⟨205262966085929415596579201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136841977390619610397719467 205262966085929415596579201)
    ·
      refine ⟨153947224564447061697434401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205262966085929415596579201 153947224564447061697434401)
      ·
        refine ⟨115460418423335296273075801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153947224564447061697434401 115460418423335296273075801)
        ·
          refine ⟨86595313817501472204806851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115460418423335296273075801 86595313817501472204806851)
          ·
            refine ⟨129892970726252208307210277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86595313817501472204806851 129892970726252208307210277)
            ·
              refine ⟨24354932011172289057601927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129892970726252208307210277 24354932011172289057601927)
              ·
                refine ⟨36532398016758433586402891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24354932011172289057601927 36532398016758433586402891)
                ·
                  refine ⟨54798597025137650379604337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36532398016758433586402891 54798597025137650379604337)
                  ·
                    refine ⟨41098947768853237784703253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54798597025137650379604337 41098947768853237784703253)
                    ·
                      refine ⟨1926513176664995521157965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41098947768853237784703253 1926513176664995521157965)
                      ·
                        rfl

theorem cell23_3751871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_3751871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751871 prefixEnd_3751871 := by exact prefixLift 3751871
  have htrace : WordTrace (prefixWord ++ tailWord_3751871) baseStart_3751871 baseEnd_3751871 := by
    simpa [prefixWord, tailWord_3751871, baseEnd_3751871] using wordTrace_append hprefix tailTrace_3751871
  have hstable : (prefixWord ++ tailWord_3751871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751871).length < 2 ^ (prefixWord ++ tailWord_3751871).sum := by decide
  have hdescent : baseEnd_3751871 < baseStart_3751871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751895 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 3]
def baseStart_3751895 : Nat := 118140960795 + 3751895 * 2 ^ 59
def prefixEnd_3751895 : Nat := 4983230072969 + 3 ^ 40 * 3751895 * 2
def baseEnd_3751895 : Nat := 1926525500200703427257855

theorem tailTrace_3751895 : CollatzResearch.WordTrace tailWord_3751895 prefixEnd_3751895 1926525500200703427257855 := by
  unfold tailWord_3751895
  simp only [CollatzResearch.WordTrace]
  refine ⟨136842852742532662496593139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91228568495021774997728759 136842852742532662496593139)
  ·
    refine ⟨205264279113798993744889709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136842852742532662496593139 205264279113798993744889709)
    ·
      refine ⟨76974104667674622654333641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205264279113798993744889709 76974104667674622654333641)
      ·
        refine ⟨57730578500755966990750231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76974104667674622654333641 57730578500755966990750231)
        ·
          refine ⟨86595867751133950486125347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57730578500755966990750231 86595867751133950486125347)
          ·
            refine ⟨129893801626700925729188021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86595867751133950486125347 129893801626700925729188021)
            ·
              refine ⟨12177543902503211787111377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129893801626700925729188021 12177543902503211787111377)
              ·
                refine ⟨9133157926877408840333533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12177543902503211787111377 9133157926877408840333533)
                ·
                  refine ⟨3424934222579028315125075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9133157926877408840333533 3424934222579028315125075)
                  ·
                    refine ⟨5137401333868542472687613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3424934222579028315125075 5137401333868542472687613)
                    ·
                      refine ⟨1926525500200703427257855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5137401333868542472687613 1926525500200703427257855)
                      ·
                        rfl

theorem cell23_3751895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_3751895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751895 prefixEnd_3751895 := by exact prefixLift 3751895
  have htrace : WordTrace (prefixWord ++ tailWord_3751895) baseStart_3751895 baseEnd_3751895 := by
    simpa [prefixWord, tailWord_3751895, baseEnd_3751895] using wordTrace_append hprefix tailTrace_3751895
  have hstable : (prefixWord ++ tailWord_3751895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751895).length < 2 ^ (prefixWord ++ tailWord_3751895).sum := by decide
  have hdescent : baseEnd_3751895 < baseStart_3751895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751906 : List Nat := [3, 3, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3751906 : Nat := 118140960795 + 3751906 * 2 ^ 59
def prefixEnd_3751906 : Nat := 4983230072969 + 3 ^ 40 * 3751906 * 2
def baseEnd_3751906 : Nat := 642177049495967628073435

theorem tailTrace_3751906 : CollatzResearch.WordTrace tailWord_3751906 prefixEnd_3751906 642177049495967628073435 := by
  unfold tailWord_3751906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34210813486373202843810893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91228835963661874250162381 34210813486373202843810893)
  ·
    refine ⟨12829055057389951066429085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34210813486373202843810893 12829055057389951066429085)
    ·
      refine ⟨4810895646521231649910907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12829055057389951066429085 4810895646521231649910907)
      ·
        refine ⟨7216343469781847474866361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4810895646521231649910907 7216343469781847474866361)
        ·
          refine ⟨5412257602336385606149771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7216343469781847474866361 5412257602336385606149771)
          ·
            refine ⟨8118386403504578409224657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412257602336385606149771 8118386403504578409224657)
            ·
              refine ⟨6088789802628433806918493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8118386403504578409224657 6088789802628433806918493)
              ·
                refine ⟨2283296175985662677594435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6088789802628433806918493 2283296175985662677594435)
                ·
                  refine ⟨3424944263978494016391653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283296175985662677594435 3424944263978494016391653)
                  ·
                    refine ⟨642177049495967628073435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3424944263978494016391653 642177049495967628073435)
                    ·
                      rfl

theorem cell23_3751906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3751906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751906 prefixEnd_3751906 := by exact prefixLift 3751906
  have htrace : WordTrace (prefixWord ++ tailWord_3751906) baseStart_3751906 baseEnd_3751906 := by
    simpa [prefixWord, tailWord_3751906, baseEnd_3751906] using wordTrace_append hprefix tailTrace_3751906
  have hstable : (prefixWord ++ tailWord_3751906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751906).length < 2 ^ (prefixWord ++ tailWord_3751906).sum := by decide
  have hdescent : baseEnd_3751906 < baseStart_3751906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751948 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_3751948 : Nat := 118140960795 + 3751948 * 2 ^ 59
def prefixEnd_3751948 : Nat := 4983230072969 + 3 ^ 40 * 3751948 * 2
def baseEnd_3751948 : Nat := 1926552714675391719895111

theorem tailTrace_3751948 : CollatzResearch.WordTrace tailWord_3751948 prefixEnd_3751948 1926552714675391719895111 := by
  unfold tailWord_3751948
  simp only [CollatzResearch.WordTrace]
  refine ⟨68422392905670326274136249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91229857207560435032181665 68422392905670326274136249)
  ·
    refine ⟨51316794679252744705602187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68422392905670326274136249 51316794679252744705602187)
    ·
      refine ⟨76975192018879117058403281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51316794679252744705602187 76975192018879117058403281)
      ·
        refine ⟨57731394014159337793802461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76975192018879117058403281 57731394014159337793802461)
        ·
          refine ⟨21649272755309751672675923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57731394014159337793802461 21649272755309751672675923)
          ·
            refine ⟨32473909132964627509013885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21649272755309751672675923 32473909132964627509013885)
            ·
              refine ⟨12177715924861735315880207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32473909132964627509013885 12177715924861735315880207)
              ·
                refine ⟨18266573887292602973820311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12177715924861735315880207 18266573887292602973820311)
                ·
                  refine ⟨27399860830938904460730467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18266573887292602973820311 27399860830938904460730467)
                  ·
                    refine ⟨41099791246408356691095701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27399860830938904460730467 41099791246408356691095701)
                    ·
                      refine ⟨1926552714675391719895111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41099791246408356691095701 1926552714675391719895111)
                      ·
                        rfl

theorem cell23_3751948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_3751948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751948 prefixEnd_3751948 := by exact prefixLift 3751948
  have htrace : WordTrace (prefixWord ++ tailWord_3751948) baseStart_3751948 baseEnd_3751948 := by
    simpa [prefixWord, tailWord_3751948, baseEnd_3751948] using wordTrace_append hprefix tailTrace_3751948
  have hstable : (prefixWord ++ tailWord_3751948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751948).length < 2 ^ (prefixWord ++ tailWord_3751948).sum := by decide
  have hdescent : baseEnd_3751948 < baseStart_3751948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751955 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 3]
def baseStart_3751955 : Nat := 118140960795 + 3751955 * 2 ^ 59
def prefixEnd_3751955 : Nat := 4983230072969 + 3 ^ 40 * 3751955 * 2
def baseEnd_3751955 : Nat := 1926556309039973192507579

theorem tailTrace_3751955 : CollatzResearch.WordTrace tailWord_3751955 prefixEnd_3751955 1926556309039973192507579 := by
  unfold tailWord_3751955
  simp only [CollatzResearch.WordTrace]
  refine ⟨136845041122315292743777319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91230027414876861829184879 136845041122315292743777319)
  ·
    refine ⟨205267561683472939115665979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136845041122315292743777319 205267561683472939115665979)
    ·
      refine ⟨307901342525209408673498969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205267561683472939115665979 307901342525209408673498969)
      ·
        refine ⟨230926006893907056505124227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307901342525209408673498969 230926006893907056505124227)
        ·
          refine ⟨346389010340860584757686341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230926006893907056505124227 346389010340860584757686341)
          ·
            refine ⟨64947939438911359642066189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346389010340860584757686341 64947939438911359642066189)
            ·
              refine ⟨24355477289591759865774821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64947939438911359642066189 24355477289591759865774821)
              ·
                refine ⟨4566651991798454974832779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24355477289591759865774821 4566651991798454974832779)
                ·
                  refine ⟨6849977987697682462249169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566651991798454974832779 6849977987697682462249169)
                  ·
                    refine ⟨5137483490773261846686877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6849977987697682462249169 5137483490773261846686877)
                    ·
                      refine ⟨1926556309039973192507579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5137483490773261846686877 1926556309039973192507579)
                      ·
                        rfl

theorem cell23_3751955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 3].length) (baseStart_3751955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751955 prefixEnd_3751955 := by exact prefixLift 3751955
  have htrace : WordTrace (prefixWord ++ tailWord_3751955) baseStart_3751955 baseEnd_3751955 := by
    simpa [prefixWord, tailWord_3751955, baseEnd_3751955] using wordTrace_append hprefix tailTrace_3751955
  have hstable : (prefixWord ++ tailWord_3751955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751955).length < 2 ^ (prefixWord ++ tailWord_3751955).sum := by decide
  have hdescent : baseEnd_3751955 < baseStart_3751955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751972 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3751972 : Nat := 118140960795 + 3751972 * 2 ^ 59
def prefixEnd_3751972 : Nat := 4983230072969 + 3 ^ 40 * 3751972 * 2
def baseEnd_3751972 : Nat := 1926565038211099625995001

theorem tailTrace_3751972 : CollatzResearch.WordTrace tailWord_3751972 prefixEnd_3751972 1926565038211099625995001 := by
  unfold tailWord_3751972
  simp only [CollatzResearch.WordTrace]
  refine ⟨68422830581626852323573085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91230440775502469764764113 68422830581626852323573085)
  ·
    refine ⟨25658561468110069621339907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68422830581626852323573085 25658561468110069621339907)
    ·
      refine ⟨38487842202165104432009861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25658561468110069621339907 38487842202165104432009861)
      ·
        refine ⟨7216470412905957081001849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38487842202165104432009861 7216470412905957081001849)
        ·
          refine ⟨5412352809679467810751387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7216470412905957081001849 5412352809679467810751387)
          ·
            refine ⟨8118529214519201716127081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412352809679467810751387 8118529214519201716127081)
            ·
              refine ⟨6088896910889401287095311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8118529214519201716127081 6088896910889401287095311)
              ·
                refine ⟨9133345366334101930642967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6088896910889401287095311 9133345366334101930642967)
                ·
                  refine ⟨13700018049501152895964451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9133345366334101930642967 13700018049501152895964451)
                  ·
                    refine ⟨20550027074251729343946677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13700018049501152895964451 20550027074251729343946677)
                    ·
                      refine ⟨1926565038211099625995001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20550027074251729343946677 1926565038211099625995001)
                      ·
                        rfl

theorem cell23_3751972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3751972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751972 prefixEnd_3751972 := by exact prefixLift 3751972
  have htrace : WordTrace (prefixWord ++ tailWord_3751972) baseStart_3751972 baseEnd_3751972 := by
    simpa [prefixWord, tailWord_3751972, baseEnd_3751972] using wordTrace_append hprefix tailTrace_3751972
  have hstable : (prefixWord ++ tailWord_3751972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751972).length < 2 ^ (prefixWord ++ tailWord_3751972).sum := by decide
  have hdescent : baseEnd_3751972 < baseStart_3751972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3751995 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 5, 3, 2]
def baseStart_3751995 : Nat := 118140960795 + 3751995 * 2 ^ 59
def prefixEnd_3751995 : Nat := 4983230072969 + 3 ^ 40 * 3751995 * 2
def baseEnd_3751995 : Nat := 1926576848266153036007395

theorem tailTrace_3751995 : CollatzResearch.WordTrace tailWord_3751995 prefixEnd_3751995 1926576848266153036007395 := by
  unfold tailWord_3751995
  simp only [CollatzResearch.WordTrace]
  refine ⟨136846500042170379575233439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91231000028113586383488959 136846500042170379575233439)
  ·
    refine ⟨205269750063255569362850159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136846500042170379575233439 205269750063255569362850159)
    ·
      refine ⟨307904625094883354044275239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205269750063255569362850159 307904625094883354044275239)
      ·
        refine ⟨461856937642325031066412859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307904625094883354044275239 461856937642325031066412859)
        ·
          refine ⟨692785406463487546599619289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461856937642325031066412859 692785406463487546599619289)
          ·
            refine ⟨519589054847615659949714467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692785406463487546599619289 519589054847615659949714467)
            ·
              refine ⟨779383582271423489924571701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519589054847615659949714467 779383582271423489924571701)
              ·
                refine ⟨73067210837945952180428597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 779383582271423489924571701 73067210837945952180428597)
                ·
                  refine ⟨6850051016057433016915181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73067210837945952180428597 6850051016057433016915181)
                  ·
                    refine ⟨2568769131021537381343193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6850051016057433016915181 2568769131021537381343193)
                    ·
                      refine ⟨1926576848266153036007395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568769131021537381343193 1926576848266153036007395)
                      ·
                        rfl

theorem cell23_3751995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 3, 2].length) (baseStart_3751995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3751995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3751995 prefixEnd_3751995 := by exact prefixLift 3751995
  have htrace : WordTrace (prefixWord ++ tailWord_3751995) baseStart_3751995 baseEnd_3751995 := by
    simpa [prefixWord, tailWord_3751995, baseEnd_3751995] using wordTrace_append hprefix tailTrace_3751995
  have hstable : (prefixWord ++ tailWord_3751995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3751995).length < 2 ^ (prefixWord ++ tailWord_3751995).sum := by decide
  have hdescent : baseEnd_3751995 < baseStart_3751995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3751995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752008 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_3752008 : Nat := 118140960795 + 3752008 * 2 ^ 59
def prefixEnd_3752008 : Nat := 4983230072969 + 3 ^ 40 * 3752008 * 2
def baseEnd_3752008 : Nat := 1926583523514661485144835

theorem tailTrace_3752008 : CollatzResearch.WordTrace tailWord_3752008 prefixEnd_3752008 1926583523514661485144835 := by
  unfold tailWord_3752008
  simp only [CollatzResearch.WordTrace]
  refine ⟨68423487095561641397728339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91231316127415521863637785 68423487095561641397728339)
  ·
    refine ⟨102635230643342462096592509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68423487095561641397728339 102635230643342462096592509)
    ·
      refine ⟨38488211491253423286222191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102635230643342462096592509 38488211491253423286222191)
      ·
        refine ⟨57732317236880134929333287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38488211491253423286222191 57732317236880134929333287)
        ·
          refine ⟨86598475855320202393999931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57732317236880134929333287 86598475855320202393999931)
          ·
            refine ⟨129897713782980303590999897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86598475855320202393999931 129897713782980303590999897)
            ·
              refine ⟨97423285337235227693249923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129897713782980303590999897 97423285337235227693249923)
              ·
                refine ⟨146134928005852841539874885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97423285337235227693249923 146134928005852841539874885)
                ·
                  refine ⟨27400299001097407788726541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146134928005852841539874885 27400299001097407788726541)
                  ·
                    refine ⟨10275112125411527920772453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27400299001097407788726541 10275112125411527920772453)
                    ·
                      refine ⟨1926583523514661485144835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10275112125411527920772453 1926583523514661485144835)
                      ·
                        rfl

theorem cell23_3752008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_3752008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752008 prefixEnd_3752008 := by exact prefixLift 3752008
  have htrace : WordTrace (prefixWord ++ tailWord_3752008) baseStart_3752008 baseEnd_3752008 := by
    simpa [prefixWord, tailWord_3752008, baseEnd_3752008] using wordTrace_append hprefix tailTrace_3752008
  have hstable : (prefixWord ++ tailWord_3752008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752008).length < 2 ^ (prefixWord ++ tailWord_3752008).sum := by decide
  have hdescent : baseEnd_3752008 < baseStart_3752008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752045 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_3752045 : Nat := 118140960795 + 3752045 * 2 ^ 59
def prefixEnd_3752045 : Nat := 4983230072969 + 3 ^ 40 * 3752045 * 2
def baseEnd_3752045 : Nat := 1926602522298877840382165

theorem tailTrace_3752045 : CollatzResearch.WordTrace tailWord_3752045 prefixEnd_3752045 1926602522298877840382165 := by
  unfold tailWord_3752045
  simp only [CollatzResearch.WordTrace]
  refine ⟨136848323691989238114553589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91232215794659492076369059 136848323691989238114553589)
  ·
    refine ⟨12829530346123991073239399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136848323691989238114553589 12829530346123991073239399)
    ·
      refine ⟨19244295519185986609859099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12829530346123991073239399 19244295519185986609859099)
      ·
        refine ⟨28866443278778979914788649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19244295519185986609859099 28866443278778979914788649)
        ·
          refine ⟨21649832459084234936091487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28866443278778979914788649 21649832459084234936091487)
          ·
            refine ⟨32474748688626352404137231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21649832459084234936091487 32474748688626352404137231)
            ·
              refine ⟨48712123032939528606205847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32474748688626352404137231 48712123032939528606205847)
              ·
                refine ⟨73068184549409292909308771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48712123032939528606205847 73068184549409292909308771)
                ·
                  refine ⟨109602276824113939363963157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73068184549409292909308771 109602276824113939363963157)
                  ·
                    refine ⟨5137606726130340907685773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109602276824113939363963157 5137606726130340907685773)
                    ·
                      refine ⟨1926602522298877840382165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5137606726130340907685773 1926602522298877840382165)
                      ·
                        rfl

theorem cell23_3752045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_3752045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752045 prefixEnd_3752045 := by exact prefixLift 3752045
  have htrace : WordTrace (prefixWord ++ tailWord_3752045) baseStart_3752045 baseEnd_3752045 := by
    simpa [prefixWord, tailWord_3752045, baseEnd_3752045] using wordTrace_append hprefix tailTrace_3752045
  have hstable : (prefixWord ++ tailWord_3752045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752045).length < 2 ^ (prefixWord ++ tailWord_3752045).sum := by decide
  have hdescent : baseEnd_3752045 < baseStart_3752045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752055 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_3752055 : Nat := 118140960795 + 3752055 * 2 ^ 59
def prefixEnd_3752055 : Nat := 4983230072969 + 3 ^ 40 * 3752055 * 2
def baseEnd_3752055 : Nat := 1926607657105422801257119

theorem tailTrace_3752055 : CollatzResearch.WordTrace tailWord_3752055 prefixEnd_3752055 1926607657105422801257119 := by
  unfold tailWord_3752055
  simp only [CollatzResearch.WordTrace]
  refine ⟨136848688421953009822417619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91232458947968673214945079 136848688421953009822417619)
  ·
    refine ⟨205273032632929514733626429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136848688421953009822417619 205273032632929514733626429)
    ·
      refine ⟨76977387237348568025109911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205273032632929514733626429 76977387237348568025109911)
      ·
        refine ⟨115466080856022852037664867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76977387237348568025109911 115466080856022852037664867)
        ·
          refine ⟨173199121284034278056497301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115466080856022852037664867 173199121284034278056497301)
          ·
            refine ⟨8118708810189106783898311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173199121284034278056497301 8118708810189106783898311)
            ·
              refine ⟨12178063215283660175847467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8118708810189106783898311 12178063215283660175847467)
              ·
                refine ⟨18267094822925490263771201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12178063215283660175847467 18267094822925490263771201)
                ·
                  refine ⟨13700321117194117697828401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18267094822925490263771201 13700321117194117697828401)
                  ·
                    refine ⟨10275240837895588273371301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13700321117194117697828401 10275240837895588273371301)
                    ·
                      refine ⟨1926607657105422801257119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10275240837895588273371301 1926607657105422801257119)
                      ·
                        rfl

theorem cell23_3752055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_3752055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752055 prefixEnd_3752055 := by exact prefixLift 3752055
  have htrace : WordTrace (prefixWord ++ tailWord_3752055) baseStart_3752055 baseEnd_3752055 := by
    simpa [prefixWord, tailWord_3752055, baseEnd_3752055] using wordTrace_append hprefix tailTrace_3752055
  have hstable : (prefixWord ++ tailWord_3752055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752055).length < 2 ^ (prefixWord ++ tailWord_3752055).sum := by decide
  have hdescent : baseEnd_3752055 < baseStart_3752055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752110 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3752110 : Nat := 118140960795 + 3752110 * 2 ^ 59
def prefixEnd_3752110 : Nat := 4983230072969 + 3 ^ 40 * 3752110 * 2
def baseEnd_3752110 : Nat := 1926635898541420086069367

theorem tailTrace_3752110 : CollatzResearch.WordTrace tailWord_3752110 prefixEnd_3752110 1926635898541420086069367 := by
  unfold tailWord_3752110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17106336804594219276958723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91233796291169169477113189 17106336804594219276958723)
  ·
    refine ⟨25659505206891328915438085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17106336804594219276958723 25659505206891328915438085)
    ·
      refine ⟨4811157226292124171644641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25659505206891328915438085 4811157226292124171644641)
      ·
        refine ⟨3608367919719093128733481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4811157226292124171644641 3608367919719093128733481)
        ·
          refine ⟨2706275939789319846550111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3608367919719093128733481 2706275939789319846550111)
          ·
            refine ⟨4059413909683979769825167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706275939789319846550111 4059413909683979769825167)
            ·
              refine ⟨6089120864525969654737751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059413909683979769825167 6089120864525969654737751)
              ·
                refine ⟨9133681296788954482106627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089120864525969654737751 9133681296788954482106627)
                ·
                  refine ⟨13700521945183431723159941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9133681296788954482106627 13700521945183431723159941)
                  ·
                    refine ⟨2568847864721893448092489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13700521945183431723159941 2568847864721893448092489)
                    ·
                      refine ⟨1926635898541420086069367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568847864721893448092489 1926635898541420086069367)
                      ·
                        rfl

theorem cell23_3752110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3752110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752110 prefixEnd_3752110 := by exact prefixLift 3752110
  have htrace : WordTrace (prefixWord ++ tailWord_3752110) baseStart_3752110 baseEnd_3752110 := by
    simpa [prefixWord, tailWord_3752110, baseEnd_3752110] using wordTrace_append hprefix tailTrace_3752110
  have hstable : (prefixWord ++ tailWord_3752110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752110).length < 2 ^ (prefixWord ++ tailWord_3752110).sum := by decide
  have hdescent : baseEnd_3752110 < baseStart_3752110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752132 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3752132 : Nat := 118140960795 + 3752132 * 2 ^ 59
def prefixEnd_3752132 : Nat := 4983230072969 + 3 ^ 40 * 3752132 * 2
def baseEnd_3752132 : Nat := 1926647195115818999994265

theorem tailTrace_3752132 : CollatzResearch.WordTrace tailWord_3752132 prefixEnd_3752132 1926647195115818999994265 := by
  unfold tailWord_3752132
  simp only [CollatzResearch.WordTrace]
  refine ⟨68425748421337025986485325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91234331228449367981980433 68425748421337025986485325)
  ·
    refine ⟨25659655658001384744931997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68425748421337025986485325 25659655658001384744931997)
    ·
      refine ⟨9622370871750519279349499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25659655658001384744931997 9622370871750519279349499)
      ·
        refine ⟨14433556307625778919024249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9622370871750519279349499 14433556307625778919024249)
        ·
          refine ⟨10825167230719334189268187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14433556307625778919024249 10825167230719334189268187)
          ·
            refine ⟨16237750846079001283902281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10825167230719334189268187 16237750846079001283902281)
            ·
              refine ⟨12178313134559250962926711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16237750846079001283902281 12178313134559250962926711)
              ·
                refine ⟨18267469701838876444390067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12178313134559250962926711 18267469701838876444390067)
                ·
                  refine ⟨27401204552758314666585101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18267469701838876444390067 27401204552758314666585101)
                  ·
                    refine ⟨10275451707284367999969413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27401204552758314666585101 10275451707284367999969413)
                    ·
                      refine ⟨1926647195115818999994265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10275451707284367999969413 1926647195115818999994265)
                      ·
                        rfl

theorem cell23_3752132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3752132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752132 prefixEnd_3752132 := by exact prefixLift 3752132
  have htrace : WordTrace (prefixWord ++ tailWord_3752132) baseStart_3752132 baseEnd_3752132 := by
    simpa [prefixWord, tailWord_3752132, baseEnd_3752132] using wordTrace_append hprefix tailTrace_3752132
  have hstable : (prefixWord ++ tailWord_3752132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752132).length < 2 ^ (prefixWord ++ tailWord_3752132).sum := by decide
  have hdescent : baseEnd_3752132 < baseStart_3752132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752149 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3752149 : Nat := 118140960795 + 3752149 * 2 ^ 59
def prefixEnd_3752149 : Nat := 4983230072969 + 3 ^ 40 * 3752149 * 2
def baseEnd_3752149 : Nat := 1926655924286945433481687

theorem tailTrace_3752149 : CollatzResearch.WordTrace tailWord_3752149 prefixEnd_3752149 1926655924286945433481687 := by
  unfold tailWord_3752149
  simp only [CollatzResearch.WordTrace]
  refine ⟨136852116883612463876339501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91234744589074975917559667 136852116883612463876339501)
  ·
    refine ⟨51319543831354673953627313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136852116883612463876339501 51319543831354673953627313)
    ·
      refine ⟨38489657873516005465220485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51319543831354673953627313 38489657873516005465220485)
      ·
        refine ⟨7216810851284251024728841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38489657873516005465220485 7216810851284251024728841)
        ·
          refine ⟨5412608138463188268546631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7216810851284251024728841 5412608138463188268546631)
          ·
            refine ⟨8118912207694782402819947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412608138463188268546631 8118912207694782402819947)
            ·
              refine ⟨12178368311542173604229921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8118912207694782402819947 12178368311542173604229921)
              ·
                refine ⟨9133776233656630203172441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12178368311542173604229921 9133776233656630203172441)
                ·
                  refine ⟨6850332175242472652379331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9133776233656630203172441 6850332175242472652379331)
                  ·
                    refine ⟨10275498262863708978568997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6850332175242472652379331 10275498262863708978568997)
                    ·
                      refine ⟨1926655924286945433481687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10275498262863708978568997 1926655924286945433481687)
                      ·
                        rfl

theorem cell23_3752149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3752149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752149 prefixEnd_3752149 := by exact prefixLift 3752149
  have htrace : WordTrace (prefixWord ++ tailWord_3752149) baseStart_3752149 baseEnd_3752149 := by
    simpa [prefixWord, tailWord_3752149, baseEnd_3752149] using wordTrace_append hprefix tailTrace_3752149
  have hstable : (prefixWord ++ tailWord_3752149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752149).length < 2 ^ (prefixWord ++ tailWord_3752149).sum := by decide
  have hdescent : baseEnd_3752149 < baseStart_3752149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752152 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_3752152 : Nat := 118140960795 + 3752152 * 2 ^ 59
def prefixEnd_3752152 : Nat := 4983230072969 + 3 ^ 40 * 3752152 * 2
def baseEnd_3752152 : Nat := 1926657464728908921744173

theorem tailTrace_3752152 : CollatzResearch.WordTrace tailWord_3752152 prefixEnd_3752152 1926657464728908921744173 := by
  unfold tailWord_3752152
  simp only [CollatzResearch.WordTrace]
  refine ⟨68426113151300797694349355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91234817535067730259132473 68426113151300797694349355)
  ·
    refine ⟨102639169726951196541524033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68426113151300797694349355 102639169726951196541524033)
    ·
      refine ⟨76979377295213397406143025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102639169726951196541524033 76979377295213397406143025)
      ·
        refine ⟨57734532971410048054607269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76979377295213397406143025 57734532971410048054607269)
        ·
          refine ⟨10825224932139384010238863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57734532971410048054607269 10825224932139384010238863)
          ·
            refine ⟨16237837398209076015358295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10825224932139384010238863 16237837398209076015358295)
            ·
              refine ⟨24356756097313614023037443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16237837398209076015358295 24356756097313614023037443)
              ·
                refine ⟨36535134145970421034556165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24356756097313614023037443 36535134145970421034556165)
                ·
                  refine ⟨6850337652369453943979281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36535134145970421034556165 6850337652369453943979281)
                  ·
                    refine ⟨5137753239277090457984461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6850337652369453943979281 5137753239277090457984461)
                    ·
                      refine ⟨1926657464728908921744173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5137753239277090457984461 1926657464728908921744173)
                      ·
                        rfl

theorem cell23_3752152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_3752152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752152 prefixEnd_3752152 := by exact prefixLift 3752152
  have htrace : WordTrace (prefixWord ++ tailWord_3752152) baseStart_3752152 baseEnd_3752152 := by
    simpa [prefixWord, tailWord_3752152, baseEnd_3752152] using wordTrace_append hprefix tailTrace_3752152
  have hstable : (prefixWord ++ tailWord_3752152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752152).length < 2 ^ (prefixWord ++ tailWord_3752152).sum := by decide
  have hdescent : baseEnd_3752152 < baseStart_3752152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752182 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3752182 : Nat := 118140960795 + 3752182 * 2 ^ 59
def prefixEnd_3752182 : Nat := 4983230072969 + 3 ^ 40 * 3752182 * 2
def baseEnd_3752182 : Nat := 1926672869148543804369035

theorem tailTrace_3752182 : CollatzResearch.WordTrace tailWord_3752182 prefixEnd_3752182 1926672869148543804369035 := by
  unfold tailWord_3752182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8553332530780806907018175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91235546994995273674860533 8553332530780806907018175)
  ·
    refine ⟨12829998796171210360527263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8553332530780806907018175 12829998796171210360527263)
    ·
      refine ⟨19244998194256815540790895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12829998796171210360527263 19244998194256815540790895)
      ·
        refine ⟨28867497291385223311186343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19244998194256815540790895 28867497291385223311186343)
        ·
          refine ⟨43301245937077834966779515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28867497291385223311186343 43301245937077834966779515)
          ·
            refine ⟨64951868905616752450169273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43301245937077834966779515 64951868905616752450169273)
            ·
              refine ⟨48713901679212564337626955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64951868905616752450169273 48713901679212564337626955)
              ·
                refine ⟨73070852518818846506440433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48713901679212564337626955 73070852518818846506440433)
                ·
                  refine ⟨54803139389114134879830325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73070852518818846506440433 54803139389114134879830325)
                  ·
                    refine ⟨5137794317729450144984093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54803139389114134879830325 5137794317729450144984093)
                    ·
                      refine ⟨1926672869148543804369035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5137794317729450144984093 1926672869148543804369035)
                      ·
                        rfl

theorem cell23_3752182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3752182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752182 prefixEnd_3752182 := by exact prefixLift 3752182
  have htrace : WordTrace (prefixWord ++ tailWord_3752182) baseStart_3752182 baseEnd_3752182 := by
    simpa [prefixWord, tailWord_3752182, baseEnd_3752182] using wordTrace_append hprefix tailTrace_3752182
  have hstable : (prefixWord ++ tailWord_3752182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752182).length < 2 ^ (prefixWord ++ tailWord_3752182).sum := by decide
  have hdescent : baseEnd_3752182 < baseStart_3752182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752192 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 1, 5, 2]
def baseStart_3752192 : Nat := 118140960795 + 3752192 * 2 ^ 59
def prefixEnd_3752192 : Nat := 4983230072969 + 3 ^ 40 * 3752192 * 2
def baseEnd_3752192 : Nat := 1926678003955088765243989

theorem tailTrace_3752192 : CollatzResearch.WordTrace tailWord_3752192 prefixEnd_3752192 1926678003955088765243989 := by
  unfold tailWord_3752192
  simp only [CollatzResearch.WordTrace]
  refine ⟨68426842611228341110077415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91235790148304454813436553 68426842611228341110077415)
  ·
    refine ⟨102640263916842511665116123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68426842611228341110077415 102640263916842511665116123)
    ·
      refine ⟨153960395875263767497674185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102640263916842511665116123 153960395875263767497674185)
      ·
        refine ⟨115470296906447825623255639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153960395875263767497674185 115470296906447825623255639)
        ·
          refine ⟨173205445359671738434883459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115470296906447825623255639 173205445359671738434883459)
          ·
            refine ⟨259808168039507607652325189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173205445359671738434883459 259808168039507607652325189)
            ·
              refine ⟨48714031507407676434810973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259808168039507607652325189 48714031507407676434810973)
              ·
                refine ⟨18267761815277878663054115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48714031507407676434810973 18267761815277878663054115)
                ·
                  refine ⟨27401642722916817994581173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18267761815277878663054115 27401642722916817994581173)
                  ·
                    refine ⟨2568904005273451686991985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27401642722916817994581173 2568904005273451686991985)
                    ·
                      refine ⟨1926678003955088765243989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568904005273451686991985 1926678003955088765243989)
                      ·
                        rfl

theorem cell23_3752192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_3752192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752192 prefixEnd_3752192 := by exact prefixLift 3752192
  have htrace : WordTrace (prefixWord ++ tailWord_3752192) baseStart_3752192 baseEnd_3752192 := by
    simpa [prefixWord, tailWord_3752192, baseEnd_3752192] using wordTrace_append hprefix tailTrace_3752192
  have hstable : (prefixWord ++ tailWord_3752192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752192).length < 2 ^ (prefixWord ++ tailWord_3752192).sum := by decide
  have hdescent : baseEnd_3752192 < baseStart_3752192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752202 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_3752202 : Nat := 118140960795 + 3752202 * 2 ^ 59
def prefixEnd_3752202 : Nat := 4983230072969 + 3 ^ 40 * 3752202 * 2
def baseEnd_3752202 : Nat := 642227712920544575372981

theorem tailTrace_3752202 : CollatzResearch.WordTrace tailWord_3752202 prefixEnd_3752202 642227712920544575372981 := by
  unfold tailWord_3752202
  simp only [CollatzResearch.WordTrace]
  refine ⟨34213512488105113482004715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91236033301613635952012573 34213512488105113482004715)
  ·
    refine ⟨51320268732157670223007073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34213512488105113482004715 51320268732157670223007073)
    ·
      refine ⟨38490201549118252667255305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51320268732157670223007073 38490201549118252667255305)
      ·
        refine ⟨28867651161838689500441479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38490201549118252667255305 28867651161838689500441479)
        ·
          refine ⟨43301476742758034250662219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28867651161838689500441479 43301476742758034250662219)
          ·
            refine ⟨64952215114137051375993329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43301476742758034250662219 64952215114137051375993329)
            ·
              refine ⟨48714161335602788531994997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64952215114137051375993329 48714161335602788531994997)
              ·
                refine ⟨4566952625212761424874531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48714161335602788531994997 4566952625212761424874531)
                ·
                  refine ⟨6850428937819142137311797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566952625212761424874531 6850428937819142137311797)
                  ·
                    refine ⟨642227712920544575372981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6850428937819142137311797 642227712920544575372981)
                    ·
                      rfl

theorem cell23_3752202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_3752202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752202 prefixEnd_3752202 := by exact prefixLift 3752202
  have htrace : WordTrace (prefixWord ++ tailWord_3752202) baseStart_3752202 baseEnd_3752202 := by
    simpa [prefixWord, tailWord_3752202, baseEnd_3752202] using wordTrace_append hprefix tailTrace_3752202
  have hstable : (prefixWord ++ tailWord_3752202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752202).length < 2 ^ (prefixWord ++ tailWord_3752202).sum := by decide
  have hdescent : baseEnd_3752202 < baseStart_3752202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752209 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 2, 3, 2]
def baseStart_3752209 : Nat := 118140960795 + 3752209 * 2 ^ 59
def prefixEnd_3752209 : Nat := 4983230072969 + 3 ^ 40 * 3752209 * 2
def baseEnd_3752209 : Nat := 1926686733126215198731411

theorem tailTrace_3752209 : CollatzResearch.WordTrace tailWord_3752209 prefixEnd_3752209 1926686733126215198731411 := by
  unfold tailWord_3752209
  simp only [CollatzResearch.WordTrace]
  refine ⟨136854305263395094123523681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91236203508930062749015787 136854305263395094123523681)
  ·
    refine ⟨102640728947546320592642761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136854305263395094123523681 102640728947546320592642761)
    ·
      refine ⟨76980546710659740444482071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102640728947546320592642761 76980546710659740444482071)
      ·
        refine ⟨115470820065989610666723107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76980546710659740444482071 115470820065989610666723107)
        ·
          refine ⟨173206230098984416000084661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115470820065989610666723107 173206230098984416000084661)
          ·
            refine ⟨16238084071779789000007937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173206230098984416000084661 16238084071779789000007937)
            ·
              refine ⟨12178563053834841750005953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16238084071779789000007937 12178563053834841750005953)
              ·
                refine ⟨9133922290376131312504465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12178563053834841750005953 9133922290376131312504465)
                ·
                  refine ⟨6850441717782098484378349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9133922290376131312504465 6850441717782098484378349)
                  ·
                    refine ⟨2568915644168286931641881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6850441717782098484378349 2568915644168286931641881)
                    ·
                      refine ⟨1926686733126215198731411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568915644168286931641881 1926686733126215198731411)
                      ·
                        rfl

theorem cell23_3752209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_3752209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752209 prefixEnd_3752209 := by exact prefixLift 3752209
  have htrace : WordTrace (prefixWord ++ tailWord_3752209) baseStart_3752209 baseEnd_3752209 := by
    simpa [prefixWord, tailWord_3752209, baseEnd_3752209] using wordTrace_append hprefix tailTrace_3752209
  have hstable : (prefixWord ++ tailWord_3752209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752209).length < 2 ^ (prefixWord ++ tailWord_3752209).sum := by decide
  have hdescent : baseEnd_3752209 < baseStart_3752209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752216 : List Nat := [2, 1, 2, 3, 1, 2, 3, 4, 1, 1, 3]
def baseStart_3752216 : Nat := 118140960795 + 3752216 * 2 ^ 59
def prefixEnd_3752216 : Nat := 4983230072969 + 3 ^ 40 * 3752216 * 2
def baseEnd_3752216 : Nat := 1926690327490796671343879

theorem tailTrace_3752216 : CollatzResearch.WordTrace tailWord_3752216 prefixEnd_3752216 1926690327490796671343879 := by
  unfold tailWord_3752216
  simp only [CollatzResearch.WordTrace]
  refine ⟨68427280287184867159514251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91236373716246489546019001 68427280287184867159514251)
  ·
    refine ⟨102640920430777300739271377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68427280287184867159514251 102640920430777300739271377)
    ·
      refine ⟨76980690323082975554453533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102640920430777300739271377 76980690323082975554453533)
      ·
        refine ⟨28867758871156115832920075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76980690323082975554453533 28867758871156115832920075)
        ·
          refine ⟨43301638306734173749380113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28867758871156115832920075 43301638306734173749380113)
          ·
            refine ⟨32476228730050630312035085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43301638306734173749380113 32476228730050630312035085)
            ·
              refine ⟨12178585773768986367013157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32476228730050630312035085 12178585773768986367013157)
              ·
                refine ⟨2283484832581684943814967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12178585773768986367013157 2283484832581684943814967)
                ·
                  refine ⟨3425227248872527415722451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283484832581684943814967 3425227248872527415722451)
                  ·
                    refine ⟨5137840873308791123583677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3425227248872527415722451 5137840873308791123583677)
                    ·
                      refine ⟨1926690327490796671343879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5137840873308791123583677 1926690327490796671343879)
                      ·
                        rfl

theorem cell23_3752216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_3752216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752216 prefixEnd_3752216 := by exact prefixLift 3752216
  have htrace : WordTrace (prefixWord ++ tailWord_3752216) baseStart_3752216 baseEnd_3752216 := by
    simpa [prefixWord, tailWord_3752216, baseEnd_3752216] using wordTrace_append hprefix tailTrace_3752216
  have hstable : (prefixWord ++ tailWord_3752216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752216).length < 2 ^ (prefixWord ++ tailWord_3752216).sum := by decide
  have hdescent : baseEnd_3752216 < baseStart_3752216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752239 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 5, 2, 2]
def baseStart_3752239 : Nat := 118140960795 + 3752239 * 2 ^ 59
def prefixEnd_3752239 : Nat := 4983230072969 + 3 ^ 40 * 3752239 * 2
def baseEnd_3752239 : Nat := 1926702137545850081356273

theorem tailTrace_3752239 : CollatzResearch.WordTrace tailWord_3752239 prefixEnd_3752239 1926702137545850081356273 := by
  unfold tailWord_3752239
  simp only [CollatzResearch.WordTrace]
  refine ⟨136855399453286409247115771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91236932968857606164743847 136855399453286409247115771)
  ·
    refine ⟨205283099179929613870673657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136855399453286409247115771 205283099179929613870673657)
    ·
      refine ⟨153962324384947210403005243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205283099179929613870673657 153962324384947210403005243)
      ·
        refine ⟨230943486577420815604507865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153962324384947210403005243 230943486577420815604507865)
        ·
          refine ⟨173207614933065611703380899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230943486577420815604507865 173207614933065611703380899)
          ·
            refine ⟨259811422399598417555071349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173207614933065611703380899 259811422399598417555071349)
            ·
              refine ⟨24357320849962351645787939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259811422399598417555071349 24357320849962351645787939)
              ·
                refine ⟨36535981274943527468681909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24357320849962351645787939 36535981274943527468681909)
                ·
                  refine ⟨3425248244525955700188929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36535981274943527468681909 3425248244525955700188929)
                  ·
                    refine ⟨2568936183394466775141697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3425248244525955700188929 2568936183394466775141697)
                    ·
                      refine ⟨1926702137545850081356273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568936183394466775141697 1926702137545850081356273)
                      ·
                        rfl

theorem cell23_3752239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 2, 2].length) (baseStart_3752239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752239 prefixEnd_3752239 := by exact prefixLift 3752239
  have htrace : WordTrace (prefixWord ++ tailWord_3752239) baseStart_3752239 baseEnd_3752239 := by
    simpa [prefixWord, tailWord_3752239, baseEnd_3752239] using wordTrace_append hprefix tailTrace_3752239
  have hstable : (prefixWord ++ tailWord_3752239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752239).length < 2 ^ (prefixWord ++ tailWord_3752239).sum := by decide
  have hdescent : baseEnd_3752239 < baseStart_3752239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752252 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3752252 : Nat := 118140960795 + 3752252 * 2 ^ 59
def prefixEnd_3752252 : Nat := 4983230072969 + 3 ^ 40 * 3752252 * 2
def baseEnd_3752252 : Nat := 1926708812794358530493713

theorem tailTrace_3752252 : CollatzResearch.WordTrace tailWord_3752252 prefixEnd_3752252 1926708812794358530493713 := by
  unfold tailWord_3752252
  simp only [CollatzResearch.WordTrace]
  refine ⟨68427936801119656233669505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91237249068159541644892673 68427936801119656233669505)
  ·
    refine ⟨51320952600839742175252129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68427936801119656233669505 51320952600839742175252129)
    ·
      refine ⟨38490714450629806631439097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51320952600839742175252129 38490714450629806631439097)
      ·
        refine ⟨28868035837972354973579323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38490714450629806631439097 28868035837972354973579323)
        ·
          refine ⟨43302053756958532460368985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28868035837972354973579323 43302053756958532460368985)
          ·
            refine ⟨32476540317718899345276739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43302053756958532460368985 32476540317718899345276739)
            ·
              refine ⟨48714810476578349017915109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32476540317718899345276739 48714810476578349017915109)
              ·
                refine ⟨9134026964358440440859083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48714810476578349017915109 9134026964358440440859083)
                ·
                  refine ⟨13701040446537660661288625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9134026964358440440859083 13701040446537660661288625)
                  ·
                    refine ⟨10275780334903245495966469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13701040446537660661288625 10275780334903245495966469)
                    ·
                      refine ⟨1926708812794358530493713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10275780334903245495966469 1926708812794358530493713)
                      ·
                        rfl

theorem cell23_3752252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3752252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752252 prefixEnd_3752252 := by exact prefixLift 3752252
  have htrace : WordTrace (prefixWord ++ tailWord_3752252) baseStart_3752252 baseEnd_3752252 := by
    simpa [prefixWord, tailWord_3752252, baseEnd_3752252] using wordTrace_append hprefix tailTrace_3752252
  have hstable : (prefixWord ++ tailWord_3752252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752252).length < 2 ^ (prefixWord ++ tailWord_3752252).sum := by decide
  have hdescent : baseEnd_3752252 < baseStart_3752252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752265 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_3752265 : Nat := 118140960795 + 3752265 * 2 ^ 59
def prefixEnd_3752265 : Nat := 4983230072969 + 3 ^ 40 * 3752265 * 2
def baseEnd_3752265 : Nat := 1926715488042866979631153

theorem tailTrace_3752265 : CollatzResearch.WordTrace tailWord_3752265 prefixEnd_3752265 1926715488042866979631153 := by
  unfold tailWord_3752265
  simp only [CollatzResearch.WordTrace]
  refine ⟨136856347751192215687562249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91237565167461477125041499 136856347751192215687562249)
  ·
    refine ⟨102642260813394161765671687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136856347751192215687562249 102642260813394161765671687)
    ·
      refine ⟨153963391220091242648507531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102642260813394161765671687 153963391220091242648507531)
      ·
        refine ⟨230945086830136863972761297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153963391220091242648507531 230945086830136863972761297)
        ·
          refine ⟨173208815122602647979570973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230945086830136863972761297 173208815122602647979570973)
          ·
            refine ⟨64953305670975992992339115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173208815122602647979570973 64953305670975992992339115)
            ·
              refine ⟨97429958506463989488508673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64953305670975992992339115 97429958506463989488508673)
              ·
                refine ⟨73072468879847992116381505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97429958506463989488508673 73072468879847992116381505)
                ·
                  refine ⟨54804351659885994087286129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73072468879847992116381505 54804351659885994087286129)
                  ·
                    refine ⟨41103263744914495565464597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54804351659885994087286129 41103263744914495565464597)
                    ·
                      refine ⟨1926715488042866979631153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41103263744914495565464597 1926715488042866979631153)
                      ·
                        rfl

theorem cell23_3752265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_3752265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752265 prefixEnd_3752265 := by exact prefixLift 3752265
  have htrace : WordTrace (prefixWord ++ tailWord_3752265) baseStart_3752265 baseEnd_3752265 := by
    simpa [prefixWord, tailWord_3752265, baseEnd_3752265] using wordTrace_append hprefix tailTrace_3752265
  have hstable : (prefixWord ++ tailWord_3752265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752265).length < 2 ^ (prefixWord ++ tailWord_3752265).sum := by decide
  have hdescent : baseEnd_3752265 < baseStart_3752265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752273 : List Nat := [1, 2, 2, 1, 4, 2, 2, 4, 1, 2, 2]
def baseStart_3752273 : Nat := 118140960795 + 3752273 * 2 ^ 59
def prefixEnd_3752273 : Nat := 4983230072969 + 3 ^ 40 * 3752273 * 2
def baseEnd_3752273 : Nat := 1926719595888102948331117

theorem tailTrace_3752273 : CollatzResearch.WordTrace tailWord_3752273 prefixEnd_3752273 1926719595888102948331117 := by
  unfold tailWord_3752273
  simp only [CollatzResearch.WordTrace]
  refine ⟨136856639535163233053853473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91237759690108822035902315 136856639535163233053853473)
  ·
    refine ⟨102642479651372424790390105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136856639535163233053853473 102642479651372424790390105)
    ·
      refine ⟨76981859738529318592792579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102642479651372424790390105 76981859738529318592792579)
      ·
        refine ⟨115472789607793977889188869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76981859738529318592792579 115472789607793977889188869)
        ·
          refine ⟨21651148051461370854222913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115472789607793977889188869 21651148051461370854222913)
          ·
            refine ⟨16238361038596028140667185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21651148051461370854222913 16238361038596028140667185)
            ·
              refine ⟨12178770778947021105500389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16238361038596028140667185 12178770778947021105500389)
              ·
                refine ⟨2283519521052566457281323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12178770778947021105500389 2283519521052566457281323)
                ·
                  refine ⟨3425279281578849685921985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283519521052566457281323 3425279281578849685921985)
                  ·
                    refine ⟨2568959461184137264441489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3425279281578849685921985 2568959461184137264441489)
                    ·
                      refine ⟨1926719595888102948331117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2568959461184137264441489 1926719595888102948331117)
                      ·
                        rfl

theorem cell23_3752273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 2, 2].length) (baseStart_3752273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752273 prefixEnd_3752273 := by exact prefixLift 3752273
  have htrace : WordTrace (prefixWord ++ tailWord_3752273) baseStart_3752273 baseEnd_3752273 := by
    simpa [prefixWord, tailWord_3752273, baseEnd_3752273] using wordTrace_append hprefix tailTrace_3752273
  have hstable : (prefixWord ++ tailWord_3752273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752273).length < 2 ^ (prefixWord ++ tailWord_3752273).sum := by decide
  have hdescent : baseEnd_3752273 < baseStart_3752273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752275 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 2, 7]
def baseStart_3752275 : Nat := 118140960795 + 3752275 * 2 ^ 59
def prefixEnd_3752275 : Nat := 4983230072969 + 3 ^ 40 * 3752275 * 2
def baseEnd_3752275 : Nat := 642240207616470646835369

theorem tailTrace_3752275 : CollatzResearch.WordTrace tailWord_3752275 prefixEnd_3752275 642240207616470646835369 := by
  unfold tailWord_3752275
  simp only [CollatzResearch.WordTrace]
  refine ⟨136856712481155987395426279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91237808320770658263617519 136856712481155987395426279)
  ·
    refine ⟨205285068721733981093139419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136856712481155987395426279 205285068721733981093139419)
    ·
      refine ⟨307927603082600971639709129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205285068721733981093139419 307927603082600971639709129)
      ·
        refine ⟨230945702311950728729781847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307927603082600971639709129 230945702311950728729781847)
        ·
          refine ⟨346418553467926093094672771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230945702311950728729781847 346418553467926093094672771)
          ·
            refine ⟨519627830201889139642009157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346418553467926093094672771 519627830201889139642009157)
            ·
              refine ⟨97430218162854213682876717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 519627830201889139642009157 97430218162854213682876717)
              ·
                refine ⟨36536331811070330131078769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97430218162854213682876717 36536331811070330131078769)
                ·
                  refine ⟨27402248858302747598309077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36536331811070330131078769 27402248858302747598309077)
                  ·
                    refine ⟨642240207616470646835369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27402248858302747598309077 642240207616470646835369)
                    ·
                      rfl

theorem cell23_3752275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 7].length) (baseStart_3752275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752275 prefixEnd_3752275 := by exact prefixLift 3752275
  have htrace : WordTrace (prefixWord ++ tailWord_3752275) baseStart_3752275 baseEnd_3752275 := by
    simpa [prefixWord, tailWord_3752275, baseEnd_3752275] using wordTrace_append hprefix tailTrace_3752275
  have hstable : (prefixWord ++ tailWord_3752275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752275).length < 2 ^ (prefixWord ++ tailWord_3752275).sum := by decide
  have hdescent : baseEnd_3752275 < baseStart_3752275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752350 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3752350 : Nat := 118140960795 + 3752350 * 2 ^ 59
def prefixEnd_3752350 : Nat := 4983230072969 + 3 ^ 40 * 3752350 * 2
def baseEnd_3752350 : Nat := 1926759133898499147068263

theorem tailTrace_3752350 : CollatzResearch.WordTrace tailWord_3752350 prefixEnd_3752350 1926759133898499147068263 := by
  unfold tailWord_3752350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17107430994485534400550813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91239631970589516802937669 17107430994485534400550813)
  ·
    refine ⟨6415286622932075400206555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17107430994485534400550813 6415286622932075400206555)
    ·
      refine ⟨9622929934398113100309833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6415286622932075400206555 9622929934398113100309833)
      ·
        refine ⟨7217197450798584825232375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9622929934398113100309833 7217197450798584825232375)
        ·
          refine ⟨10825796176197877237848563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217197450798584825232375 10825796176197877237848563)
          ·
            refine ⟨16238694264296815856772845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10825796176197877237848563 16238694264296815856772845)
            ·
              refine ⟨6089510349111305946289817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16238694264296815856772845 6089510349111305946289817)
              ·
                refine ⟨4567132761833479459717363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6089510349111305946289817 4567132761833479459717363)
                ·
                  refine ⟨6850699142750219189576045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567132761833479459717363 6850699142750219189576045)
                  ·
                    refine ⟨2569012178531332196091017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6850699142750219189576045 2569012178531332196091017)
                    ·
                      refine ⟨1926759133898499147068263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569012178531332196091017 1926759133898499147068263)
                      ·
                        rfl

theorem cell23_3752350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3752350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752350 prefixEnd_3752350 := by exact prefixLift 3752350
  have htrace : WordTrace (prefixWord ++ tailWord_3752350) baseStart_3752350 baseEnd_3752350 := by
    simpa [prefixWord, tailWord_3752350, baseEnd_3752350] using wordTrace_append hprefix tailTrace_3752350
  have hstable : (prefixWord ++ tailWord_3752350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752350).length < 2 ^ (prefixWord ++ tailWord_3752350).sum := by decide
  have hdescent : baseEnd_3752350 < baseStart_3752350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752380 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3752380 : Nat := 118140960795 + 3752380 * 2 ^ 59
def prefixEnd_3752380 : Nat := 4983230072969 + 3 ^ 40 * 3752380 * 2
def baseEnd_3752380 : Nat := 1926774538318134029693125

theorem tailTrace_3752380 : CollatzResearch.WordTrace tailWord_3752380 prefixEnd_3752380 1926774538318134029693125 := by
  unfold tailWord_3752380
  simp only [CollatzResearch.WordTrace]
  refine ⟨68430271072887795163999297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91240361430517060218665729 68430271072887795163999297)
  ·
    refine ⟨51322703304665846372999473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68430271072887795163999297 51322703304665846372999473)
    ·
      refine ⟨38492027478499384779749605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51322703304665846372999473 38492027478499384779749605)
      ·
        refine ⟨7217255152218634646203051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38492027478499384779749605 7217255152218634646203051)
        ·
          refine ⟨10825882728327951969304577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217255152218634646203051 10825882728327951969304577)
          ·
            refine ⟨8119412046245963976978433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10825882728327951969304577 8119412046245963976978433)
            ·
              refine ⟨6089559034684472982733825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8119412046245963976978433 6089559034684472982733825)
              ·
                refine ⟨4567169276013354737050369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6089559034684472982733825 4567169276013354737050369)
                ·
                  refine ⟨3425376957010016052787777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4567169276013354737050369 3425376957010016052787777)
                  ·
                    refine ⟨2569032717757512039590833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3425376957010016052787777 2569032717757512039590833)
                    ·
                      refine ⟨1926774538318134029693125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569032717757512039590833 1926774538318134029693125)
                      ·
                        rfl

theorem cell23_3752380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3752380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752380 prefixEnd_3752380 := by exact prefixLift 3752380
  have htrace : WordTrace (prefixWord ++ tailWord_3752380) baseStart_3752380 baseEnd_3752380 := by
    simpa [prefixWord, tailWord_3752380, baseEnd_3752380] using wordTrace_append hprefix tailTrace_3752380
  have hstable : (prefixWord ++ tailWord_3752380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752380).length < 2 ^ (prefixWord ++ tailWord_3752380).sum := by decide
  have hdescent : baseEnd_3752380 < baseStart_3752380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752396 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3752396 : Nat := 118140960795 + 3752396 * 2 ^ 59
def prefixEnd_3752396 : Nat := 4983230072969 + 3 ^ 40 * 3752396 * 2
def baseEnd_3752396 : Nat := 1926782754008605967093051

theorem tailTrace_3752396 : CollatzResearch.WordTrace tailWord_3752396 prefixEnd_3752396 1926782754008605967093051 := by
  unfold tailWord_3752396
  simp only [CollatzResearch.WordTrace]
  refine ⟨68430562856858812530290521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91240750475811750040387361 68430562856858812530290521)
  ·
    refine ⟨51322922142644109397717891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68430562856858812530290521 51322922142644109397717891)
    ·
      refine ⟨76984383213966164096576837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51322922142644109397717891 76984383213966164096576837)
      ·
        refine ⟨14434571852618655768108157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76984383213966164096576837 14434571852618655768108157)
        ·
          refine ⟨5412964444731995913040559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14434571852618655768108157 5412964444731995913040559)
          ·
            refine ⟨8119446667097993869560839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412964444731995913040559 8119446667097993869560839)
            ·
              refine ⟨12179170000646990804341259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8119446667097993869560839 12179170000646990804341259)
              ·
                refine ⟨18268755000970486206511889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12179170000646990804341259 18268755000970486206511889)
                ·
                  refine ⟨13701566250727864654883917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18268755000970486206511889 13701566250727864654883917)
                  ·
                    refine ⟨5138087344022949245581469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13701566250727864654883917 5138087344022949245581469)
                    ·
                      refine ⟨1926782754008605967093051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5138087344022949245581469 1926782754008605967093051)
                      ·
                        rfl

theorem cell23_3752396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3752396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752396 prefixEnd_3752396 := by exact prefixLift 3752396
  have htrace : WordTrace (prefixWord ++ tailWord_3752396) baseStart_3752396 baseEnd_3752396 := by
    simpa [prefixWord, tailWord_3752396, baseEnd_3752396] using wordTrace_append hprefix tailTrace_3752396
  have hstable : (prefixWord ++ tailWord_3752396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752396).length < 2 ^ (prefixWord ++ tailWord_3752396).sum := by decide
  have hdescent : baseEnd_3752396 < baseStart_3752396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752432 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_3752432 : Nat := 118140960795 + 3752432 * 2 ^ 59
def prefixEnd_3752432 : Nat := 4983230072969 + 3 ^ 40 * 3752432 * 2
def baseEnd_3752432 : Nat := 1926801239312167826242885

theorem tailTrace_3752432 : CollatzResearch.WordTrace tailWord_3752432 prefixEnd_3752432 1926801239312167826242885 := by
  unfold tailWord_3752432
  simp only [CollatzResearch.WordTrace]
  refine ⟨68431219370793601604445775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91241625827724802139261033 68431219370793601604445775)
  ·
    refine ⟨102646829056190402406668663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68431219370793601604445775 102646829056190402406668663)
    ·
      refine ⟨153970243584285603610002995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102646829056190402406668663 153970243584285603610002995)
      ·
        refine ⟨230955365376428405415004493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153970243584285603610002995 230955365376428405415004493)
        ·
          refine ⟨86608262016160652030626685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230955365376428405415004493 86608262016160652030626685)
          ·
            refine ⟨32478098256060244511485007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86608262016160652030626685 32478098256060244511485007)
            ·
              refine ⟨48717147384090366767227511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32478098256060244511485007 48717147384090366767227511)
              ·
                refine ⟨73075721076135550150841267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48717147384090366767227511 73075721076135550150841267)
                ·
                  refine ⟨109613581614203325226261901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73075721076135550150841267 109613581614203325226261901)
                  ·
                    refine ⟨41105093105326246959848213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109613581614203325226261901 41105093105326246959848213)
                    ·
                      refine ⟨1926801239312167826242885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41105093105326246959848213 1926801239312167826242885)
                      ·
                        rfl

theorem cell23_3752432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_3752432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752432 prefixEnd_3752432 := by exact prefixLift 3752432
  have htrace : WordTrace (prefixWord ++ tailWord_3752432) baseStart_3752432 baseEnd_3752432 := by
    simpa [prefixWord, tailWord_3752432, baseEnd_3752432] using wordTrace_append hprefix tailTrace_3752432
  have hstable : (prefixWord ++ tailWord_3752432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752432).length < 2 ^ (prefixWord ++ tailWord_3752432).sum := by decide
  have hdescent : baseEnd_3752432 < baseStart_3752432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752469 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_3752469 : Nat := 118140960795 + 3752469 * 2 ^ 59
def prefixEnd_3752469 : Nat := 4983230072969 + 3 ^ 40 * 3752469 * 2
def baseEnd_3752469 : Nat := 1926820238096384181480215

theorem tailTrace_3752469 : CollatzResearch.WordTrace tailWord_3752469 prefixEnd_3752469 1926820238096384181480215 := by
  unfold tailWord_3752469
  simp only [CollatzResearch.WordTrace]
  refine ⟨136863788242453158527988461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91242525494968772351992307 136863788242453158527988461)
  ·
    refine ⟨51323920590919934447995673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136863788242453158527988461 51323920590919934447995673)
    ·
      refine ⟨38492940443189950835996755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51323920590919934447995673 38492940443189950835996755)
      ·
        refine ⟨57739410664784926253995133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38492940443189950835996755 57739410664784926253995133)
        ·
          refine ⟨21652278999294347345248175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57739410664784926253995133 21652278999294347345248175)
          ·
            refine ⟨32478418498941521017872263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21652278999294347345248175 32478418498941521017872263)
            ·
              refine ⟨48717627748412281526808395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32478418498941521017872263 48717627748412281526808395)
              ·
                refine ⟨73076441622618422290212593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48717627748412281526808395 73076441622618422290212593)
                ·
                  refine ⟨54807331216963816717659445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73076441622618422290212593 54807331216963816717659445)
                  ·
                    refine ⟨5138187301590357817280573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54807331216963816717659445 5138187301590357817280573)
                    ·
                      refine ⟨1926820238096384181480215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5138187301590357817280573 1926820238096384181480215)
                      ·
                        rfl

theorem cell23_3752469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_3752469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752469 prefixEnd_3752469 := by exact prefixLift 3752469
  have htrace : WordTrace (prefixWord ++ tailWord_3752469) baseStart_3752469 baseEnd_3752469 := by
    simpa [prefixWord, tailWord_3752469, baseEnd_3752469] using wordTrace_append hprefix tailTrace_3752469
  have hstable : (prefixWord ++ tailWord_3752469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752469).length < 2 ^ (prefixWord ++ tailWord_3752469).sum := by decide
  have hdescent : baseEnd_3752469 < baseStart_3752469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752496 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 4, 3, 2]
def baseStart_3752496 : Nat := 118140960795 + 3752496 * 2 ^ 59
def prefixEnd_3752496 : Nat := 4983230072969 + 3 ^ 40 * 3752496 * 2
def baseEnd_3752496 : Nat := 1926834102074055575842591

theorem tailTrace_3752496 : CollatzResearch.WordTrace tailWord_3752496 prefixEnd_3752496 1926834102074055575842591 := by
  unfold tailWord_3752496
  simp only [CollatzResearch.WordTrace]
  refine ⟨68432386506677671069610671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91243182008903561426147561 68432386506677671069610671)
  ·
    refine ⟨102648579760016506604416007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68432386506677671069610671 102648579760016506604416007)
    ·
      refine ⟨153972869640024759906624011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102648579760016506604416007 153972869640024759906624011)
      ·
        refine ⟨230959304460037139859936017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153972869640024759906624011 230959304460037139859936017)
        ·
          refine ⟨173219478345027854894952013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230959304460037139859936017 173219478345027854894952013)
          ·
            refine ⟨64957304379385445585607005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173219478345027854894952013 64957304379385445585607005)
            ·
              refine ⟨24358989142269542094602627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64957304379385445585607005 24358989142269542094602627)
              ·
                refine ⟨36538483713404313141903941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24358989142269542094602627 36538483713404313141903941)
                ·
                  refine ⟨6850965696263308714106989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36538483713404313141903941 6850965696263308714106989)
                  ·
                    refine ⟨2569112136098740767790121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6850965696263308714106989 2569112136098740767790121)
                    ·
                      refine ⟨1926834102074055575842591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569112136098740767790121 1926834102074055575842591)
                      ·
                        rfl

theorem cell23_3752496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 3, 2].length) (baseStart_3752496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752496 prefixEnd_3752496 := by exact prefixLift 3752496
  have htrace : WordTrace (prefixWord ++ tailWord_3752496) baseStart_3752496 baseEnd_3752496 := by
    simpa [prefixWord, tailWord_3752496, baseEnd_3752496] using wordTrace_append hprefix tailTrace_3752496
  have hstable : (prefixWord ++ tailWord_3752496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752496).length < 2 ^ (prefixWord ++ tailWord_3752496).sum := by decide
  have hdescent : baseEnd_3752496 < baseStart_3752496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752526 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_3752526 : Nat := 118140960795 + 3752526 * 2 ^ 59
def prefixEnd_3752526 : Nat := 4983230072969 + 3 ^ 40 * 3752526 * 2
def baseEnd_3752526 : Nat := 1926849506493690458467453

theorem tailTrace_3752526 : CollatzResearch.WordTrace tailWord_3752526 prefixEnd_3752526 1926849506493690458467453 := by
  unfold tailWord_3752526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17108233400405832157851679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91243911468831104841875621 17108233400405832157851679)
  ·
    refine ⟨25662350100608748236777519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17108233400405832157851679 25662350100608748236777519)
    ·
      refine ⟨38493525150913122355166279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25662350100608748236777519 38493525150913122355166279)
      ·
        refine ⟨57740287726369683532749419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38493525150913122355166279 57740287726369683532749419)
        ·
          refine ⟨86610431589554525299124129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57740287726369683532749419 86610431589554525299124129)
          ·
            refine ⟨64957823692165893974343097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86610431589554525299124129 64957823692165893974343097)
            ·
              refine ⟨48718367769124420480757323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64957823692165893974343097 48718367769124420480757323)
              ·
                refine ⟨73077551653686630721135985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48718367769124420480757323 73077551653686630721135985)
                ·
                  refine ⟨54808163740264973040851989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73077551653686630721135985 54808163740264973040851989)
                  ·
                    refine ⟨2569132675324920611289937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54808163740264973040851989 2569132675324920611289937)
                    ·
                      refine ⟨1926849506493690458467453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569132675324920611289937 1926849506493690458467453)
                      ·
                        rfl

theorem cell23_3752526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_3752526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752526 prefixEnd_3752526 := by exact prefixLift 3752526
  have htrace : WordTrace (prefixWord ++ tailWord_3752526) baseStart_3752526 baseEnd_3752526 := by
    simpa [prefixWord, tailWord_3752526, baseEnd_3752526] using wordTrace_append hprefix tailTrace_3752526
  have hstable : (prefixWord ++ tailWord_3752526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752526).length < 2 ^ (prefixWord ++ tailWord_3752526).sum := by decide
  have hdescent : baseEnd_3752526 < baseStart_3752526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752540 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3752540 : Nat := 118140960795 + 3752540 * 2 ^ 59
def prefixEnd_3752540 : Nat := 4983230072969 + 3 ^ 40 * 3752540 * 2
def baseEnd_3752540 : Nat := 642285565074284467897463

theorem tailTrace_3752540 : CollatzResearch.WordTrace tailWord_3752540 prefixEnd_3752540 642285565074284467897463 := by
  unfold tailWord_3752540
  simp only [CollatzResearch.WordTrace]
  refine ⟨68433188912597968826911537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91244251883463958435882049 68433188912597968826911537)
  ·
    refine ⟨51324891684448476620183653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68433188912597968826911537 51324891684448476620183653)
    ·
      refine ⟨9623417190834089366284435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51324891684448476620183653 9623417190834089366284435)
      ·
        refine ⟨14435125786251134049426653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9623417190834089366284435 14435125786251134049426653)
        ·
          refine ⟨5413172169844175268534995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14435125786251134049426653 5413172169844175268534995)
          ·
            refine ⟨8119758254766262902802493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413172169844175268534995 8119758254766262902802493)
            ·
              refine ⟨3044909345537348588550935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8119758254766262902802493 3044909345537348588550935)
              ·
                refine ⟨4567364018306022882826403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044909345537348588550935 4567364018306022882826403)
                ·
                  refine ⟨6851046027459034324239605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567364018306022882826403 6851046027459034324239605)
                  ·
                    refine ⟨642285565074284467897463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6851046027459034324239605 642285565074284467897463)
                    ·
                      rfl

theorem cell23_3752540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3752540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752540 prefixEnd_3752540 := by exact prefixLift 3752540
  have htrace : WordTrace (prefixWord ++ tailWord_3752540) baseStart_3752540 baseEnd_3752540 := by
    simpa [prefixWord, tailWord_3752540, baseEnd_3752540] using wordTrace_append hprefix tailTrace_3752540
  have hstable : (prefixWord ++ tailWord_3752540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752540).length < 2 ^ (prefixWord ++ tailWord_3752540).sum := by decide
  have hdescent : baseEnd_3752540 < baseStart_3752540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752549 : List Nat := [1, 3, 1, 3, 4, 11]
def baseStart_3752549 : Nat := 118140960795 + 3752549 * 2 ^ 59
def prefixEnd_3752549 : Nat := 4983230072969 + 3 ^ 40 * 3752549 * 2
def baseEnd_3752549 : Nat := 7929470438472196989629

theorem tailTrace_3752549 : CollatzResearch.WordTrace tailWord_3752549 prefixEnd_3752549 7929470438472196989629 := by
  unfold tailWord_3752549
  simp only [CollatzResearch.WordTrace]
  refine ⟨136866706082163332190900701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91244470721442221460600467 136866706082163332190900701)
  ·
    refine ⟨51325014780811249571587763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136866706082163332190900701 51325014780811249571587763)
    ·
      refine ⟨76987522171216874357381645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51325014780811249571587763 76987522171216874357381645)
      ·
        refine ⟨28870320814206327884018117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76987522171216874357381645 28870320814206327884018117)
        ·
          refine ⟨5413185152663686478253397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28870320814206327884018117 5413185152663686478253397)
          ·
            refine ⟨7929470438472196989629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5413185152663686478253397 7929470438472196989629)
            ·
              rfl

theorem cell23_3752549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 11].length) (baseStart_3752549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752549 prefixEnd_3752549 := by exact prefixLift 3752549
  have htrace : WordTrace (prefixWord ++ tailWord_3752549) baseStart_3752549 baseEnd_3752549 := by
    simpa [prefixWord, tailWord_3752549, baseEnd_3752549] using wordTrace_append hprefix tailTrace_3752549
  have hstable : (prefixWord ++ tailWord_3752549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752549).length < 2 ^ (prefixWord ++ tailWord_3752549).sum := by decide
  have hdescent : baseEnd_3752549 < baseStart_3752549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752573 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_3752573 : Nat := 118140960795 + 3752573 * 2 ^ 59
def prefixEnd_3752573 : Nat := 4983230072969 + 3 ^ 40 * 3752573 * 2
def baseEnd_3752573 : Nat := 1926873640084451774579737

theorem tailTrace_3752573 : CollatzResearch.WordTrace tailWord_3752573 prefixEnd_3752573 1926873640084451774579737 := by
  unfold tailWord_3752573
  simp only [CollatzResearch.WordTrace]
  refine ⟨136867581434076384289774373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91245054289384256193182915 136867581434076384289774373)
  ·
    refine ⟨25662671518889322054332695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136867581434076384289774373 25662671518889322054332695)
    ·
      refine ⟨38494007278333983081499043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25662671518889322054332695 38494007278333983081499043)
      ·
        refine ⟨57741010917500974622248565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38494007278333983081499043 57741010917500974622248565)
        ·
          refine ⟨5413219773515716370835803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57741010917500974622248565 5413219773515716370835803)
          ·
            refine ⟨8119829660273574556253705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413219773515716370835803 8119829660273574556253705)
            ·
              refine ⟨6089872245205180917190279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8119829660273574556253705 6089872245205180917190279)
              ·
                refine ⟨9134808367807771375785419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089872245205180917190279 9134808367807771375785419)
                ·
                  refine ⟨13702212551711657063678129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9134808367807771375785419 13702212551711657063678129)
                  ·
                    refine ⟨10276659413783742797758597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13702212551711657063678129 10276659413783742797758597)
                    ·
                      refine ⟨1926873640084451774579737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10276659413783742797758597 1926873640084451774579737)
                      ·
                        rfl

theorem cell23_3752573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_3752573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752573 prefixEnd_3752573 := by exact prefixLift 3752573
  have htrace : WordTrace (prefixWord ++ tailWord_3752573) baseStart_3752573 baseEnd_3752573 := by
    simpa [prefixWord, tailWord_3752573, baseEnd_3752573] using wordTrace_append hprefix tailTrace_3752573
  have hstable : (prefixWord ++ tailWord_3752573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752573).length < 2 ^ (prefixWord ++ tailWord_3752573).sum := by decide
  have hdescent : baseEnd_3752573 < baseStart_3752573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752576 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 3]
def baseStart_3752576 : Nat := 118140960795 + 3752576 * 2 ^ 59
def prefixEnd_3752576 : Nat := 4983230072969 + 3 ^ 40 * 3752576 * 2
def baseEnd_3752576 : Nat := 1926875180526415262842223

theorem tailTrace_3752576 : CollatzResearch.WordTrace tailWord_3752576 prefixEnd_3752576 1926875180526415262842223 := by
  unfold tailWord_3752576
  simp only [CollatzResearch.WordTrace]
  refine ⟨68433845426532757901066791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91245127235377010534755721 68433845426532757901066791)
  ·
    refine ⟨102650768139799136851600187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68433845426532757901066791 102650768139799136851600187)
    ·
      refine ⟨153976152209698705277400281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102650768139799136851600187 153976152209698705277400281)
      ·
        refine ⟨115482114157274028958050211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153976152209698705277400281 115482114157274028958050211)
        ·
          refine ⟨173223171235911043437075317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115482114157274028958050211 173223171235911043437075317)
          ·
            refine ⟨16239672303366660322225811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173223171235911043437075317 16239672303366660322225811)
            ·
              refine ⟨24359508455049990483338717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16239672303366660322225811 24359508455049990483338717)
              ·
                refine ⟨9134815670643746431252019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24359508455049990483338717 9134815670643746431252019)
                ·
                  refine ⟨13702223505965619646878029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9134815670643746431252019 13702223505965619646878029)
                  ·
                    refine ⟨5138333814737107367579261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13702223505965619646878029 5138333814737107367579261)
                    ·
                      refine ⟨1926875180526415262842223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5138333814737107367579261 1926875180526415262842223)
                      ·
                        rfl

theorem cell23_3752576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_3752576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752576 prefixEnd_3752576 := by exact prefixLift 3752576
  have htrace : WordTrace (prefixWord ++ tailWord_3752576) baseStart_3752576 baseEnd_3752576 := by
    simpa [prefixWord, tailWord_3752576, baseEnd_3752576] using wordTrace_append hprefix tailTrace_3752576
  have hstable : (prefixWord ++ tailWord_3752576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752576).length < 2 ^ (prefixWord ++ tailWord_3752576).sum := by decide
  have hdescent : baseEnd_3752576 < baseStart_3752576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752594 : List Nat := [3, 2, 3, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_3752594 : Nat := 118140960795 + 3752594 * 2 ^ 59
def prefixEnd_3752594 : Nat := 4983230072969 + 3 ^ 40 * 3752594 * 2
def baseEnd_3752594 : Nat := 1926884423178196192417141

theorem tailTrace_3752594 : CollatzResearch.WordTrace tailWord_3752594 prefixEnd_3752594 1926884423178196192417141 := by
  unfold tailWord_3752594
  simp only [CollatzResearch.WordTrace]
  refine ⟨34217086841750076219072209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91245564911333536584192557 34217086841750076219072209)
  ·
    refine ⟨25662815131312557164304157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34217086841750076219072209 25662815131312557164304157)
    ·
      refine ⟨9623555674242208936614059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25662815131312557164304157 9623555674242208936614059)
      ·
        refine ⟨14435333511363313404921089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9623555674242208936614059 14435333511363313404921089)
        ·
          refine ⟨10826500133522485053690817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14435333511363313404921089 10826500133522485053690817)
          ·
            refine ⟨8119875100141863790268113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10826500133522485053690817 8119875100141863790268113)
            ·
              refine ⟨6089906325106397842701085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8119875100141863790268113 6089906325106397842701085)
              ·
                refine ⟨2283714871914899191012907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6089906325106397842701085 2283714871914899191012907)
                ·
                  refine ⟨3425572307872348786519361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283714871914899191012907 3425572307872348786519361)
                  ·
                    refine ⟨2569179230904261589889521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3425572307872348786519361 2569179230904261589889521)
                    ·
                      refine ⟨1926884423178196192417141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569179230904261589889521 1926884423178196192417141)
                      ·
                        rfl

theorem cell23_3752594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_3752594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752594 prefixEnd_3752594 := by exact prefixLift 3752594
  have htrace : WordTrace (prefixWord ++ tailWord_3752594) baseStart_3752594 baseEnd_3752594 := by
    simpa [prefixWord, tailWord_3752594, baseEnd_3752594] using wordTrace_append hprefix tailTrace_3752594
  have hstable : (prefixWord ++ tailWord_3752594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752594).length < 2 ^ (prefixWord ++ tailWord_3752594).sum := by decide
  have hdescent : baseEnd_3752594 < baseStart_3752594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752636 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3752636 : Nat := 118140960795 + 3752636 * 2 ^ 59
def prefixEnd_3752636 : Nat := 4983230072969 + 3 ^ 40 * 3752636 * 2
def baseEnd_3752636 : Nat := 1926905989365685028091947

theorem tailTrace_3752636 : CollatzResearch.WordTrace tailWord_3752636 prefixEnd_3752636 1926905989365685028091947 := by
  unfold tailWord_3752636
  simp only [CollatzResearch.WordTrace]
  refine ⟨68434939616424073024658881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91246586155232097366211841 68434939616424073024658881)
  ·
    refine ⟨51326204712318054768494161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68434939616424073024658881 51326204712318054768494161)
    ·
      refine ⟨38494653534238541076370621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51326204712318054768494161 38494653534238541076370621)
      ·
        refine ⟨14435495075339452903638983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38494653534238541076370621 14435495075339452903638983)
        ·
          refine ⟨21653242613009179355458475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14435495075339452903638983 21653242613009179355458475)
          ·
            refine ⟨32479863919513769033187713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21653242613009179355458475 32479863919513769033187713)
            ·
              refine ⟨24359897939635326774890785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32479863919513769033187713 24359897939635326774890785)
              ·
                refine ⟨18269923454726495081168089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24359897939635326774890785 18269923454726495081168089)
                ·
                  refine ⟨13702442591044871310876067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18269923454726495081168089 13702442591044871310876067)
                  ·
                    refine ⟨20553663886567306966314101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13702442591044871310876067 20553663886567306966314101)
                    ·
                      refine ⟨1926905989365685028091947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20553663886567306966314101 1926905989365685028091947)
                      ·
                        rfl

theorem cell23_3752636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3752636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752636 prefixEnd_3752636 := by exact prefixLift 3752636
  have htrace : WordTrace (prefixWord ++ tailWord_3752636) baseStart_3752636 baseEnd_3752636 := by
    simpa [prefixWord, tailWord_3752636, baseEnd_3752636] using wordTrace_append hprefix tailTrace_3752636
  have hstable : (prefixWord ++ tailWord_3752636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752636).length < 2 ^ (prefixWord ++ tailWord_3752636).sum := by decide
  have hdescent : baseEnd_3752636 < baseStart_3752636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752650 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_3752650 : Nat := 118140960795 + 3752650 * 2 ^ 59
def prefixEnd_3752650 : Nat := 4983230072969 + 3 ^ 40 * 3752650 * 2
def baseEnd_3752650 : Nat := 1926913178094847973316883

theorem tailTrace_3752650 : CollatzResearch.WordTrace tailWord_3752650 prefixEnd_3752650 1926913178094847973316883 := by
  unfold tailWord_3752650
  simp only [CollatzResearch.WordTrace]
  refine ⟨34217597463699356610081851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91246926569864950960218269 34217597463699356610081851)
  ·
    refine ⟨51326396195549034915122777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34217597463699356610081851 51326396195549034915122777)
    ·
      refine ⟨38494797146661776186342083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51326396195549034915122777 38494797146661776186342083)
      ·
        refine ⟨57742195719992664279513125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38494797146661776186342083 57742195719992664279513125)
        ·
          refine ⟨10826661697498624552408711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57742195719992664279513125 10826661697498624552408711)
          ·
            refine ⟨16239992546247936828613067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10826661697498624552408711 16239992546247936828613067)
            ·
              refine ⟨24359988819371905242919601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16239992546247936828613067 24359988819371905242919601)
              ·
                refine ⟨18269991614528928932189701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24359988819371905242919601 18269991614528928932189701)
                ·
                  refine ⟨3425623427724174174785569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18269991614528928932189701 3425623427724174174785569)
                  ·
                    refine ⟨2569217570793130631089177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3425623427724174174785569 2569217570793130631089177)
                    ·
                      refine ⟨1926913178094847973316883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569217570793130631089177 1926913178094847973316883)
                      ·
                        rfl

theorem cell23_3752650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_3752650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752650 prefixEnd_3752650 := by exact prefixLift 3752650
  have htrace : WordTrace (prefixWord ++ tailWord_3752650) baseStart_3752650 baseEnd_3752650 := by
    simpa [prefixWord, tailWord_3752650, baseEnd_3752650] using wordTrace_append hprefix tailTrace_3752650
  have hstable : (prefixWord ++ tailWord_3752650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752650).length < 2 ^ (prefixWord ++ tailWord_3752650).sum := by decide
  have hdescent : baseEnd_3752650 < baseStart_3752650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752673 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 7]
def baseStart_3752673 : Nat := 118140960795 + 3752673 * 2 ^ 59
def prefixEnd_3752673 : Nat := 4983230072969 + 3 ^ 40 * 3752673 * 2
def baseEnd_3752673 : Nat := 214102776461100153703253

theorem tailTrace_3752673 : CollatzResearch.WordTrace tailWord_3752673 prefixEnd_3752673 214102776461100153703253 := by
  unfold tailWord_3752673
  simp only [CollatzResearch.WordTrace]
  refine ⟨136871228733714101368414673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91247485822476067578943115 136871228733714101368414673)
  ·
    refine ⟨102653421550285576026311005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136871228733714101368414673 102653421550285576026311005)
    ·
      refine ⟨38495033081357091009866627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102653421550285576026311005 38495033081357091009866627)
      ·
        refine ⟨57742549622035636514799941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38495033081357091009866627 57742549622035636514799941)
        ·
          refine ⟨10826728054131681846524989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57742549622035636514799941 10826728054131681846524989)
          ·
            refine ⟨4060023020299380692446871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10826728054131681846524989 4060023020299380692446871)
            ·
              refine ⟨6090034530449071038670307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060023020299380692446871 6090034530449071038670307)
              ·
                refine ⟨9135051795673606558005461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090034530449071038670307 9135051795673606558005461)
                ·
                  refine ⟨214102776461100153703253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9135051795673606558005461 214102776461100153703253)
                  ·
                    rfl

theorem cell23_3752673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 7].length) (baseStart_3752673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752673 prefixEnd_3752673 := by exact prefixLift 3752673
  have htrace : WordTrace (prefixWord ++ tailWord_3752673) baseStart_3752673 baseEnd_3752673 := by
    simpa [prefixWord, tailWord_3752673, baseEnd_3752673] using wordTrace_append hprefix tailTrace_3752673
  have hstable : (prefixWord ++ tailWord_3752673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752673).length < 2 ^ (prefixWord ++ tailWord_3752673).sum := by decide
  have hdescent : baseEnd_3752673 < baseStart_3752673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752723 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 2, 4, 2]
def baseStart_3752723 : Nat := 118140960795 + 3752723 * 2 ^ 59
def prefixEnd_3752723 : Nat := 4983230072969 + 3 ^ 40 * 3752723 * 2
def baseEnd_3752723 : Nat := 1926950662182626187704047

theorem tailTrace_3752723 : CollatzResearch.WordTrace tailWord_3752723 prefixEnd_3752723 1926950662182626187704047 := by
  unfold tailWord_3752723
  simp only [CollatzResearch.WordTrace]
  refine ⟨136873052383532959907734823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91248701589021973271823215 136873052383532959907734823)
  ·
    refine ⟨205309578575299439861602235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136873052383532959907734823 205309578575299439861602235)
    ·
      refine ⟨307964367862949159792403353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205309578575299439861602235 307964367862949159792403353)
      ·
        refine ⟨230973275897211869844302515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307964367862949159792403353 230973275897211869844302515)
        ·
          refine ⟨346459913845817804766453773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230973275897211869844302515 346459913845817804766453773)
          ·
            refine ⟨129922467692181676787420165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346459913845817804766453773 129922467692181676787420165)
            ·
              refine ⟨24360462692284064397641281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129922467692181676787420165 24360462692284064397641281)
              ·
                refine ⟨18270347019213048298230961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24360462692284064397641281 18270347019213048298230961)
                ·
                  refine ⟨13702760264409786223673221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18270347019213048298230961 13702760264409786223673221)
                  ·
                    refine ⟨2569267549576834916938729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13702760264409786223673221 2569267549576834916938729)
                    ·
                      refine ⟨1926950662182626187704047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569267549576834916938729 1926950662182626187704047)
                      ·
                        rfl

theorem cell23_3752723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 4, 2].length) (baseStart_3752723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752723 prefixEnd_3752723 := by exact prefixLift 3752723
  have htrace : WordTrace (prefixWord ++ tailWord_3752723) baseStart_3752723 baseEnd_3752723 := by
    simpa [prefixWord, tailWord_3752723, baseEnd_3752723] using wordTrace_append hprefix tailTrace_3752723
  have hstable : (prefixWord ++ tailWord_3752723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752723).length < 2 ^ (prefixWord ++ tailWord_3752723).sum := by decide
  have hdescent : baseEnd_3752723 < baseStart_3752723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752750 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3752750 : Nat := 118140960795 + 3752750 * 2 ^ 59
def prefixEnd_3752750 : Nat := 4983230072969 + 3 ^ 40 * 3752750 * 2
def baseEnd_3752750 : Nat := 642321508720099194022141

theorem tailTrace_3752750 : CollatzResearch.WordTrace tailWord_3752750 prefixEnd_3752750 642321508720099194022141 := by
  unfold tailWord_3752750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17109254644304392939870963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91249358102956762345978469 17109254644304392939870963)
  ·
    refine ⟨25663881966456589409806445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17109254644304392939870963 25663881966456589409806445)
    ·
      refine ⟨9623955737421221028677417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25663881966456589409806445 9623955737421221028677417)
      ·
        refine ⟨7217966803065915771508063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9623955737421221028677417 7217966803065915771508063)
        ·
          refine ⟨10826950204598873657262095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217966803065915771508063 10826950204598873657262095)
          ·
            refine ⟨16240425306898310485893143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10826950204598873657262095 16240425306898310485893143)
            ·
              refine ⟨24360637960347465728839715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16240425306898310485893143 24360637960347465728839715)
              ·
                refine ⟨36540956940521198593259573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24360637960347465728839715 36540956940521198593259573)
                ·
                  refine ⟨3425714713173862368118085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36540956940521198593259573 3425714713173862368118085)
                  ·
                    refine ⟨642321508720099194022141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3425714713173862368118085 642321508720099194022141)
                    ·
                      rfl

theorem cell23_3752750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3752750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752750 prefixEnd_3752750 := by exact prefixLift 3752750
  have htrace : WordTrace (prefixWord ++ tailWord_3752750) baseStart_3752750 baseEnd_3752750 := by
    simpa [prefixWord, tailWord_3752750, baseEnd_3752750] using wordTrace_append hprefix tailTrace_3752750
  have hstable : (prefixWord ++ tailWord_3752750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752750).length < 2 ^ (prefixWord ++ tailWord_3752750).sum := by decide
  have hdescent : baseEnd_3752750 < baseStart_3752750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752767 : List Nat := [1, 1, 2, 2, 5, 2, 2, 3, 1, 4]
def baseStart_3752767 : Nat := 118140960795 + 3752767 * 2 ^ 59
def prefixEnd_3752767 : Nat := 4983230072969 + 3 ^ 40 * 3752767 * 2
def baseEnd_3752767 : Nat := 642324418443808005184615

theorem tailTrace_3752767 : CollatzResearch.WordTrace tailWord_3752767 prefixEnd_3752767 642324418443808005184615 := by
  unfold tailWord_3752767
  simp only [CollatzResearch.WordTrace]
  refine ⟨136874657195373555422336555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91249771463582370281557703 136874657195373555422336555)
  ·
    refine ⟨205311985793060333133504833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136874657195373555422336555 205311985793060333133504833)
    ·
      refine ⟨153983989344795249850128625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205311985793060333133504833 153983989344795249850128625)
      ·
        refine ⟨115487992008596437387596469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153983989344795249850128625 115487992008596437387596469)
        ·
          refine ⟨10826999250805916005087169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115487992008596437387596469 10826999250805916005087169)
          ·
            refine ⟨8120249438104437003815377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10826999250805916005087169 8120249438104437003815377)
            ·
              refine ⟨6090187078578327752861533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120249438104437003815377 6090187078578327752861533)
              ·
                refine ⟨2283820154466872907323075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6090187078578327752861533 2283820154466872907323075)
                ·
                  refine ⟨3425730231700309360984613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283820154466872907323075 3425730231700309360984613)
                  ·
                    refine ⟨642324418443808005184615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3425730231700309360984613 642324418443808005184615)
                    ·
                      rfl

theorem cell23_3752767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 4].length) (baseStart_3752767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752767 prefixEnd_3752767 := by exact prefixLift 3752767
  have htrace : WordTrace (prefixWord ++ tailWord_3752767) baseStart_3752767 baseEnd_3752767 := by
    simpa [prefixWord, tailWord_3752767, baseEnd_3752767] using wordTrace_append hprefix tailTrace_3752767
  have hstable : (prefixWord ++ tailWord_3752767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752767).length < 2 ^ (prefixWord ++ tailWord_3752767).sum := by decide
  have hdescent : baseEnd_3752767 < baseStart_3752767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752780 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 6]
def baseStart_3752780 : Nat := 118140960795 + 3752780 * 2 ^ 59
def prefixEnd_3752780 : Nat := 4983230072969 + 3 ^ 40 * 3752780 * 2
def baseEnd_3752780 : Nat := 214108881175548051632365

theorem tailTrace_3752780 : CollatzResearch.WordTrace tailWord_3752780 prefixEnd_3752780 214108881175548051632365 := by
  unfold tailWord_3752780
  simp only [CollatzResearch.WordTrace]
  refine ⟨68437565672163229321279897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91250087562884305761706529 68437565672163229321279897)
  ·
    refine ⟨51328174254122421990959923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68437565672163229321279897 51328174254122421990959923)
    ·
      refine ⟨76992261381183632986439885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51328174254122421990959923 76992261381183632986439885)
      ·
        refine ⟨28872098017943862369914957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76992261381183632986439885 28872098017943862369914957)
        ·
          refine ⟨10827036756728948388718109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28872098017943862369914957 10827036756728948388718109)
          ·
            refine ⟨4060138783773355645769291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10827036756728948388718109 4060138783773355645769291)
            ·
              refine ⟨6090208175660033468653937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060138783773355645769291 6090208175660033468653937)
              ·
                refine ⟨4567656131745025101490453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6090208175660033468653937 4567656131745025101490453)
                ·
                  refine ⟨214108881175548051632365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4567656131745025101490453 214108881175548051632365)
                  ·
                    rfl

theorem cell23_3752780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_3752780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752780 prefixEnd_3752780 := by exact prefixLift 3752780
  have htrace : WordTrace (prefixWord ++ tailWord_3752780) baseStart_3752780 baseEnd_3752780 := by
    simpa [prefixWord, tailWord_3752780, baseEnd_3752780] using wordTrace_append hprefix tailTrace_3752780
  have hstable : (prefixWord ++ tailWord_3752780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752780).length < 2 ^ (prefixWord ++ tailWord_3752780).sum := by decide
  have hdescent : baseEnd_3752780 < baseStart_3752780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752840 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 4, 4]
def baseStart_3752840 : Nat := 118140960795 + 3752840 * 2 ^ 59
def prefixEnd_3752840 : Nat := 4983230072969 + 3 ^ 40 * 3752840 * 2
def baseEnd_3752840 : Nat := 642336913139734076647003

theorem tailTrace_3752840 : CollatzResearch.WordTrace tailWord_3752840 prefixEnd_3752840 642336913139734076647003 := by
  unfold tailWord_3752840
  simp only [CollatzResearch.WordTrace]
  refine ⟨68438659862054544444871987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91251546482739392593162649 68438659862054544444871987)
  ·
    refine ⟨102657989793081816667307981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68438659862054544444871987 102657989793081816667307981)
    ·
      refine ⟨38496746172405681250240493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102657989793081816667307981 38496746172405681250240493)
      ·
        refine ⟨14436279814652130468840185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38496746172405681250240493 14436279814652130468840185)
        ·
          refine ⟨10827209860989097851630139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14436279814652130468840185 10827209860989097851630139)
          ·
            refine ⟨16240814791483646777445209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10827209860989097851630139 16240814791483646777445209)
            ·
              refine ⟨12180611093612735083083907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16240814791483646777445209 12180611093612735083083907)
              ·
                refine ⟨18270916640419102624625861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12180611093612735083083907 18270916640419102624625861)
                ·
                  refine ⟨3425796870078581742117349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18270916640419102624625861 3425796870078581742117349)
                  ·
                    refine ⟨642336913139734076647003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3425796870078581742117349 642336913139734076647003)
                    ·
                      rfl

theorem cell23_3752840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_3752840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752840 prefixEnd_3752840 := by exact prefixLift 3752840
  have htrace : WordTrace (prefixWord ++ tailWord_3752840) baseStart_3752840 baseEnd_3752840 := by
    simpa [prefixWord, tailWord_3752840, baseEnd_3752840] using wordTrace_append hprefix tailTrace_3752840
  have hstable : (prefixWord ++ tailWord_3752840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752840).length < 2 ^ (prefixWord ++ tailWord_3752840).sum := by decide
  have hdescent : baseEnd_3752840 < baseStart_3752840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752853 : List Nat := [1, 3, 2, 1, 1, 5, 2, 8]
def baseStart_3752853 : Nat := 118140960795 + 3752853 * 2 ^ 59
def prefixEnd_3752853 : Nat := 4983230072969 + 3 ^ 40 * 3752853 * 2
def baseEnd_3752853 : Nat := 71371015358063358484387

theorem tailTrace_3752853 : CollatzResearch.WordTrace tailWord_3752853 prefixEnd_3752853 71371015358063358484387 := by
  unfold tailWord_3752853
  simp only [CollatzResearch.WordTrace]
  refine ⟨136877793873061992109967213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91251862582041328073311475 136877793873061992109967213)
  ·
    refine ⟨51329172702398247041237705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136877793873061992109967213 51329172702398247041237705)
    ·
      refine ⟨38496879526798685280928279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51329172702398247041237705 38496879526798685280928279)
      ·
        refine ⟨57745319290198027921392419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38496879526798685280928279 57745319290198027921392419)
        ·
          refine ⟨86617978935297041882088629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57745319290198027921392419 86617978935297041882088629)
          ·
            refine ⟨8120435525184097676445809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86617978935297041882088629 8120435525184097676445809)
            ·
              refine ⟨6090326643888073257334357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120435525184097676445809 6090326643888073257334357)
              ·
                refine ⟨71371015358063358484387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6090326643888073257334357 71371015358063358484387)
                ·
                  rfl

theorem cell23_3752853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 8].length) (baseStart_3752853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752853 prefixEnd_3752853 := by exact prefixLift 3752853
  have htrace : WordTrace (prefixWord ++ tailWord_3752853) baseStart_3752853 baseEnd_3752853 := by
    simpa [prefixWord, tailWord_3752853, baseEnd_3752853] using wordTrace_append hprefix tailTrace_3752853
  have hstable : (prefixWord ++ tailWord_3752853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752853).length < 2 ^ (prefixWord ++ tailWord_3752853).sum := by decide
  have hdescent : baseEnd_3752853 < baseStart_3752853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752884 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3752884 : Nat := 118140960795 + 3752884 * 2 ^ 59
def prefixEnd_3752884 : Nat := 4983230072969 + 3 ^ 40 * 3752884 * 2
def baseEnd_3752884 : Nat := 1927033332568000057790807

theorem tailTrace_3752884 : CollatzResearch.WordTrace tailWord_3752884 prefixEnd_3752884 1927033332568000057790807 := by
  unfold tailWord_3752884
  simp only [CollatzResearch.WordTrace]
  refine ⟨68439462267974842202172853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91252616357299789602897137 68439462267974842202172853)
  ·
    refine ⟨6416199587622641456453705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68439462267974842202172853 6416199587622641456453705)
    ·
      refine ⟨4812149690716981092340279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6416199587622641456453705 4812149690716981092340279)
      ·
        refine ⟨7218224536075471638510419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812149690716981092340279 7218224536075471638510419)
        ·
          refine ⟨10827336804113207457765629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218224536075471638510419 10827336804113207457765629)
          ·
            refine ⟨4060251301542452796662111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10827336804113207457765629 4060251301542452796662111)
            ·
              refine ⟨6090376952313679194993167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060251301542452796662111 6090376952313679194993167)
              ·
                refine ⟨9135565428470518792489751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090376952313679194993167 9135565428470518792489751)
                ·
                  refine ⟨13703348142705778188734627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9135565428470518792489751 13703348142705778188734627)
                  ·
                    refine ⟨20555022214058667283101941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13703348142705778188734627 20555022214058667283101941)
                    ·
                      refine ⟨1927033332568000057790807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20555022214058667283101941 1927033332568000057790807)
                      ·
                        rfl

theorem cell23_3752884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3752884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752884 prefixEnd_3752884 := by exact prefixLift 3752884
  have htrace : WordTrace (prefixWord ++ tailWord_3752884) baseStart_3752884 baseEnd_3752884 := by
    simpa [prefixWord, tailWord_3752884, baseEnd_3752884] using wordTrace_append hprefix tailTrace_3752884
  have hstable : (prefixWord ++ tailWord_3752884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752884).length < 2 ^ (prefixWord ++ tailWord_3752884).sum := by decide
  have hdescent : baseEnd_3752884 < baseStart_3752884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752903 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_3752903 : Nat := 118140960795 + 3752903 * 2 ^ 59
def prefixEnd_3752903 : Nat := 4983230072969 + 3 ^ 40 * 3752903 * 2
def baseEnd_3752903 : Nat := 1927043088700435483453219

theorem tailTrace_3752903 : CollatzResearch.WordTrace tailWord_3752903 prefixEnd_3752903 1927043088700435483453219 := by
  unfold tailWord_3752903
  simp only [CollatzResearch.WordTrace]
  refine ⟨136879617522880850649287363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91253078348587233766191575 136879617522880850649287363)
  ·
    refine ⟨205319426284321275973931045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136879617522880850649287363 205319426284321275973931045)
    ·
      refine ⟨38497392428310239245112071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205319426284321275973931045 38497392428310239245112071)
      ·
        refine ⟨57746088642465358867668107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38497392428310239245112071 57746088642465358867668107)
        ·
          refine ⟨86619132963698038301502161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57746088642465358867668107 86619132963698038301502161)
          ·
            refine ⟨64964349722773528726126621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86619132963698038301502161 64964349722773528726126621)
            ·
              refine ⟨24361631146040073272297483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64964349722773528726126621 24361631146040073272297483)
              ·
                refine ⟨36542446719060109908446225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24361631146040073272297483 36542446719060109908446225)
                ·
                  refine ⟨27406835039295082431334669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36542446719060109908446225 27406835039295082431334669)
                  ·
                    refine ⟨10277563139735655911750501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27406835039295082431334669 10277563139735655911750501)
                    ·
                      refine ⟨1927043088700435483453219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10277563139735655911750501 1927043088700435483453219)
                      ·
                        rfl

theorem cell23_3752903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_3752903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752903 prefixEnd_3752903 := by exact prefixLift 3752903
  have htrace : WordTrace (prefixWord ++ tailWord_3752903) baseStart_3752903 baseEnd_3752903 := by
    simpa [prefixWord, tailWord_3752903, baseEnd_3752903] using wordTrace_append hprefix tailTrace_3752903
  have hstable : (prefixWord ++ tailWord_3752903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752903).length < 2 ^ (prefixWord ++ tailWord_3752903).sum := by decide
  have hdescent : baseEnd_3752903 < baseStart_3752903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752913 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 2, 6]
def baseStart_3752913 : Nat := 118140960795 + 3752913 * 2 ^ 59
def prefixEnd_3752913 : Nat := 4983230072969 + 3 ^ 40 * 3752913 * 2
def baseEnd_3752913 : Nat := 642349407835660148109391

theorem tailTrace_3752913 : CollatzResearch.WordTrace tailWord_3752913 prefixEnd_3752913 642349407835660148109391 := by
  unfold tailWord_3752913
  simp only [CollatzResearch.WordTrace]
  refine ⟨136879982252844622357151393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91253321501896414904767595 136879982252844622357151393)
  ·
    refine ⟨102659986689633466767863545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136879982252844622357151393 102659986689633466767863545)
    ·
      refine ⟨76994990017225100075897659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102659986689633466767863545 76994990017225100075897659)
      ·
        refine ⟨115492485025837650113846489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76994990017225100075897659 115492485025837650113846489)
        ·
          refine ⟨86619363769378237585384867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115492485025837650113846489 86619363769378237585384867)
          ·
            refine ⟨129929045654067356378077301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86619363769378237585384867 129929045654067356378077301)
            ·
              refine ⟨12180848030068814660444747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129929045654067356378077301 12180848030068814660444747)
              ·
                refine ⟨18271272045103221990667121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12180848030068814660444747 18271272045103221990667121)
                ·
                  refine ⟨13703454033827416493000341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18271272045103221990667121 13703454033827416493000341)
                  ·
                    refine ⟨642349407835660148109391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13703454033827416493000341 642349407835660148109391)
                    ·
                      rfl

theorem cell23_3752913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_3752913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752913 prefixEnd_3752913 := by exact prefixLift 3752913
  have htrace : WordTrace (prefixWord ++ tailWord_3752913) baseStart_3752913 baseEnd_3752913 := by
    simpa [prefixWord, tailWord_3752913, baseEnd_3752913] using wordTrace_append hprefix tailTrace_3752913
  have hstable : (prefixWord ++ tailWord_3752913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752913).length < 2 ^ (prefixWord ++ tailWord_3752913).sum := by decide
  have hdescent : baseEnd_3752913 < baseStart_3752913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752914 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3752914 : Nat := 118140960795 + 3752914 * 2 ^ 59
def prefixEnd_3752914 : Nat := 4983230072969 + 3 ^ 40 * 3752914 * 2
def baseEnd_3752914 : Nat := 1927048736987634940415669

theorem tailTrace_3752914 : CollatzResearch.WordTrace tailWord_3752914 prefixEnd_3752914 1927048736987634940415669 := by
  unfold tailWord_3752914
  simp only [CollatzResearch.WordTrace]
  refine ⟨34220004681460249881984449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91253345817227333018625197 34220004681460249881984449)
  ·
    refine ⟨25665003511095187411488337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34220004681460249881984449 25665003511095187411488337)
    ·
      refine ⟨19248752633321390558616253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25665003511095187411488337 19248752633321390558616253)
      ·
        refine ⟨7218282237495521459481095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19248752633321390558616253 7218282237495521459481095)
        ·
          refine ⟨10827423356243282189221643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218282237495521459481095 10827423356243282189221643)
          ·
            refine ⟨16241135034364923283832465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10827423356243282189221643 16241135034364923283832465)
            ·
              refine ⟨12180851275773692462874349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16241135034364923283832465 12180851275773692462874349)
              ·
                refine ⟨4567819228415134673577881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12180851275773692462874349 4567819228415134673577881)
                ·
                  refine ⟨3425864421311351005183411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4567819228415134673577881 3425864421311351005183411)
                  ·
                    refine ⟨5138796631967026507775117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3425864421311351005183411 5138796631967026507775117)
                    ·
                      refine ⟨1927048736987634940415669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5138796631967026507775117 1927048736987634940415669)
                      ·
                        rfl

theorem cell23_3752914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3752914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752914 prefixEnd_3752914 := by exact prefixLift 3752914
  have htrace : WordTrace (prefixWord ++ tailWord_3752914) baseStart_3752914 baseEnd_3752914 := by
    simpa [prefixWord, tailWord_3752914, baseEnd_3752914] using wordTrace_append hprefix tailTrace_3752914
  have hstable : (prefixWord ++ tailWord_3752914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752914).length < 2 ^ (prefixWord ++ tailWord_3752914).sum := by decide
  have hdescent : baseEnd_3752914 < baseStart_3752914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752971 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 2, 2, 2]
def baseStart_3752971 : Nat := 118140960795 + 3752971 * 2 ^ 59
def prefixEnd_3752971 : Nat := 4983230072969 + 3 ^ 40 * 3752971 * 2
def baseEnd_3752971 : Nat := 1927078005384941217402907

theorem tailTrace_3752971 : CollatzResearch.WordTrace tailWord_3752971 prefixEnd_3752971 1927078005384941217402907 := by
  unfold tailWord_3752971
  simp only [CollatzResearch.WordTrace]
  refine ⟨136882097686634498262762767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91254731791089665508508511 136882097686634498262762767)
  ·
    refine ⟨205323146529951747394144151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136882097686634498262762767 205323146529951747394144151)
    ·
      refine ⟨307984719794927621091216227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205323146529951747394144151 307984719794927621091216227)
      ·
        refine ⟨461977079692391431636824341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307984719794927621091216227 461977079692391431636824341)
        ·
          refine ⟨21655175610580848357976141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 461977079692391431636824341 21655175610580848357976141)
          ·
            refine ⟨8120690853967818134241053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21655175610580848357976141 8120690853967818134241053)
            ·
              refine ⟨3045259070237931800340395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8120690853967818134241053 3045259070237931800340395)
              ·
                refine ⟨4567888605356897700510593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3045259070237931800340395 4567888605356897700510593)
                ·
                  refine ⟨3425916454017673275382945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4567888605356897700510593 3425916454017673275382945)
                  ·
                    refine ⟨2569437340513254956537209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3425916454017673275382945 2569437340513254956537209)
                    ·
                      refine ⟨1927078005384941217402907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569437340513254956537209 1927078005384941217402907)
                      ·
                        rfl

theorem cell23_3752971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 2, 2].length) (baseStart_3752971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752971 prefixEnd_3752971 := by exact prefixLift 3752971
  have htrace : WordTrace (prefixWord ++ tailWord_3752971) baseStart_3752971 baseEnd_3752971 := by
    simpa [prefixWord, tailWord_3752971, baseEnd_3752971] using wordTrace_append hprefix tailTrace_3752971
  have hstable : (prefixWord ++ tailWord_3752971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752971).length < 2 ^ (prefixWord ++ tailWord_3752971).sum := by decide
  have hdescent : baseEnd_3752971 < baseStart_3752971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3752994 : List Nat := [3, 3, 1, 1, 1, 5, 1, 3, 5]
def baseStart_3752994 : Nat := 118140960795 + 3752994 * 2 ^ 59
def prefixEnd_3752994 : Nat := 4983230072969 + 3 ^ 40 * 3752994 * 2
def baseEnd_3752994 : Nat := 214121090604443847490589

theorem tailTrace_3752994 : CollatzResearch.WordTrace tailWord_3752994 prefixEnd_3752994 214121090604443847490589 := by
  unfold tailWord_3752994
  simp only [CollatzResearch.WordTrace]
  refine ⟨34220734141387793297712509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91255291043700782127233357 34220734141387793297712509)
  ·
    refine ⟨12832775303020422486642191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34220734141387793297712509 12832775303020422486642191)
    ·
      refine ⟨19249162954530633729963287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12832775303020422486642191 19249162954530633729963287)
      ·
        refine ⟨28873744431795950594944931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19249162954530633729963287 28873744431795950594944931)
        ·
          refine ⟨43310616647693925892417397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28873744431795950594944931 43310616647693925892417397)
          ·
            refine ⟨4060370310721305552414131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43310616647693925892417397 4060370310721305552414131)
            ·
              refine ⟨6090555466081958328621197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060370310721305552414131 6090555466081958328621197)
              ·
                refine ⟨2283958299780734373232949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6090555466081958328621197 2283958299780734373232949)
                ·
                  refine ⟨214121090604443847490589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2283958299780734373232949 214121090604443847490589)
                  ·
                    rfl

theorem cell23_3752994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_3752994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3752994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3752994 prefixEnd_3752994 := by exact prefixLift 3752994
  have htrace : WordTrace (prefixWord ++ tailWord_3752994) baseStart_3752994 baseEnd_3752994 := by
    simpa [prefixWord, tailWord_3752994, baseEnd_3752994] using wordTrace_append hprefix tailTrace_3752994
  have hstable : (prefixWord ++ tailWord_3752994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3752994).length < 2 ^ (prefixWord ++ tailWord_3752994).sum := by decide
  have hdescent : baseEnd_3752994 < baseStart_3752994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3752994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753033 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 10]
def baseStart_3753033 : Nat := 118140960795 + 3753033 * 2 ^ 59
def prefixEnd_3753033 : Nat := 4983230072969 + 3 ^ 40 * 3753033 * 2
def baseEnd_3753033 : Nat := 214123315687279997203069

theorem tailTrace_3753033 : CollatzResearch.WordTrace tailWord_3753033 prefixEnd_3753033 214123315687279997203069 := by
  unfold tailWord_3753033
  simp only [CollatzResearch.WordTrace]
  refine ⟨136884359012409882851519753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91256239341606588567679835 136884359012409882851519753)
  ·
    refine ⟨102663269259307412138639815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136884359012409882851519753 102663269259307412138639815)
    ·
      refine ⟨153994903888961118207959723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102663269259307412138639815 153994903888961118207959723)
      ·
        refine ⟨230992355833441677311939585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153994903888961118207959723 230992355833441677311939585)
        ·
          refine ⟨173244266875081257983954689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230992355833441677311939585 173244266875081257983954689)
          ·
            refine ⟨129933200156310943487966017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173244266875081257983954689 129933200156310943487966017)
            ·
              refine ⟨97449900117233207615974513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129933200156310943487966017 97449900117233207615974513)
              ·
                refine ⟨73087425087924905711980885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97449900117233207615974513 73087425087924905711980885)
                ·
                  refine ⟨214123315687279997203069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 73087425087924905711980885 214123315687279997203069)
                  ·
                    rfl

theorem cell23_3753033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 10].length) (baseStart_3753033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753033 prefixEnd_3753033 := by exact prefixLift 3753033
  have htrace : WordTrace (prefixWord ++ tailWord_3753033) baseStart_3753033 baseEnd_3753033 := by
    simpa [prefixWord, tailWord_3753033, baseEnd_3753033] using wordTrace_append hprefix tailTrace_3753033
  have hstable : (prefixWord ++ tailWord_3753033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753033).length < 2 ^ (prefixWord ++ tailWord_3753033).sum := by decide
  have hdescent : baseEnd_3753033 < baseStart_3753033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753080 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 3, 5]
def baseStart_3753080 : Nat := 118140960795 + 3753080 * 2 ^ 59
def prefixEnd_3753080 : Nat := 4983230072969 + 3 ^ 40 * 3753080 * 2
def baseEnd_3753080 : Nat := 642377991592093763646635

theorem tailTrace_3753080 : CollatzResearch.WordTrace tailWord_3753080 prefixEnd_3753080 642377991592093763646635 := by
  unfold tailWord_3753080
  simp only [CollatzResearch.WordTrace]
  refine ⟨68443036621619804939240347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91257382162159739918987129 68443036621619804939240347)
  ·
    refine ⟨102664554932429707408860521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68443036621619804939240347 102664554932429707408860521)
    ·
      refine ⟨76998416199322280556645391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102664554932429707408860521 76998416199322280556645391)
      ·
        refine ⟨115497624298983420834968087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76998416199322280556645391 115497624298983420834968087)
        ·
          refine ⟨173246436448475131252452131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115497624298983420834968087 173246436448475131252452131)
          ·
            refine ⟨259869654672712696878678197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173246436448475131252452131 259869654672712696878678197)
            ·
              refine ⟨24362780125566815332376081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259869654672712696878678197 24362780125566815332376081)
              ·
                refine ⟨18272085094175111499282061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24362780125566815332376081 18272085094175111499282061)
                ·
                  refine ⟨6852031910315666812230773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18272085094175111499282061 6852031910315666812230773)
                  ·
                    refine ⟨642377991592093763646635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6852031910315666812230773 642377991592093763646635)
                    ·
                      rfl

theorem cell23_3753080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_3753080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753080 prefixEnd_3753080 := by exact prefixLift 3753080
  have htrace : WordTrace (prefixWord ++ tailWord_3753080) baseStart_3753080 baseEnd_3753080 := by
    simpa [prefixWord, tailWord_3753080, baseEnd_3753080] using wordTrace_append hprefix tailTrace_3753080
  have hstable : (prefixWord ++ tailWord_3753080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753080).length < 2 ^ (prefixWord ++ tailWord_3753080).sum := by decide
  have hdescent : baseEnd_3753080 < baseStart_3753080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753111 : List Nat := [1, 1, 3, 3, 3, 1, 1, 5, 1, 1, 3]
def baseStart_3753111 : Nat := 118140960795 + 3753111 * 2 ^ 59
def prefixEnd_3753111 : Nat := 4983230072969 + 3 ^ 40 * 3753111 * 2
def baseEnd_3753111 : Nat := 1927149892676570669652263

theorem tailTrace_3753111 : CollatzResearch.WordTrace tailWord_3753111 prefixEnd_3753111 1927149892676570669652263 := by
  unfold tailWord_3753111
  simp only [CollatzResearch.WordTrace]
  refine ⟨136887203906127302172859187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91258135937418201448572791 136887203906127302172859187)
  ·
    refine ⟨205330805859190953259288781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136887203906127302172859187 205330805859190953259288781)
    ·
      refine ⟨76999052197196607472233293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205330805859190953259288781 76999052197196607472233293)
      ·
        refine ⟨28874644573948727802087485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76999052197196607472233293 28874644573948727802087485)
        ·
          refine ⟨10827991715230772925782807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28874644573948727802087485 10827991715230772925782807)
          ·
            refine ⟨16241987572846159388674211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10827991715230772925782807 16241987572846159388674211)
            ·
              refine ⟨24362981359269239083011317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16241987572846159388674211 24362981359269239083011317)
              ·
                refine ⟨2284029502431491164032311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24362981359269239083011317 2284029502431491164032311)
                ·
                  refine ⟨3426044253647236746048467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284029502431491164032311 3426044253647236746048467)
                  ·
                    refine ⟨5139066380470855119072701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3426044253647236746048467 5139066380470855119072701)
                    ·
                      refine ⟨1927149892676570669652263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5139066380470855119072701 1927149892676570669652263)
                      ·
                        rfl

theorem cell23_3753111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_3753111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753111 prefixEnd_3753111 := by exact prefixLift 3753111
  have htrace : WordTrace (prefixWord ++ tailWord_3753111) baseStart_3753111 baseEnd_3753111 := by
    simpa [prefixWord, tailWord_3753111, baseEnd_3753111] using wordTrace_append hprefix tailTrace_3753111
  have hstable : (prefixWord ++ tailWord_3753111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753111).length < 2 ^ (prefixWord ++ tailWord_3753111).sum := by decide
  have hdescent : baseEnd_3753111 < baseStart_3753111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753114 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_3753114 : Nat := 118140960795 + 3753114 * 2 ^ 59
def prefixEnd_3753114 : Nat := 4983230072969 + 3 ^ 40 * 3753114 * 2
def baseEnd_3753114 : Nat := 642383811039511385971583

theorem tailTrace_3753114 : CollatzResearch.WordTrace tailWord_3753114 prefixEnd_3753114 642383811039511385971583 := by
  unfold tailWord_3753114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34221828331279108421304599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91258208883410955790145597 34221828331279108421304599)
  ·
    refine ⟨51332742496918662631956899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34221828331279108421304599 51332742496918662631956899)
    ·
      refine ⟨76999113745377993947935349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51332742496918662631956899 76999113745377993947935349)
      ·
        refine ⟨7218666913629186932618939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76999113745377993947935349 7218666913629186932618939)
        ·
          refine ⟨10828000370443780398928409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218666913629186932618939 10828000370443780398928409)
          ·
            refine ⟨8121000277832835299196307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10828000370443780398928409 8121000277832835299196307)
            ·
              refine ⟨12181500416749252948794461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8121000277832835299196307 12181500416749252948794461)
              ·
                refine ⟨4568062656280969855797923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12181500416749252948794461 4568062656280969855797923)
                ·
                  refine ⟨6852093984421454783696885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568062656280969855797923 6852093984421454783696885)
                  ·
                    refine ⟨642383811039511385971583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6852093984421454783696885 642383811039511385971583)
                    ·
                      rfl

theorem cell23_3753114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_3753114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753114 prefixEnd_3753114 := by exact prefixLift 3753114
  have htrace : WordTrace (prefixWord ++ tailWord_3753114) baseStart_3753114 baseEnd_3753114 := by
    simpa [prefixWord, tailWord_3753114, baseEnd_3753114] using wordTrace_append hprefix tailTrace_3753114
  have hstable : (prefixWord ++ tailWord_3753114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753114).length < 2 ^ (prefixWord ++ tailWord_3753114).sum := by decide
  have hdescent : baseEnd_3753114 < baseStart_3753114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753137 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3753137 : Nat := 118140960795 + 3753137 * 2 ^ 59
def prefixEnd_3753137 : Nat := 4983230072969 + 3 ^ 40 * 3753137 * 2
def baseEnd_3753137 : Nat := 1927163243173587567927143

theorem tailTrace_3753137 : CollatzResearch.WordTrace tailWord_3753137 prefixEnd_3753137 1927163243173587567927143 := by
  unfold tailWord_3753137
  simp only [CollatzResearch.WordTrace]
  refine ⟨136888152204033108613305665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91258768136022072408870443 136888152204033108613305665)
  ·
    refine ⟨102666114153024831459979249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136888152204033108613305665 102666114153024831459979249)
    ·
      refine ⟨76999585614768623594984437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102666114153024831459979249 76999585614768623594984437)
      ·
        refine ⟨7218711151384558462029791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76999585614768623594984437 7218711151384558462029791)
        ·
          refine ⟨10828066727076837693044687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218711151384558462029791 10828066727076837693044687)
          ·
            refine ⟨16242100090615256539567031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10828066727076837693044687 16242100090615256539567031)
            ·
              refine ⟨24363150135922884809350547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16242100090615256539567031 24363150135922884809350547)
              ·
                refine ⟨36544725203884327214025821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24363150135922884809350547 36544725203884327214025821)
                ·
                  refine ⟨13704271951456622705259683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36544725203884327214025821 13704271951456622705259683)
                  ·
                    refine ⟨20556407927184934057889525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13704271951456622705259683 20556407927184934057889525)
                    ·
                      refine ⟨1927163243173587567927143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20556407927184934057889525 1927163243173587567927143)
                      ·
                        rfl

theorem cell23_3753137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3753137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753137 prefixEnd_3753137 := by exact prefixLift 3753137
  have htrace : WordTrace (prefixWord ++ tailWord_3753137) baseStart_3753137 baseEnd_3753137 := by
    simpa [prefixWord, tailWord_3753137, baseEnd_3753137] using wordTrace_append hprefix tailTrace_3753137
  have hstable : (prefixWord ++ tailWord_3753137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753137).length < 2 ^ (prefixWord ++ tailWord_3753137).sum := by decide
  have hdescent : baseEnd_3753137 < baseStart_3753137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753184 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 4, 1, 3]
def baseStart_3753184 : Nat := 118140960795 + 3753184 * 2 ^ 59
def prefixEnd_3753184 : Nat := 4983230072969 + 3 ^ 40 * 3753184 * 2
def baseEnd_3753184 : Nat := 1927187376764348884039427

theorem tailTrace_3753184 : CollatzResearch.WordTrace tailWord_3753184 prefixEnd_3753184 1927187376764348884039427 := by
  unfold tailWord_3753184
  simp only [CollatzResearch.WordTrace]
  refine ⟨68444933217431417820133303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91259910956575223760177737 68444933217431417820133303)
  ·
    refine ⟨102667399826147126730199955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68444933217431417820133303 102667399826147126730199955)
    ·
      refine ⟨154001099739220690095299933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102667399826147126730199955 154001099739220690095299933)
      ·
        refine ⟨57750412402207758785737475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154001099739220690095299933 57750412402207758785737475)
        ·
          refine ⟨86625618603311638178606213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57750412402207758785737475 86625618603311638178606213)
          ·
            refine ⟨16242303488120932158488665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86625618603311638178606213 16242303488120932158488665)
            ·
              refine ⟨12181727616090699118866499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16242303488120932158488665 12181727616090699118866499)
              ·
                refine ⟨18272591424136048678299749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12181727616090699118866499 18272591424136048678299749)
                ·
                  refine ⟨3426110892025509127181203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18272591424136048678299749 3426110892025509127181203)
                  ·
                    refine ⟨5139166338038263690771805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3426110892025509127181203 5139166338038263690771805)
                    ·
                      refine ⟨1927187376764348884039427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5139166338038263690771805 1927187376764348884039427)
                      ·
                        rfl

theorem cell23_3753184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_3753184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753184 prefixEnd_3753184 := by exact prefixLift 3753184
  have htrace : WordTrace (prefixWord ++ tailWord_3753184) baseStart_3753184 baseEnd_3753184 := by
    simpa [prefixWord, tailWord_3753184, baseEnd_3753184] using wordTrace_append hprefix tailTrace_3753184
  have hstable : (prefixWord ++ tailWord_3753184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753184).length < 2 ^ (prefixWord ++ tailWord_3753184).sum := by decide
  have hdescent : baseEnd_3753184 < baseStart_3753184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753185 : List Nat := [1, 2, 3, 1, 3, 3, 3, 2, 1, 2, 2]
def baseStart_3753185 : Nat := 118140960795 + 3753185 * 2 ^ 59
def prefixEnd_3753185 : Nat := 4983230072969 + 3 ^ 40 * 3753185 * 2
def baseEnd_3753185 : Nat := 1927187890245003380126923

theorem tailTrace_3753185 : CollatzResearch.WordTrace tailWord_3753185 prefixEnd_3753185 1927187890245003380126923 := by
  unfold tailWord_3753185
  simp only [CollatzResearch.WordTrace]
  refine ⟨136889902907859212811053009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91259935271906141874035339 136889902907859212811053009)
  ·
    refine ⟨102667427180894409608289757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136889902907859212811053009 102667427180894409608289757)
    ·
      refine ⟨38500285192835403603108659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102667427180894409608289757 38500285192835403603108659)
      ·
        refine ⟨57750427789253105404662989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38500285192835403603108659 57750427789253105404662989)
        ·
          refine ⟨21656410420969914526748621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57750427789253105404662989 21656410420969914526748621)
          ·
            refine ⟨8121153907863717947530733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21656410420969914526748621 8121153907863717947530733)
            ·
              refine ⟨3045432715448894230324025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8121153907863717947530733 3045432715448894230324025)
              ·
                refine ⟨2284074536586670672743019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3045432715448894230324025 2284074536586670672743019)
                ·
                  refine ⟨3426111804880006009114529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284074536586670672743019 3426111804880006009114529)
                  ·
                    refine ⟨2569583853660004506835897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3426111804880006009114529 2569583853660004506835897)
                    ·
                      refine ⟨1927187890245003380126923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569583853660004506835897 1927187890245003380126923)
                      ·
                        rfl

theorem cell23_3753185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_3753185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753185 prefixEnd_3753185 := by exact prefixLift 3753185
  have htrace : WordTrace (prefixWord ++ tailWord_3753185) baseStart_3753185 baseEnd_3753185 := by
    simpa [prefixWord, tailWord_3753185, baseEnd_3753185] using wordTrace_append hprefix tailTrace_3753185
  have hstable : (prefixWord ++ tailWord_3753185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753185).length < 2 ^ (prefixWord ++ tailWord_3753185).sum := by decide
  have hdescent : baseEnd_3753185 < baseStart_3753185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753227 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 5]
def baseStart_3753227 : Nat := 118140960795 + 3753227 * 2 ^ 59
def prefixEnd_3753227 : Nat := 4983230072969 + 3 ^ 40 * 3753227 * 2
def baseEnd_3753227 : Nat := 1927209456432492215801729

theorem tailTrace_3753227 : CollatzResearch.WordTrace tailWord_3753227 prefixEnd_3753227 1927209456432492215801729 := by
  unfold tailWord_3753227
  simp only [CollatzResearch.WordTrace]
  refine ⟨136891434773707053984081935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91260956515804702656054623 136891434773707053984081935)
  ·
    refine ⟨205337152160560580976122903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136891434773707053984081935 205337152160560580976122903)
    ·
      refine ⟨308005728240840871464184355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205337152160560580976122903 308005728240840871464184355)
      ·
        refine ⟨462008592361261307196276533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308005728240840871464184355 462008592361261307196276533)
        ·
          refine ⟨43313305533868247549650925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462008592361261307196276533 43313305533868247549650925)
          ·
            refine ⟨16242489575200592831119097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43313305533868247549650925 16242489575200592831119097)
            ·
              refine ⟨12181867181400444623339323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16242489575200592831119097 12181867181400444623339323)
              ·
                refine ⟨18272800772100666935008985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12181867181400444623339323 18272800772100666935008985)
                ·
                  refine ⟨13704600579075500201256739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18272800772100666935008985 13704600579075500201256739)
                  ·
                    refine ⟨20556900868613250301885109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13704600579075500201256739 20556900868613250301885109)
                    ·
                      refine ⟨1927209456432492215801729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20556900868613250301885109 1927209456432492215801729)
                      ·
                        rfl

theorem cell23_3753227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 5].length) (baseStart_3753227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753227 prefixEnd_3753227 := by exact prefixLift 3753227
  have htrace : WordTrace (prefixWord ++ tailWord_3753227) baseStart_3753227 baseEnd_3753227 := by
    simpa [prefixWord, tailWord_3753227, baseEnd_3753227] using wordTrace_append hprefix tailTrace_3753227
  have hstable : (prefixWord ++ tailWord_3753227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753227).length < 2 ^ (prefixWord ++ tailWord_3753227).sum := by decide
  have hdescent : baseEnd_3753227 < baseStart_3753227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753228 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 1, 3, 2]
def baseStart_3753228 : Nat := 118140960795 + 3753228 * 2 ^ 59
def prefixEnd_3753228 : Nat := 4983230072969 + 3 ^ 40 * 3753228 * 2
def baseEnd_3753228 : Nat := 1927209969913146711889225

theorem tailTrace_3753228 : CollatzResearch.WordTrace tailWord_3753228 prefixEnd_3753228 1927209969913146711889225 := by
  unfold tailWord_3753228
  simp only [CollatzResearch.WordTrace]
  refine ⟨68445735623351715577434169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91260980831135620769912225 68445735623351715577434169)
  ·
    refine ⟨51334301717513786683075627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68445735623351715577434169 51334301717513786683075627)
    ·
      refine ⟨77001452576270680024613441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51334301717513786683075627 77001452576270680024613441)
      ·
        refine ⟨57751089432203010018460081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77001452576270680024613441 57751089432203010018460081)
        ·
          refine ⟨43313317074152257513845061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57751089432203010018460081 43313317074152257513845061)
          ·
            refine ⟨8121246951403548283845949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43313317074152257513845061 8121246951403548283845949)
            ·
              refine ⟨3045467606776330606442231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8121246951403548283845949 3045467606776330606442231)
              ·
                refine ⟨4568201410164495909663347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3045467606776330606442231 4568201410164495909663347)
                ·
                  refine ⟨6852302115246743864495021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568201410164495909663347 6852302115246743864495021)
                  ·
                    refine ⟨2569613293217528949185633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6852302115246743864495021 2569613293217528949185633)
                    ·
                      refine ⟨1927209969913146711889225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569613293217528949185633 1927209969913146711889225)
                      ·
                        rfl

theorem cell23_3753228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_3753228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753228 prefixEnd_3753228 := by exact prefixLift 3753228
  have htrace : WordTrace (prefixWord ++ tailWord_3753228) baseStart_3753228 baseEnd_3753228 := by
    simpa [prefixWord, tailWord_3753228, baseEnd_3753228] using wordTrace_append hprefix tailTrace_3753228
  have hstable : (prefixWord ++ tailWord_3753228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753228).length < 2 ^ (prefixWord ++ tailWord_3753228).sum := by decide
  have hdescent : baseEnd_3753228 < baseStart_3753228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753237 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3753237 : Nat := 118140960795 + 3753237 * 2 ^ 59
def prefixEnd_3753237 : Nat := 4983230072969 + 3 ^ 40 * 3753237 * 2
def baseEnd_3753237 : Nat := 1927214591239037176676683

theorem tailTrace_3753237 : CollatzResearch.WordTrace tailWord_3753237 prefixEnd_3753237 1927214591239037176676683 := by
  unfold tailWord_3753237
  simp only [CollatzResearch.WordTrace]
  refine ⟨136891799503670825691945965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91261199669113883794630643 136891799503670825691945965)
  ·
    refine ⟨51334424813876559634479737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136891799503670825691945965 51334424813876559634479737)
    ·
      refine ⟨38500818610407419725859803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51334424813876559634479737 38500818610407419725859803)
      ·
        refine ⟨57751227915611129588789705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38500818610407419725859803 57751227915611129588789705)
        ·
          refine ⟨43313420936708347191592279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57751227915611129588789705 43313420936708347191592279)
          ·
            refine ⟨64970131405062520787388419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43313420936708347191592279 64970131405062520787388419)
            ·
              refine ⟨97455197107593781181082629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64970131405062520787388419 97455197107593781181082629)
              ·
                refine ⟨18272849457673833971452993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97455197107593781181082629 18272849457673833971452993)
                ·
                  refine ⟨13704637093255375478589745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18272849457673833971452993 13704637093255375478589745)
                  ·
                    refine ⟨10278477819941531608942309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13704637093255375478589745 10278477819941531608942309)
                    ·
                      refine ⟨1927214591239037176676683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10278477819941531608942309 1927214591239037176676683)
                      ·
                        rfl

theorem cell23_3753237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3753237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753237 prefixEnd_3753237 := by exact prefixLift 3753237
  have htrace : WordTrace (prefixWord ++ tailWord_3753237) baseStart_3753237 baseEnd_3753237 := by
    simpa [prefixWord, tailWord_3753237, baseEnd_3753237] using wordTrace_append hprefix tailTrace_3753237
  have hstable : (prefixWord ++ tailWord_3753237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753237).length < 2 ^ (prefixWord ++ tailWord_3753237).sum := by decide
  have hdescent : baseEnd_3753237 < baseStart_3753237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753258 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3753258 : Nat := 118140960795 + 3753258 * 2 ^ 59
def prefixEnd_3753258 : Nat := 4983230072969 + 3 ^ 40 * 3753258 * 2
def baseEnd_3753258 : Nat := 1927225374332781594514087

theorem tailTrace_3753258 : CollatzResearch.WordTrace tailWord_3753258 prefixEnd_3753258 1927225374332781594514087 := by
  unfold tailWord_3753258
  simp only [CollatzResearch.WordTrace]
  refine ⟨34223141359148686569615107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91261710291063164185640285 34223141359148686569615107)
  ·
    refine ⟨51334712038723029854422661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34223141359148686569615107 51334712038723029854422661)
    ·
      refine ⟨9625258507260568097704249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51334712038723029854422661 9625258507260568097704249)
      ·
        refine ⟨7218943880445426073278187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9625258507260568097704249 7218943880445426073278187)
        ·
          refine ⟨10828415820668139109917281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218943880445426073278187 10828415820668139109917281)
          ·
            refine ⟨8121311865501104332437961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10828415820668139109917281 8121311865501104332437961)
            ·
              refine ⟨6090983899125828249328471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8121311865501104332437961 6090983899125828249328471)
              ·
                refine ⟨9136475848688742373992707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090983899125828249328471 9136475848688742373992707)
                ·
                  refine ⟨13704713773033113560989061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9136475848688742373992707 13704713773033113560989061)
                  ·
                    refine ⟨2569633832443708792685449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13704713773033113560989061 2569633832443708792685449)
                    ·
                      refine ⟨1927225374332781594514087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569633832443708792685449 1927225374332781594514087)
                      ·
                        rfl

theorem cell23_3753258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3753258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753258 prefixEnd_3753258 := by exact prefixLift 3753258
  have htrace : WordTrace (prefixWord ++ tailWord_3753258) baseStart_3753258 baseEnd_3753258 := by
    simpa [prefixWord, tailWord_3753258, baseEnd_3753258] using wordTrace_append hprefix tailTrace_3753258
  have hstable : (prefixWord ++ tailWord_3753258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753258).length < 2 ^ (prefixWord ++ tailWord_3753258).sum := by decide
  have hdescent : baseEnd_3753258 < baseStart_3753258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753281 : List Nat := [1, 2, 5, 2, 1, 1, 1, 5, 5]
def baseStart_3753281 : Nat := 118140960795 + 3753281 * 2 ^ 59
def prefixEnd_3753281 : Nat := 4983230072969 + 3 ^ 40 * 3753281 * 2
def baseEnd_3753281 : Nat := 214137464931981667169609

theorem tailTrace_3753281 : CollatzResearch.WordTrace tailWord_3753281 prefixEnd_3753281 214137464931981667169609 := by
  unfold tailWord_3753281
  simp only [CollatzResearch.WordTrace]
  refine ⟨136893404315511421206547697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91262269543674280804365131 136893404315511421206547697)
  ·
    refine ⟨102670053236633565904910773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136893404315511421206547697 102670053236633565904910773)
    ·
      refine ⟨9625317490934396803585385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102670053236633565904910773 9625317490934396803585385)
      ·
        refine ⟨7218988118200797602689039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9625317490934396803585385 7218988118200797602689039)
        ·
          refine ⟨10828482177301196404033559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218988118200797602689039 10828482177301196404033559)
          ·
            refine ⟨16242723265951794606050339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10828482177301196404033559 16242723265951794606050339)
            ·
              refine ⟨24364084898927691909075509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16242723265951794606050339 24364084898927691909075509)
              ·
                refine ⟨2284132959274471116475829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24364084898927691909075509 2284132959274471116475829)
                ·
                  refine ⟨214137464931981667169609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2284132959274471116475829 214137464931981667169609)
                  ·
                    rfl

theorem cell23_3753281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 5].length) (baseStart_3753281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753281 prefixEnd_3753281 := by exact prefixLift 3753281
  have htrace : WordTrace (prefixWord ++ tailWord_3753281) baseStart_3753281 baseEnd_3753281 := by
    simpa [prefixWord, tailWord_3753281, baseEnd_3753281] using wordTrace_append hprefix tailTrace_3753281
  have hstable : (prefixWord ++ tailWord_3753281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753281).length < 2 ^ (prefixWord ++ tailWord_3753281).sum := by decide
  have hdescent : baseEnd_3753281 < baseStart_3753281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753309 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3753309 : Nat := 118140960795 + 3753309 * 2 ^ 59
def prefixEnd_3753309 : Nat := 4983230072969 + 3 ^ 40 * 3753309 * 2
def baseEnd_3753309 : Nat := 1927251561846160894976353

theorem tailTrace_3753309 : CollatzResearch.WordTrace tailWord_3753309 prefixEnd_3753309 1927251561846160894976353 := by
  unfold tailWord_3753309
  simp only [CollatzResearch.WordTrace]
  refine ⟨136894425559409981988566981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91262950372939987992377987 136894425559409981988566981)
  ·
    refine ⟨25667704792389371622856309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136894425559409981988566981 25667704792389371622856309)
    ·
      refine ⟨2406347324286503589642779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25667704792389371622856309 2406347324286503589642779)
      ·
        refine ⟨3609520986429755384464169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406347324286503589642779 3609520986429755384464169)
        ·
          refine ⟨2707140739822316538348127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3609520986429755384464169 2707140739822316538348127)
          ·
            refine ⟨4060711109733474807522191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707140739822316538348127 4060711109733474807522191)
            ·
              refine ⟨6091066664600212211283287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060711109733474807522191 6091066664600212211283287)
              ·
                refine ⟨9136599996900318316924931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091066664600212211283287 9136599996900318316924931)
                ·
                  refine ⟨13704899995350477475387397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9136599996900318316924931 13704899995350477475387397)
                  ·
                    refine ⟨2569668749128214526635137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13704899995350477475387397 2569668749128214526635137)
                    ·
                      refine ⟨1927251561846160894976353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569668749128214526635137 1927251561846160894976353)
                      ·
                        rfl

theorem cell23_3753309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3753309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753309 prefixEnd_3753309 := by exact prefixLift 3753309
  have htrace : WordTrace (prefixWord ++ tailWord_3753309) baseStart_3753309 baseEnd_3753309 := by
    simpa [prefixWord, tailWord_3753309, baseEnd_3753309] using wordTrace_append hprefix tailTrace_3753309
  have hstable : (prefixWord ++ tailWord_3753309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753309).length < 2 ^ (prefixWord ++ tailWord_3753309).sum := by decide
  have hdescent : baseEnd_3753309 < baseStart_3753309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753314 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3753314 : Nat := 118140960795 + 3753314 * 2 ^ 59
def prefixEnd_3753314 : Nat := 4983230072969 + 3 ^ 40 * 3753314 * 2
def baseEnd_3753314 : Nat := 1927254129249433375413829

theorem tailTrace_3753314 : CollatzResearch.WordTrace tailWord_3753314 prefixEnd_3753314 1927254129249433375413829 := by
  unfold tailWord_3753314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34223651981097966960624749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91263071949594578561665997 34223651981097966960624749)
  ·
    refine ⟨12833869492911737610234281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34223651981097966960624749 12833869492911737610234281)
    ·
      refine ⟨9625402119683803207675711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12833869492911737610234281 9625402119683803207675711)
      ·
        refine ⟨14438103179525704811513567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9625402119683803207675711 14438103179525704811513567)
        ·
          refine ⟨21657154769288557217270351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14438103179525704811513567 21657154769288557217270351)
          ·
            refine ⟨32485732153932835825905527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21657154769288557217270351 32485732153932835825905527)
            ·
              refine ⟨48728598230899253738858291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32485732153932835825905527 48728598230899253738858291)
              ·
                refine ⟨73092897346348880608287437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48728598230899253738858291 73092897346348880608287437)
                ·
                  refine ⟨27409836504880830228107789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73092897346348880608287437 27409836504880830228107789)
                  ·
                    refine ⟨10278688689330311335540421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27409836504880830228107789 10278688689330311335540421)
                    ·
                      refine ⟨1927254129249433375413829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10278688689330311335540421 1927254129249433375413829)
                      ·
                        rfl

theorem cell23_3753314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3753314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753314 prefixEnd_3753314 := by exact prefixLift 3753314
  have htrace : WordTrace (prefixWord ++ tailWord_3753314) baseStart_3753314 baseEnd_3753314 := by
    simpa [prefixWord, tailWord_3753314, baseEnd_3753314] using wordTrace_append hprefix tailTrace_3753314
  have hstable : (prefixWord ++ tailWord_3753314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753314).length < 2 ^ (prefixWord ++ tailWord_3753314).sum := by decide
  have hdescent : baseEnd_3753314 < baseStart_3753314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753327 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_3753327 : Nat := 118140960795 + 3753327 * 2 ^ 59
def prefixEnd_3753327 : Nat := 4983230072969 + 3 ^ 40 * 3753327 * 2
def baseEnd_3753327 : Nat := 1927260804497941824551269

theorem tailTrace_3753327 : CollatzResearch.WordTrace tailWord_3753327 prefixEnd_3753327 1927260804497941824551269 := by
  unfold tailWord_3753327
  simp only [CollatzResearch.WordTrace]
  refine ⟨136895082073344771062722235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91263388048896514041814823 136895082073344771062722235)
  ·
    refine ⟨205342623110017156594083353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136895082073344771062722235 205342623110017156594083353)
    ·
      refine ⟨154006967332512867445562515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205342623110017156594083353 154006967332512867445562515)
      ·
        refine ⟨231010450998769301168343773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154006967332512867445562515 231010450998769301168343773)
        ·
          refine ⟨86628919124538487938128915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231010450998769301168343773 86628919124538487938128915)
          ·
            refine ⟨129943378686807731907193373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86628919124538487938128915 129943378686807731907193373)
            ·
              refine ⟨48728767007552899465197515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129943378686807731907193373 48728767007552899465197515)
              ·
                refine ⟨73093150511329349197796273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48728767007552899465197515 73093150511329349197796273)
                ·
                  refine ⟨54819862883497011898347205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73093150511329349197796273 54819862883497011898347205)
                  ·
                    refine ⟨10278724290655689730940101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54819862883497011898347205 10278724290655689730940101)
                    ·
                      refine ⟨1927260804497941824551269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10278724290655689730940101 1927260804497941824551269)
                      ·
                        rfl

theorem cell23_3753327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_3753327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753327 prefixEnd_3753327 := by exact prefixLift 3753327
  have htrace : WordTrace (prefixWord ++ tailWord_3753327) baseStart_3753327 baseEnd_3753327 := by
    simpa [prefixWord, tailWord_3753327, baseEnd_3753327] using wordTrace_append hprefix tailTrace_3753327
  have hstable : (prefixWord ++ tailWord_3753327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753327).length < 2 ^ (prefixWord ++ tailWord_3753327).sum := by decide
  have hdescent : baseEnd_3753327 < baseStart_3753327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753337 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 8]
def baseStart_3753337 : Nat := 118140960795 + 3753337 * 2 ^ 59
def prefixEnd_3753337 : Nat := 4983230072969 + 3 ^ 40 * 3753337 * 2
def baseEnd_3753337 : Nat := 214140659922720753936247

theorem tailTrace_3753337 : CollatzResearch.WordTrace tailWord_3753337 prefixEnd_3753337 214140659922720753936247 := by
  unfold tailWord_3753337
  simp only [CollatzResearch.WordTrace]
  refine ⟨136895446803308542770586265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91263631202205695180390843 136895446803308542770586265)
  ·
    refine ⟨102671585102481407077939699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136895446803308542770586265 102671585102481407077939699)
    ·
      refine ⟨154007377653722110616909549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102671585102481407077939699 154007377653722110616909549)
      ·
        refine ⟨57752766620145791481341081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154007377653722110616909549 57752766620145791481341081)
        ·
          refine ⟨43314574965109343611005811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57752766620145791481341081 43314574965109343611005811)
          ·
            refine ⟨64971862447664015416508717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43314574965109343611005811 64971862447664015416508717)
            ·
              refine ⟨24364448417874005781190769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64971862447664015416508717 24364448417874005781190769)
              ·
                refine ⟨18273336313405504335893077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24364448417874005781190769 18273336313405504335893077)
                ·
                  refine ⟨214140659922720753936247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18273336313405504335893077 214140659922720753936247)
                  ·
                    rfl

theorem cell23_3753337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 8].length) (baseStart_3753337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753337 prefixEnd_3753337 := by exact prefixLift 3753337
  have htrace : WordTrace (prefixWord ++ tailWord_3753337) baseStart_3753337 baseEnd_3753337 := by
    simpa [prefixWord, tailWord_3753337, baseEnd_3753337] using wordTrace_append hprefix tailTrace_3753337
  have hstable : (prefixWord ++ tailWord_3753337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753337).length < 2 ^ (prefixWord ++ tailWord_3753337).sum := by decide
  have hdescent : baseEnd_3753337 < baseStart_3753337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753351 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_3753351 : Nat := 118140960795 + 3753351 * 2 ^ 59
def prefixEnd_3753351 : Nat := 4983230072969 + 3 ^ 40 * 3753351 * 2
def baseEnd_3753351 : Nat := 1927273128033649730651159

theorem tailTrace_3753351 : CollatzResearch.WordTrace tailWord_3753351 prefixEnd_3753351 1927273128033649730651159 := by
  unfold tailWord_3753351
  simp only [CollatzResearch.WordTrace]
  refine ⟨136895957425257823161595907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91263971616838548774397271 136895957425257823161595907)
  ·
    refine ⟨205343936137886734742393861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136895957425257823161595907 205343936137886734742393861)
    ·
      refine ⟨38501988025853762764198849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205343936137886734742393861 38501988025853762764198849)
      ·
        refine ⟨28876491019390322073149137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38501988025853762764198849 28876491019390322073149137)
        ·
          refine ⟨21657368264542741554861853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28876491019390322073149137 21657368264542741554861853)
          ·
            refine ⟨8121513099203528083073195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21657368264542741554861853 8121513099203528083073195)
            ·
              refine ⟨12182269648805292124609793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8121513099203528083073195 12182269648805292124609793)
              ·
                refine ⟨9136702236603969093457345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12182269648805292124609793 9136702236603969093457345)
                ·
                  refine ⟨6852526677452976820093009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9136702236603969093457345 6852526677452976820093009)
                  ·
                    refine ⟨5139395008089732615069757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6852526677452976820093009 5139395008089732615069757)
                    ·
                      refine ⟨1927273128033649730651159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5139395008089732615069757 1927273128033649730651159)
                      ·
                        rfl

theorem cell23_3753351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_3753351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753351 prefixEnd_3753351 := by exact prefixLift 3753351
  have htrace : WordTrace (prefixWord ++ tailWord_3753351) baseStart_3753351 baseEnd_3753351 := by
    simpa [prefixWord, tailWord_3753351, baseEnd_3753351] using wordTrace_append hprefix tailTrace_3753351
  have hstable : (prefixWord ++ tailWord_3753351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753351).length < 2 ^ (prefixWord ++ tailWord_3753351).sum := by decide
  have hdescent : baseEnd_3753351 < baseStart_3753351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753367 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 2, 9]
def baseStart_3753367 : Nat := 118140960795 + 3753367 * 2 ^ 59
def prefixEnd_3753367 : Nat := 4983230072969 + 3 ^ 40 * 3753367 * 2
def baseEnd_3753367 : Nat := 642427114574707222683695

theorem tailTrace_3753367 : CollatzResearch.WordTrace tailWord_3753367 prefixEnd_3753367 642427114574707222683695 := by
  unfold tailWord_3753367
  simp only [CollatzResearch.WordTrace]
  refine ⟨136896540993199857894178355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91264360662133238596118903 136896540993199857894178355)
  ·
    refine ⟨205344811489799786841267533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136896540993199857894178355 205344811489799786841267533)
    ·
      refine ⟨77004304308674920065475325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205344811489799786841267533 77004304308674920065475325)
      ·
        refine ⟨28876614115753095024553247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77004304308674920065475325 28876614115753095024553247)
        ·
          refine ⟨43314921173629642536829871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28876614115753095024553247 43314921173629642536829871)
          ·
            refine ⟨64972381760444463805244807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43314921173629642536829871 64972381760444463805244807)
            ·
              refine ⟨97458572640666695707867211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64972381760444463805244807 97458572640666695707867211)
              ·
                refine ⟨146187858961000043561800817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97458572640666695707867211 146187858961000043561800817)
                ·
                  refine ⟨109640894220750032671350613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146187858961000043561800817 109640894220750032671350613)
                  ·
                    refine ⟨642427114574707222683695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 109640894220750032671350613 642427114574707222683695)
                    ·
                      rfl

theorem cell23_3753367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_3753367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753367 prefixEnd_3753367 := by exact prefixLift 3753367
  have htrace : WordTrace (prefixWord ++ tailWord_3753367) baseStart_3753367 baseEnd_3753367 := by
    simpa [prefixWord, tailWord_3753367, baseEnd_3753367] using wordTrace_append hprefix tailTrace_3753367
  have hstable : (prefixWord ++ tailWord_3753367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753367).length < 2 ^ (prefixWord ++ tailWord_3753367).sum := by decide
  have hdescent : baseEnd_3753367 < baseStart_3753367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753441 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_3753441 : Nat := 118140960795 + 3753441 * 2 ^ 59
def prefixEnd_3753441 : Nat := 4983230072969 + 3 ^ 40 * 3753441 * 2
def baseEnd_3753441 : Nat := 1927319341292554378525745

theorem tailTrace_3753441 : CollatzResearch.WordTrace tailWord_3753441 prefixEnd_3753441 1927319341292554378525745 := by
  unfold tailWord_3753441
  simp only [CollatzResearch.WordTrace]
  refine ⟨136899239994931768532372177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91266159996621179021581451 136899239994931768532372177)
  ·
    refine ⟨102674429996198826399279133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136899239994931768532372177 102674429996198826399279133)
    ·
      refine ⟨38502911248574559899729675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102674429996198826399279133 38502911248574559899729675)
      ·
        refine ⟨57754366872861839849594513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38502911248574559899729675 57754366872861839849594513)
        ·
          refine ⟨43315775154646379887195885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57754366872861839849594513 43315775154646379887195885)
          ·
            refine ⟨16243415682992392457698457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43315775154646379887195885 16243415682992392457698457)
            ·
              refine ⟨12182561762244294343273843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16243415682992392457698457 12182561762244294343273843)
              ·
                refine ⟨18273842643366441514910765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12182561762244294343273843 18273842643366441514910765)
                ·
                  refine ⟨6852690991262415568091537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18273842643366441514910765 6852690991262415568091537)
                  ·
                    refine ⟨5139518243446811676068653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6852690991262415568091537 5139518243446811676068653)
                    ·
                      refine ⟨1927319341292554378525745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5139518243446811676068653 1927319341292554378525745)
                      ·
                        rfl

theorem cell23_3753441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_3753441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753441 prefixEnd_3753441 := by exact prefixLift 3753441
  have htrace : WordTrace (prefixWord ++ tailWord_3753441) baseStart_3753441 baseEnd_3753441 := by
    simpa [prefixWord, tailWord_3753441, baseEnd_3753441] using wordTrace_append hprefix tailTrace_3753441
  have hstable : (prefixWord ++ tailWord_3753441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753441).length < 2 ^ (prefixWord ++ tailWord_3753441).sum := by decide
  have hdescent : baseEnd_3753441 < baseStart_3753441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753455 : List Nat := [1, 1, 2, 1, 4, 1, 3, 5, 1, 2, 2]
def baseStart_3753455 : Nat := 118140960795 + 3753455 * 2 ^ 59
def prefixEnd_3753455 : Nat := 4983230072969 + 3 ^ 40 * 3753455 * 2
def baseEnd_3753455 : Nat := 1927326530021717323750681

theorem tailTrace_3753455 : CollatzResearch.WordTrace tailWord_3753455 prefixEnd_3753455 1927326530021717323750681 := by
  unfold tailWord_3753455
  simp only [CollatzResearch.WordTrace]
  refine ⟨136899750616881048923381819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91266500411254032615587879 136899750616881048923381819)
  ·
    refine ⟨205349625925321573385072729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136899750616881048923381819 205349625925321573385072729)
    ·
      refine ⟨154012219443991180038804547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205349625925321573385072729 154012219443991180038804547)
      ·
        refine ⟨231018329165986770058206821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154012219443991180038804547 231018329165986770058206821)
        ·
          refine ⟨43315936718622519385913779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231018329165986770058206821 43315936718622519385913779)
          ·
            refine ⟨64973905077933779078870669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43315936718622519385913779 64973905077933779078870669)
            ·
              refine ⟨24365214404225167154576501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64973905077933779078870669 24365214404225167154576501)
              ·
                refine ⟨2284238850396109420741547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24365214404225167154576501 2284238850396109420741547)
                ·
                  refine ⟨3426358275594164131112321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284238850396109420741547 3426358275594164131112321)
                  ·
                    refine ⟨2569768706695623098334241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3426358275594164131112321 2569768706695623098334241)
                    ·
                      refine ⟨1927326530021717323750681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569768706695623098334241 1927326530021717323750681)
                      ·
                        rfl

theorem cell23_3753455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 2, 2].length) (baseStart_3753455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753455 prefixEnd_3753455 := by exact prefixLift 3753455
  have htrace : WordTrace (prefixWord ++ tailWord_3753455) baseStart_3753455 baseEnd_3753455 := by
    simpa [prefixWord, tailWord_3753455, baseEnd_3753455] using wordTrace_append hprefix tailTrace_3753455
  have hstable : (prefixWord ++ tailWord_3753455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753455).length < 2 ^ (prefixWord ++ tailWord_3753455).sum := by decide
  have hdescent : baseEnd_3753455 < baseStart_3753455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753461 : List Nat := [1, 3, 5, 1, 1, 2, 10]
def baseStart_3753461 : Nat := 118140960795 + 3753461 * 2 ^ 59
def prefixEnd_3753461 : Nat := 4983230072969 + 3 ^ 40 * 3753461 * 2
def baseEnd_3753461 : Nat := 23794192727230176546613

theorem tailTrace_3753461 : CollatzResearch.WordTrace tailWord_3753461 prefixEnd_3753461 23794192727230176546613 := by
  unfold tailWord_3753461
  simp only [CollatzResearch.WordTrace]
  refine ⟨136899969454859311948100237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91266646303239541298733491 136899969454859311948100237)
  ·
    refine ⟨51337488545572241980537589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136899969454859311948100237 51337488545572241980537589)
    ·
      refine ⟨4812889551147397685675399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51337488545572241980537589 4812889551147397685675399)
      ·
        refine ⟨7219334326721096528513099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812889551147397685675399 7219334326721096528513099)
        ·
          refine ⟨10829001490081644792769649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7219334326721096528513099 10829001490081644792769649)
          ·
            refine ⟨8121751117561233594577237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10829001490081644792769649 8121751117561233594577237)
            ·
              refine ⟨23794192727230176546613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8121751117561233594577237 23794192727230176546613)
              ·
                rfl

theorem cell23_3753461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 10].length) (baseStart_3753461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753461 prefixEnd_3753461 := by exact prefixLift 3753461
  have htrace : WordTrace (prefixWord ++ tailWord_3753461) baseStart_3753461 baseEnd_3753461 := by
    simpa [prefixWord, tailWord_3753461, baseEnd_3753461] using wordTrace_append hprefix tailTrace_3753461
  have hstable : (prefixWord ++ tailWord_3753461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753461).length < 2 ^ (prefixWord ++ tailWord_3753461).sum := by decide
  have hdescent : baseEnd_3753461 < baseStart_3753461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753485 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3753485 : Nat := 118140960795 + 3753485 * 2 ^ 59
def prefixEnd_3753485 : Nat := 4983230072969 + 3 ^ 40 * 3753485 * 2
def baseEnd_3753485 : Nat := 1927341934441352206375543

theorem tailTrace_3753485 : CollatzResearch.WordTrace tailWord_3753485 prefixEnd_3753485 1927341934441352206375543 := by
  unfold tailWord_3753485
  simp only [CollatzResearch.WordTrace]
  refine ⟨136900844806772364046973909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91267229871181576031315939 136900844806772364046973909)
  ·
    refine ⟨3208613550158727282350951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 136900844806772364046973909 3208613550158727282350951)
    ·
      refine ⟨4812920325238090923526427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3208613550158727282350951 4812920325238090923526427)
      ·
        refine ⟨7219380487857136385289641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812920325238090923526427 7219380487857136385289641)
        ·
          refine ⟨5414535365892852288967231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7219380487857136385289641 5414535365892852288967231)
          ·
            refine ⟨8121803048839278433450847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414535365892852288967231 8121803048839278433450847)
            ·
              refine ⟨12182704573258917650176271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8121803048839278433450847 12182704573258917650176271)
              ·
                refine ⟨18274056859888376475264407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12182704573258917650176271 18274056859888376475264407)
                ·
                  refine ⟨27411085289832564712896611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18274056859888376475264407 27411085289832564712896611)
                  ·
                    refine ⟨41116627934748847069344917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27411085289832564712896611 41116627934748847069344917)
                    ·
                      refine ⟨1927341934441352206375543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41116627934748847069344917 1927341934441352206375543)
                      ·
                        rfl

theorem cell23_3753485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3753485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753485 prefixEnd_3753485 := by exact prefixLift 3753485
  have htrace : WordTrace (prefixWord ++ tailWord_3753485) baseStart_3753485 baseEnd_3753485 := by
    simpa [prefixWord, tailWord_3753485, baseEnd_3753485] using wordTrace_append hprefix tailTrace_3753485
  have hstable : (prefixWord ++ tailWord_3753485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753485).length < 2 ^ (prefixWord ++ tailWord_3753485).sum := by decide
  have hdescent : baseEnd_3753485 < baseStart_3753485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753492 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3753492 : Nat := 118140960795 + 3753492 * 2 ^ 59
def prefixEnd_3753492 : Nat := 4983230072969 + 3 ^ 40 * 3753492 * 2
def baseEnd_3753492 : Nat := 1927345528805933678988011

theorem tailTrace_3753492 : CollatzResearch.WordTrace tailWord_3753492 prefixEnd_3753492 1927345528805933678988011 := by
  unfold tailWord_3753492
  simp only [CollatzResearch.WordTrace]
  refine ⟨68450550058873502121239365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91267400078498002828319153 68450550058873502121239365)
  ·
    refine ⟨12834478136038781647732381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68450550058873502121239365 12834478136038781647732381)
    ·
      refine ⟨4812929301014543117899643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12834478136038781647732381 4812929301014543117899643)
      ·
        refine ⟨7219393951521814676849465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812929301014543117899643 7219393951521814676849465)
        ·
          refine ⟨5414545463641361007637099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7219393951521814676849465 5414545463641361007637099)
          ·
            refine ⟨8121818195462041511455649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414545463641361007637099 8121818195462041511455649)
            ·
              refine ⟨6091363646596531133591737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8121818195462041511455649 6091363646596531133591737)
              ·
                refine ⟨4568522734947398350193803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6091363646596531133591737 4568522734947398350193803)
                ·
                  refine ⟨6852784102421097525290705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568522734947398350193803 6852784102421097525290705)
                  ·
                    refine ⟨5139588076815823143968029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6852784102421097525290705 5139588076815823143968029)
                    ·
                      refine ⟨1927345528805933678988011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5139588076815823143968029 1927345528805933678988011)
                      ·
                        rfl

theorem cell23_3753492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3753492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753492 prefixEnd_3753492 := by exact prefixLift 3753492
  have htrace : WordTrace (prefixWord ++ tailWord_3753492) baseStart_3753492 baseEnd_3753492 := by
    simpa [prefixWord, tailWord_3753492, baseEnd_3753492] using wordTrace_append hprefix tailTrace_3753492
  have hstable : (prefixWord ++ tailWord_3753492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753492).length < 2 ^ (prefixWord ++ tailWord_3753492).sum := by decide
  have hdescent : baseEnd_3753492 < baseStart_3753492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753549 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_3753549 : Nat := 118140960795 + 3753549 * 2 ^ 59
def prefixEnd_3753549 : Nat := 4983230072969 + 3 ^ 40 * 3753549 * 2
def baseEnd_3753549 : Nat := 1927374797203239955975249

theorem tailTrace_3753549 : CollatzResearch.WordTrace tailWord_3753549 prefixEnd_3753549 1927374797203239955975249 := by
  unfold tailWord_3753549
  simp only [CollatzResearch.WordTrace]
  refine ⟨136903179078540502977303701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91268786052360335318202467 136903179078540502977303701)
  ·
    refine ⟨6417336519306586077061111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136903179078540502977303701 6417336519306586077061111)
    ·
      refine ⟨9626004778959879115591667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6417336519306586077061111 9626004778959879115591667)
      ·
        refine ⟨14439007168439818673387501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626004778959879115591667 14439007168439818673387501)
        ·
          refine ⟨5414627688164932002520313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14439007168439818673387501 5414627688164932002520313)
          ·
            refine ⟨4060970766123699001890235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5414627688164932002520313 4060970766123699001890235)
            ·
              refine ⟨6091456149185548502835353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060970766123699001890235 6091456149185548502835353)
              ·
                refine ⟨4568592111889161377126515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6091456149185548502835353 4568592111889161377126515)
                ·
                  refine ⟨6852888167833742065689773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568592111889161377126515 6852888167833742065689773)
                  ·
                    refine ⟨2569833062937653274633665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6852888167833742065689773 2569833062937653274633665)
                    ·
                      refine ⟨1927374797203239955975249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569833062937653274633665 1927374797203239955975249)
                      ·
                        rfl

theorem cell23_3753549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_3753549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753549 prefixEnd_3753549 := by exact prefixLift 3753549
  have htrace : WordTrace (prefixWord ++ tailWord_3753549) baseStart_3753549 baseEnd_3753549 := by
    simpa [prefixWord, tailWord_3753549, baseEnd_3753549] using wordTrace_append hprefix tailTrace_3753549
  have hstable : (prefixWord ++ tailWord_3753549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753549).length < 2 ^ (prefixWord ++ tailWord_3753549).sum := by decide
  have hdescent : baseEnd_3753549 < baseStart_3753549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753645 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3753645 : Nat := 118140960795 + 3753645 * 2 ^ 59
def prefixEnd_3753645 : Nat := 4983230072969 + 3 ^ 40 * 3753645 * 2
def baseEnd_3753645 : Nat := 642474697115357193458269

theorem tailTrace_3753645 : CollatzResearch.WordTrace tailWord_3753645 prefixEnd_3753645 642474697115357193458269 := by
  unfold tailWord_3753645
  simp only [CollatzResearch.WordTrace]
  refine ⟨136906680486192711372798389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91271120324128474248532259 136906680486192711372798389)
  ·
    refine ⟨12835001295580566691199849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136906680486192711372798389 12835001295580566691199849)
    ·
      refine ⟨9626250971685425018399887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12835001295580566691199849 9626250971685425018399887)
      ·
        refine ⟨14439376457528137527599831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626250971685425018399887 14439376457528137527599831)
        ·
          refine ⟨21659064686292206291399747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14439376457528137527599831 21659064686292206291399747)
          ·
            refine ⟨32488597029438309437099621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21659064686292206291399747 32488597029438309437099621)
            ·
              refine ⟨6091611943019683019456179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32488597029438309437099621 6091611943019683019456179)
              ·
                refine ⟨9137417914529524529184269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091611943019683019456179 9137417914529524529184269)
                ·
                  refine ⟨3426531717948571698444101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9137417914529524529184269 3426531717948571698444101)
                  ·
                    refine ⟨642474697115357193458269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3426531717948571698444101 642474697115357193458269)
                    ·
                      rfl

theorem cell23_3753645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3753645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753645 prefixEnd_3753645 := by exact prefixLift 3753645
  have htrace : WordTrace (prefixWord ++ tailWord_3753645) baseStart_3753645 baseEnd_3753645 := by
    simpa [prefixWord, tailWord_3753645, baseEnd_3753645] using wordTrace_append hprefix tailTrace_3753645
  have hstable : (prefixWord ++ tailWord_3753645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753645).length < 2 ^ (prefixWord ++ tailWord_3753645).sum := by decide
  have hdescent : baseEnd_3753645 < baseStart_3753645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753661 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3753661 : Nat := 118140960795 + 3753661 * 2 ^ 59
def prefixEnd_3753661 : Nat := 4983230072969 + 3 ^ 40 * 3753661 * 2
def baseEnd_3753661 : Nat := 1927432307036543517774733

theorem tailTrace_3753661 : CollatzResearch.WordTrace tailWord_3753661 prefixEnd_3753661 1927432307036543517774733 := by
  unfold tailWord_3753661
  simp only [CollatzResearch.WordTrace]
  refine ⟨136907264054134746105380837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91271509369423164070253891 136907264054134746105380837)
  ·
    refine ⟨25670112010150264894758907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136907264054134746105380837 25670112010150264894758907)
    ·
      refine ⟨38505168015225397342138361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25670112010150264894758907 38505168015225397342138361)
      ·
        refine ⟨28878876011419048006603771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38505168015225397342138361 28878876011419048006603771)
        ·
          refine ⟨43318314017128572009905657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28878876011419048006603771 43318314017128572009905657)
          ·
            refine ⟨32488735512846429007429243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43318314017128572009905657 32488735512846429007429243)
            ·
              refine ⟨48733103269269643511143865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32488735512846429007429243 48733103269269643511143865)
              ·
                refine ⟨36549827451952232633357899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48733103269269643511143865 36549827451952232633357899)
                ·
                  refine ⟨54824741177928348950036849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36549827451952232633357899 54824741177928348950036849)
                  ·
                    refine ⟨41118555883446261712527637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54824741177928348950036849 41118555883446261712527637)
                    ·
                      refine ⟨1927432307036543517774733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41118555883446261712527637 1927432307036543517774733)
                      ·
                        rfl

theorem cell23_3753661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3753661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753661 prefixEnd_3753661 := by exact prefixLift 3753661
  have htrace : WordTrace (prefixWord ++ tailWord_3753661) baseStart_3753661 baseEnd_3753661 := by
    simpa [prefixWord, tailWord_3753661, baseEnd_3753661] using wordTrace_append hprefix tailTrace_3753661
  have hstable : (prefixWord ++ tailWord_3753661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753661).length < 2 ^ (prefixWord ++ tailWord_3753661).sum := by decide
  have hdescent : baseEnd_3753661 < baseStart_3753661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753668 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3753668 : Nat := 118140960795 + 3753668 * 2 ^ 59
def prefixEnd_3753668 : Nat := 4983230072969 + 3 ^ 40 * 3753668 * 2
def baseEnd_3753668 : Nat := 1927435901401124990387201

theorem tailTrace_3753668 : CollatzResearch.WordTrace tailWord_3753668 prefixEnd_3753668 1927435901401124990387201 := by
  unfold tailWord_3753668
  simp only [CollatzResearch.WordTrace]
  refine ⟨68453759682554693150442829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91271679576739590867257105 68453759682554693150442829)
  ·
    refine ⟨25670159880958009931416061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68453759682554693150442829 25670159880958009931416061)
    ·
      refine ⟨9626309955359253724281023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25670159880958009931416061 9626309955359253724281023)
      ·
        refine ⟨14439464933038880586421535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626309955359253724281023 14439464933038880586421535)
        ·
          refine ⟨21659197399558320879632303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14439464933038880586421535 21659197399558320879632303)
          ·
            refine ⟨32488796099337481319448455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21659197399558320879632303 32488796099337481319448455)
            ·
              refine ⟨48733194149006221979172683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32488796099337481319448455 48733194149006221979172683)
              ·
                refine ⟨73099791223509332968759025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48733194149006221979172683 73099791223509332968759025)
                ·
                  refine ⟨54824843417631999726569269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73099791223509332968759025 54824843417631999726569269)
                  ·
                    refine ⟨5139829070402999974365869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54824843417631999726569269 5139829070402999974365869)
                    ·
                      refine ⟨1927435901401124990387201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5139829070402999974365869 1927435901401124990387201)
                      ·
                        rfl

theorem cell23_3753668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3753668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753668 prefixEnd_3753668 := by exact prefixLift 3753668
  have htrace : WordTrace (prefixWord ++ tailWord_3753668) baseStart_3753668 baseEnd_3753668 := by
    simpa [prefixWord, tailWord_3753668, baseEnd_3753668] using wordTrace_append hprefix tailTrace_3753668
  have hstable : (prefixWord ++ tailWord_3753668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753668).length < 2 ^ (prefixWord ++ tailWord_3753668).sum := by decide
  have hdescent : baseEnd_3753668 < baseStart_3753668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753688 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 1, 5]
def baseStart_3753688 : Nat := 118140960795 + 3753688 * 2 ^ 59
def prefixEnd_3753688 : Nat := 4983230072969 + 3 ^ 40 * 3753688 * 2
def baseEnd_3753688 : Nat := 642482057004738304045703

theorem tailTrace_3753688 : CollatzResearch.WordTrace tailWord_3753688 prefixEnd_3753688 642482057004738304045703 := by
  unfold tailWord_3753688
  simp only [CollatzResearch.WordTrace]
  refine ⟨68454124412518464858306859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91272165883357953144409145 68454124412518464858306859)
  ·
    refine ⟨102681186618777697287460289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68454124412518464858306859 102681186618777697287460289)
    ·
      refine ⟨77010889964083272965595217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102681186618777697287460289 77010889964083272965595217)
      ·
        refine ⟨57758167473062454724196413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77010889964083272965595217 57758167473062454724196413)
        ·
          refine ⟨21659312802398420521573655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57758167473062454724196413 21659312802398420521573655)
          ·
            refine ⟨32488969203597630782360483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21659312802398420521573655 32488969203597630782360483)
            ·
              refine ⟨48733453805396446173540725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32488969203597630782360483 48733453805396446173540725)
              ·
                refine ⟨4568761294255916828769443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48733453805396446173540725 4568761294255916828769443)
                ·
                  refine ⟨6853141941383875243154165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568761294255916828769443 6853141941383875243154165)
                  ·
                    refine ⟨642482057004738304045703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6853141941383875243154165 642482057004738304045703)
                    ·
                      rfl

theorem cell23_3753688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_3753688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753688 prefixEnd_3753688 := by exact prefixLift 3753688
  have htrace : WordTrace (prefixWord ++ tailWord_3753688) baseStart_3753688 baseEnd_3753688 := by
    simpa [prefixWord, tailWord_3753688, baseEnd_3753688] using wordTrace_append hprefix tailTrace_3753688
  have hstable : (prefixWord ++ tailWord_3753688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753688).length < 2 ^ (prefixWord ++ tailWord_3753688).sum := by decide
  have hdescent : baseEnd_3753688 < baseStart_3753688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753695 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 2, 3, 2]
def baseStart_3753695 : Nat := 118140960795 + 3753695 * 2 ^ 59
def prefixEnd_3753695 : Nat := 4983230072969 + 3 ^ 40 * 3753695 * 2
def baseEnd_3753695 : Nat := 1927449765378796384749577

theorem tailTrace_3753695 : CollatzResearch.WordTrace tailWord_3753695 prefixEnd_3753695 1927449765378796384749577 := by
  unfold tailWord_3753695
  simp only [CollatzResearch.WordTrace]
  refine ⟨136908504136011569912118539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91272336090674379941412359 136908504136011569912118539)
  ·
    refine ⟨205362756204017354868177809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136908504136011569912118539 205362756204017354868177809)
    ·
      refine ⟨154022067153013016151133357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205362756204017354868177809 154022067153013016151133357)
      ·
        refine ⟨57758275182379881056675009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154022067153013016151133357 57758275182379881056675009)
        ·
          refine ⟨43318706386784910792506257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57758275182379881056675009 43318706386784910792506257)
          ·
            refine ⟨32489029790088683094379693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43318706386784910792506257 32489029790088683094379693)
            ·
              refine ⟨12183386171283256160392385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32489029790088683094379693 12183386171283256160392385)
              ·
                refine ⟨9137539628462442120294289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12183386171283256160392385 9137539628462442120294289)
                ·
                  refine ⟨6853154721346831590220717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9137539628462442120294289 6853154721346831590220717)
                  ·
                    refine ⟨2569933020505061846332769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6853154721346831590220717 2569933020505061846332769)
                    ·
                      refine ⟨1927449765378796384749577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569933020505061846332769 1927449765378796384749577)
                      ·
                        rfl

theorem cell23_3753695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_3753695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753695 prefixEnd_3753695 := by exact prefixLift 3753695
  have htrace : WordTrace (prefixWord ++ tailWord_3753695) baseStart_3753695 baseEnd_3753695 := by
    simpa [prefixWord, tailWord_3753695, baseEnd_3753695] using wordTrace_append hprefix tailTrace_3753695
  have hstable : (prefixWord ++ tailWord_3753695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753695).length < 2 ^ (prefixWord ++ tailWord_3753695).sum := by decide
  have hdescent : baseEnd_3753695 < baseStart_3753695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753728 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 3]
def baseStart_3753728 : Nat := 118140960795 + 3753728 * 2 ^ 59
def prefixEnd_3753728 : Nat := 4983230072969 + 3 ^ 40 * 3753728 * 2
def baseEnd_3753728 : Nat := 1927466710240394755636925

theorem tailTrace_3753728 : CollatzResearch.WordTrace tailWord_3753728 prefixEnd_3753728 1927466710240394755636925 := by
  unfold tailWord_3753728
  simp only [CollatzResearch.WordTrace]
  refine ⟨68454853872446008274034919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91273138496594677698713225 68454853872446008274034919)
  ·
    refine ⟨102682280808669012411052379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68454853872446008274034919 102682280808669012411052379)
    ·
      refine ⟨154023421213003518616578569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102682280808669012411052379 154023421213003518616578569)
      ·
        refine ⟨115517565909752638962433927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154023421213003518616578569 115517565909752638962433927)
        ·
          refine ⟨173276348864628958443650891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115517565909752638962433927 173276348864628958443650891)
          ·
            refine ⟨259914523296943437665476337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173276348864628958443650891 259914523296943437665476337)
            ·
              refine ⟨194935892472707578249107253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259914523296943437665476337 194935892472707578249107253)
              ·
                refine ⟨18275239919316335460853805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194935892472707578249107253 18275239919316335460853805)
                ·
                  refine ⟨6853214969743625797820177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18275239919316335460853805 6853214969743625797820177)
                  ·
                    refine ⟨5139911227307719348365133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6853214969743625797820177 5139911227307719348365133)
                    ·
                      refine ⟨1927466710240394755636925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5139911227307719348365133 1927466710240394755636925)
                      ·
                        rfl

theorem cell23_3753728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_3753728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753728 prefixEnd_3753728 := by exact prefixLift 3753728
  have htrace : WordTrace (prefixWord ++ tailWord_3753728) baseStart_3753728 baseEnd_3753728 := by
    simpa [prefixWord, tailWord_3753728, baseEnd_3753728] using wordTrace_append hprefix tailTrace_3753728
  have hstable : (prefixWord ++ tailWord_3753728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753728).length < 2 ^ (prefixWord ++ tailWord_3753728).sum := by decide
  have hdescent : baseEnd_3753728 < baseStart_3753728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753731 : List Nat := [1, 1, 1, 3, 2, 2, 4, 9]
def baseStart_3753731 : Nat := 118140960795 + 3753731 * 2 ^ 59
def prefixEnd_3753731 : Nat := 4983230072969 + 3 ^ 40 * 3753731 * 2
def baseEnd_3753731 : Nat := 71387712988235490514793

theorem tailTrace_3753731 : CollatzResearch.WordTrace tailWord_3753731 prefixEnd_3753731 71387712988235490514793 := by
  unfold tailWord_3753731
  simp only [CollatzResearch.WordTrace]
  refine ⟨136909817163881148060429047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91273211442587432040286031 136909817163881148060429047)
  ·
    refine ⟨205364725745821722090643571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136909817163881148060429047 205364725745821722090643571)
    ·
      refine ⟨308047088618732583135965357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205364725745821722090643571 308047088618732583135965357)
      ·
        refine ⟨115517658232024718675987009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308047088618732583135965357 115517658232024718675987009)
        ·
          refine ⟨86638243674018539006990257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115517658232024718675987009 86638243674018539006990257)
          ·
            refine ⟨64978682755513904255242693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86638243674018539006990257 64978682755513904255242693)
            ·
              refine ⟨12183503016658857047858005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64978682755513904255242693 12183503016658857047858005)
              ·
                refine ⟨71387712988235490514793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12183503016658857047858005 71387712988235490514793)
                ·
                  rfl

theorem cell23_3753731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 9].length) (baseStart_3753731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753731 prefixEnd_3753731 := by exact prefixLift 3753731
  have htrace : WordTrace (prefixWord ++ tailWord_3753731) baseStart_3753731 baseEnd_3753731 := by
    simpa [prefixWord, tailWord_3753731, baseEnd_3753731] using wordTrace_append hprefix tailTrace_3753731
  have hstable : (prefixWord ++ tailWord_3753731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753731).length < 2 ^ (prefixWord ++ tailWord_3753731).sum := by decide
  have hdescent : baseEnd_3753731 < baseStart_3753731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753735 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 1, 6]
def baseStart_3753735 : Nat := 118140960795 + 3753735 * 2 ^ 59
def prefixEnd_3753735 : Nat := 4983230072969 + 3 ^ 40 * 3753735 * 2
def baseEnd_3753735 : Nat := 642490101534992076083131

theorem tailTrace_3753735 : CollatzResearch.WordTrace tailWord_3753735 prefixEnd_3753735 642490101534992076083131 := by
  unfold tailWord_3753735
  simp only [CollatzResearch.WordTrace]
  refine ⟨136909963055866656743574659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91273308703911104495716439 136909963055866656743574659)
  ·
    refine ⟨205364944583799985115361989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136909963055866656743574659 205364944583799985115361989)
    ·
      refine ⟨38505927109462497209130373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205364944583799985115361989 38505927109462497209130373)
      ·
        refine ⟨7219861333024218226711945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38505927109462497209130373 7219861333024218226711945)
        ·
          refine ⟨5414895999768163670033959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7219861333024218226711945 5414895999768163670033959)
          ·
            refine ⟨8122343999652245505050939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414895999768163670033959 8122343999652245505050939)
            ·
              refine ⟨12183515999478368257576409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122343999652245505050939 12183515999478368257576409)
              ·
                refine ⟨9137636999608776193182307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12183515999478368257576409 9137636999608776193182307)
                ·
                  refine ⟨13706455499413164289773461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137636999608776193182307 13706455499413164289773461)
                  ·
                    refine ⟨642490101534992076083131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13706455499413164289773461 642490101534992076083131)
                    ·
                      rfl

theorem cell23_3753735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_3753735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753735 prefixEnd_3753735 := by exact prefixLift 3753735
  have htrace : WordTrace (prefixWord ++ tailWord_3753735) baseStart_3753735 baseEnd_3753735 := by
    simpa [prefixWord, tailWord_3753735, baseEnd_3753735] using wordTrace_append hprefix tailTrace_3753735
  have hstable : (prefixWord ++ tailWord_3753735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753735).length < 2 ^ (prefixWord ++ tailWord_3753735).sum := by decide
  have hdescent : baseEnd_3753735 < baseStart_3753735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753738 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_3753738 : Nat := 118140960795 + 3753738 * 2 ^ 59
def prefixEnd_3753738 : Nat := 4983230072969 + 3 ^ 40 * 3753738 * 2
def baseEnd_3753738 : Nat := 1927471845046939716511879

theorem tailTrace_3753738 : CollatzResearch.WordTrace tailWord_3753738 prefixEnd_3753738 1927471845046939716511879 := by
  unfold tailWord_3753738
  simp only [CollatzResearch.WordTrace]
  refine ⟨34227518118713947063983467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91273381649903858837289245 34227518118713947063983467)
  ·
    refine ⟨51341277178070920595975201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34227518118713947063983467 51341277178070920595975201)
    ·
      refine ⟨38505957883553190446981401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51341277178070920595975201 38505957883553190446981401)
      ·
        refine ⟨28879468412664892835236051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38505957883553190446981401 28879468412664892835236051)
        ·
          refine ⟨43319202618997339252854077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28879468412664892835236051 43319202618997339252854077)
          ·
            refine ⟨16244700982124002219820279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43319202618997339252854077 16244700982124002219820279)
            ·
              refine ⟨24367051473186003329730419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16244700982124002219820279 24367051473186003329730419)
              ·
                refine ⟨36550577209779004994595629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24367051473186003329730419 36550577209779004994595629)
                ·
                  refine ⟨13706466453667126872973361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36550577209779004994595629 13706466453667126872973361)
                  ·
                    refine ⟨10279849840250345154730021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13706466453667126872973361 10279849840250345154730021)
                    ·
                      refine ⟨1927471845046939716511879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10279849840250345154730021 1927471845046939716511879)
                      ·
                        rfl

theorem cell23_3753738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_3753738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753738 prefixEnd_3753738 := by exact prefixLift 3753738
  have htrace : WordTrace (prefixWord ++ tailWord_3753738) baseStart_3753738 baseEnd_3753738 := by
    simpa [prefixWord, tailWord_3753738, baseEnd_3753738] using wordTrace_append hprefix tailTrace_3753738
  have hstable : (prefixWord ++ tailWord_3753738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753738).length < 2 ^ (prefixWord ++ tailWord_3753738).sum := by decide
  have hdescent : baseEnd_3753738 < baseStart_3753738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753759 : List Nat := [1, 1, 2, 4, 2, 1, 3, 4, 1, 2, 2]
def baseStart_3753759 : Nat := 118140960795 + 3753759 * 2 ^ 59
def prefixEnd_3753759 : Nat := 4983230072969 + 3 ^ 40 * 3753759 * 2
def baseEnd_3753759 : Nat := 1927482628140684134349283

theorem tailTrace_3753759 : CollatzResearch.WordTrace tailWord_3753759 prefixEnd_3753759 1927482628140684134349283 := by
  unfold tailWord_3753759
  simp only [CollatzResearch.WordTrace]
  refine ⟨136910838407779708842448331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91273892271853139228298887 136910838407779708842448331)
  ·
    refine ⟨205366257611669563263672497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136910838407779708842448331 205366257611669563263672497)
    ·
      refine ⟨154024693208752172447754373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205366257611669563263672497 154024693208752172447754373)
      ·
        refine ⟨28879629976641032333953945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154024693208752172447754373 28879629976641032333953945)
        ·
          refine ⟨21659722482480774250465459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28879629976641032333953945 21659722482480774250465459)
          ·
            refine ⟨32489583723721161375698189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21659722482480774250465459 32489583723721161375698189)
            ·
              refine ⟨12183593896395435515886821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32489583723721161375698189 12183593896395435515886821)
              ·
                refine ⟨2284423855574144159228779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12183593896395435515886821 2284423855574144159228779)
                ·
                  refine ⟨3426635783361216238843169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284423855574144159228779 3426635783361216238843169)
                  ·
                    refine ⟨2569976837520912179132377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3426635783361216238843169 2569976837520912179132377)
                    ·
                      refine ⟨1927482628140684134349283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2569976837520912179132377 1927482628140684134349283)
                      ·
                        rfl

theorem cell23_3753759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_3753759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753759 prefixEnd_3753759 := by exact prefixLift 3753759
  have htrace : WordTrace (prefixWord ++ tailWord_3753759) baseStart_3753759 baseEnd_3753759 := by
    simpa [prefixWord, tailWord_3753759, baseEnd_3753759] using wordTrace_append hprefix tailTrace_3753759
  have hstable : (prefixWord ++ tailWord_3753759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753759).length < 2 ^ (prefixWord ++ tailWord_3753759).sum := by decide
  have hdescent : baseEnd_3753759 < baseStart_3753759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753782 : List Nat := [5, 1, 2, 2, 1, 2, 3, 7]
def baseStart_3753782 : Nat := 118140960795 + 3753782 * 2 ^ 59
def prefixEnd_3753782 : Nat := 4983230072969 + 3 ^ 40 * 3753782 * 2
def baseEnd_3753782 : Nat := 71388682896138427568951

theorem tailTrace_3753782 : CollatzResearch.WordTrace tailWord_3753782 prefixEnd_3753782 71388682896138427568951 := by
  unfold tailWord_3753782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8556979830418523985658475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91274451524464255847023733 8556979830418523985658475)
  ·
    refine ⟨12835469745627785978487713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8556979830418523985658475 12835469745627785978487713)
    ·
      refine ⟨9626602309220839483865785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12835469745627785978487713 9626602309220839483865785)
      ·
        refine ⟨7219951731915629612899339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9626602309220839483865785 7219951731915629612899339)
        ·
          refine ⟨10829927597873444419349009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7219951731915629612899339 10829927597873444419349009)
          ·
            refine ⟨8122445698405083314511757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10829927597873444419349009 8122445698405083314511757)
            ·
              refine ⟨3045917136901906242941909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8122445698405083314511757 3045917136901906242941909)
              ·
                refine ⟨71388682896138427568951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3045917136901906242941909 71388682896138427568951)
                ·
                  rfl

theorem cell23_3753782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_3753782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753782 prefixEnd_3753782 := by exact prefixLift 3753782
  have htrace : WordTrace (prefixWord ++ tailWord_3753782) baseStart_3753782 baseEnd_3753782 := by
    simpa [prefixWord, tailWord_3753782, baseEnd_3753782] using wordTrace_append hprefix tailTrace_3753782
  have hstable : (prefixWord ++ tailWord_3753782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753782).length < 2 ^ (prefixWord ++ tailWord_3753782).sum := by decide
  have hdescent : baseEnd_3753782 < baseStart_3753782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753802 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_3753802 : Nat := 118140960795 + 3753802 * 2 ^ 59
def prefixEnd_3753802 : Nat := 4983230072969 + 3 ^ 40 * 3753802 * 2
def baseEnd_3753802 : Nat := 1927504707808827466111585

theorem tailTrace_3753802 : CollatzResearch.WordTrace tailWord_3753802 prefixEnd_3753802 1927504707808827466111585 := by
  unfold tailWord_3753802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34228101686655981796565915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91274937831082618124175773 34228101686655981796565915)
  ·
    refine ⟨51342152529983972694848873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34228101686655981796565915 51342152529983972694848873)
    ·
      refine ⟨38506614397487979521136655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51342152529983972694848873 38506614397487979521136655)
      ·
        refine ⟨57759921596231969281704983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38506614397487979521136655 57759921596231969281704983)
        ·
          refine ⟨86639882394347953922557475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57759921596231969281704983 86639882394347953922557475)
          ·
            refine ⟨129959823591521930883836213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86639882394347953922557475 129959823591521930883836213)
            ·
              refine ⟨12183733461705181020359645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129959823591521930883836213 12183733461705181020359645)
              ·
                refine ⟨4568900048139442882634867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12183733461705181020359645 4568900048139442882634867)
                ·
                  refine ⟨6853350072209164323952301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568900048139442882634867 6853350072209164323952301)
                  ·
                    refine ⟨2570006277078436621482113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6853350072209164323952301 2570006277078436621482113)
                    ·
                      refine ⟨1927504707808827466111585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2570006277078436621482113 1927504707808827466111585)
                      ·
                        rfl

theorem cell23_3753802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_3753802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753802 prefixEnd_3753802 := by exact prefixLift 3753802
  have htrace : WordTrace (prefixWord ++ tailWord_3753802) baseStart_3753802 baseEnd_3753802 := by
    simpa [prefixWord, tailWord_3753802, baseEnd_3753802] using wordTrace_append hprefix tailTrace_3753802
  have hstable : (prefixWord ++ tailWord_3753802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753802).length < 2 ^ (prefixWord ++ tailWord_3753802).sum := by decide
  have hdescent : baseEnd_3753802 < baseStart_3753802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753809 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 3]
def baseStart_3753809 : Nat := 118140960795 + 3753809 * 2 ^ 59
def prefixEnd_3753809 : Nat := 4983230072969 + 3 ^ 40 * 3753809 * 2
def baseEnd_3753809 : Nat := 1927508302173408938724053

theorem tailTrace_3753809 : CollatzResearch.WordTrace tailWord_3753809 prefixEnd_3753809 1927508302173408938724053 := by
  unfold tailWord_3753809
  simp only [CollatzResearch.WordTrace]
  refine ⟨136912662057598567381768481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91275108038399044921178987 136912662057598567381768481)
  ·
    refine ⟨102684496543198925536326361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136912662057598567381768481 102684496543198925536326361)
    ·
      refine ⟨77013372407399194152244771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102684496543198925536326361 77013372407399194152244771)
      ·
        refine ⟨115520058611098791228367157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77013372407399194152244771 115520058611098791228367157)
        ·
          refine ⟨10830005494790511677659421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115520058611098791228367157 10830005494790511677659421)
          ·
            refine ⟨4061252060546441879122283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10830005494790511677659421 4061252060546441879122283)
            ·
              refine ⟨6091878090819662818683425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061252060546441879122283 6091878090819662818683425)
              ·
                refine ⟨4568908568114747114012569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6091878090819662818683425 4568908568114747114012569)
                ·
                  refine ⟨3426681426086060335509427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4568908568114747114012569 3426681426086060335509427)
                  ·
                    refine ⟨5140022139129090503264141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3426681426086060335509427 5140022139129090503264141)
                    ·
                      refine ⟨1927508302173408938724053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5140022139129090503264141 1927508302173408938724053)
                      ·
                        rfl

theorem cell23_3753809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_3753809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753809 prefixEnd_3753809 := by exact prefixLift 3753809
  have htrace : WordTrace (prefixWord ++ tailWord_3753809) baseStart_3753809 baseEnd_3753809 := by
    simpa [prefixWord, tailWord_3753809, baseEnd_3753809] using wordTrace_append hprefix tailTrace_3753809
  have hstable : (prefixWord ++ tailWord_3753809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753809).length < 2 ^ (prefixWord ++ tailWord_3753809).sum := by decide
  have hdescent : baseEnd_3753809 < baseStart_3753809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753826 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_3753826 : Nat := 118140960795 + 3753826 * 2 ^ 59
def prefixEnd_3753826 : Nat := 4983230072969 + 3 ^ 40 * 3753826 * 2
def baseEnd_3753826 : Nat := 1927517031344535372211475

theorem tailTrace_3753826 : CollatzResearch.WordTrace tailWord_3753826 prefixEnd_3753826 1927517031344535372211475 := by
  unfold tailWord_3753826
  simp only [CollatzResearch.WordTrace]
  refine ⟨34228320524634244821284333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91275521399024652856758221 34228320524634244821284333)
  ·
    refine ⟨12835620196737841807981625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34228320524634244821284333 12835620196737841807981625)
    ·
      refine ⟨9626715147553381355986219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12835620196737841807981625 9626715147553381355986219)
      ·
        refine ⟨14440072721330072033979329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626715147553381355986219 14440072721330072033979329)
        ·
          refine ⟨10830054540997554025484497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14440072721330072033979329 10830054540997554025484497)
          ·
            refine ⟨8122540905748165519113373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10830054540997554025484497 8122540905748165519113373)
            ·
              refine ⟨3045952839655562069667515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8122540905748165519113373 3045952839655562069667515)
              ·
                refine ⟨4568929259483343104501273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3045952839655562069667515 4568929259483343104501273)
                ·
                  refine ⟨3426696944612507328375955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4568929259483343104501273 3426696944612507328375955)
                  ·
                    refine ⟨5140045416918760992563933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3426696944612507328375955 5140045416918760992563933)
                    ·
                      refine ⟨1927517031344535372211475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5140045416918760992563933 1927517031344535372211475)
                      ·
                        rfl

theorem cell23_3753826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_3753826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753826 prefixEnd_3753826 := by exact prefixLift 3753826
  have htrace : WordTrace (prefixWord ++ tailWord_3753826) baseStart_3753826 baseEnd_3753826 := by
    simpa [prefixWord, tailWord_3753826, baseEnd_3753826] using wordTrace_append hprefix tailTrace_3753826
  have hstable : (prefixWord ++ tailWord_3753826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753826).length < 2 ^ (prefixWord ++ tailWord_3753826).sum := by decide
  have hdescent : baseEnd_3753826 < baseStart_3753826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753925 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_3753925 : Nat := 118140960795 + 3753925 * 2 ^ 59
def prefixEnd_3753925 : Nat := 4983230072969 + 3 ^ 40 * 3753925 * 2
def baseEnd_3753925 : Nat := 1927567865929330484873519

theorem tailTrace_3753925 : CollatzResearch.WordTrace tailWord_3753925 prefixEnd_3753925 1927567865929330484873519 := by
  unfold tailWord_3753925
  simp only [CollatzResearch.WordTrace]
  refine ⟨136916892925178319192991229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91277928616785546128660819 136916892925178319192991229)
  ·
    refine ⟨51343834846941869697371711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136916892925178319192991229 51343834846941869697371711)
    ·
      refine ⟨77015752270412804546057567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51343834846941869697371711 77015752270412804546057567)
      ·
        refine ⟨115523628405619206819086351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77015752270412804546057567 115523628405619206819086351)
        ·
          refine ⟨173285442608428810228629527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115523628405619206819086351 173285442608428810228629527)
          ·
            refine ⟨259928163912643215342944291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173285442608428810228629527 259928163912643215342944291)
            ·
              refine ⟨389892245868964823014416437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259928163912643215342944291 389892245868964823014416437)
              ·
                refine ⟨36552398050215452157601541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389892245868964823014416437 36552398050215452157601541)
                ·
                  refine ⟨6853574634415397279550289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36552398050215452157601541 6853574634415397279550289)
                  ·
                    refine ⟨5140180975811547959662717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6853574634415397279550289 5140180975811547959662717)
                    ·
                      refine ⟨1927567865929330484873519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5140180975811547959662717 1927567865929330484873519)
                      ·
                        rfl

theorem cell23_3753925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_3753925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753925 prefixEnd_3753925 := by exact prefixLift 3753925
  have htrace : WordTrace (prefixWord ++ tailWord_3753925) baseStart_3753925 baseEnd_3753925 := by
    simpa [prefixWord, tailWord_3753925, baseEnd_3753925] using wordTrace_append hprefix tailTrace_3753925
  have hstable : (prefixWord ++ tailWord_3753925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753925).length < 2 ^ (prefixWord ++ tailWord_3753925).sum := by decide
  have hdescent : baseEnd_3753925 < baseStart_3753925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753949 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3753949 : Nat := 118140960795 + 3753949 * 2 ^ 59
def prefixEnd_3753949 : Nat := 4983230072969 + 3 ^ 40 * 3753949 * 2
def baseEnd_3753949 : Nat := 642526729821679463657803

theorem tailTrace_3753949 : CollatzResearch.WordTrace tailWord_3753949 prefixEnd_3753949 642526729821679463657803 := by
  unfold tailWord_3753949
  simp only [CollatzResearch.WordTrace]
  refine ⟨136917768277091371291864901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91278512184727580861243267 136917768277091371291864901)
  ·
    refine ⟨25672081551954632117224669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136917768277091371291864901 25672081551954632117224669)
    ·
      refine ⟨9627030581982987043959251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25672081551954632117224669 9627030581982987043959251)
      ·
        refine ⟨14440545872974480565938877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9627030581982987043959251 14440545872974480565938877)
        ·
          refine ⟨5415204702365430212227079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14440545872974480565938877 5415204702365430212227079)
          ·
            refine ⟨8122807053548145318340619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415204702365430212227079 8122807053548145318340619)
            ·
              refine ⟨12184210580322217977510929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122807053548145318340619 12184210580322217977510929)
              ·
                refine ⟨9138157935241663483133197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12184210580322217977510929 9138157935241663483133197)
                ·
                  refine ⟨3426809225715623806174949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9138157935241663483133197 3426809225715623806174949)
                  ·
                    refine ⟨642526729821679463657803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3426809225715623806174949 642526729821679463657803)
                    ·
                      rfl

theorem cell23_3753949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3753949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753949 prefixEnd_3753949 := by exact prefixLift 3753949
  have htrace : WordTrace (prefixWord ++ tailWord_3753949) baseStart_3753949 baseEnd_3753949 := by
    simpa [prefixWord, tailWord_3753949, baseEnd_3753949] using wordTrace_append hprefix tailTrace_3753949
  have hstable : (prefixWord ++ tailWord_3753949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753949).length < 2 ^ (prefixWord ++ tailWord_3753949).sum := by decide
  have hdescent : baseEnd_3753949 < baseStart_3753949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753966 : List Nat := [4, 1, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3753966 : Nat := 118140960795 + 3753966 * 2 ^ 59
def prefixEnd_3753966 : Nat := 4983230072969 + 3 ^ 40 * 3753966 * 2
def baseEnd_3753966 : Nat := 642529639545388274820277

theorem tailTrace_3753966 : CollatzResearch.WordTrace tailWord_3753966 prefixEnd_3753966 642529639545388274820277 := by
  unfold tailWord_3753966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17114798539753722899404219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91278925545353188796822501 17114798539753722899404219)
  ·
    refine ⟨25672197809630584349106329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17114798539753722899404219 25672197809630584349106329)
    ·
      refine ⟨19254148357222938261829747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25672197809630584349106329 19254148357222938261829747)
      ·
        refine ⟨28881222535834407392744621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19254148357222938261829747 28881222535834407392744621)
        ·
          refine ⟨10830458450937902772279233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28881222535834407392744621 10830458450937902772279233)
          ·
            refine ⟨8122843838203427079209425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10830458450937902772279233 8122843838203427079209425)
            ·
              refine ⟨6092132878652570309407069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8122843838203427079209425 6092132878652570309407069)
              ·
                refine ⟨2284549829494713866027651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6092132878652570309407069 2284549829494713866027651)
                ·
                  refine ⟨3426824744242070799041477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284549829494713866027651 3426824744242070799041477)
                  ·
                    refine ⟨642529639545388274820277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3426824744242070799041477 642529639545388274820277)
                    ·
                      rfl

theorem cell23_3753966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3753966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753966 prefixEnd_3753966 := by exact prefixLift 3753966
  have htrace : WordTrace (prefixWord ++ tailWord_3753966) baseStart_3753966 baseEnd_3753966 := by
    simpa [prefixWord, tailWord_3753966, baseEnd_3753966] using wordTrace_append hprefix tailTrace_3753966
  have hstable : (prefixWord ++ tailWord_3753966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753966).length < 2 ^ (prefixWord ++ tailWord_3753966).sum := by decide
  have hdescent : baseEnd_3753966 < baseStart_3753966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753982 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3753982 : Nat := 118140960795 + 3753982 * 2 ^ 59
def prefixEnd_3753982 : Nat := 4983230072969 + 3 ^ 40 * 3753982 * 2
def baseEnd_3753982 : Nat := 1927597134326636761860757

theorem tailTrace_3753982 : CollatzResearch.WordTrace tailWord_3753982 prefixEnd_3753982 1927597134326636761860757 := by
  unfold tailWord_3753982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17114871485746477240977025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91279314590647878618544133 17114871485746477240977025)
  ·
    refine ⟨12836153614309857930732769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17114871485746477240977025 12836153614309857930732769)
    ·
      refine ⟨9627115210732393448049577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12836153614309857930732769 9627115210732393448049577)
      ·
        refine ⟨7220336408049295086037183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9627115210732393448049577 7220336408049295086037183)
        ·
          refine ⟨10830504612073942629055775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7220336408049295086037183 10830504612073942629055775)
          ·
            refine ⟨16245756918110913943583663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10830504612073942629055775 16245756918110913943583663)
            ·
              refine ⟨24368635377166370915375495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16245756918110913943583663 24368635377166370915375495)
              ·
                refine ⟨36552953065749556373063243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24368635377166370915375495 36552953065749556373063243)
                ·
                  refine ⟨54829429598624334559594865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36552953065749556373063243 54829429598624334559594865)
                  ·
                    refine ⟨41122072198968250919696149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54829429598624334559594865 41122072198968250919696149)
                    ·
                      refine ⟨1927597134326636761860757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41122072198968250919696149 1927597134326636761860757)
                      ·
                        rfl

theorem cell23_3753982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3753982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753982 prefixEnd_3753982 := by exact prefixLift 3753982
  have htrace : WordTrace (prefixWord ++ tailWord_3753982) baseStart_3753982 baseEnd_3753982 := by
    simpa [prefixWord, tailWord_3753982, baseEnd_3753982] using wordTrace_append hprefix tailTrace_3753982
  have hstable : (prefixWord ++ tailWord_3753982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753982).length < 2 ^ (prefixWord ++ tailWord_3753982).sum := by decide
  have hdescent : baseEnd_3753982 < baseStart_3753982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753989 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 3]
def baseStart_3753989 : Nat := 118140960795 + 3753989 * 2 ^ 59
def prefixEnd_3753989 : Nat := 4983230072969 + 3 ^ 40 * 3753989 * 2
def baseEnd_3753989 : Nat := 1927600728691218234473225

theorem tailTrace_3753989 : CollatzResearch.WordTrace tailWord_3753989 prefixEnd_3753989 1927600728691218234473225 := by
  unfold tailWord_3753989
  simp only [CollatzResearch.WordTrace]
  refine ⟨136919227196946458123321021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91279484797964305415547347 136919227196946458123321021)
  ·
    refine ⟨51344710198854921796245383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136919227196946458123321021 51344710198854921796245383)
    ·
      refine ⟨77017065298282382694368075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51344710198854921796245383 77017065298282382694368075)
      ·
        refine ⟨115525597947423574041552113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77017065298282382694368075 115525597947423574041552113)
        ·
          refine ⟨86644198460567680531164085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115525597947423574041552113 86644198460567680531164085)
          ·
            refine ⟨8122893605678220049796633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86644198460567680531164085 8122893605678220049796633)
            ·
              refine ⟨6092170204258665037347475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8122893605678220049796633 6092170204258665037347475)
              ·
                refine ⟨9138255306387997556021213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092170204258665037347475 9138255306387997556021213)
                ·
                  refine ⟨3426845739895499083507955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9138255306387997556021213 3426845739895499083507955)
                  ·
                    refine ⟨5140268609843248625261933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3426845739895499083507955 5140268609843248625261933)
                    ·
                      refine ⟨1927600728691218234473225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5140268609843248625261933 1927600728691218234473225)
                      ·
                        rfl

theorem cell23_3753989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_3753989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3753989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3753989 prefixEnd_3753989 := by exact prefixLift 3753989
  have htrace : WordTrace (prefixWord ++ tailWord_3753989) baseStart_3753989 baseEnd_3753989 := by
    simpa [prefixWord, tailWord_3753989, baseEnd_3753989] using wordTrace_append hprefix tailTrace_3753989
  have hstable : (prefixWord ++ tailWord_3753989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753989).length < 2 ^ (prefixWord ++ tailWord_3753989).sum := by decide
  have hdescent : baseEnd_3753989 < baseStart_3753989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754015 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_3754015 : Nat := 118140960795 + 3754015 * 2 ^ 59
def prefixEnd_3754015 : Nat := 4983230072969 + 3 ^ 40 * 3754015 * 2
def baseEnd_3754015 : Nat := 1927614079188235132748105

theorem tailTrace_3754015 : CollatzResearch.WordTrace tailWord_3754015 prefixEnd_3754015 1927614079188235132748105 := by
  unfold tailWord_3754015
  simp only [CollatzResearch.WordTrace]
  refine ⟨136920175494852264563767499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91280116996568176375844999 136920175494852264563767499)
  ·
    refine ⟨205380263242278396845651249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136920175494852264563767499 205380263242278396845651249)
    ·
      refine ⟨154035197431708797634238437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205380263242278396845651249 154035197431708797634238437)
      ·
        refine ⟨28881599518445399556419707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154035197431708797634238437 28881599518445399556419707)
        ·
          refine ⟨43322399277668099334629561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28881599518445399556419707 43322399277668099334629561)
          ·
            refine ⟨32491799458251074500972171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43322399277668099334629561 32491799458251074500972171)
            ·
              refine ⟨48737699187376611751458257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32491799458251074500972171 48737699187376611751458257)
              ·
                refine ⟨36553274390532458813593693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48737699187376611751458257 36553274390532458813593693)
                ·
                  refine ⟨13707477896449672055097635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36553274390532458813593693 13707477896449672055097635)
                  ·
                    refine ⟨20561216844674508082646453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13707477896449672055097635 20561216844674508082646453)
                    ·
                      refine ⟨1927614079188235132748105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20561216844674508082646453 1927614079188235132748105)
                      ·
                        rfl

theorem cell23_3754015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_3754015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754015 prefixEnd_3754015 := by exact prefixLift 3754015
  have htrace : WordTrace (prefixWord ++ tailWord_3754015) baseStart_3754015 baseEnd_3754015 := by
    simpa [prefixWord, tailWord_3754015, baseEnd_3754015] using wordTrace_append hprefix tailTrace_3754015
  have hstable : (prefixWord ++ tailWord_3754015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754015).length < 2 ^ (prefixWord ++ tailWord_3754015).sum := by decide
  have hdescent : baseEnd_3754015 < baseStart_3754015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754032 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 5]
def baseStart_3754032 : Nat := 118140960795 + 3754032 * 2 ^ 59
def prefixEnd_3754032 : Nat := 4983230072969 + 3 ^ 40 * 3754032 * 2
def baseEnd_3754032 : Nat := 1927622808359361566235527

theorem tailTrace_3754032 : CollatzResearch.WordTrace tailWord_3754032 prefixEnd_3754032 1927622808359361566235527 := by
  unfold tailWord_3754032
  simp only [CollatzResearch.WordTrace]
  refine ⟨68460397767895338233568175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91280530357193784311424233 68460397767895338233568175)
  ·
    refine ⟨102690596651843007350352263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68460397767895338233568175 102690596651843007350352263)
    ·
      refine ⟨154035894977764511025528395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102690596651843007350352263 154035894977764511025528395)
      ·
        refine ⟨231053842466646766538292593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154035894977764511025528395 231053842466646766538292593)
        ·
          refine ⟨173290381849985074903719445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231053842466646766538292593 173290381849985074903719445)
          ·
            refine ⟨8122986649218050386111849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173290381849985074903719445 8122986649218050386111849)
            ·
              refine ⟨6092239986913537789583887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8122986649218050386111849 6092239986913537789583887)
              ·
                refine ⟨9138359980370306684375831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092239986913537789583887 9138359980370306684375831)
                ·
                  refine ⟨13707539970555460026563747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9138359980370306684375831 13707539970555460026563747)
                  ·
                    refine ⟨20561309955833190039845621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13707539970555460026563747 20561309955833190039845621)
                    ·
                      refine ⟨1927622808359361566235527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20561309955833190039845621 1927622808359361566235527)
                      ·
                        rfl

theorem cell23_3754032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_3754032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754032 prefixEnd_3754032 := by exact prefixLift 3754032
  have htrace : WordTrace (prefixWord ++ tailWord_3754032) baseStart_3754032 baseEnd_3754032 := by
    simpa [prefixWord, tailWord_3754032, baseEnd_3754032] using wordTrace_append hprefix tailTrace_3754032
  have hstable : (prefixWord ++ tailWord_3754032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754032).length < 2 ^ (prefixWord ++ tailWord_3754032).sum := by decide
  have hdescent : baseEnd_3754032 < baseStart_3754032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754055 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_3754055 : Nat := 118140960795 + 3754055 * 2 ^ 59
def prefixEnd_3754055 : Nat := 4983230072969 + 3 ^ 40 * 3754055 * 2
def baseEnd_3754055 : Nat := 1927634618414414976247921

theorem tailTrace_3754055 : CollatzResearch.WordTrace tailWord_3754055 prefixEnd_3754055 1927634618414414976247921 := by
  unfold tailWord_3754055
  simp only [CollatzResearch.WordTrace]
  refine ⟨136921634414707351395223619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91281089609804900930149079 136921634414707351395223619)
  ·
    refine ⟨205382451622061027092835429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136921634414707351395223619 205382451622061027092835429)
    ·
      refine ⟨38509209679136442579906643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205382451622061027092835429 38509209679136442579906643)
      ·
        refine ⟨57763814518704663869859965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38509209679136442579906643 57763814518704663869859965)
        ·
          refine ⟨21661430444514248951197487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57763814518704663869859965 21661430444514248951197487)
          ·
            refine ⟨32492145666771373426796231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21661430444514248951197487 32492145666771373426796231)
            ·
              refine ⟨48738218500157060140194347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32492145666771373426796231 48738218500157060140194347)
              ·
                refine ⟨73107327750235590210291521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48738218500157060140194347 73107327750235590210291521)
                ·
                  refine ⟨54830495812676692657718641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73107327750235590210291521 54830495812676692657718641)
                  ·
                    refine ⟨41122871859507519493288981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54830495812676692657718641 41122871859507519493288981)
                    ·
                      refine ⟨1927634618414414976247921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41122871859507519493288981 1927634618414414976247921)
                      ·
                        rfl

theorem cell23_3754055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_3754055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754055 prefixEnd_3754055 := by exact prefixLift 3754055
  have htrace : WordTrace (prefixWord ++ tailWord_3754055) baseStart_3754055 baseEnd_3754055 := by
    simpa [prefixWord, tailWord_3754055, baseEnd_3754055] using wordTrace_append hprefix tailTrace_3754055
  have hstable : (prefixWord ++ tailWord_3754055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754055).length < 2 ^ (prefixWord ++ tailWord_3754055).sum := by decide
  have hdescent : baseEnd_3754055 < baseStart_3754055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754096 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 2, 1, 3]
def baseStart_3754096 : Nat := 118140960795 + 3754096 * 2 ^ 59
def prefixEnd_3754096 : Nat := 4983230072969 + 3 ^ 40 * 3754096 * 2
def baseEnd_3754096 : Nat := 1927655671121249315835233

theorem tailTrace_3754096 : CollatzResearch.WordTrace tailWord_3754096 prefixEnd_3754096 1927655671121249315835233 := by
  unfold tailWord_3754096
  simp only [CollatzResearch.WordTrace]
  refine ⟨68461564903779407698733071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91282086538372543598310761 68461564903779407698733071)
  ·
    refine ⟨102692347355669111548099607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68461564903779407698733071 102692347355669111548099607)
    ·
      refine ⟨154038521033503667322149411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102692347355669111548099607 154038521033503667322149411)
      ·
        refine ⟨231057781550255500983224117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154038521033503667322149411 231057781550255500983224117)
        ·
          refine ⟨21661667020336453217177261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231057781550255500983224117 21661667020336453217177261)
          ·
            refine ⟨8123125132626169956441473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21661667020336453217177261 8123125132626169956441473)
            ·
              refine ⟨6092343849469627467331105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8123125132626169956441473 6092343849469627467331105)
              ·
                refine ⟨4569257887102220600498329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6092343849469627467331105 4569257887102220600498329)
                ·
                  refine ⟨3426943415326665450373747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4569257887102220600498329 3426943415326665450373747)
                  ·
                    refine ⟨5140415122989998175560621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3426943415326665450373747 5140415122989998175560621)
                    ·
                      refine ⟨1927655671121249315835233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5140415122989998175560621 1927655671121249315835233)
                      ·
                        rfl

theorem cell23_3754096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 1, 3].length) (baseStart_3754096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754096 prefixEnd_3754096 := by exact prefixLift 3754096
  have htrace : WordTrace (prefixWord ++ tailWord_3754096) baseStart_3754096 baseEnd_3754096 := by
    simpa [prefixWord, tailWord_3754096, baseEnd_3754096] using wordTrace_append hprefix tailTrace_3754096
  have hstable : (prefixWord ++ tailWord_3754096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754096).length < 2 ^ (prefixWord ++ tailWord_3754096).sum := by decide
  have hdescent : baseEnd_3754096 < baseStart_3754096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754119 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_3754119 : Nat := 118140960795 + 3754119 * 2 ^ 59
def prefixEnd_3754119 : Nat := 4983230072969 + 3 ^ 40 * 3754119 * 2
def baseEnd_3754119 : Nat := 1927667481176302725847627

theorem tailTrace_3754119 : CollatzResearch.WordTrace tailWord_3754119 prefixEnd_3754119 1927667481176302725847627 := by
  unfold tailWord_3754119
  simp only [CollatzResearch.WordTrace]
  refine ⟨136923968686475490325553411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91282645790983660217035607 136923968686475490325553411)
  ·
    refine ⟨205385953029713235488330117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136923968686475490325553411 205385953029713235488330117)
    ·
      refine ⟨38509866193071231654061897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205385953029713235488330117 38509866193071231654061897)
      ·
        refine ⟨28882399644803423740546423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38509866193071231654061897 28882399644803423740546423)
        ·
          refine ⟨43323599467205135610819635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28882399644803423740546423 43323599467205135610819635)
          ·
            refine ⟨64985399200807703416229453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43323599467205135610819635 64985399200807703416229453)
            ·
              refine ⟨24369524700302888781086045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64985399200807703416229453 24369524700302888781086045)
              ·
                refine ⟨9138571762613583292907267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24369524700302888781086045 9138571762613583292907267)
                ·
                  refine ⟨13707857643920374939360901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9138571762613583292907267 13707857643920374939360901)
                  ·
                    refine ⟨2570223308235070301130169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13707857643920374939360901 2570223308235070301130169)
                    ·
                      refine ⟨1927667481176302725847627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2570223308235070301130169 1927667481176302725847627)
                      ·
                        rfl

theorem cell23_3754119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_3754119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754119 prefixEnd_3754119 := by exact prefixLift 3754119
  have htrace : WordTrace (prefixWord ++ tailWord_3754119) baseStart_3754119 baseEnd_3754119 := by
    simpa [prefixWord, tailWord_3754119, baseEnd_3754119] using wordTrace_append hprefix tailTrace_3754119
  have hstable : (prefixWord ++ tailWord_3754119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754119).length < 2 ^ (prefixWord ++ tailWord_3754119).sum := by decide
  have hdescent : baseEnd_3754119 < baseStart_3754119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754164 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_3754164 : Nat := 118140960795 + 3754164 * 2 ^ 59
def prefixEnd_3754164 : Nat := 4983230072969 + 3 ^ 40 * 3754164 * 2
def baseEnd_3754164 : Nat := 1927690587805755049784921

theorem tailTrace_3754164 : CollatzResearch.WordTrace tailWord_3754164 prefixEnd_3754164 1927690587805755049784921 := by
  unfold tailWord_3754164
  simp only [CollatzResearch.WordTrace]
  refine ⟨68462804985656231505470773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91283739980874975340627697 68462804985656231505470773)
  ·
    refine ⟨6418387967405271703637885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68462804985656231505470773 6418387967405271703637885)
    ·
      refine ⟨2406895487776976888864207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6418387967405271703637885 2406895487776976888864207)
      ·
        refine ⟨3610343231665465333296311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406895487776976888864207 3610343231665465333296311)
        ·
          refine ⟨5415514847498197999944467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610343231665465333296311 5415514847498197999944467)
          ·
            refine ⟨8123272271247296999916701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415514847498197999944467 8123272271247296999916701)
            ·
              refine ⟨3046227101717736374968763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8123272271247296999916701 3046227101717736374968763)
              ·
                refine ⟨4569340652576604562453145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046227101717736374968763 4569340652576604562453145)
                ·
                  refine ⟨3427005489432453421839859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4569340652576604562453145 3427005489432453421839859)
                  ·
                    refine ⟨5140508234148680132759789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3427005489432453421839859 5140508234148680132759789)
                    ·
                      refine ⟨1927690587805755049784921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5140508234148680132759789 1927690587805755049784921)
                      ·
                        rfl

theorem cell23_3754164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_3754164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754164 prefixEnd_3754164 := by exact prefixLift 3754164
  have htrace : WordTrace (prefixWord ++ tailWord_3754164) baseStart_3754164 baseEnd_3754164 := by
    simpa [prefixWord, tailWord_3754164, baseEnd_3754164] using wordTrace_append hprefix tailTrace_3754164
  have hstable : (prefixWord ++ tailWord_3754164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754164).length < 2 ^ (prefixWord ++ tailWord_3754164).sum := by decide
  have hdescent : baseEnd_3754164 < baseStart_3754164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754192 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_3754192 : Nat := 118140960795 + 3754192 * 2 ^ 59
def prefixEnd_3754192 : Nat := 4983230072969 + 3 ^ 40 * 3754192 * 2
def baseEnd_3754192 : Nat := 1927704965264080940234791

theorem tailTrace_3754192 : CollatzResearch.WordTrace tailWord_3754192 prefixEnd_3754192 1927704965264080940234791 := by
  unfold tailWord_3754192
  simp only [CollatzResearch.WordTrace]
  refine ⟨68463315607605511896480415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91284420810140682528640553 68463315607605511896480415)
  ·
    refine ⟨102694973411408267844720623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68463315607605511896480415 102694973411408267844720623)
    ·
      refine ⟨154042460117112401767080935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102694973411408267844720623 154042460117112401767080935)
      ·
        refine ⟨231063690175668602650621403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154042460117112401767080935 231063690175668602650621403)
        ·
          refine ⟨346595535263502903975932105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231063690175668602650621403 346595535263502903975932105)
          ·
            refine ⟨259946651447627177981949079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346595535263502903975932105 259946651447627177981949079)
            ·
              refine ⟨389919977171440766972923619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259946651447627177981949079 389919977171440766972923619)
              ·
                refine ⟨584879965757161150459385429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389919977171440766972923619 584879965757161150459385429)
                ·
                  refine ⟨6854062098716732231945923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 584879965757161150459385429 6854062098716732231945923)
                  ·
                    refine ⟨10281093148075098347918885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6854062098716732231945923 10281093148075098347918885)
                    ·
                      refine ⟨1927704965264080940234791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10281093148075098347918885 1927704965264080940234791)
                      ·
                        rfl

theorem cell23_3754192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_3754192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754192 prefixEnd_3754192 := by exact prefixLift 3754192
  have htrace : WordTrace (prefixWord ++ tailWord_3754192) baseStart_3754192 baseEnd_3754192 := by
    simpa [prefixWord, tailWord_3754192, baseEnd_3754192] using wordTrace_append hprefix tailTrace_3754192
  have hstable : (prefixWord ++ tailWord_3754192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754192).length < 2 ^ (prefixWord ++ tailWord_3754192).sum := by decide
  have hdescent : baseEnd_3754192 < baseStart_3754192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754209 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3754209 : Nat := 118140960795 + 3754209 * 2 ^ 59
def prefixEnd_3754209 : Nat := 4983230072969 + 3 ^ 40 * 3754209 * 2
def baseEnd_3754209 : Nat := 1927713694435207373722213

theorem tailTrace_3754209 : CollatzResearch.WordTrace tailWord_3754209 prefixEnd_3754209 1927713694435207373722213 := by
  unfold tailWord_3754209
  simp only [CollatzResearch.WordTrace]
  refine ⟨136927251256149435696329681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91284834170766290464219787 136927251256149435696329681)
  ·
    refine ⟨102695438442112076772247261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136927251256149435696329681 102695438442112076772247261)
    ·
      refine ⟨38510789415792028789592723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102695438442112076772247261 38510789415792028789592723)
      ·
        refine ⟨57766184123688043184389085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38510789415792028789592723 57766184123688043184389085)
        ·
          refine ⟨21662319046383016194145907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57766184123688043184389085 21662319046383016194145907)
          ·
            refine ⟨32493478569574524291218861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21662319046383016194145907 32493478569574524291218861)
            ·
              refine ⟨12185054463590446609207073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32493478569574524291218861 12185054463590446609207073)
              ·
                refine ⟨9138790847692834956905305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12185054463590446609207073 9138790847692834956905305)
                ·
                  refine ⟨6854093135769626217678979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9138790847692834956905305 6854093135769626217678979)
                  ·
                    refine ⟨10281139703654439326518469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6854093135769626217678979 10281139703654439326518469)
                    ·
                      refine ⟨1927713694435207373722213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10281139703654439326518469 1927713694435207373722213)
                      ·
                        rfl

theorem cell23_3754209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3754209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754209 prefixEnd_3754209 := by exact prefixLift 3754209
  have htrace : WordTrace (prefixWord ++ tailWord_3754209) baseStart_3754209 baseEnd_3754209 := by
    simpa [prefixWord, tailWord_3754209, baseEnd_3754209] using wordTrace_append hprefix tailTrace_3754209
  have hstable : (prefixWord ++ tailWord_3754209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754209).length < 2 ^ (prefixWord ++ tailWord_3754209).sum := by decide
  have hdescent : baseEnd_3754209 < baseStart_3754209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754210 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 7]
def baseStart_3754210 : Nat := 118140960795 + 3754210 * 2 ^ 59
def prefixEnd_3754210 : Nat := 4983230072969 + 3 ^ 40 * 3754210 * 2
def baseEnd_3754210 : Nat := 214190467546206874423301

theorem tailTrace_3754210 : CollatzResearch.WordTrace tailWord_3754210 prefixEnd_3754210 214190467546206874423301 := by
  unfold tailWord_3754210
  simp only [CollatzResearch.WordTrace]
  refine ⟨34231821932286453216779021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91284858486097208578077389 34231821932286453216779021)
  ·
    refine ⟨12836933224607419956292133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34231821932286453216779021 12836933224607419956292133)
    ·
      refine ⟨2406924979613891241804775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12836933224607419956292133 2406924979613891241804775)
      ·
        refine ⟨3610387469420836862707163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406924979613891241804775 3610387469420836862707163)
        ·
          refine ⟨5415581204131255294060745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610387469420836862707163 5415581204131255294060745)
          ·
            refine ⟨4061685903098441470545559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5415581204131255294060745 4061685903098441470545559)
            ·
              refine ⟨6092528854647662205818339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061685903098441470545559 6092528854647662205818339)
              ·
                refine ⟨9138793281971493308727509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092528854647662205818339 9138793281971493308727509)
                ·
                  refine ⟨214190467546206874423301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9138793281971493308727509 214190467546206874423301)
                  ·
                    rfl

theorem cell23_3754210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_3754210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754210 prefixEnd_3754210 := by exact prefixLift 3754210
  have htrace : WordTrace (prefixWord ++ tailWord_3754210) baseStart_3754210 baseEnd_3754210 := by
    simpa [prefixWord, tailWord_3754210, baseEnd_3754210] using wordTrace_append hprefix tailTrace_3754210
  have hstable : (prefixWord ++ tailWord_3754210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754210).length < 2 ^ (prefixWord ++ tailWord_3754210).sum := by decide
  have hdescent : baseEnd_3754210 < baseStart_3754210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754266 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 6]
def baseStart_3754266 : Nat := 118140960795 + 3754266 * 2 ^ 59
def prefixEnd_3754266 : Nat := 4983230072969 + 3 ^ 40 * 3754266 * 2
def baseEnd_3754266 : Nat := 214193662536945961189939

theorem tailTrace_3754266 : CollatzResearch.WordTrace tailWord_3754266 prefixEnd_3754266 214193662536945961189939 := by
  unfold tailWord_3754266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34232332554235733607788663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91286220144628622954103101 34232332554235733607788663)
  ·
    refine ⟨51348498831353600411682995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34232332554235733607788663 51348498831353600411682995)
    ·
      refine ⟨77022748247030400617524493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51348498831353600411682995 77022748247030400617524493)
      ·
        refine ⟨28883530592636400231571685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77022748247030400617524493 28883530592636400231571685)
        ·
          refine ⟨5415661986119325043419691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28883530592636400231571685 5415661986119325043419691)
          ·
            refine ⟨8123492979178987565129537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415661986119325043419691 8123492979178987565129537)
            ·
              refine ⟨6092619734384240673847153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8123492979178987565129537 6092619734384240673847153)
              ·
                refine ⟨4569464800788180505385365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6092619734384240673847153 4569464800788180505385365)
                ·
                  refine ⟨214193662536945961189939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4569464800788180505385365 214193662536945961189939)
                  ·
                    rfl

theorem cell23_3754266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_3754266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754266 prefixEnd_3754266 := by exact prefixLift 3754266
  have htrace : WordTrace (prefixWord ++ tailWord_3754266) baseStart_3754266 baseEnd_3754266 := by
    simpa [prefixWord, tailWord_3754266, baseEnd_3754266] using wordTrace_append hprefix tailTrace_3754266
  have hstable : (prefixWord ++ tailWord_3754266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754266).length < 2 ^ (prefixWord ++ tailWord_3754266).sum := by decide
  have hdescent : baseEnd_3754266 < baseStart_3754266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754316 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 1, 1, 4]
def baseStart_3754316 : Nat := 118140960795 + 3754316 * 2 ^ 59
def prefixEnd_3754316 : Nat := 4983230072969 + 3 ^ 40 * 3754316 * 2
def baseEnd_3754316 : Nat := 1927768636865238455084221

theorem tailTrace_3754316 : CollatzResearch.WordTrace tailWord_3754316 prefixEnd_3754316 1927768636865238455084221 := by
  unfold tailWord_3754316
  simp only [CollatzResearch.WordTrace]
  refine ⟨68465576933380896485237401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91287435911174528646983201 68465576933380896485237401)
  ·
    refine ⟨51349182700035672363928051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68465576933380896485237401 51349182700035672363928051)
    ·
      refine ⟨77023774050053508545892077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51349182700035672363928051 77023774050053508545892077)
      ·
        refine ⟨28883915268770065704709529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77023774050053508545892077 28883915268770065704709529)
        ·
          refine ⟨21662936451577549278532147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28883915268770065704709529 21662936451577549278532147)
          ·
            refine ⟨32494404677366323917798221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21662936451577549278532147 32494404677366323917798221)
            ·
              refine ⟨12185401754012371469174333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32494404677366323917798221 12185401754012371469174333)
              ·
                refine ⟨4569525657754639300940375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12185401754012371469174333 4569525657754639300940375)
                ·
                  refine ⟨6854288486631958951410563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569525657754639300940375 6854288486631958951410563)
                  ·
                    refine ⟨10281432729947938427115845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6854288486631958951410563 10281432729947938427115845)
                    ·
                      refine ⟨1927768636865238455084221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10281432729947938427115845 1927768636865238455084221)
                      ·
                        rfl

theorem cell23_3754316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_3754316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754316 prefixEnd_3754316 := by exact prefixLift 3754316
  have htrace : WordTrace (prefixWord ++ tailWord_3754316) baseStart_3754316 baseEnd_3754316 := by
    simpa [prefixWord, tailWord_3754316, baseEnd_3754316] using wordTrace_append hprefix tailTrace_3754316
  have hstable : (prefixWord ++ tailWord_3754316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754316).length < 2 ^ (prefixWord ++ tailWord_3754316).sum := by decide
  have hdescent : baseEnd_3754316 < baseStart_3754316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754319 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 3]
def baseStart_3754319 : Nat := 118140960795 + 3754319 * 2 ^ 59
def prefixEnd_3754319 : Nat := 4983230072969 + 3 ^ 40 * 3754319 * 2
def baseEnd_3754319 : Nat := 1927770177307201943346707

theorem tailTrace_3754319 : CollatzResearch.WordTrace tailWord_3754319 prefixEnd_3754319 1927770177307201943346707 := by
  unfold tailWord_3754319
  simp only [CollatzResearch.WordTrace]
  refine ⟨136931263285750924482834011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91287508857167282988556007 136931263285750924482834011)
  ·
    refine ⟨205396894928626386724251017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136931263285750924482834011 205396894928626386724251017)
    ·
      refine ⟨154047671196469790043188263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205396894928626386724251017 154047671196469790043188263)
      ·
        refine ⟨231071506794704685064782395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154047671196469790043188263 231071506794704685064782395)
        ·
          refine ⟨346607260192057027597173593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231071506794704685064782395 346607260192057027597173593)
          ·
            refine ⟨259955445144042770697880195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346607260192057027597173593 259955445144042770697880195)
            ·
              refine ⟨389933167716064156046820293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259955445144042770697880195 389933167716064156046820293)
              ·
                refine ⟨73112468946762029258778805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389933167716064156046820293 73112468946762029258778805)
                ·
                  refine ⟨6854293963758940243010513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73112468946762029258778805 6854293963758940243010513)
                  ·
                    refine ⟨5140720472819205182257885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6854293963758940243010513 5140720472819205182257885)
                    ·
                      refine ⟨1927770177307201943346707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5140720472819205182257885 1927770177307201943346707)
                      ·
                        rfl

theorem cell23_3754319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_3754319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754319 prefixEnd_3754319 := by exact prefixLift 3754319
  have htrace : WordTrace (prefixWord ++ tailWord_3754319) baseStart_3754319 baseEnd_3754319 := by
    simpa [prefixWord, tailWord_3754319, baseEnd_3754319] using wordTrace_append hprefix tailTrace_3754319
  have hstable : (prefixWord ++ tailWord_3754319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754319).length < 2 ^ (prefixWord ++ tailWord_3754319).sum := by decide
  have hdescent : baseEnd_3754319 < baseStart_3754319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754334 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_3754334 : Nat := 118140960795 + 3754334 * 2 ^ 59
def prefixEnd_3754334 : Nat := 4983230072969 + 3 ^ 40 * 3754334 * 2
def baseEnd_3754334 : Nat := 214197542168557709406571

theorem tailTrace_3754334 : CollatzResearch.WordTrace tailWord_3754334 prefixEnd_3754334 214197542168557709406571 := by
  unfold tailWord_3754334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17116476297587072755578757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91287873587131054696420037 17116476297587072755578757)
  ·
    refine ⟨3209339305797576141671017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17116476297587072755578757 3209339305797576141671017)
    ·
      refine ⟨2407004479348182106253263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3209339305797576141671017 2407004479348182106253263)
      ·
        refine ⟨3610506719022273159379895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407004479348182106253263 3610506719022273159379895)
        ·
          refine ⟨5415760078533409739069843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610506719022273159379895 5415760078533409739069843)
          ·
            refine ⟨8123640117800114608604765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415760078533409739069843 8123640117800114608604765)
            ·
              refine ⟨3046365044175042978226787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8123640117800114608604765 3046365044175042978226787)
              ·
                refine ⟨4569547566262564467340181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046365044175042978226787 4569547566262564467340181)
                ·
                  refine ⟨214197542168557709406571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4569547566262564467340181 214197542168557709406571)
                  ·
                    rfl

theorem cell23_3754334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_3754334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754334 prefixEnd_3754334 := by exact prefixLift 3754334
  have htrace : WordTrace (prefixWord ++ tailWord_3754334) baseStart_3754334 baseEnd_3754334 := by
    simpa [prefixWord, tailWord_3754334, baseEnd_3754334] using wordTrace_append hprefix tailTrace_3754334
  have hstable : (prefixWord ++ tailWord_3754334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754334).length < 2 ^ (prefixWord ++ tailWord_3754334).sum := by decide
  have hdescent : baseEnd_3754334 < baseStart_3754334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754336 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 5]
def baseStart_3754336 : Nat := 118140960795 + 3754336 * 2 ^ 59
def prefixEnd_3754336 : Nat := 4983230072969 + 3 ^ 40 * 3754336 * 2
def baseEnd_3754336 : Nat := 1927778906478328376834129

theorem tailTrace_3754336 : CollatzResearch.WordTrace tailWord_3754336 prefixEnd_3754336 1927778906478328376834129 := by
  unfold tailWord_3754336
  simp only [CollatzResearch.WordTrace]
  refine ⟨68465941663344668193101431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91287922217792890924135241 68465941663344668193101431)
  ·
    refine ⟨102698912495017002289652147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68465941663344668193101431 102698912495017002289652147)
    ·
      refine ⟨154048368742525503434478221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102698912495017002289652147 154048368742525503434478221)
      ·
        refine ⟨57768138278447063787929333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154048368742525503434478221 57768138278447063787929333)
        ·
          refine ⟨5415762963604412230118375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57768138278447063787929333 5415762963604412230118375)
          ·
            refine ⟨8123644445406618345177563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415762963604412230118375 8123644445406618345177563)
            ·
              refine ⟨12185466668109927517766345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123644445406618345177563 12185466668109927517766345)
              ·
                refine ⟨9139100001082445638324759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12185466668109927517766345 9139100001082445638324759)
                ·
                  refine ⟨13708650001623668457487139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9139100001082445638324759 13708650001623668457487139)
                  ·
                    refine ⟨20562975002435502686230709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13708650001623668457487139 20562975002435502686230709)
                    ·
                      refine ⟨1927778906478328376834129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20562975002435502686230709 1927778906478328376834129)
                      ·
                        rfl

theorem cell23_3754336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_3754336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754336 prefixEnd_3754336 := by exact prefixLift 3754336
  have htrace : WordTrace (prefixWord ++ tailWord_3754336) baseStart_3754336 baseEnd_3754336 := by
    simpa [prefixWord, tailWord_3754336, baseEnd_3754336] using wordTrace_append hprefix tailTrace_3754336
  have hstable : (prefixWord ++ tailWord_3754336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754336).length < 2 ^ (prefixWord ++ tailWord_3754336).sum := by decide
  have hdescent : baseEnd_3754336 < baseStart_3754336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754346 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3754346 : Nat := 118140960795 + 3754346 * 2 ^ 59
def prefixEnd_3754346 : Nat := 4983230072969 + 3 ^ 40 * 3754346 * 2
def baseEnd_3754346 : Nat := 1927784041284873337709083

theorem tailTrace_3754346 : CollatzResearch.WordTrace tailWord_3754346 prefixEnd_3754346 1927784041284873337709083 := by
  unfold tailWord_3754346
  simp only [CollatzResearch.WordTrace]
  refine ⟨34233062014163277023516723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91288165371102072062711261 34233062014163277023516723)
  ·
    refine ⟨51349593021244915535275085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34233062014163277023516723 51349593021244915535275085)
    ·
      refine ⟨19256097382966843325728157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51349593021244915535275085 19256097382966843325728157)
      ·
        refine ⟨7221036518612566247148059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19256097382966843325728157 7221036518612566247148059)
        ·
          refine ⟨10831554777918849370722089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7221036518612566247148059 10831554777918849370722089)
          ·
            refine ⟨8123666083439137028041567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10831554777918849370722089 8123666083439137028041567)
            ·
              refine ⟨12185499125158705542062351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123666083439137028041567 12185499125158705542062351)
              ·
                refine ⟨18278248687738058313093527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12185499125158705542062351 18278248687738058313093527)
                ·
                  refine ⟨27417373031607087469640291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18278248687738058313093527 27417373031607087469640291)
                  ·
                    refine ⟨41126059547410631204460437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27417373031607087469640291 41126059547410631204460437)
                    ·
                      refine ⟨1927784041284873337709083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41126059547410631204460437 1927784041284873337709083)
                      ·
                        rfl

theorem cell23_3754346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3754346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754346 prefixEnd_3754346 := by exact prefixLift 3754346
  have htrace : WordTrace (prefixWord ++ tailWord_3754346) baseStart_3754346 baseEnd_3754346 := by
    simpa [prefixWord, tailWord_3754346, baseEnd_3754346] using wordTrace_append hprefix tailTrace_3754346
  have hstable : (prefixWord ++ tailWord_3754346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754346).length < 2 ^ (prefixWord ++ tailWord_3754346).sum := by decide
  have hdescent : baseEnd_3754346 < baseStart_3754346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754370 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3754370 : Nat := 118140960795 + 3754370 * 2 ^ 59
def prefixEnd_3754370 : Nat := 4983230072969 + 3 ^ 40 * 3754370 * 2
def baseEnd_3754370 : Nat := 1927796364820581243808973

theorem tailTrace_3754370 : CollatzResearch.WordTrace tailWord_3754370 prefixEnd_3754370 1927796364820581243808973 := by
  unfold tailWord_3754370
  simp only [CollatzResearch.WordTrace]
  refine ⟨34233280852141540048235141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91288748939044106795293709 34233280852141540048235141)
  ·
    refine ⟨6418740159776538759044089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34233280852141540048235141 6418740159776538759044089)
    ·
      refine ⟨4814055119832404069283067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6418740159776538759044089 4814055119832404069283067)
      ·
        refine ⟨7221082679748606103924601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4814055119832404069283067 7221082679748606103924601)
        ·
          refine ⟨5415812009811454577943451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7221082679748606103924601 5415812009811454577943451)
          ·
            refine ⟨8123718014717181866915177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415812009811454577943451 8123718014717181866915177)
            ·
              refine ⟨6092788511037886400186383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8123718014717181866915177 6092788511037886400186383)
              ·
                refine ⟨9139182766556829600279575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092788511037886400186383 9139182766556829600279575)
                ·
                  refine ⟨13708774149835244400419363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9139182766556829600279575 13708774149835244400419363)
                  ·
                    refine ⟨20563161224752866600629045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13708774149835244400419363 20563161224752866600629045)
                    ·
                      refine ⟨1927796364820581243808973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20563161224752866600629045 1927796364820581243808973)
                      ·
                        rfl

theorem cell23_3754370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3754370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754370 prefixEnd_3754370 := by exact prefixLift 3754370
  have htrace : WordTrace (prefixWord ++ tailWord_3754370) baseStart_3754370 baseEnd_3754370 := by
    simpa [prefixWord, tailWord_3754370, baseEnd_3754370] using wordTrace_append hprefix tailTrace_3754370
  have hstable : (prefixWord ++ tailWord_3754370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754370).length < 2 ^ (prefixWord ++ tailWord_3754370).sum := by decide
  have hdescent : baseEnd_3754370 < baseStart_3754370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754389 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3754389 : Nat := 118140960795 + 3754389 * 2 ^ 59
def prefixEnd_3754389 : Nat := 4983230072969 + 3 ^ 40 * 3754389 * 2
def baseEnd_3754389 : Nat := 1927806120953016669471385

theorem tailTrace_3754389 : CollatzResearch.WordTrace tailWord_3754389 prefixEnd_3754389 1927806120953016669471385 := by
  unfold tailWord_3754389
  simp only [CollatzResearch.WordTrace]
  refine ⟨136933816395497326437882221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91289210930331550958588147 136933816395497326437882221)
  ·
    refine ⟨51350181148311497414205833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136933816395497326437882221 51350181148311497414205833)
    ·
      refine ⟨38512635861233623060654375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51350181148311497414205833 38512635861233623060654375)
      ·
        refine ⟨57768953791850434590981563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38512635861233623060654375 57768953791850434590981563)
        ·
          refine ⟨86653430687775651886472345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57768953791850434590981563 86653430687775651886472345)
          ·
            refine ⟨64990073015831738914854259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86653430687775651886472345 64990073015831738914854259)
            ·
              refine ⟨97485109523747608372281389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64990073015831738914854259 97485109523747608372281389)
              ·
                refine ⟨36556916071405353139605521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97485109523747608372281389 36556916071405353139605521)
                ·
                  refine ⟨27417687053554014854704141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36556916071405353139605521 27417687053554014854704141)
                  ·
                    refine ⟨10281632645082755570514053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27417687053554014854704141 10281632645082755570514053)
                    ·
                      refine ⟨1927806120953016669471385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10281632645082755570514053 1927806120953016669471385)
                      ·
                        rfl

theorem cell23_3754389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3754389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754389 prefixEnd_3754389 := by exact prefixLift 3754389
  have htrace : WordTrace (prefixWord ++ tailWord_3754389) baseStart_3754389 baseEnd_3754389 := by
    simpa [prefixWord, tailWord_3754389, baseEnd_3754389] using wordTrace_append hprefix tailTrace_3754389
  have hstable : (prefixWord ++ tailWord_3754389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754389).length < 2 ^ (prefixWord ++ tailWord_3754389).sum := by decide
  have hdescent : baseEnd_3754389 < baseStart_3754389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754399 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 1, 8]
def baseStart_3754399 : Nat := 118140960795 + 3754399 * 2 ^ 59
def prefixEnd_3754399 : Nat := 4983230072969 + 3 ^ 40 * 3754399 * 2
def baseEnd_3754399 : Nat := 642603751919853876782113

theorem tailTrace_3754399 : CollatzResearch.WordTrace tailWord_3754399 prefixEnd_3754399 642603751919853876782113 := by
  unfold tailWord_3754399
  simp only [CollatzResearch.WordTrace]
  refine ⟨136934181125461098145746251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91289454083640732097164167 136934181125461098145746251)
  ·
    refine ⟨205401271688191647218619377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136934181125461098145746251 205401271688191647218619377)
    ·
      refine ⟨154050953766143735413964533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205401271688191647218619377 154050953766143735413964533)
      ·
        refine ⟨14442276915575975195059175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154050953766143735413964533 14442276915575975195059175)
        ·
          refine ⟨21663415373363962792588763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14442276915575975195059175 21663415373363962792588763)
          ·
            refine ⟨32495123060045944188883145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21663415373363962792588763 32495123060045944188883145)
            ·
              refine ⟨24371342295034458141662359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32495123060045944188883145 24371342295034458141662359)
              ·
                refine ⟨36557013442551687212493539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24371342295034458141662359 36557013442551687212493539)
                ·
                  refine ⟨54835520163827530818740309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36557013442551687212493539 54835520163827530818740309)
                  ·
                    refine ⟨642603751919853876782113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54835520163827530818740309 642603751919853876782113)
                    ·
                      rfl

theorem cell23_3754399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_3754399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754399 prefixEnd_3754399 := by exact prefixLift 3754399
  have htrace : WordTrace (prefixWord ++ tailWord_3754399) baseStart_3754399 baseEnd_3754399 := by
    simpa [prefixWord, tailWord_3754399, baseEnd_3754399] using wordTrace_append hprefix tailTrace_3754399
  have hstable : (prefixWord ++ tailWord_3754399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754399).length < 2 ^ (prefixWord ++ tailWord_3754399).sum := by decide
  have hdescent : baseEnd_3754399 < baseStart_3754399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754400 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 2, 1, 3]
def baseStart_3754400 : Nat := 118140960795 + 3754400 * 2 ^ 59
def prefixEnd_3754400 : Nat := 4983230072969 + 3 ^ 40 * 3754400 * 2
def baseEnd_3754400 : Nat := 1927811769240216126433835

theorem tailTrace_3754400 : CollatzResearch.WordTrace tailWord_3754400 prefixEnd_3754400 1927811769240216126433835 := by
  unfold tailWord_3754400
  simp only [CollatzResearch.WordTrace]
  refine ⟨68467108799228737658266327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91289478398971650211021769 68467108799228737658266327)
  ·
    refine ⟨102700663198843106487399491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68467108799228737658266327 102700663198843106487399491)
    ·
      refine ⟨154050994798264659731099237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102700663198843106487399491 154050994798264659731099237)
      ·
        refine ⟨28884561524674623699581107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154050994798264659731099237 28884561524674623699581107)
        ·
          refine ⟨43326842287011935549371661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28884561524674623699581107 43326842287011935549371661)
          ·
            refine ⟨16247565857629475831014373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43326842287011935549371661 16247565857629475831014373)
            ·
              refine ⟨3046418598305526718315195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16247565857629475831014373 3046418598305526718315195)
              ·
                refine ⟨4569627897458290077472793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046418598305526718315195 4569627897458290077472793)
                ·
                  refine ⟨3427220923093717558104595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4569627897458290077472793 3427220923093717558104595)
                  ·
                    refine ⟨5140831384640576337156893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3427220923093717558104595 5140831384640576337156893)
                    ·
                      refine ⟨1927811769240216126433835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5140831384640576337156893 1927811769240216126433835)
                      ·
                        rfl

theorem cell23_3754400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_3754400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754400 prefixEnd_3754400 := by exact prefixLift 3754400
  have htrace : WordTrace (prefixWord ++ tailWord_3754400) baseStart_3754400 baseEnd_3754400 := by
    simpa [prefixWord, tailWord_3754400, baseEnd_3754400] using wordTrace_append hprefix tailTrace_3754400
  have hstable : (prefixWord ++ tailWord_3754400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754400).length < 2 ^ (prefixWord ++ tailWord_3754400).sum := by decide
  have hdescent : baseEnd_3754400 < baseStart_3754400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754419 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 4]
def baseStart_3754419 : Nat := 118140960795 + 3754419 * 2 ^ 59
def prefixEnd_3754419 : Nat := 4983230072969 + 3 ^ 40 * 3754419 * 2
def baseEnd_3754419 : Nat := 1927821525372651552096247

theorem tailTrace_3754419 : CollatzResearch.WordTrace tailWord_3754419 prefixEnd_3754419 1927821525372651552096247 := by
  unfold tailWord_3754419
  simp only [CollatzResearch.WordTrace]
  refine ⟨136934910585388641561474311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91289940390259094374316207 136934910585388641561474311)
  ·
    refine ⟨205402365878082962342211467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136934910585388641561474311 205402365878082962342211467)
    ·
      refine ⟨308103548817124443513317201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205402365878082962342211467 308103548817124443513317201)
      ·
        refine ⟨231077661612843332634987901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308103548817124443513317201 231077661612843332634987901)
        ·
          refine ⟨86654123104816249738120463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231077661612843332634987901 86654123104816249738120463)
          ·
            refine ⟨129981184657224374607180695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86654123104816249738120463 129981184657224374607180695)
            ·
              refine ⟨194971776985836561910771043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129981184657224374607180695 194971776985836561910771043)
              ·
                refine ⟨292457665478754842866156565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194971776985836561910771043 292457665478754842866156565)
                ·
                  refine ⟨13708953069316633259351089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 292457665478754842866156565 13708953069316633259351089)
                  ·
                    refine ⟨10281714801987474944513317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13708953069316633259351089 10281714801987474944513317)
                    ·
                      refine ⟨1927821525372651552096247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10281714801987474944513317 1927821525372651552096247)
                      ·
                        rfl

theorem cell23_3754419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_3754419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754419 prefixEnd_3754419 := by exact prefixLift 3754419
  have htrace : WordTrace (prefixWord ++ tailWord_3754419) baseStart_3754419 baseEnd_3754419 := by
    simpa [prefixWord, tailWord_3754419, baseEnd_3754419] using wordTrace_append hprefix tailTrace_3754419
  have hstable : (prefixWord ++ tailWord_3754419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754419).length < 2 ^ (prefixWord ++ tailWord_3754419).sum := by decide
  have hdescent : baseEnd_3754419 < baseStart_3754419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754423 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 1, 4, 2]
def baseStart_3754423 : Nat := 118140960795 + 3754423 * 2 ^ 59
def prefixEnd_3754423 : Nat := 4983230072969 + 3 ^ 40 * 3754423 * 2
def baseEnd_3754423 : Nat := 1927823579295269536446229

theorem tailTrace_3754423 : CollatzResearch.WordTrace tailWord_3754423 prefixEnd_3754423 1927823579295269536446229 := by
  unfold tailWord_3754423
  simp only [CollatzResearch.WordTrace]
  refine ⟨136935056477374150244619923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91290037651582766829746615 136935056477374150244619923)
  ·
    refine ⟨205402584716061225366929885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136935056477374150244619923 205402584716061225366929885)
    ·
      refine ⟨77025969268522959512598707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205402584716061225366929885 77025969268522959512598707)
      ·
        refine ⟨115538953902784439268898061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77025969268522959512598707 115538953902784439268898061)
        ·
          refine ⟨43327107713544164725836773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115538953902784439268898061 43327107713544164725836773)
          ·
            refine ⟨8123832696289530886094395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43327107713544164725836773 8123832696289530886094395)
            ·
              refine ⟨12185749044434296329141593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123832696289530886094395 12185749044434296329141593)
              ·
                refine ⟨9139311783325722246856195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12185749044434296329141593 9139311783325722246856195)
                ·
                  refine ⟨13708967674988583370284293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9139311783325722246856195 13708967674988583370284293)
                  ·
                    refine ⟨2570431439060359381928305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13708967674988583370284293 2570431439060359381928305)
                    ·
                      refine ⟨1927823579295269536446229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2570431439060359381928305 1927823579295269536446229)
                      ·
                        rfl

theorem cell23_3754423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_3754423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3754423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3754423 prefixEnd_3754423 := by exact prefixLift 3754423
  have htrace : WordTrace (prefixWord ++ tailWord_3754423) baseStart_3754423 baseEnd_3754423 := by
    simpa [prefixWord, tailWord_3754423, baseEnd_3754423] using wordTrace_append hprefix tailTrace_3754423
  have hstable : (prefixWord ++ tailWord_3754423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754423).length < 2 ^ (prefixWord ++ tailWord_3754423).sum := by decide
  have hdescent : baseEnd_3754423 < baseStart_3754423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
