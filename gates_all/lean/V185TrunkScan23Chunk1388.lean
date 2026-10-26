import V185TrunkScan23Chunk1387

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8221177 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 4, 4]
def baseStart_8221177 : Nat := 118140960795 + 8221177 * 2 ^ 59
def prefixEnd_8221177 : Nat := 4983230072969 + 3 ^ 40 * 8221177 * 2
def baseEnd_8221177 : Nat := 1407138448896095446959667

theorem tailTrace_8221177 : CollatzResearch.WordTrace tailWord_8221177 prefixEnd_8221177 1407138448896095446959667 := by
  unfold tailWord_8221177
  simp only [CollatzResearch.WordTrace]
  refine ⟨299850958937087269093365785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199900639291391512728910523 299850958937087269093365785)
  ·
    refine ⟨224888219202815451820024339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299850958937087269093365785 224888219202815451820024339)
    ·
      refine ⟨337332328804223177730036509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224888219202815451820024339 337332328804223177730036509)
      ·
        refine ⟨126499623301583691648763691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337332328804223177730036509 126499623301583691648763691)
        ·
          refine ⟨189749434952375537473145537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126499623301583691648763691 189749434952375537473145537)
          ·
            refine ⟨142312076214281653104859153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189749434952375537473145537 142312076214281653104859153)
            ·
              refine ⟨106734057160711239828644365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142312076214281653104859153 106734057160711239828644365)
              ·
                refine ⟨40025271435266714935741637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106734057160711239828644365 40025271435266714935741637)
                ·
                  refine ⟨7504738394112509050451557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40025271435266714935741637 7504738394112509050451557)
                  ·
                    refine ⟨1407138448896095446959667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504738394112509050451557 1407138448896095446959667)
                    ·
                      rfl

theorem cell23_8221177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 4].length) (baseStart_8221177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221177 prefixEnd_8221177 := by exact prefixLift 8221177
  have htrace : WordTrace (prefixWord ++ tailWord_8221177) baseStart_8221177 baseEnd_8221177 := by
    simpa [prefixWord, tailWord_8221177, baseEnd_8221177] using wordTrace_append hprefix tailTrace_8221177
  have hstable : (prefixWord ++ tailWord_8221177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221177).length < 2 ^ (prefixWord ++ tailWord_8221177).sum := by decide
  have hdescent : baseEnd_8221177 < baseStart_8221177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221184 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 9, 2, 2]
def baseStart_8221184 : Nat := 118140960795 + 8221184 * 2 ^ 59
def prefixEnd_8221184 : Nat := 4983230072969 + 3 ^ 40 * 8221184 * 2
def baseEnd_8221184 : Nat := 4221418941052867813491469

theorem tailTrace_8221184 : CollatzResearch.WordTrace tailWord_8221184 prefixEnd_8221184 4221418941052867813491469 := by
  unfold tailWord_8221184
  simp only [CollatzResearch.WordTrace]
  refine ⟨149925607124030954644435303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199900809498707939525913737 149925607124030954644435303)
  ·
    refine ⟨224888410686046431966652955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149925607124030954644435303 224888410686046431966652955)
    ·
      refine ⟨337332616029069647949979433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224888410686046431966652955 337332616029069647949979433)
      ·
        refine ⟨252999462021802235962484575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337332616029069647949979433 252999462021802235962484575)
        ·
          refine ⟨379499193032703353943726863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252999462021802235962484575 379499193032703353943726863)
          ·
            refine ⟨569248789549055030915590295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379499193032703353943726863 569248789549055030915590295)
            ·
              refine ⟨853873184323582546373385443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569248789549055030915590295 853873184323582546373385443)
              ·
                refine ⟨1280809776485373819560078165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853873184323582546373385443 1280809776485373819560078165)
                ·
                  refine ⟨7504744784093987223984833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1280809776485373819560078165 7504744784093987223984833)
                  ·
                    refine ⟨5628558588070490417988625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7504744784093987223984833 5628558588070490417988625)
                    ·
                      refine ⟨4221418941052867813491469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628558588070490417988625 4221418941052867813491469)
                      ·
                        rfl

theorem cell23_8221184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_8221184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221184 prefixEnd_8221184 := by exact prefixLift 8221184
  have htrace : WordTrace (prefixWord ++ tailWord_8221184) baseStart_8221184 baseEnd_8221184 := by
    simpa [prefixWord, tailWord_8221184, baseEnd_8221184] using wordTrace_append hprefix tailTrace_8221184
  have hstable : (prefixWord ++ tailWord_8221184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221184).length < 2 ^ (prefixWord ++ tailWord_8221184).sum := by decide
  have hdescent : baseEnd_8221184 < baseStart_8221184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221187 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 3]
def baseStart_8221187 : Nat := 118140960795 + 8221187 * 2 ^ 59
def prefixEnd_8221187 : Nat := 4983230072969 + 3 ^ 40 * 8221187 * 2
def baseEnd_8221187 : Nat := 4221420481494831301753955

theorem tailTrace_8221187 : CollatzResearch.WordTrace tailWord_8221187 prefixEnd_8221187 4221420481494831301753955 := by
  unfold tailWord_8221187
  simp only [CollatzResearch.WordTrace]
  refine ⟨299851323667051040801229815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199900882444700693867486543 299851323667051040801229815)
  ·
    refine ⟨449776985500576561201844723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299851323667051040801229815 449776985500576561201844723)
    ·
      refine ⟨674665478250864841802767085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449776985500576561201844723 674665478250864841802767085)
      ·
        refine ⟨252999554344074315676037657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674665478250864841802767085 252999554344074315676037657)
        ·
          refine ⟨189749665758055736757028243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252999554344074315676037657 189749665758055736757028243)
          ·
            refine ⟨284624498637083605135542365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189749665758055736757028243 284624498637083605135542365)
            ·
              refine ⟨106734186988906351925828387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284624498637083605135542365 106734186988906351925828387)
              ·
                refine ⟨160101280483359527888742581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106734186988906351925828387 160101280483359527888742581)
                ·
                  refine ⟨15009495045314955739569617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160101280483359527888742581 15009495045314955739569617)
                  ·
                    refine ⟨11257121283986216804677213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15009495045314955739569617 11257121283986216804677213)
                    ·
                      refine ⟨4221420481494831301753955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11257121283986216804677213 4221420481494831301753955)
                      ·
                        rfl

theorem cell23_8221187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_8221187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221187 prefixEnd_8221187 := by exact prefixLift 8221187
  have htrace : WordTrace (prefixWord ++ tailWord_8221187) baseStart_8221187 baseEnd_8221187 := by
    simpa [prefixWord, tailWord_8221187, baseEnd_8221187] using wordTrace_append hprefix tailTrace_8221187
  have hstable : (prefixWord ++ tailWord_8221187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221187).length < 2 ^ (prefixWord ++ tailWord_8221187).sum := by decide
  have hdescent : baseEnd_8221187 < baseStart_8221187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221194 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_8221194 : Nat := 118140960795 + 8221194 * 2 ^ 59
def prefixEnd_8221194 : Nat := 4983230072969 + 3 ^ 40 * 8221194 * 2
def baseEnd_8221194 : Nat := 1407141358619804258122141

theorem tailTrace_8221194 : CollatzResearch.WordTrace tailWord_8221194 prefixEnd_8221194 1407141358619804258122141 := by
  unfold tailWord_8221194
  simp only [CollatzResearch.WordTrace]
  refine ⟨74962894744506420249183659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199901052652017120664489757 74962894744506420249183659)
  ·
    refine ⟨112444342116759630373775489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74962894744506420249183659 112444342116759630373775489)
    ·
      refine ⟨84333256587569722780331617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112444342116759630373775489 84333256587569722780331617)
      ·
        refine ⟨63249942440677292085248713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84333256587569722780331617 63249942440677292085248713)
        ·
          refine ⟨47437456830507969063936535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63249942440677292085248713 47437456830507969063936535)
          ·
            refine ⟨71156185245761953595904803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47437456830507969063936535 71156185245761953595904803)
            ·
              refine ⟨106734277868642930393857205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71156185245761953595904803 106734277868642930393857205)
              ·
                refine ⟨10006338550185274724424113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106734277868642930393857205 10006338550185274724424113)
                ·
                  refine ⟨7504753912638956043318085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10006338550185274724424113 7504753912638956043318085)
                  ·
                    refine ⟨1407141358619804258122141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504753912638956043318085 1407141358619804258122141)
                    ·
                      rfl

theorem cell23_8221194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_8221194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221194 prefixEnd_8221194 := by exact prefixLift 8221194
  have htrace : WordTrace (prefixWord ++ tailWord_8221194) baseStart_8221194 baseEnd_8221194 := by
    simpa [prefixWord, tailWord_8221194, baseEnd_8221194] using wordTrace_append hprefix tailTrace_8221194
  have hstable : (prefixWord ++ tailWord_8221194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221194).length < 2 ^ (prefixWord ++ tailWord_8221194).sum := by decide
  have hdescent : baseEnd_8221194 < baseStart_8221194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221221 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 1, 2, 3]
def baseStart_8221221 : Nat := 118140960795 + 8221221 * 2 ^ 59
def prefixEnd_8221221 : Nat := 4983230072969 + 3 ^ 40 * 8221221 * 2
def baseEnd_8221221 : Nat := 4221437939837084168728799

theorem tailTrace_8221221 : CollatzResearch.WordTrace tailWord_8221221 prefixEnd_8221221 4221437939837084168728799 := by
  unfold tailWord_8221221
  simp only [CollatzResearch.WordTrace]
  refine ⟨299852563748927864607967517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199901709165951909738645011 299852563748927864607967517)
  ·
    refine ⟨112444711405847949227987819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299852563748927864607967517 112444711405847949227987819)
    ·
      refine ⟨168667067108771923841981729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112444711405847949227987819 168667067108771923841981729)
      ·
        refine ⟨126500300331578942881486297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168667067108771923841981729 126500300331578942881486297)
        ·
          refine ⟨94875225248684207161114723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126500300331578942881486297 94875225248684207161114723)
          ·
            refine ⟨142312837873026310741672085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94875225248684207161114723 142312837873026310741672085)
            ·
              refine ⟨6670914275298108316015879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142312837873026310741672085 6670914275298108316015879)
              ·
                refine ⟨10006371412947162474023819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670914275298108316015879 10006371412947162474023819)
                ·
                  refine ⟨15009557119420743711035729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10006371412947162474023819 15009557119420743711035729)
                  ·
                    refine ⟨11257167839565557783276797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15009557119420743711035729 11257167839565557783276797)
                    ·
                      refine ⟨4221437939837084168728799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11257167839565557783276797 4221437939837084168728799)
                      ·
                        rfl

theorem cell23_8221221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_8221221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221221 prefixEnd_8221221 := by exact prefixLift 8221221
  have htrace : WordTrace (prefixWord ++ tailWord_8221221) baseStart_8221221 baseEnd_8221221 := by
    simpa [prefixWord, tailWord_8221221, baseEnd_8221221] using wordTrace_append hprefix tailTrace_8221221
  have hstable : (prefixWord ++ tailWord_8221221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221221).length < 2 ^ (prefixWord ++ tailWord_8221221).sum := by decide
  have hdescent : baseEnd_8221221 < baseStart_8221221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221302 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_8221302 : Nat := 118140960795 + 8221302 * 2 ^ 59
def prefixEnd_8221302 : Nat := 4983230072969 + 3 ^ 40 * 8221302 * 2
def baseEnd_8221302 : Nat := 4221479531770098351815927

theorem tailTrace_8221302 : CollatzResearch.WordTrace tailWord_8221302 prefixEnd_8221302 4221479531770098351815927 := by
  unfold tailWord_8221302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740969878852150965104135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199903678707756276961110773 18740969878852150965104135)
  ·
    refine ⟨28111454818278226447656203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18740969878852150965104135 28111454818278226447656203)
    ·
      refine ⟨42167182227417339671484305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28111454818278226447656203 42167182227417339671484305)
      ·
        refine ⟨31625386670563004753613229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42167182227417339671484305 31625386670563004753613229)
        ·
          refine ⟨11859520001461126782604961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31625386670563004753613229 11859520001461126782604961)
          ·
            refine ⟨8894640001095845086953721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11859520001461126782604961 8894640001095845086953721)
            ·
              refine ⟨6670980000821883815215291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8894640001095845086953721 6670980000821883815215291)
              ·
                refine ⟨10006470001232825722822937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670980000821883815215291 10006470001232825722822937)
                ·
                  refine ⟨7504852500924619292117203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10006470001232825722822937 7504852500924619292117203)
                  ·
                    refine ⟨11257278751386928938175805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504852500924619292117203 11257278751386928938175805)
                    ·
                      refine ⟨4221479531770098351815927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11257278751386928938175805 4221479531770098351815927)
                      ·
                        rfl

theorem cell23_8221302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_8221302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221302 prefixEnd_8221302 := by exact prefixLift 8221302
  have htrace : WordTrace (prefixWord ++ tailWord_8221302) baseStart_8221302 baseEnd_8221302 := by
    simpa [prefixWord, tailWord_8221302, baseEnd_8221302] using wordTrace_append hprefix tailTrace_8221302
  have hstable : (prefixWord ++ tailWord_8221302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221302).length < 2 ^ (prefixWord ++ tailWord_8221302).sum := by decide
  have hdescent : baseEnd_8221302 < baseStart_8221302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221327 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 6, 5]
def baseStart_8221327 : Nat := 118140960795 + 8221327 * 2 ^ 59
def prefixEnd_8221327 : Nat := 4983230072969 + 3 ^ 40 * 8221327 * 2
def baseEnd_8221327 : Nat := 1407164122928820251334437

theorem tailTrace_8221327 : CollatzResearch.WordTrace tailWord_8221327 prefixEnd_8221327 1407164122928820251334437 := by
  unfold tailWord_8221327
  simp only [CollatzResearch.WordTrace]
  refine ⟨299856429886543844711326235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199904286591029229807550823 299856429886543844711326235)
  ·
    refine ⟨449784644829815767066989353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299856429886543844711326235 449784644829815767066989353)
    ·
      refine ⟨337338483622361825300242015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449784644829815767066989353 337338483622361825300242015)
      ·
        refine ⟨506007725433542737950363023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337338483622361825300242015 506007725433542737950363023)
        ·
          refine ⟨759011588150314106925544535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506007725433542737950363023 759011588150314106925544535)
          ·
            refine ⟨1138517382225471160388316803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759011588150314106925544535 1138517382225471160388316803)
            ·
              refine ⟨1707776073338206740582475205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138517382225471160388316803 1707776073338206740582475205)
              ·
                refine ⟨320208013750913763859214101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1707776073338206740582475205 320208013750913763859214101)
                ·
                  refine ⟨15009750644574082680900661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 320208013750913763859214101 15009750644574082680900661)
                  ·
                    refine ⟨1407164122928820251334437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15009750644574082680900661 1407164122928820251334437)
                    ·
                      rfl

theorem cell23_8221327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_8221327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221327 prefixEnd_8221327 := by exact prefixLift 8221327
  have htrace : WordTrace (prefixWord ++ tailWord_8221327) baseStart_8221327 baseEnd_8221327 := by
    simpa [prefixWord, tailWord_8221327, baseEnd_8221327] using wordTrace_append hprefix tailTrace_8221327
  have hstable : (prefixWord ++ tailWord_8221327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221327).length < 2 ^ (prefixWord ++ tailWord_8221327).sum := by decide
  have hdescent : baseEnd_8221327 < baseStart_8221327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221337 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_8221337 : Nat := 118140960795 + 8221337 * 2 ^ 59
def prefixEnd_8221337 : Nat := 4983230072969 + 3 ^ 40 * 8221337 * 2
def baseEnd_8221337 : Nat := 4221497503593005714878265

theorem tailTrace_8221337 : CollatzResearch.WordTrace tailWord_8221337 prefixEnd_8221337 4221497503593005714878265 := by
  unfold tailWord_8221337
  simp only [CollatzResearch.WordTrace]
  refine ⟨299856794616507616419190265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199904529744338410946126843 299856794616507616419190265)
  ·
    refine ⟨224892595962380712314392699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299856794616507616419190265 224892595962380712314392699)
    ·
      refine ⟨337338893943571068471589049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224892595962380712314392699 337338893943571068471589049)
      ·
        refine ⟨253004170457678301353691787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337338893943571068471589049 253004170457678301353691787)
        ·
          refine ⟨379506255686517452030537681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253004170457678301353691787 379506255686517452030537681)
          ·
            refine ⟨284629691764888089022903261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379506255686517452030537681 284629691764888089022903261)
            ·
              refine ⟨106736134411833033383588723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284629691764888089022903261 106736134411833033383588723)
              ·
                refine ⟨160104201617749550075383085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106736134411833033383588723 160104201617749550075383085)
                ·
                  refine ⟨60039075606656081278268657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160104201617749550075383085 60039075606656081278268657)
                  ·
                    refine ⟨45029306704992060958701493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60039075606656081278268657 45029306704992060958701493)
                    ·
                      refine ⟨4221497503593005714878265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45029306704992060958701493 4221497503593005714878265)
                      ·
                        rfl

theorem cell23_8221337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_8221337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221337 prefixEnd_8221337 := by exact prefixLift 8221337
  have htrace : WordTrace (prefixWord ++ tailWord_8221337) baseStart_8221337 baseEnd_8221337 := by
    simpa [prefixWord, tailWord_8221337, baseEnd_8221337] using wordTrace_append hprefix tailTrace_8221337
  have hstable : (prefixWord ++ tailWord_8221337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221337).length < 2 ^ (prefixWord ++ tailWord_8221337).sum := by decide
  have hdescent : baseEnd_8221337 < baseStart_8221337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221358 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_8221358 : Nat := 118140960795 + 8221358 * 2 ^ 59
def prefixEnd_8221358 : Nat := 4983230072969 + 3 ^ 40 * 8221358 * 2
def baseEnd_8221358 : Nat := 4221508286686750132715669

theorem tailTrace_8221358 : CollatzResearch.WordTrace tailWord_8221358 prefixEnd_8221358 4221508286686750132715669 := by
  unfold tailWord_8221358
  simp only [CollatzResearch.WordTrace]
  refine ⟨37482195068678942125713091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199905040366287691337136485 37482195068678942125713091)
  ·
    refine ⟨56223292603018413188569637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37482195068678942125713091 56223292603018413188569637)
    ·
      refine ⟨10541867363065952472856807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56223292603018413188569637 10541867363065952472856807)
      ·
        refine ⟨15812801044598928709285211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10541867363065952472856807 15812801044598928709285211)
        ·
          refine ⟨23719201566898393063927817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15812801044598928709285211 23719201566898393063927817)
          ·
            refine ⟨17789401175173794797945863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23719201566898393063927817 17789401175173794797945863)
            ·
              refine ⟨26684101762760692196918795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17789401175173794797945863 26684101762760692196918795)
              ·
                refine ⟨40026152644141038295378193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26684101762760692196918795 40026152644141038295378193)
                ·
                  refine ⟨30019614483105778721533645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40026152644141038295378193 30019614483105778721533645)
                  ·
                    refine ⟨11257355431164667020575117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30019614483105778721533645 11257355431164667020575117)
                    ·
                      refine ⟨4221508286686750132715669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11257355431164667020575117 4221508286686750132715669)
                      ·
                        rfl

theorem cell23_8221358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_8221358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221358 prefixEnd_8221358 := by exact prefixLift 8221358
  have htrace : WordTrace (prefixWord ++ tailWord_8221358) baseStart_8221358 baseEnd_8221358 := by
    simpa [prefixWord, tailWord_8221358, baseEnd_8221358] using wordTrace_append hprefix tailTrace_8221358
  have hstable : (prefixWord ++ tailWord_8221358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221358).length < 2 ^ (prefixWord ++ tailWord_8221358).sum := by decide
  have hdescent : baseEnd_8221358 < baseStart_8221358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221382 : List Nat := [6, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_8221382 : Nat := 118140960795 + 8221382 * 2 ^ 59
def prefixEnd_8221382 : Nat := 4983230072969 + 3 ^ 40 * 8221382 * 2
def baseEnd_8221382 : Nat := 469057845580273115423951

theorem tailTrace_8221382 : CollatzResearch.WordTrace tailWord_8221382 prefixEnd_8221382 469057845580273115423951 := by
  unfold tailWord_8221382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9370576121917018409518075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199905623934229726069718933 9370576121917018409518075)
  ·
    refine ⟨14055864182875527614277113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9370576121917018409518075 14055864182875527614277113)
    ·
      refine ⟨10541898137156645710707835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14055864182875527614277113 10541898137156645710707835)
      ·
        refine ⟨15812847205734968566061753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10541898137156645710707835 15812847205734968566061753)
        ·
          refine ⟨11859635404301226424546315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15812847205734968566061753 11859635404301226424546315)
          ·
            refine ⟨17789453106451839636819473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11859635404301226424546315 17789453106451839636819473)
            ·
              refine ⟨13342089829838879727614605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17789453106451839636819473 13342089829838879727614605)
              ·
                refine ⟨5003283686189579897855477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13342089829838879727614605 5003283686189579897855477)
                ·
                  refine ⟨469057845580273115423951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5003283686189579897855477 469057845580273115423951)
                  ·
                    rfl

theorem cell23_8221382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_8221382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221382 prefixEnd_8221382 := by exact prefixLift 8221382
  have htrace : WordTrace (prefixWord ++ tailWord_8221382) baseStart_8221382 baseEnd_8221382 := by
    simpa [prefixWord, tailWord_8221382, baseEnd_8221382] using wordTrace_append hprefix tailTrace_8221382
  have hstable : (prefixWord ++ tailWord_8221382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221382).length < 2 ^ (prefixWord ++ tailWord_8221382).sum := by decide
  have hdescent : baseEnd_8221382 < baseStart_8221382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221434 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_8221434 : Nat := 118140960795 + 8221434 * 2 ^ 59
def prefixEnd_8221434 : Nat := 4983230072969 + 3 ^ 40 * 8221434 * 2
def baseEnd_8221434 : Nat := 1407182437072163945121773

theorem tailTrace_8221434 : CollatzResearch.WordTrace tailWord_8221434 prefixEnd_8221434 1407182437072163945121773 := by
  unfold tailWord_8221434
  simp only [CollatzResearch.WordTrace]
  refine ⟨74965083124289050496367839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199906888331437467990314237 74965083124289050496367839)
  ·
    refine ⟨112447624686433575744551759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74965083124289050496367839 112447624686433575744551759)
    ·
      refine ⟨168671437029650363616827639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112447624686433575744551759 168671437029650363616827639)
      ·
        refine ⟨253007155544475545425241459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168671437029650363616827639 253007155544475545425241459)
        ·
          refine ⟨379510733316713318137862189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253007155544475545425241459 379510733316713318137862189)
          ·
            refine ⟨142316524993767494301698321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379510733316713318137862189 142316524993767494301698321)
            ·
              refine ⟨106737393745325620726273741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142316524993767494301698321 106737393745325620726273741)
              ·
                refine ⟨40026522654497107772352653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106737393745325620726273741 40026522654497107772352653)
                ·
                  refine ⟨15009945995436415414632245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40026522654497107772352653 15009945995436415414632245)
                  ·
                    refine ⟨1407182437072163945121773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15009945995436415414632245 1407182437072163945121773)
                    ·
                      rfl

theorem cell23_8221434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_8221434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221434 prefixEnd_8221434 := by exact prefixLift 8221434
  have htrace : WordTrace (prefixWord ++ tailWord_8221434) baseStart_8221434 baseEnd_8221434 := by
    simpa [prefixWord, tailWord_8221434, baseEnd_8221434] using wordTrace_append hprefix tailTrace_8221434
  have hstable : (prefixWord ++ tailWord_8221434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221434).length < 2 ^ (prefixWord ++ tailWord_8221434).sum := by decide
  have hdescent : baseEnd_8221434 < baseStart_8221434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221442 : List Nat := [3, 4, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_8221442 : Nat := 118140960795 + 8221442 * 2 ^ 59
def prefixEnd_8221442 : Nat := 4983230072969 + 3 ^ 40 * 8221442 * 2
def baseEnd_8221442 : Nat := 1407183806353909268021761

theorem tailTrace_8221442 : CollatzResearch.WordTrace tailWord_8221442 prefixEnd_8221442 1407183806353909268021761 := by
  unfold tailWord_8221442
  simp only [CollatzResearch.WordTrace]
  refine ⟨74965156070281804837940645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199907082854084812901175053 74965156070281804837940645)
  ·
    refine ⟨14055966763177838407113871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74965156070281804837940645 14055966763177838407113871)
    ·
      refine ⟨21083950144766757610670807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14055966763177838407113871 21083950144766757610670807)
      ·
        refine ⟨31625925217150136416006211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21083950144766757610670807 31625925217150136416006211)
        ·
          refine ⟨47438887825725204624009317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31625925217150136416006211 47438887825725204624009317)
          ·
            refine ⟨8894791467323475867001747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47438887825725204624009317 8894791467323475867001747)
            ·
              refine ⟨13342187200985213800502621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8894791467323475867001747 13342187200985213800502621)
              ·
                refine ⟨5003320200369455175188483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13342187200985213800502621 5003320200369455175188483)
                ·
                  refine ⟨7504980300554182762782725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003320200369455175188483 7504980300554182762782725)
                  ·
                    refine ⟨1407183806353909268021761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504980300554182762782725 1407183806353909268021761)
                    ·
                      rfl

theorem cell23_8221442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_8221442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221442 prefixEnd_8221442 := by exact prefixLift 8221442
  have htrace : WordTrace (prefixWord ++ tailWord_8221442) baseStart_8221442 baseEnd_8221442 := by
    simpa [prefixWord, tailWord_8221442, baseEnd_8221442] using wordTrace_append hprefix tailTrace_8221442
  have hstable : (prefixWord ++ tailWord_8221442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221442).length < 2 ^ (prefixWord ++ tailWord_8221442).sum := by decide
  have hdescent : baseEnd_8221442 < baseStart_8221442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221481 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 2, 4]
def baseStart_8221481 : Nat := 118140960795 + 8221481 * 2 ^ 59
def prefixEnd_8221481 : Nat := 4983230072969 + 3 ^ 40 * 8221481 * 2
def baseEnd_8221481 : Nat := 1407190481602417717159201

theorem tailTrace_8221481 : CollatzResearch.WordTrace tailWord_8221481 prefixEnd_8221481 1407190481602417717159201 := by
  unfold tailWord_8221481
  simp only [CollatzResearch.WordTrace]
  refine ⟨299862046727985929012432297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199908031151990619341621531 299862046727985929012432297)
  ·
    refine ⟨224896535045989446759324223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299862046727985929012432297 224896535045989446759324223)
    ·
      refine ⟨337344802568984170138986335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224896535045989446759324223 337344802568984170138986335)
      ·
        refine ⟨506017203853476255208479503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337344802568984170138986335 506017203853476255208479503)
        ·
          refine ⟨759025805780214382812719255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506017203853476255208479503 759025805780214382812719255)
          ·
            refine ⟨1138538708670321574219078883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759025805780214382812719255 1138538708670321574219078883)
            ·
              refine ⟨1707808063005482361328618325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138538708670321574219078883 1707808063005482361328618325)
              ·
                refine ⟨10006687869172748210909873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1707808063005482361328618325 10006687869172748210909873)
                ·
                  refine ⟨7505015901879561158182405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10006687869172748210909873 7505015901879561158182405)
                  ·
                    refine ⟨1407190481602417717159201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7505015901879561158182405 1407190481602417717159201)
                    ·
                      rfl

theorem cell23_8221481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 4].length) (baseStart_8221481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221481 prefixEnd_8221481 := by exact prefixLift 8221481
  have htrace : WordTrace (prefixWord ++ tailWord_8221481) baseStart_8221481 baseEnd_8221481 := by
    simpa [prefixWord, tailWord_8221481, baseEnd_8221481] using wordTrace_append hprefix tailTrace_8221481
  have hstable : (prefixWord ++ tailWord_8221481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221481).length < 2 ^ (prefixWord ++ tailWord_8221481).sum := by decide
  have hdescent : baseEnd_8221481 < baseStart_8221481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221484 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_8221484 : Nat := 118140960795 + 8221484 * 2 ^ 59
def prefixEnd_8221484 : Nat := 4983230072969 + 3 ^ 40 * 8221484 * 2
def baseEnd_8221484 : Nat := 4221572985249216639740089

theorem tailTrace_8221484 : CollatzResearch.WordTrace tailWord_8221484 prefixEnd_8221484 4221572985249216639740089 := by
  unfold tailWord_8221484
  simp only [CollatzResearch.WordTrace]
  refine ⟨149931078073487530262395753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199908104097983373683194337 149931078073487530262395753)
  ·
    refine ⟨112448308555115647696796815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149931078073487530262395753 112448308555115647696796815)
    ·
      refine ⟨168672462832673471545195223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112448308555115647696796815 168672462832673471545195223)
      ·
        refine ⟨253008694249010207317792835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168672462832673471545195223 253008694249010207317792835)
        ·
          refine ⟨379513041373515310976689253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253008694249010207317792835 379513041373515310976689253)
          ·
            refine ⟨71158695257534120808129235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379513041373515310976689253 71158695257534120808129235)
            ·
              refine ⟨106738042886301181212193853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71158695257534120808129235 106738042886301181212193853)
              ·
                refine ⟨40026766082362942954572695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106738042886301181212193853 40026766082362942954572695)
                ·
                  refine ⟨60040149123544414431859043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40026766082362942954572695 60040149123544414431859043)
                  ·
                    refine ⟨90060223685316621647788565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60040149123544414431859043 90060223685316621647788565)
                    ·
                      refine ⟨4221572985249216639740089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90060223685316621647788565 4221572985249216639740089)
                      ·
                        rfl

theorem cell23_8221484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_8221484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221484 prefixEnd_8221484 := by exact prefixLift 8221484
  have htrace : WordTrace (prefixWord ++ tailWord_8221484) baseStart_8221484 baseEnd_8221484 := by
    simpa [prefixWord, tailWord_8221484, baseEnd_8221484] using wordTrace_append hprefix tailTrace_8221484
  have hstable : (prefixWord ++ tailWord_8221484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221484).length < 2 ^ (prefixWord ++ tailWord_8221484).sum := by decide
  have hdescent : baseEnd_8221484 < baseStart_8221484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221485 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_8221485 : Nat := 118140960795 + 8221485 * 2 ^ 59
def prefixEnd_8221485 : Nat := 4983230072969 + 3 ^ 40 * 8221485 * 2
def baseEnd_8221485 : Nat := 1407191166243290378609195

theorem tailTrace_8221485 : CollatzResearch.WordTrace tailWord_8221485 prefixEnd_8221485 1407191166243290378609195 := by
  unfold tailWord_8221485
  simp only [CollatzResearch.WordTrace]
  refine ⟨299862192619971437695577909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199908128413314291797051939 299862192619971437695577909)
  ·
    refine ⟨28112080558122322283960429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299862192619971437695577909 28112080558122322283960429)
    ·
      refine ⟨10542030209295870856485161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28112080558122322283960429 10542030209295870856485161)
      ·
        refine ⟨7906522656971903142363871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10542030209295870856485161 7906522656971903142363871)
        ·
          refine ⟨11859783985457854713545807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906522656971903142363871 11859783985457854713545807)
          ·
            refine ⟨17789675978186782070318711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11859783985457854713545807 17789675978186782070318711)
            ·
              refine ⟨26684513967280173105478067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17789675978186782070318711 26684513967280173105478067)
              ·
                refine ⟨40026770950920259658217101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26684513967280173105478067 40026770950920259658217101)
                ·
                  refine ⟨15010039106595097371831413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40026770950920259658217101 15010039106595097371831413)
                  ·
                    refine ⟨1407191166243290378609195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15010039106595097371831413 1407191166243290378609195)
                    ·
                      rfl

theorem cell23_8221485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_8221485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221485 prefixEnd_8221485 := by exact prefixLift 8221485
  have htrace : WordTrace (prefixWord ++ tailWord_8221485) baseStart_8221485 baseEnd_8221485 := by
    simpa [prefixWord, tailWord_8221485, baseEnd_8221485] using wordTrace_append hprefix tailTrace_8221485
  have hstable : (prefixWord ++ tailWord_8221485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221485).length < 2 ^ (prefixWord ++ tailWord_8221485).sum := by decide
  have hdescent : baseEnd_8221485 < baseStart_8221485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221488 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 3, 2, 2]
def baseStart_8221488 : Nat := 118140960795 + 8221488 * 2 ^ 59
def prefixEnd_8221488 : Nat := 4983230072969 + 3 ^ 40 * 8221488 * 2
def baseEnd_8221488 : Nat := 4221575039171834624090071

theorem tailTrace_8221488 : CollatzResearch.WordTrace tailWord_8221488 prefixEnd_8221488 4221575039171834624090071 := by
  unfold tailWord_8221488
  simp only [CollatzResearch.WordTrace]
  refine ⟨149931151019480284603968559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199908201359307046138624745 149931151019480284603968559)
  ·
    refine ⟨224896726529220426905952839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149931151019480284603968559 224896726529220426905952839)
    ·
      refine ⟨337345089793830640358929259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224896726529220426905952839 337345089793830640358929259)
      ·
        refine ⟨506017634690745960538393889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337345089793830640358929259 506017634690745960538393889)
        ·
          refine ⟨379513226018059470403795417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506017634690745960538393889 379513226018059470403795417)
          ·
            refine ⟨284634919513544602802846563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379513226018059470403795417 284634919513544602802846563)
            ·
              refine ⟨426952379270316904204269845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284634919513544602802846563 426952379270316904204269845)
              ·
                refine ⟨20013392778296104884575149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 426952379270316904204269845 20013392778296104884575149)
                ·
                  refine ⟨7505022291861039331715681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20013392778296104884575149 7505022291861039331715681)
                  ·
                    refine ⟨5628766718895779498786761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7505022291861039331715681 5628766718895779498786761)
                    ·
                      refine ⟨4221575039171834624090071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628766718895779498786761 4221575039171834624090071)
                      ·
                        rfl

theorem cell23_8221488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 2, 2].length) (baseStart_8221488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221488 prefixEnd_8221488 := by exact prefixLift 8221488
  have htrace : WordTrace (prefixWord ++ tailWord_8221488) baseStart_8221488 baseEnd_8221488 := by
    simpa [prefixWord, tailWord_8221488, baseEnd_8221488] using wordTrace_append hprefix tailTrace_8221488
  have hstable : (prefixWord ++ tailWord_8221488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221488).length < 2 ^ (prefixWord ++ tailWord_8221488).sum := by decide
  have hdescent : baseEnd_8221488 < baseStart_8221488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221492 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_8221492 : Nat := 118140960795 + 8221492 * 2 ^ 59
def prefixEnd_8221492 : Nat := 4983230072969 + 3 ^ 40 * 8221492 * 2
def baseEnd_8221492 : Nat := 4221577093094452608440053

theorem tailTrace_8221492 : CollatzResearch.WordTrace tailWord_8221492 prefixEnd_8221492 4221577093094452608440053 := by
  unfold tailWord_8221492
  simp only [CollatzResearch.WordTrace]
  refine ⟨149931223965473038945541365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199908298620630718594055153 149931223965473038945541365)
  ·
    refine ⟨14056052246763097401144503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149931223965473038945541365 14056052246763097401144503)
    ·
      refine ⟨21084078370144646101716755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14056052246763097401144503 21084078370144646101716755)
      ·
        refine ⟨31626117555216969152575133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21084078370144646101716755 31626117555216969152575133)
        ·
          refine ⟨11859794083206363432215675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31626117555216969152575133 11859794083206363432215675)
          ·
            refine ⟨17789691124809545148323513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11859794083206363432215675 17789691124809545148323513)
            ·
              refine ⟨13342268343607158861242635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17789691124809545148323513 13342268343607158861242635)
              ·
                refine ⟨20013402515410738291863953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13342268343607158861242635 20013402515410738291863953)
                ·
                  refine ⟨15010051886558053718897965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20013402515410738291863953 15010051886558053718897965)
                  ·
                    refine ⟨5628769457459270144586737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15010051886558053718897965 5628769457459270144586737)
                    ·
                      refine ⟨4221577093094452608440053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628769457459270144586737 4221577093094452608440053)
                      ·
                        rfl

theorem cell23_8221492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_8221492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221492 prefixEnd_8221492 := by exact prefixLift 8221492
  have htrace : WordTrace (prefixWord ++ tailWord_8221492) baseStart_8221492 baseEnd_8221492 := by
    simpa [prefixWord, tailWord_8221492, baseEnd_8221492] using wordTrace_append hprefix tailTrace_8221492
  have hstable : (prefixWord ++ tailWord_8221492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221492).length < 2 ^ (prefixWord ++ tailWord_8221492).sum := by decide
  have hdescent : baseEnd_8221492 < baseStart_8221492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221514 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_8221514 : Nat := 118140960795 + 8221514 * 2 ^ 59
def prefixEnd_8221514 : Nat := 4983230072969 + 3 ^ 40 * 8221514 * 2
def baseEnd_8221514 : Nat := 4221588389668851522364951

theorem tailTrace_8221514 : CollatzResearch.WordTrace tailWord_8221514 prefixEnd_8221514 4221588389668851522364951 := by
  unfold tailWord_8221514
  simp only [CollatzResearch.WordTrace]
  refine ⟨74965812584216593912095899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199908833557910917098922397 74965812584216593912095899)
  ·
    refine ⟨112448718876324890868143849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74965812584216593912095899 112448718876324890868143849)
    ·
      refine ⟨84336539157243668151107887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112448718876324890868143849 84336539157243668151107887)
      ·
        refine ⟨126504808735865502226661831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84336539157243668151107887 126504808735865502226661831)
        ·
          refine ⟨189757213103798253339992747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126504808735865502226661831 189757213103798253339992747)
          ·
            refine ⟨284635819655697380009989121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189757213103798253339992747 284635819655697380009989121)
            ·
              refine ⟨213476864741773035007491841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284635819655697380009989121 213476864741773035007491841)
              ·
                refine ⟨160107648556329776255618881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213476864741773035007491841 160107648556329776255618881)
                ·
                  refine ⟨120080736417247332191714161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160107648556329776255618881 120080736417247332191714161)
                  ·
                    refine ⟨90060552312935499143785621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120080736417247332191714161 90060552312935499143785621)
                    ·
                      refine ⟨4221588389668851522364951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90060552312935499143785621 4221588389668851522364951)
                      ·
                        rfl

theorem cell23_8221514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_8221514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221514 prefixEnd_8221514 := by exact prefixLift 8221514
  have htrace : WordTrace (prefixWord ++ tailWord_8221514) baseStart_8221514 baseEnd_8221514 := by
    simpa [prefixWord, tailWord_8221514, baseEnd_8221514] using wordTrace_append hprefix tailTrace_8221514
  have hstable : (prefixWord ++ tailWord_8221514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221514).length < 2 ^ (prefixWord ++ tailWord_8221514).sum := by decide
  have hdescent : baseEnd_8221514 < baseStart_8221514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221522 : List Nat := [3, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_8221522 : Nat := 118140960795 + 8221522 * 2 ^ 59
def prefixEnd_8221522 : Nat := 4983230072969 + 3 ^ 40 * 8221522 * 2
def baseEnd_8221522 : Nat := 4221592497514087491064915

theorem tailTrace_8221522 : CollatzResearch.WordTrace tailWord_8221522 prefixEnd_8221522 4221592497514087491064915 := by
  unfold tailWord_8221522
  simp only [CollatzResearch.WordTrace]
  refine ⟨74965885530209348253668705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199909028080558262009783213 74965885530209348253668705)
  ·
    refine ⟨56224414147657011190251529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74965885530209348253668705 56224414147657011190251529)
    ·
      refine ⟨42168310610742758392688647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56224414147657011190251529 42168310610742758392688647)
      ·
        refine ⟨63252465916114137589032971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42168310610742758392688647 63252465916114137589032971)
        ·
          refine ⟨94878698874171206383549457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63252465916114137589032971 94878698874171206383549457)
          ·
            refine ⟨71159024155628404787662093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94878698874171206383549457 71159024155628404787662093)
            ·
              refine ⟨26684634058360651795373285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71159024155628404787662093 26684634058360651795373285)
              ·
                refine ⟨5003368885942622211632491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26684634058360651795373285 5003368885942622211632491)
                ·
                  refine ⟨7505053328913933317448737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003368885942622211632491 7505053328913933317448737)
                  ·
                    refine ⟨5628789996685449988086553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7505053328913933317448737 5628789996685449988086553)
                    ·
                      refine ⟨4221592497514087491064915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628789996685449988086553 4221592497514087491064915)
                      ·
                        rfl

theorem cell23_8221522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_8221522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221522 prefixEnd_8221522 := by exact prefixLift 8221522
  have htrace : WordTrace (prefixWord ++ tailWord_8221522) baseStart_8221522 baseEnd_8221522 := by
    simpa [prefixWord, tailWord_8221522, baseEnd_8221522] using wordTrace_append hprefix tailTrace_8221522
  have hstable : (prefixWord ++ tailWord_8221522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221522).length < 2 ^ (prefixWord ++ tailWord_8221522).sum := by decide
  have hdescent : baseEnd_8221522 < baseStart_8221522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221548 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 3, 3, 2]
def baseStart_8221548 : Nat := 118140960795 + 8221548 * 2 ^ 59
def prefixEnd_8221548 : Nat := 4983230072969 + 3 ^ 40 * 8221548 * 2
def baseEnd_8221548 : Nat := 4221605848011104389339795

theorem tailTrace_8221548 : CollatzResearch.WordTrace tailWord_8221548 prefixEnd_8221548 4221605848011104389339795 := by
  unfold tailWord_8221548
  simp only [CollatzResearch.WordTrace]
  refine ⟨149932245209371599727560649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199909660279162132970080865 149932245209371599727560649)
  ·
    refine ⟨112449183907028699795670487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149932245209371599727560649 112449183907028699795670487)
    ·
      refine ⟨168673775860543049693505731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112449183907028699795670487 168673775860543049693505731)
      ·
        refine ⟨253010663790814574540258597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168673775860543049693505731 253010663790814574540258597)
        ·
          refine ⟨47439499460777732726298487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253010663790814574540258597 47439499460777732726298487)
          ·
            refine ⟨71159249191166599089447731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47439499460777732726298487 71159249191166599089447731)
            ·
              refine ⟨106738873786749898634171597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71159249191166599089447731 106738873786749898634171597)
              ·
                refine ⟨40027077670031211987814349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106738873786749898634171597 40027077670031211987814349)
                ·
                  refine ⟨15010154126261704495430381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40027077670031211987814349 15010154126261704495430381)
                  ·
                    refine ⟨5628807797348139185786393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15010154126261704495430381 5628807797348139185786393)
                    ·
                      refine ⟨4221605848011104389339795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628807797348139185786393 4221605848011104389339795)
                      ·
                        rfl

theorem cell23_8221548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_8221548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221548 prefixEnd_8221548 := by exact prefixLift 8221548
  have htrace : WordTrace (prefixWord ++ tailWord_8221548) baseStart_8221548 baseEnd_8221548 := by
    simpa [prefixWord, tailWord_8221548, baseEnd_8221548] using wordTrace_append hprefix tailTrace_8221548
  have hstable : (prefixWord ++ tailWord_8221548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221548).length < 2 ^ (prefixWord ++ tailWord_8221548).sum := by decide
  have hdescent : baseEnd_8221548 < baseStart_8221548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221591 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_8221591 : Nat := 118140960795 + 8221591 * 2 ^ 59
def prefixEnd_8221591 : Nat := 4983230072969 + 3 ^ 40 * 8221591 * 2
def baseEnd_8221591 : Nat := 4221627927679247721102097

theorem tailTrace_8221591 : CollatzResearch.WordTrace tailWord_8221591 prefixEnd_8221591 4221627927679247721102097 := by
  unfold tailWord_8221591
  simp only [CollatzResearch.WordTrace]
  refine ⟨299866058757587417798936627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199910705838391611865957751 299866058757587417798936627)
  ·
    refine ⟨449799088136381126698404941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299866058757587417798936627 449799088136381126698404941)
    ·
      refine ⟨168674658051142922511901853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449799088136381126698404941 168674658051142922511901853)
      ·
        refine ⟨63252996769178595941963195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168674658051142922511901853 63252996769178595941963195)
        ·
          refine ⟨94879495153767893912944793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63252996769178595941963195 94879495153767893912944793)
          ·
            refine ⟨71159621365325920434708595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94879495153767893912944793 71159621365325920434708595)
            ·
              refine ⟨106739432047988880652062893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71159621365325920434708595 106739432047988880652062893)
              ·
                refine ⟨40027287017995830244523585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106739432047988880652062893 40027287017995830244523585)
                ·
                  refine ⟨30020465263496872683392689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40027287017995830244523585 30020465263496872683392689)
                  ·
                    refine ⟨22515348947622654512544517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30020465263496872683392689 22515348947622654512544517)
                    ·
                      refine ⟨4221627927679247721102097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22515348947622654512544517 4221627927679247721102097)
                      ·
                        rfl

theorem cell23_8221591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_8221591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221591 prefixEnd_8221591 := by exact prefixLift 8221591
  have htrace : WordTrace (prefixWord ++ tailWord_8221591) baseStart_8221591 baseEnd_8221591 := by
    simpa [prefixWord, tailWord_8221591, baseEnd_8221591] using wordTrace_append hprefix tailTrace_8221591
  have hstable : (prefixWord ++ tailWord_8221591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221591).length < 2 ^ (prefixWord ++ tailWord_8221591).sum := by decide
  have hdescent : baseEnd_8221591 < baseStart_8221591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221668 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_8221668 : Nat := 118140960795 + 8221668 * 2 ^ 59
def prefixEnd_8221668 : Nat := 4983230072969 + 3 ^ 40 * 8221668 * 2
def baseEnd_8221668 : Nat := 4221667465689643919839243

theorem tailTrace_8221668 : CollatzResearch.WordTrace tailWord_8221668 prefixEnd_8221668 4221667465689643919839243 := by
  unfold tailWord_8221668
  simp only [CollatzResearch.WordTrace]
  refine ⟨149934433589154229974744829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199912578118872306632993105 149934433589154229974744829)
  ·
    refine ⟨56225412595932836240529311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149934433589154229974744829 56225412595932836240529311)
    ·
      refine ⟨84338118893899254360793967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56225412595932836240529311 84338118893899254360793967)
      ·
        refine ⟨126507178340848881541190951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84338118893899254360793967 126507178340848881541190951)
        ·
          refine ⟨189760767511273322311786427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126507178340848881541190951 189760767511273322311786427)
          ·
            refine ⟨284641151266909983467679641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189760767511273322311786427 284641151266909983467679641)
            ·
              refine ⟨213480863450182487600759731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284641151266909983467679641 213480863450182487600759731)
              ·
                refine ⟨320221295175273731401139597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213480863450182487600759731 320221295175273731401139597)
                ·
                  refine ⟨120082985690727649275427349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320221295175273731401139597 120082985690727649275427349)
                  ·
                    refine ⟨5628889954252858559785657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120082985690727649275427349 5628889954252858559785657)
                    ·
                      refine ⟨4221667465689643919839243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628889954252858559785657 4221667465689643919839243)
                      ·
                        rfl

theorem cell23_8221668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_8221668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221668 prefixEnd_8221668 := by exact prefixLift 8221668
  have htrace : WordTrace (prefixWord ++ tailWord_8221668) baseStart_8221668 baseEnd_8221668 := by
    simpa [prefixWord, tailWord_8221668, baseEnd_8221668] using wordTrace_append hprefix tailTrace_8221668
  have hstable : (prefixWord ++ tailWord_8221668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221668).length < 2 ^ (prefixWord ++ tailWord_8221668).sum := by decide
  have hdescent : baseEnd_8221668 < baseStart_8221668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221708 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 6]
def baseStart_8221708 : Nat := 118140960795 + 8221708 * 2 ^ 59
def prefixEnd_8221708 : Nat := 4983230072969 + 3 ^ 40 * 8221708 * 2
def baseEnd_8221708 : Nat := 469076444990647084815451

theorem tailTrace_8221708 : CollatzResearch.WordTrace tailWord_8221708 prefixEnd_8221708 469076444990647084815451 := by
  unfold tailWord_8221708
  simp only [CollatzResearch.WordTrace]
  refine ⟨149935163049081773390472889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199913550732109031187297185 149935163049081773390472889)
  ·
    refine ⟨112451372286811330042854667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149935163049081773390472889 112451372286811330042854667)
    ·
      refine ⟨168677058430216995064282001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112451372286811330042854667 168677058430216995064282001)
      ·
        refine ⟨126507793822662746298211501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168677058430216995064282001 126507793822662746298211501)
        ·
          refine ⟨47440422683498529861829313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126507793822662746298211501 47440422683498529861829313)
          ·
            refine ⟨35580317012623897396371985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47440422683498529861829313 35580317012623897396371985)
            ·
              refine ⟨26685237759467923047278989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35580317012623897396371985 26685237759467923047278989)
              ·
                refine ⟨10006964159800471142729621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26685237759467923047278989 10006964159800471142729621)
                ·
                  refine ⟨469076444990647084815451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10006964159800471142729621 469076444990647084815451)
                  ·
                    rfl

theorem cell23_8221708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_8221708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221708 prefixEnd_8221708 := by exact prefixLift 8221708
  have htrace : WordTrace (prefixWord ++ tailWord_8221708) baseStart_8221708 baseEnd_8221708 := by
    simpa [prefixWord, tailWord_8221708, baseEnd_8221708] using wordTrace_append hprefix tailTrace_8221708
  have hstable : (prefixWord ++ tailWord_8221708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221708).length < 2 ^ (prefixWord ++ tailWord_8221708).sum := by decide
  have hdescent : baseEnd_8221708 < baseStart_8221708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221745 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 4, 3, 2]
def baseStart_8221745 : Nat := 118140960795 + 8221745 * 2 ^ 59
def prefixEnd_8221745 : Nat := 4983230072969 + 3 ^ 40 * 8221745 * 2
def baseEnd_8221745 : Nat := 4221707003700040118576389

theorem tailTrace_8221745 : CollatzResearch.WordTrace tailWord_8221745 prefixEnd_8221745 4221707003700040118576389 := by
  unfold tailWord_8221745
  simp only [CollatzResearch.WordTrace]
  refine ⟨299871675599029502100042689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199914450399353001400028459 299871675599029502100042689)
  ·
    refine ⟨224903756699272126575032017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299871675599029502100042689 224903756699272126575032017)
    ·
      refine ⟨168677817524454094931274013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224903756699272126575032017 168677817524454094931274013)
      ·
        refine ⟨63254181571670285599227755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168677817524454094931274013 63254181571670285599227755)
        ·
          refine ⟨94881272357505428398841633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63254181571670285599227755 94881272357505428398841633)
          ·
            refine ⟨71160954268129071299131225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94881272357505428398841633 71160954268129071299131225)
            ·
              refine ⟨53370715701096803474348419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71160954268129071299131225 53370715701096803474348419)
              ·
                refine ⟨80056073551645205211522629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53370715701096803474348419 80056073551645205211522629)
                ·
                  refine ⟨15010513790933475977160493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80056073551645205211522629 15010513790933475977160493)
                  ·
                    refine ⟨5628942671600053491435185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15010513790933475977160493 5628942671600053491435185)
                    ·
                      refine ⟨4221707003700040118576389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5628942671600053491435185 4221707003700040118576389)
                      ·
                        rfl

theorem cell23_8221745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_8221745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221745 prefixEnd_8221745 := by exact prefixLift 8221745
  have htrace : WordTrace (prefixWord ++ tailWord_8221745) baseStart_8221745 baseEnd_8221745 := by
    simpa [prefixWord, tailWord_8221745, baseEnd_8221745] using wordTrace_append hprefix tailTrace_8221745
  have hstable : (prefixWord ++ tailWord_8221745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221745).length < 2 ^ (prefixWord ++ tailWord_8221745).sum := by decide
  have hdescent : baseEnd_8221745 < baseStart_8221745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221752 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 3, 1, 3]
def baseStart_8221752 : Nat := 118140960795 + 8221752 * 2 ^ 59
def prefixEnd_8221752 : Nat := 4983230072969 + 3 ^ 40 * 8221752 * 2
def baseEnd_8221752 : Nat := 4221710598064621591188857

theorem tailTrace_8221752 : CollatzResearch.WordTrace tailWord_8221752 prefixEnd_8221752 4221710598064621591188857 := by
  unfold tailWord_8221752
  simp only [CollatzResearch.WordTrace]
  refine ⟨149935965455002071147773755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199914620606669428197031673 149935965455002071147773755)
  ·
    refine ⟨224903948182503106721660633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149935965455002071147773755 224903948182503106721660633)
    ·
      refine ⟨168677961136877330041245475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224903948182503106721660633 168677961136877330041245475)
      ·
        refine ⟨253016941705315995061868213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168677961136877330041245475 253016941705315995061868213)
        ·
          refine ⟨23720338284873374537050145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253016941705315995061868213 23720338284873374537050145)
          ·
            refine ⟨17790253713655030902787609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23720338284873374537050145 17790253713655030902787609)
            ·
              refine ⟨13342690285241273177090707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17790253713655030902787609 13342690285241273177090707)
              ·
                refine ⟨20014035427861909765636061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13342690285241273177090707 20014035427861909765636061)
                ·
                  refine ⟨7505263285448216162113523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20014035427861909765636061 7505263285448216162113523)
                  ·
                    refine ⟨11257894928172324243170285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7505263285448216162113523 11257894928172324243170285)
                    ·
                      refine ⟨4221710598064621591188857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11257894928172324243170285 4221710598064621591188857)
                      ·
                        rfl

theorem cell23_8221752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_8221752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221752 prefixEnd_8221752 := by exact prefixLift 8221752
  have htrace : WordTrace (prefixWord ++ tailWord_8221752) baseStart_8221752 baseEnd_8221752 := by
    simpa [prefixWord, tailWord_8221752, baseEnd_8221752] using wordTrace_append hprefix tailTrace_8221752
  have hstable : (prefixWord ++ tailWord_8221752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221752).length < 2 ^ (prefixWord ++ tailWord_8221752).sum := by decide
  have hdescent : baseEnd_8221752 < baseStart_8221752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221829 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 3]
def baseStart_8221829 : Nat := 118140960795 + 8221829 * 2 ^ 59
def prefixEnd_8221829 : Nat := 4983230072969 + 3 ^ 40 * 8221829 * 2
def baseEnd_8221829 : Nat := 4221750136075017789926003

theorem tailTrace_8221829 : CollatzResearch.WordTrace tailWord_8221829 prefixEnd_8221829 4221750136075017789926003 := by
  unfold tailWord_8221829
  simp only [CollatzResearch.WordTrace]
  refine ⟨299874739330725184446100541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199916492887150122964067027 299874739330725184446100541)
  ·
    refine ⟨112453027249021944167287703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299874739330725184446100541 112453027249021944167287703)
    ·
      refine ⟨168679540873532916250931555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112453027249021944167287703 168679540873532916250931555)
      ·
        refine ⟨253019311310299374376397333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168679540873532916250931555 253019311310299374376397333)
        ·
          refine ⟨11860280217670283173893625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253019311310299374376397333 11860280217670283173893625)
          ·
            refine ⟨8895210163252712380420219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11860280217670283173893625 8895210163252712380420219)
            ·
              refine ⟨13342815244879068570630329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8895210163252712380420219 13342815244879068570630329)
              ·
                refine ⟨10007111433659301427972747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13342815244879068570630329 10007111433659301427972747)
                ·
                  refine ⟨15010667150488952141959121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10007111433659301427972747 15010667150488952141959121)
                  ·
                    refine ⟨11258000362866714106469341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15010667150488952141959121 11258000362866714106469341)
                    ·
                      refine ⟨4221750136075017789926003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11258000362866714106469341 4221750136075017789926003)
                      ·
                        rfl

theorem cell23_8221829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_8221829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221829 prefixEnd_8221829 := by exact prefixLift 8221829
  have htrace : WordTrace (prefixWord ++ tailWord_8221829) baseStart_8221829 baseEnd_8221829 := by
    simpa [prefixWord, tailWord_8221829, baseEnd_8221829] using wordTrace_append hprefix tailTrace_8221829
  have hstable : (prefixWord ++ tailWord_8221829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221829).length < 2 ^ (prefixWord ++ tailWord_8221829).sum := by decide
  have hdescent : baseEnd_8221829 < baseStart_8221829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221842 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_8221842 : Nat := 118140960795 + 8221842 * 2 ^ 59
def prefixEnd_8221842 : Nat := 4983230072969 + 3 ^ 40 * 8221842 * 2
def baseEnd_8221842 : Nat := 4221756811323526239063443

theorem tailTrace_8221842 : CollatzResearch.WordTrace tailWord_8221842 prefixEnd_8221842 4221756811323526239063443 := by
  unfold tailWord_8221842
  simp only [CollatzResearch.WordTrace]
  refine ⟨74968803369919521916580945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199916808986452058444215853 74968803369919521916580945)
  ·
    refine ⟨56226602527439641437435709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74968803369919521916580945 56226602527439641437435709)
    ·
      refine ⟨21084975947789865539038391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56226602527439641437435709 21084975947789865539038391)
      ·
        refine ⟨31627463921684798308557587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21084975947789865539038391 31627463921684798308557587)
        ·
          refine ⟨47441195882527197462836381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31627463921684798308557587 47441195882527197462836381)
          ·
            refine ⟨17790448455947699048563643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47441195882527197462836381 17790448455947699048563643)
            ·
              refine ⟨26685672683921548572845465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17790448455947699048563643 26685672683921548572845465)
              ·
                refine ⟨20014254512941161429634099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26685672683921548572845465 20014254512941161429634099)
                ·
                  refine ⟨30021381769411742144451149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20014254512941161429634099 30021381769411742144451149)
                  ·
                    refine ⟨11258018163529403304169181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30021381769411742144451149 11258018163529403304169181)
                    ·
                      refine ⟨4221756811323526239063443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11258018163529403304169181 4221756811323526239063443)
                      ·
                        rfl

theorem cell23_8221842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_8221842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221842 prefixEnd_8221842 := by exact prefixLift 8221842
  have htrace : WordTrace (prefixWord ++ tailWord_8221842) baseStart_8221842 baseEnd_8221842 := by
    simpa [prefixWord, tailWord_8221842, baseEnd_8221842] using wordTrace_append hprefix tailTrace_8221842
  have hstable : (prefixWord ++ tailWord_8221842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221842).length < 2 ^ (prefixWord ++ tailWord_8221842).sum := by decide
  have hdescent : baseEnd_8221842 < baseStart_8221842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221868 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_8221868 : Nat := 118140960795 + 8221868 * 2 ^ 59
def prefixEnd_8221868 : Nat := 4983230072969 + 3 ^ 40 * 8221868 * 2
def baseEnd_8221868 : Nat := 4221770161820543137338323

theorem tailTrace_8221868 : CollatzResearch.WordTrace tailWord_8221868 prefixEnd_8221868 4221770161820543137338323 := by
  unfold tailWord_8221868
  simp only [CollatzResearch.WordTrace]
  refine ⟨149938080888791947053385129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199917441185055929404513505 149938080888791947053385129)
  ·
    refine ⟨112453560666593960290038847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149938080888791947053385129 112453560666593960290038847)
    ·
      refine ⟨168680340999890940435058271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112453560666593960290038847 168680340999890940435058271)
      ·
        refine ⟨253020511499836410652587407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168680340999890940435058271 253020511499836410652587407)
        ·
          refine ⟨379530767249754615978881111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253020511499836410652587407 379530767249754615978881111)
          ·
            refine ⟨569296150874631923968321667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379530767249754615978881111 569296150874631923968321667)
            ·
              refine ⟨853944226311947885952482501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569296150874631923968321667 853944226311947885952482501)
              ·
                refine ⟨160114542433490228616090469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 853944226311947885952482501 160114542433490228616090469)
                ·
                  refine ⟨30021476706279417865516963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160114542433490228616090469 30021476706279417865516963)
                  ·
                    refine ⟨45032215059419126798275445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30021476706279417865516963 45032215059419126798275445)
                    ·
                      refine ⟨4221770161820543137338323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45032215059419126798275445 4221770161820543137338323)
                      ·
                        rfl

theorem cell23_8221868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_8221868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221868 prefixEnd_8221868 := by exact prefixLift 8221868
  have htrace : WordTrace (prefixWord ++ tailWord_8221868) baseStart_8221868 baseEnd_8221868 := by
    simpa [prefixWord, tailWord_8221868, baseEnd_8221868] using wordTrace_append hprefix tailTrace_8221868
  have hstable : (prefixWord ++ tailWord_8221868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221868).length < 2 ^ (prefixWord ++ tailWord_8221868).sum := by decide
  have hdescent : baseEnd_8221868 < baseStart_8221868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221882 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2]
def baseStart_8221882 : Nat := 118140960795 + 8221882 * 2 ^ 59
def prefixEnd_8221882 : Nat := 4983230072969 + 3 ^ 40 * 8221882 * 2
def baseEnd_8221882 : Nat := 4221777350549706082563259

theorem tailTrace_8221882 : CollatzResearch.WordTrace tailWord_8221882 prefixEnd_8221882 4221777350549706082563259 := by
  unfold tailWord_8221882
  simp only [CollatzResearch.WordTrace]
  refine ⟨74969168099883293624444975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199917781599688782998519933 74969168099883293624444975)
  ·
    refine ⟨112453752149824940436667463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74969168099883293624444975 112453752149824940436667463)
    ·
      refine ⟨168680628224737410655001195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112453752149824940436667463 168680628224737410655001195)
      ·
        refine ⟨253020942337106115982501793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168680628224737410655001195 253020942337106115982501793)
        ·
          refine ⟨189765706752829586986876345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253020942337106115982501793 189765706752829586986876345)
          ·
            refine ⟨142324280064622190240157259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189765706752829586986876345 142324280064622190240157259)
            ·
              refine ⟨213486420096933285360235889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142324280064622190240157259 213486420096933285360235889)
              ·
                refine ⟨160114815072699964020176917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213486420096933285360235889 160114815072699964020176917)
                ·
                  refine ⟨7505381956532810813445793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160114815072699964020176917 7505381956532810813445793)
                  ·
                    refine ⟨5629036467399608110084345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7505381956532810813445793 5629036467399608110084345)
                    ·
                      refine ⟨4221777350549706082563259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629036467399608110084345 4221777350549706082563259)
                      ·
                        rfl

theorem cell23_8221882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_8221882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221882 prefixEnd_8221882 := by exact prefixLift 8221882
  have htrace : WordTrace (prefixWord ++ tailWord_8221882) baseStart_8221882 baseEnd_8221882 := by
    simpa [prefixWord, tailWord_8221882, baseEnd_8221882] using wordTrace_append hprefix tailTrace_8221882
  have hstable : (prefixWord ++ tailWord_8221882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221882).length < 2 ^ (prefixWord ++ tailWord_8221882).sum := by decide
  have hdescent : baseEnd_8221882 < baseStart_8221882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221910 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_8221910 : Nat := 118140960795 + 8221910 * 2 ^ 59
def prefixEnd_8221910 : Nat := 4983230072969 + 3 ^ 40 * 8221910 * 2
def baseEnd_8221910 : Nat := 4221791728008031973013131

theorem tailTrace_8221910 : CollatzResearch.WordTrace tailWord_8221910 prefixEnd_8221910 4221791728008031973013131 := by
  unfold tailWord_8221910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18742355852714483454987449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199918462428954490186532789 18742355852714483454987449)
  ·
    refine ⟨14056766889535862591240587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18742355852714483454987449 14056766889535862591240587)
    ·
      refine ⟨21085150334303793886860881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14056766889535862591240587 21085150334303793886860881)
      ·
        refine ⟨15813862750727845415145661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21085150334303793886860881 15813862750727845415145661)
        ·
          refine ⟨5930198531522942030679623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15813862750727845415145661 5930198531522942030679623)
          ·
            refine ⟨8895297797284413046019435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5930198531522942030679623 8895297797284413046019435)
            ·
              refine ⟨13342946695926619569029153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8895297797284413046019435 13342946695926619569029153)
              ·
                refine ⟨10007210021944964676771865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13342946695926619569029153 10007210021944964676771865)
                ·
                  refine ⟨7505407516458723507578899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10007210021944964676771865 7505407516458723507578899)
                  ·
                    refine ⟨11258111274688085261368349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7505407516458723507578899 11258111274688085261368349)
                    ·
                      refine ⟨4221791728008031973013131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11258111274688085261368349 4221791728008031973013131)
                      ·
                        rfl

theorem cell23_8221910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_8221910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221910 prefixEnd_8221910 := by exact prefixLift 8221910
  have htrace : WordTrace (prefixWord ++ tailWord_8221910) baseStart_8221910 baseEnd_8221910 := by
    simpa [prefixWord, tailWord_8221910, baseEnd_8221910] using wordTrace_append hprefix tailTrace_8221910
  have hstable : (prefixWord ++ tailWord_8221910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221910).length < 2 ^ (prefixWord ++ tailWord_8221910).sum := by decide
  have hdescent : baseEnd_8221910 < baseStart_8221910 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221933 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_8221933 : Nat := 118140960795 + 8221933 * 2 ^ 59
def prefixEnd_8221933 : Nat := 4983230072969 + 3 ^ 40 * 8221933 * 2
def baseEnd_8221933 : Nat := 4221803538063085383025525

theorem tailTrace_8221933 : CollatzResearch.WordTrace tailWord_8221933 prefixEnd_8221933 4221803538063085383025525 := by
  unfold tailWord_8221933
  simp only [CollatzResearch.WordTrace]
  refine ⟨299878532522348410207886453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199919021681565606805257635 299878532522348410207886453)
  ·
    refine ⟨28113612423970163456989355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299878532522348410207886453 28113612423970163456989355)
    ·
      refine ⟨42170418635955245185484033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28113612423970163456989355 42170418635955245185484033)
      ·
        refine ⟨31627813976966433889113025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42170418635955245185484033 31627813976966433889113025)
        ·
          refine ⟨23720860482724825416834769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31627813976966433889113025 23720860482724825416834769)
          ·
            refine ⟨17790645362043619062626077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23720860482724825416834769 17790645362043619062626077)
            ·
              refine ⟨6671492010766357148484779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17790645362043619062626077 6671492010766357148484779)
              ·
                refine ⟨10007238016149535722727169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671492010766357148484779 10007238016149535722727169)
                ·
                  refine ⟨7505428512112151792045377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10007238016149535722727169 7505428512112151792045377)
                  ·
                    refine ⟨5629071384084113844034033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7505428512112151792045377 5629071384084113844034033)
                    ·
                      refine ⟨4221803538063085383025525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629071384084113844034033 4221803538063085383025525)
                      ·
                        rfl

theorem cell23_8221933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_8221933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221933 prefixEnd_8221933 := by exact prefixLift 8221933
  have htrace : WordTrace (prefixWord ++ tailWord_8221933) baseStart_8221933 baseEnd_8221933 := by
    simpa [prefixWord, tailWord_8221933, baseEnd_8221933] using wordTrace_append hprefix tailTrace_8221933
  have hstable : (prefixWord ++ tailWord_8221933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221933).length < 2 ^ (prefixWord ++ tailWord_8221933).sum := by decide
  have hdescent : baseEnd_8221933 < baseStart_8221933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8221955 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 4]
def baseStart_8221955 : Nat := 118140960795 + 8221955 * 2 ^ 59
def prefixEnd_8221955 : Nat := 4983230072969 + 3 ^ 40 * 8221955 * 2
def baseEnd_8221955 : Nat := 4221814834637484296950423

theorem tailTrace_8221955 : CollatzResearch.WordTrace tailWord_8221955 prefixEnd_8221955 4221814834637484296950423 := by
  unfold tailWord_8221955
  simp only [CollatzResearch.WordTrace]
  refine ⟨299879334928268707965187319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199919556618845805310124879 299879334928268707965187319)
  ·
    refine ⟨449819002392403061947780979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299879334928268707965187319 449819002392403061947780979)
    ·
      refine ⟨674728503588604592921671469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449819002392403061947780979 674728503588604592921671469)
      ·
        refine ⟨253023188845726722345626801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674728503588604592921671469 253023188845726722345626801)
        ·
          refine ⟨189767391634295041759220101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253023188845726722345626801 189767391634295041759220101)
          ·
            refine ⟨35581385931430320329853769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189767391634295041759220101 35581385931430320329853769)
            ·
              refine ⟨26686039448572740247390327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35581385931430320329853769 26686039448572740247390327)
              ·
                refine ⟨40029059172859110371085491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26686039448572740247390327 40029059172859110371085491)
                ·
                  refine ⟨60043588759288665556628237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40029059172859110371085491 60043588759288665556628237)
                  ·
                    refine ⟨22516345784733249583735589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60043588759288665556628237 22516345784733249583735589)
                    ·
                      refine ⟨4221814834637484296950423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22516345784733249583735589 4221814834637484296950423)
                      ·
                        rfl

theorem cell23_8221955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_8221955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8221955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8221955 prefixEnd_8221955 := by exact prefixLift 8221955
  have htrace : WordTrace (prefixWord ++ tailWord_8221955) baseStart_8221955 baseEnd_8221955 := by
    simpa [prefixWord, tailWord_8221955, baseEnd_8221955] using wordTrace_append hprefix tailTrace_8221955
  have hstable : (prefixWord ++ tailWord_8221955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8221955).length < 2 ^ (prefixWord ++ tailWord_8221955).sum := by decide
  have hdescent : baseEnd_8221955 < baseStart_8221955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8221955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222056 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_8222056 : Nat := 118140960795 + 8222056 * 2 ^ 59
def prefixEnd_8222056 : Nat := 4983230072969 + 3 ^ 40 * 8222056 * 2
def baseEnd_8222056 : Nat := 4221866696183588401787459

theorem tailTrace_8222056 : CollatzResearch.WordTrace tailWord_8222056 prefixEnd_8222056 4221866696183588401787459 := by
  unfold tailWord_8222056
  simp only [CollatzResearch.WordTrace]
  refine ⟨149941509350451401107307011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199922012467268534809742681 149941509350451401107307011)
  ·
    refine ⟨224912264025677101660960517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149941509350451401107307011 224912264025677101660960517)
    ·
      refine ⟨42171049504814456561430097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224912264025677101660960517 42171049504814456561430097)
      ·
        refine ⟨31628287128610842421072573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42171049504814456561430097 31628287128610842421072573)
        ·
          refine ⟨11860607673229065907902215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31628287128610842421072573 11860607673229065907902215)
          ·
            refine ⟨17790911509843598861853323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11860607673229065907902215 17790911509843598861853323)
            ·
              refine ⟨26686367264765398292779985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17790911509843598861853323 26686367264765398292779985)
              ·
                refine ⟨20014775448574048719584989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26686367264765398292779985 20014775448574048719584989)
                ·
                  refine ⟨7505540793215268269844371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20014775448574048719584989 7505540793215268269844371)
                  ·
                    refine ⟨11258311189822902404766557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7505540793215268269844371 11258311189822902404766557)
                    ·
                      refine ⟨4221866696183588401787459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11258311189822902404766557 4221866696183588401787459)
                      ·
                        rfl

theorem cell23_8222056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_8222056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222056 prefixEnd_8222056 := by exact prefixLift 8222056
  have htrace : WordTrace (prefixWord ++ tailWord_8222056) baseStart_8222056 baseEnd_8222056 := by
    simpa [prefixWord, tailWord_8222056, baseEnd_8222056] using wordTrace_append hprefix tailTrace_8222056
  have hstable : (prefixWord ++ tailWord_8222056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222056).length < 2 ^ (prefixWord ++ tailWord_8222056).sum := by decide
  have hdescent : baseEnd_8222056 < baseStart_8222056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222089 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 4, 4]
def baseStart_8222089 : Nat := 118140960795 + 8222089 * 2 ^ 59
def prefixEnd_8222089 : Nat := 4983230072969 + 3 ^ 40 * 8222089 * 2
def baseEnd_8222089 : Nat := 1407294547015062257558269

theorem tailTrace_8222089 : CollatzResearch.WordTrace tailWord_8222089 prefixEnd_8222089 1407294547015062257558269 := by
  unfold tailWord_8222089
  simp only [CollatzResearch.WordTrace]
  refine ⟨299884222309783248850565321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199922814873188832567043547 299884222309783248850565321)
  ·
    refine ⟨224913166732337436637923991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299884222309783248850565321 224913166732337436637923991)
    ·
      refine ⟨337369750098506154956885987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224913166732337436637923991 337369750098506154956885987)
      ·
        refine ⟨506054625147759232435328981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337369750098506154956885987 506054625147759232435328981)
        ·
          refine ⟨11860655276900607010203023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 506054625147759232435328981 11860655276900607010203023)
          ·
            refine ⟨17790982915350910515304535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11860655276900607010203023 17790982915350910515304535)
            ·
              refine ⟨26686474373026365772956803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17790982915350910515304535 26686474373026365772956803)
              ·
                refine ⟨40029711559539548659435205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26686474373026365772956803 40029711559539548659435205)
                ·
                  refine ⟨7505570917413665373644101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40029711559539548659435205 7505570917413665373644101)
                  ·
                    refine ⟨1407294547015062257558269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7505570917413665373644101 1407294547015062257558269)
                    ·
                      rfl

theorem cell23_8222089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 4].length) (baseStart_8222089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222089 prefixEnd_8222089 := by exact prefixLift 8222089
  have htrace : WordTrace (prefixWord ++ tailWord_8222089) baseStart_8222089 baseEnd_8222089 := by
    simpa [prefixWord, tailWord_8222089, baseEnd_8222089] using wordTrace_append hprefix tailTrace_8222089
  have hstable : (prefixWord ++ tailWord_8222089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222089).length < 2 ^ (prefixWord ++ tailWord_8222089).sum := by decide
  have hdescent : baseEnd_8222089 < baseStart_8222089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222106 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_8222106 : Nat := 118140960795 + 8222106 * 2 ^ 59
def prefixEnd_8222106 : Nat := 4983230072969 + 3 ^ 40 * 8222106 * 2
def baseEnd_8222106 : Nat := 1407297456738771068720743

theorem tailTrace_8222106 : CollatzResearch.WordTrace tailWord_8222106 prefixEnd_8222106 1407297456738771068720743 := by
  unfold tailWord_8222106
  simp only [CollatzResearch.WordTrace]
  refine ⟨74971210587680415188483543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199923228233814440502622781 74971210587680415188483543)
  ·
    refine ⟨112456815881520622782725315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74971210587680415188483543 112456815881520622782725315)
    ·
      refine ⟨168685223822280934174087973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112456815881520622782725315 168685223822280934174087973)
      ·
        refine ⟨31628479466677675157641495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168685223822280934174087973 31628479466677675157641495)
        ·
          refine ⟨47442719200016512736462243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31628479466677675157641495 47442719200016512736462243)
          ·
            refine ⟨71164078800024769104693365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47442719200016512736462243 71164078800024769104693365)
            ·
              refine ⟨6671632387502322103565003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71164078800024769104693365 6671632387502322103565003)
              ·
                refine ⟨10007448581253483155347505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671632387502322103565003 10007448581253483155347505)
                ·
                  refine ⟨7505586435940112366510629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10007448581253483155347505 7505586435940112366510629)
                  ·
                    refine ⟨1407297456738771068720743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7505586435940112366510629 1407297456738771068720743)
                    ·
                      rfl

theorem cell23_8222106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_8222106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222106 prefixEnd_8222106 := by exact prefixLift 8222106
  have htrace : WordTrace (prefixWord ++ tailWord_8222106) baseStart_8222106 baseEnd_8222106 := by
    simpa [prefixWord, tailWord_8222106, baseEnd_8222106] using wordTrace_append hprefix tailTrace_8222106
  have hstable : (prefixWord ++ tailWord_8222106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222106).length < 2 ^ (prefixWord ++ tailWord_8222106).sum := by decide
  have hdescent : baseEnd_8222106 < baseStart_8222106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222109 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_8222109 : Nat := 118140960795 + 8222109 * 2 ^ 59
def prefixEnd_8222109 : Nat := 4983230072969 + 3 ^ 40 * 8222109 * 2
def baseEnd_8222109 : Nat := 4221893910658276694424715

theorem tailTrace_8222109 : CollatzResearch.WordTrace tailWord_8222109 prefixEnd_8222109 4221893910658276694424715 := by
  unfold tailWord_8222109
  simp only [CollatzResearch.WordTrace]
  refine ⟨299884951769710792266293381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199923301179807194844195587 299884951769710792266293381)
  ·
    refine ⟨56228428456820773549930009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299884951769710792266293381 56228428456820773549930009)
    ·
      refine ⟨42171321342615580162447507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56228428456820773549930009 42171321342615580162447507)
      ·
        refine ⟨63256982013923370243671261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42171321342615580162447507 63256982013923370243671261)
        ·
          refine ⟨23721368255221263841376723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63256982013923370243671261 23721368255221263841376723)
          ·
            refine ⟨35582052382831895762065085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23721368255221263841376723 35582052382831895762065085)
            ·
              refine ⟨13343269643561960910774407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35582052382831895762065085 13343269643561960910774407)
              ·
                refine ⟨20014904465342941366161611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13343269643561960910774407 20014904465342941366161611)
                ·
                  refine ⟨30022356698014412049242417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20014904465342941366161611 30022356698014412049242417)
                  ·
                    refine ⟨22516767523510809036931813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30022356698014412049242417 22516767523510809036931813)
                    ·
                      refine ⟨4221893910658276694424715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22516767523510809036931813 4221893910658276694424715)
                      ·
                        rfl

theorem cell23_8222109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_8222109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222109 prefixEnd_8222109 := by exact prefixLift 8222109
  have htrace : WordTrace (prefixWord ++ tailWord_8222109) baseStart_8222109 baseEnd_8222109 := by
    simpa [prefixWord, tailWord_8222109, baseEnd_8222109] using wordTrace_append hprefix tailTrace_8222109
  have hstable : (prefixWord ++ tailWord_8222109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222109).length < 2 ^ (prefixWord ++ tailWord_8222109).sum := by decide
  have hdescent : baseEnd_8222109 < baseStart_8222109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222129 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 3]
def baseStart_8222129 : Nat := 118140960795 + 8222129 * 2 ^ 59
def prefixEnd_8222129 : Nat := 4983230072969 + 3 ^ 40 * 8222129 * 2
def baseEnd_8222129 : Nat := 4221904180271366616174623

theorem tailTrace_8222129 : CollatzResearch.WordTrace tailWord_8222129 prefixEnd_8222129 4221904180271366616174623 := by
  unfold tailWord_8222129
  simp only [CollatzResearch.WordTrace]
  refine ⟨299885681229638335682021441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199923787486425557121347627 299885681229638335682021441)
  ·
    refine ⟨224914260922228751761516081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299885681229638335682021441 224914260922228751761516081)
    ·
      refine ⟨168685695691671563821137061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224914260922228751761516081 168685695691671563821137061)
      ·
        refine ⟨31628567942188418216463199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168685695691671563821137061 31628567942188418216463199)
        ·
          refine ⟨47442851913282627324694799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31628567942188418216463199 47442851913282627324694799)
          ·
            refine ⟨71164277869923940987042199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47442851913282627324694799 71164277869923940987042199)
            ·
              refine ⟨106746416804885911480563299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71164277869923940987042199 106746416804885911480563299)
              ·
                refine ⟨160119625207328867220844949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106746416804885911480563299 160119625207328867220844949)
                ·
                  refine ⟨7505607431593540650977107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160119625207328867220844949 7505607431593540650977107)
                  ·
                    refine ⟨11258411147390310976465661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7505607431593540650977107 11258411147390310976465661)
                    ·
                      refine ⟨4221904180271366616174623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11258411147390310976465661 4221904180271366616174623)
                      ·
                        rfl

theorem cell23_8222129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_8222129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222129 prefixEnd_8222129 := by exact prefixLift 8222129
  have htrace : WordTrace (prefixWord ++ tailWord_8222129) baseStart_8222129 baseEnd_8222129 := by
    simpa [prefixWord, tailWord_8222129, baseEnd_8222129] using wordTrace_append hprefix tailTrace_8222129
  have hstable : (prefixWord ++ tailWord_8222129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222129).length < 2 ^ (prefixWord ++ tailWord_8222129).sum := by decide
  have hdescent : baseEnd_8222129 < baseStart_8222129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222142 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_8222142 : Nat := 118140960795 + 8222142 * 2 ^ 59
def prefixEnd_8222142 : Nat := 4983230072969 + 3 ^ 40 * 8222142 * 2
def baseEnd_8222142 : Nat := 4221910855519875065312063

theorem tailTrace_8222142 : CollatzResearch.WordTrace tailWord_8222142 prefixEnd_8222142 4221910855519875065312063 := by
  unfold tailWord_8222142
  simp only [CollatzResearch.WordTrace]
  refine ⟨37485769422323904862780585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199924103585727492601496453 37485769422323904862780585)
  ·
    refine ⟨28114327066742928647085439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37485769422323904862780585 28114327066742928647085439)
    ·
      refine ⟨42171490600114392970628159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28114327066742928647085439 42171490600114392970628159)
      ·
        refine ⟨63257235900171589455942239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42171490600114392970628159 63257235900171589455942239)
        ·
          refine ⟨94885853850257384183913359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63257235900171589455942239 94885853850257384183913359)
          ·
            refine ⟨142328780775386076275870039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94885853850257384183913359 142328780775386076275870039)
            ·
              refine ⟨213493171163079114413805059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142328780775386076275870039 213493171163079114413805059)
              ·
                refine ⟨320239756744618671620707589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213493171163079114413805059 320239756744618671620707589)
                ·
                  refine ⟨60044954389616000928882673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320239756744618671620707589 60044954389616000928882673)
                  ·
                    refine ⟨45033715792212000696662005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60044954389616000928882673 45033715792212000696662005)
                    ·
                      refine ⟨4221910855519875065312063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45033715792212000696662005 4221910855519875065312063)
                      ·
                        rfl

theorem cell23_8222142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_8222142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222142 prefixEnd_8222142 := by exact prefixLift 8222142
  have htrace : WordTrace (prefixWord ++ tailWord_8222142) baseStart_8222142 baseEnd_8222142 := by
    simpa [prefixWord, tailWord_8222142, baseEnd_8222142] using wordTrace_append hprefix tailTrace_8222142
  have hstable : (prefixWord ++ tailWord_8222142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222142).length < 2 ^ (prefixWord ++ tailWord_8222142).sum := by decide
  have hdescent : baseEnd_8222142 < baseStart_8222142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222152 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_8222152 : Nat := 118140960795 + 8222152 * 2 ^ 59
def prefixEnd_8222152 : Nat := 4983230072969 + 3 ^ 40 * 8222152 * 2
def baseEnd_8222152 : Nat := 4221915990326420026187017

theorem tailTrace_8222152 : CollatzResearch.WordTrace tailWord_8222152 prefixEnd_8222152 4221915990326420026187017 := by
  unfold tailWord_8222152
  simp only [CollatzResearch.WordTrace]
  refine ⟨149943260054277505305054355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199924346739036673740072473 149943260054277505305054355)
  ·
    refine ⟨224914890081416257957581533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149943260054277505305054355 224914890081416257957581533)
    ·
      refine ⟨84343083780531096734093075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224914890081416257957581533 84343083780531096734093075)
      ·
        refine ⟨126514625670796645101139613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84343083780531096734093075 126514625670796645101139613)
        ·
          refine ⟨47442984626548741912927355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126514625670796645101139613 47442984626548741912927355)
          ·
            refine ⟨71164476939823112869391033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47442984626548741912927355 71164476939823112869391033)
            ·
              refine ⟨53373357704867334652043275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71164476939823112869391033 53373357704867334652043275)
              ·
                refine ⟨80060036557301001978064913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53373357704867334652043275 80060036557301001978064913)
                ·
                  refine ⟨60045027417975751483548685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80060036557301001978064913 60045027417975751483548685)
                  ·
                    refine ⟨22516885281740906806330757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60045027417975751483548685 22516885281740906806330757)
                    ·
                      refine ⟨4221915990326420026187017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22516885281740906806330757 4221915990326420026187017)
                      ·
                        rfl

theorem cell23_8222152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_8222152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222152 prefixEnd_8222152 := by exact prefixLift 8222152
  have htrace : WordTrace (prefixWord ++ tailWord_8222152) baseStart_8222152 baseEnd_8222152 := by
    simpa [prefixWord, tailWord_8222152, baseEnd_8222152] using wordTrace_append hprefix tailTrace_8222152
  have hstable : (prefixWord ++ tailWord_8222152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222152).length < 2 ^ (prefixWord ++ tailWord_8222152).sum := by decide
  have hdescent : baseEnd_8222152 < baseStart_8222152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222173 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_8222173 : Nat := 118140960795 + 8222173 * 2 ^ 59
def prefixEnd_8222173 : Nat := 4983230072969 + 3 ^ 40 * 8222173 * 2
def baseEnd_8222173 : Nat := 4221926773420164444024421

theorem tailTrace_8222173 : CollatzResearch.WordTrace tailWord_8222173 prefixEnd_8222173 4221926773420164444024421 := by
  unfold tailWord_8222173
  simp only [CollatzResearch.WordTrace]
  refine ⟨299887286041478931196623173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199924857360985954131082115 299887286041478931196623173)
  ·
    refine ⟨56228866132777299599366845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299887286041478931196623173 56228866132777299599366845)
    ·
      refine ⟨21085824799791487349762567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56228866132777299599366845 21085824799791487349762567)
      ·
        refine ⟨31628737199687231024643851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21085824799791487349762567 31628737199687231024643851)
        ·
          refine ⟨47443105799530846536965777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31628737199687231024643851 47443105799530846536965777)
          ·
            refine ⟨35582329349648134902724333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47443105799530846536965777 35582329349648134902724333)
            ·
              refine ⟨13343373506118050588521625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35582329349648134902724333 13343373506118050588521625)
              ·
                refine ⟨10007530129588537941391219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13343373506118050588521625 10007530129588537941391219)
                ·
                  refine ⟨15011295194382806912086829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10007530129588537941391219 15011295194382806912086829)
                  ·
                    refine ⟨5629235697893552592032561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15011295194382806912086829 5629235697893552592032561)
                    ·
                      refine ⟨4221926773420164444024421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629235697893552592032561 4221926773420164444024421)
                      ·
                        rfl

theorem cell23_8222173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_8222173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222173 prefixEnd_8222173 := by exact prefixLift 8222173
  have htrace : WordTrace (prefixWord ++ tailWord_8222173) baseStart_8222173 baseEnd_8222173 := by
    simpa [prefixWord, tailWord_8222173, baseEnd_8222173] using wordTrace_append hprefix tailTrace_8222173
  have hstable : (prefixWord ++ tailWord_8222173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222173).length < 2 ^ (prefixWord ++ tailWord_8222173).sum := by decide
  have hdescent : baseEnd_8222173 < baseStart_8222173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222239 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 2, 5]
def baseStart_8222239 : Nat := 118140960795 + 8222239 * 2 ^ 59
def prefixEnd_8222239 : Nat := 4983230072969 + 3 ^ 40 * 8222239 * 2
def baseEnd_8222239 : Nat := 1407320221047787061933039

theorem tailTrace_8222239 : CollatzResearch.WordTrace tailWord_8222239 prefixEnd_8222239 1407320221047787061933039 := by
  unfold tailWord_8222239
  simp only [CollatzResearch.WordTrace]
  refine ⟨299889693259239824468525771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199926462172826549645683847 299889693259239824468525771)
  ·
    refine ⟨449834539888859736702788657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299889693259239824468525771 449834539888859736702788657)
    ·
      refine ⟨337375904916644802527091493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449834539888859736702788657 337375904916644802527091493)
      ·
        refine ⟨63257982171870900473829655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337375904916644802527091493 63257982171870900473829655)
        ·
          refine ⟨94886973257806350710744483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63257982171870900473829655 94886973257806350710744483)
          ·
            refine ⟨142330459886709526066116725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94886973257806350710744483 142330459886709526066116725)
            ·
              refine ⟨13343480614379018068698443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142330459886709526066116725 13343480614379018068698443)
              ·
                refine ⟨20015220921568527103047665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13343480614379018068698443 20015220921568527103047665)
                ·
                  refine ⟨15011415691176395327285749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20015220921568527103047665 15011415691176395327285749)
                  ·
                    refine ⟨1407320221047787061933039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15011415691176395327285749 1407320221047787061933039)
                    ·
                      rfl

theorem cell23_8222239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_8222239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222239 prefixEnd_8222239 := by exact prefixLift 8222239
  have htrace : WordTrace (prefixWord ++ tailWord_8222239) baseStart_8222239 baseEnd_8222239 := by
    simpa [prefixWord, tailWord_8222239, baseEnd_8222239] using wordTrace_append hprefix tailTrace_8222239
  have hstable : (prefixWord ++ tailWord_8222239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222239).length < 2 ^ (prefixWord ++ tailWord_8222239).sum := by decide
  have hdescent : baseEnd_8222239 < baseStart_8222239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222272 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_8222272 : Nat := 118140960795 + 8222272 * 2 ^ 59
def prefixEnd_8222272 : Nat := 4983230072969 + 3 ^ 40 * 8222272 * 2
def baseEnd_8222272 : Nat := 4221977608004959556686465

theorem tailTrace_8222272 : CollatzResearch.WordTrace tailWord_8222272 prefixEnd_8222272 4221977608004959556686465 := by
  unfold tailWord_8222272
  simp only [CollatzResearch.WordTrace]
  refine ⟨149945448434060135552238535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199927264578746847402984713 149945448434060135552238535)
  ·
    refine ⟨224918172651090203328357803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149945448434060135552238535 224918172651090203328357803)
    ·
      refine ⟨337377258976635304992536705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224918172651090203328357803 337377258976635304992536705)
      ·
        refine ⟨253032944232476478744402529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337377258976635304992536705 253032944232476478744402529)
        ·
          refine ⟨189774708174357359058301897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253032944232476478744402529 189774708174357359058301897)
          ·
            refine ⟨142331031130768019293726423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189774708174357359058301897 142331031130768019293726423)
            ·
              refine ⟨213496546696152028940589635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142331031130768019293726423 213496546696152028940589635)
              ·
                refine ⟨320244820044228043410884453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213496546696152028940589635 320244820044228043410884453)
                ·
                  refine ⟨60045903758292758139540835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320244820044228043410884453 60045903758292758139540835)
                  ·
                    refine ⟨90068855637439137209311253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60045903758292758139540835 90068855637439137209311253)
                    ·
                      refine ⟨4221977608004959556686465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90068855637439137209311253 4221977608004959556686465)
                      ·
                        rfl

theorem cell23_8222272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_8222272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222272 prefixEnd_8222272 := by exact prefixLift 8222272
  have htrace : WordTrace (prefixWord ++ tailWord_8222272) baseStart_8222272 baseEnd_8222272 := by
    simpa [prefixWord, tailWord_8222272, baseEnd_8222272] using wordTrace_append hprefix tailTrace_8222272
  have hstable : (prefixWord ++ tailWord_8222272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222272).length < 2 ^ (prefixWord ++ tailWord_8222272).sum := by decide
  have hdescent : baseEnd_8222272 < baseStart_8222272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222294 : List Nat := [5, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_8222294 : Nat := 118140960795 + 8222294 * 2 ^ 59
def prefixEnd_8222294 : Nat := 4983230072969 + 3 ^ 40 * 8222294 * 2
def baseEnd_8222294 : Nat := 469109878286595385623485

theorem tailTrace_8222294 : CollatzResearch.WordTrace tailWord_8222294 prefixEnd_8222294 469109878286595385623485 := by
  unfold tailWord_8222294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18743231204627535553861121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199927799516027045907851957 18743231204627535553861121)
  ·
    refine ⟨14057423403470651665395841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18743231204627535553861121 14057423403470651665395841)
    ·
      refine ⟨10543067552602988749046881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14057423403470651665395841 10543067552602988749046881)
      ·
        refine ⟨7907300664452241561785161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10543067552602988749046881 7907300664452241561785161)
        ·
          refine ⟨5930475498339181171338871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7907300664452241561785161 5930475498339181171338871)
          ·
            refine ⟨8895713247508771757008307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5930475498339181171338871 8895713247508771757008307)
            ·
              refine ⟨13343569871263157635512461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8895713247508771757008307 13343569871263157635512461)
              ·
                refine ⟨5003838701723684113317173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13343569871263157635512461 5003838701723684113317173)
                ·
                  refine ⟨469109878286595385623485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5003838701723684113317173 469109878286595385623485)
                  ·
                    rfl

theorem cell23_8222294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_8222294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222294 prefixEnd_8222294 := by exact prefixLift 8222294
  have htrace : WordTrace (prefixWord ++ tailWord_8222294) baseStart_8222294 baseEnd_8222294 := by
    simpa [prefixWord, tailWord_8222294, baseEnd_8222294] using wordTrace_append hprefix tailTrace_8222294
  have hstable : (prefixWord ++ tailWord_8222294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222294).length < 2 ^ (prefixWord ++ tailWord_8222294).sum := by decide
  have hdescent : baseEnd_8222294 < baseStart_8222294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222320 : List Nat := [2, 1, 1, 1, 6, 2, 3, 2, 1, 4]
def baseStart_8222320 : Nat := 118140960795 + 8222320 * 2 ^ 59
def prefixEnd_8222320 : Nat := 4983230072969 + 3 ^ 40 * 8222320 * 2
def baseEnd_8222320 : Nat := 1407334085025458456295415

theorem tailTrace_8222320 : CollatzResearch.WordTrace tailWord_8222320 prefixEnd_8222320 1407334085025458456295415 := by
  unfold tailWord_8222320
  simp only [CollatzResearch.WordTrace]
  refine ⟨149946323785973187651112207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199928431714630916868149609 149946323785973187651112207)
  ·
    refine ⟨224919485678959781476668311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149946323785973187651112207 224919485678959781476668311)
    ·
      refine ⟨337379228518439672215002467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224919485678959781476668311 337379228518439672215002467)
      ·
        refine ⟨506068842777659508322503701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337379228518439672215002467 506068842777659508322503701)
        ·
          refine ⟨23721977005202789452617361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 506068842777659508322503701 23721977005202789452617361)
          ·
            refine ⟨17791482753902092089463021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23721977005202789452617361 17791482753902092089463021)
            ·
              refine ⟨6671806032713284533548633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17791482753902092089463021 6671806032713284533548633)
              ·
                refine ⟨5003854524534963400161475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6671806032713284533548633 5003854524534963400161475)
                ·
                  refine ⟨7505781786802445100242213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003854524534963400161475 7505781786802445100242213)
                  ·
                    refine ⟨1407334085025458456295415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7505781786802445100242213 1407334085025458456295415)
                    ·
                      rfl

theorem cell23_8222320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 4].length) (baseStart_8222320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222320 prefixEnd_8222320 := by exact prefixLift 8222320
  have htrace : WordTrace (prefixWord ++ tailWord_8222320) baseStart_8222320 baseEnd_8222320 := by
    simpa [prefixWord, tailWord_8222320, baseEnd_8222320] using wordTrace_append hprefix tailTrace_8222320
  have hstable : (prefixWord ++ tailWord_8222320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222320).length < 2 ^ (prefixWord ++ tailWord_8222320).sum := by decide
  have hdescent : baseEnd_8222320 < baseStart_8222320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222329 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 3, 5]
def baseStart_8222329 : Nat := 118140960795 + 8222329 * 2 ^ 59
def prefixEnd_8222329 : Nat := 4983230072969 + 3 ^ 40 * 8222329 * 2
def baseEnd_8222329 : Nat := 1407335625467421944557901

theorem tailTrace_8222329 : CollatzResearch.WordTrace tailWord_8222329 prefixEnd_8222329 1407335625467421944557901 := by
  unfold tailWord_8222329
  simp only [CollatzResearch.WordTrace]
  refine ⟨299892975828913769839302041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199928650552609179892868027 299892975828913769839302041)
  ·
    refine ⟨224919731871685327379476531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299892975828913769839302041 224919731871685327379476531)
    ·
      refine ⟨337379597807527991069214797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224919731871685327379476531 337379597807527991069214797)
      ·
        refine ⟨126517349177822996650955549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337379597807527991069214797 126517349177822996650955549)
        ·
          refine ⟨47444005941683623744108331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126517349177822996650955549 47444005941683623744108331)
          ·
            refine ⟨71166008912525435616162497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47444005941683623744108331 71166008912525435616162497)
            ·
              refine ⟨53374506684394076712121873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71166008912525435616162497 53374506684394076712121873)
              ·
                refine ⟨40030880013295557534091405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53374506684394076712121873 40030880013295557534091405)
                ·
                  refine ⟨15011580004985834075284277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40030880013295557534091405 15011580004985834075284277)
                  ·
                    refine ⟨1407335625467421944557901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15011580004985834075284277 1407335625467421944557901)
                    ·
                      rfl

theorem cell23_8222329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_8222329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222329 prefixEnd_8222329 := by exact prefixLift 8222329
  have htrace : WordTrace (prefixWord ++ tailWord_8222329) baseStart_8222329 baseEnd_8222329 := by
    simpa [prefixWord, tailWord_8222329, baseEnd_8222329] using wordTrace_append hprefix tailTrace_8222329
  have hstable : (prefixWord ++ tailWord_8222329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222329).length < 2 ^ (prefixWord ++ tailWord_8222329).sum := by decide
  have hdescent : baseEnd_8222329 < baseStart_8222329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222333 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 6]
def baseStart_8222333 : Nat := 118140960795 + 8222333 * 2 ^ 59
def prefixEnd_8222333 : Nat := 4983230072969 + 3 ^ 40 * 8222333 * 2
def baseEnd_8222333 : Nat := 469112103369431535335965

theorem tailTrace_8222333 : CollatzResearch.WordTrace tailWord_8222333 prefixEnd_8222333 469112103369431535335965 := by
  unfold tailWord_8222333
  simp only [CollatzResearch.WordTrace]
  refine ⟨299893121720899278522447653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199928747813932852348298435 299893121720899278522447653)
  ·
    refine ⟨56229960322668614722958935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299893121720899278522447653 56229960322668614722958935)
    ·
      refine ⟨84344940484002922084438403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56229960322668614722958935 84344940484002922084438403)
      ·
        refine ⟨126517410726004383126657605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84344940484002922084438403 126517410726004383126657605)
        ·
          refine ⟨23722014511125821836248301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126517410726004383126657605 23722014511125821836248301)
          ·
            refine ⟨8895755441672183188593113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23722014511125821836248301 8895755441672183188593113)
            ·
              refine ⟨6671816581254137391444835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8895755441672183188593113 6671816581254137391444835)
              ·
                refine ⟨10007724871881206087167253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671816581254137391444835 10007724871881206087167253)
                ·
                  refine ⟨469112103369431535335965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10007724871881206087167253 469112103369431535335965)
                  ·
                    rfl

theorem cell23_8222333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_8222333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222333 prefixEnd_8222333 := by exact prefixLift 8222333
  have htrace : WordTrace (prefixWord ++ tailWord_8222333) baseStart_8222333 baseEnd_8222333 := by
    simpa [prefixWord, tailWord_8222333, baseEnd_8222333] using wordTrace_append hprefix tailTrace_8222333
  have hstable : (prefixWord ++ tailWord_8222333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222333).length < 2 ^ (prefixWord ++ tailWord_8222333).sum := by decide
  have hdescent : baseEnd_8222333 < baseStart_8222333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222336 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 4, 3, 2]
def baseStart_8222336 : Nat := 118140960795 + 8222336 * 2 ^ 59
def prefixEnd_8222336 : Nat := 4983230072969 + 3 ^ 40 * 8222336 * 2
def baseEnd_8222336 : Nat := 4222010470766847306286171

theorem tailTrace_8222336 : CollatzResearch.WordTrace tailWord_8222336 prefixEnd_8222336 4222010470766847306286171 := by
  unfold tailWord_8222336
  simp only [CollatzResearch.WordTrace]
  refine ⟨149946615569944205017403431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199928820759925606689871241 149946615569944205017403431)
  ·
    refine ⟨224919923354916307526105147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149946615569944205017403431 224919923354916307526105147)
    ·
      refine ⟨337379885032374461289157721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224919923354916307526105147 337379885032374461289157721)
      ·
        refine ⟨253034913774280845966868291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337379885032374461289157721 253034913774280845966868291)
        ·
          refine ⟨379552370661421268950302437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253034913774280845966868291 379552370661421268950302437)
          ·
            refine ⟨71166069499016487928181707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379552370661421268950302437 71166069499016487928181707)
            ·
              refine ⟨106749104248524731892272561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71166069499016487928181707 106749104248524731892272561)
              ·
                refine ⟨80061828186393548919204421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106749104248524731892272561 80061828186393548919204421)
                ·
                  refine ⟨15011592784948790422350829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80061828186393548919204421 15011592784948790422350829)
                  ·
                    refine ⟨5629347294355796408381561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15011592784948790422350829 5629347294355796408381561)
                    ·
                      refine ⟨4222010470766847306286171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629347294355796408381561 4222010470766847306286171)
                      ·
                        rfl

theorem cell23_8222336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_8222336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222336 prefixEnd_8222336 := by exact prefixLift 8222336
  have htrace : WordTrace (prefixWord ++ tailWord_8222336) baseStart_8222336 baseEnd_8222336 := by
    simpa [prefixWord, tailWord_8222336, baseEnd_8222336] using wordTrace_append hprefix tailTrace_8222336
  have hstable : (prefixWord ++ tailWord_8222336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222336).length < 2 ^ (prefixWord ++ tailWord_8222336).sum := by decide
  have hdescent : baseEnd_8222336 < baseStart_8222336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222346 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_8222346 : Nat := 118140960795 + 8222346 * 2 ^ 59
def prefixEnd_8222346 : Nat := 4983230072969 + 3 ^ 40 * 8222346 * 2
def baseEnd_8222346 : Nat := 1407338535191130755720375

theorem tailTrace_8222346 : CollatzResearch.WordTrace tailWord_8222346 prefixEnd_8222346 1407338535191130755720375 := by
  unfold tailWord_8222346
  simp only [CollatzResearch.WordTrace]
  refine ⟨74973398967463045435667723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199929063913234787828447261 74973398967463045435667723)
  ·
    refine ⟨112460098451194568153501585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74973398967463045435667723 112460098451194568153501585)
    ·
      refine ⟨84345073838395926115126189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112460098451194568153501585 84345073838395926115126189)
      ·
        refine ⟨31629402689398472293172321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84345073838395926115126189 31629402689398472293172321)
        ·
          refine ⟨23722052017048854219879241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31629402689398472293172321 23722052017048854219879241)
          ·
            refine ⟨17791539012786640664909431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23722052017048854219879241 17791539012786640664909431)
            ·
              refine ⟨26687308519179960997364147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17791539012786640664909431 26687308519179960997364147)
              ·
                refine ⟨40030962778769941496046221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26687308519179960997364147 40030962778769941496046221)
                ·
                  refine ⟨15011611042038728061017333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40030962778769941496046221 15011611042038728061017333)
                  ·
                    refine ⟨1407338535191130755720375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15011611042038728061017333 1407338535191130755720375)
                    ·
                      rfl

theorem cell23_8222346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_8222346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222346 prefixEnd_8222346 := by exact prefixLift 8222346
  have htrace : WordTrace (prefixWord ++ tailWord_8222346) baseStart_8222346 baseEnd_8222346 := by
    simpa [prefixWord, tailWord_8222346, baseEnd_8222346] using wordTrace_append hprefix tailTrace_8222346
  have hstable : (prefixWord ++ tailWord_8222346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222346).length < 2 ^ (prefixWord ++ tailWord_8222346).sum := by decide
  have hdescent : baseEnd_8222346 < baseStart_8222346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222359 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 3, 6]
def baseStart_8222359 : Nat := 118140960795 + 8222359 * 2 ^ 59
def prefixEnd_8222359 : Nat := 4983230072969 + 3 ^ 40 * 8222359 * 2
def baseEnd_8222359 : Nat := 1407340760273966905432855

theorem tailTrace_8222359 : CollatzResearch.WordTrace tailWord_8222359 prefixEnd_8222359 1407340760273966905432855 := by
  unfold tailWord_8222359
  simp only [CollatzResearch.WordTrace]
  refine ⟨299894070018805084962894131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199929380012536723308596087 299894070018805084962894131)
  ·
    refine ⟨449841105028207627444341197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299894070018805084962894131 449841105028207627444341197)
    ·
      refine ⟨168690414385577860291627949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449841105028207627444341197 168690414385577860291627949)
      ·
        refine ⟨63258905394591697609360481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168690414385577860291627949 63258905394591697609360481)
        ·
          refine ⟨47444179045943773207020361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63258905394591697609360481 47444179045943773207020361)
          ·
            refine ⟨35583134284457829905265271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47444179045943773207020361 35583134284457829905265271)
            ·
              refine ⟨53374701426686744857897907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35583134284457829905265271 53374701426686744857897907)
              ·
                refine ⟨80062052140030117286846861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53374701426686744857897907 80062052140030117286846861)
                ·
                  refine ⟨30023269552511293982567573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80062052140030117286846861 30023269552511293982567573)
                  ·
                    refine ⟨1407340760273966905432855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30023269552511293982567573 1407340760273966905432855)
                    ·
                      rfl

theorem cell23_8222359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_8222359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222359 prefixEnd_8222359 := by exact prefixLift 8222359
  have htrace : WordTrace (prefixWord ++ tailWord_8222359) baseStart_8222359 baseEnd_8222359 := by
    simpa [prefixWord, tailWord_8222359, baseEnd_8222359] using wordTrace_append hprefix tailTrace_8222359
  have hstable : (prefixWord ++ tailWord_8222359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222359).length < 2 ^ (prefixWord ++ tailWord_8222359).sum := by decide
  have hdescent : baseEnd_8222359 < baseStart_8222359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222383 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 3, 2, 2]
def baseStart_8222383 : Nat := 118140960795 + 8222383 * 2 ^ 59
def prefixEnd_8222383 : Nat := 4983230072969 + 3 ^ 40 * 8222383 * 2
def baseEnd_8222383 : Nat := 4222034604357608622398455

theorem tailTrace_8222383 : CollatzResearch.WordTrace tailWord_8222383 prefixEnd_8222383 4222034604357608622398455 := by
  unfold tailWord_8222383
  simp only [CollatzResearch.WordTrace]
  refine ⟨299894945370718137061767803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199929963580478758041178535 299894945370718137061767803)
  ·
    refine ⟨449842418056077205592651705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299894945370718137061767803 449842418056077205592651705)
    ·
      refine ⟨337381813542057904194488779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449842418056077205592651705 337381813542057904194488779)
      ·
        refine ⟨506072720313086856291733169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337381813542057904194488779 506072720313086856291733169)
        ·
          refine ⟨379554540234815142218799877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506072720313086856291733169 379554540234815142218799877)
          ·
            refine ⟨71166476294027839166024977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379554540234815142218799877 71166476294027839166024977)
            ·
              refine ⟨53374857220520879374518733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71166476294027839166024977 53374857220520879374518733)
              ·
                refine ⟨20015571457695329765444525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53374857220520879374518733 20015571457695329765444525)
                ·
                  refine ⟨7505839296635748662041697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20015571457695329765444525 7505839296635748662041697)
                  ·
                    refine ⟨5629379472476811496531273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7505839296635748662041697 5629379472476811496531273)
                    ·
                      refine ⟨4222034604357608622398455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629379472476811496531273 4222034604357608622398455)
                      ·
                        rfl

theorem cell23_8222383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 2, 2].length) (baseStart_8222383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222383 prefixEnd_8222383 := by exact prefixLift 8222383
  have htrace : WordTrace (prefixWord ++ tailWord_8222383) baseStart_8222383 baseEnd_8222383 := by
    simpa [prefixWord, tailWord_8222383, baseEnd_8222383] using wordTrace_append hprefix tailTrace_8222383
  have hstable : (prefixWord ++ tailWord_8222383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222383).length < 2 ^ (prefixWord ++ tailWord_8222383).sum := by decide
  have hdescent : baseEnd_8222383 < baseStart_8222383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222386 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_8222386 : Nat := 118140960795 + 8222386 * 2 ^ 59
def prefixEnd_8222386 : Nat := 4983230072969 + 3 ^ 40 * 8222386 * 2
def baseEnd_8222386 : Nat := 4222036144799572110660941

theorem tailTrace_8222386 : CollatzResearch.WordTrace tailWord_8222386 prefixEnd_8222386 4222036144799572110660941 := by
  unfold tailWord_8222386
  simp only [CollatzResearch.WordTrace]
  refine ⟨74973763697426817143531753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199930036526471512382751341 74973763697426817143531753)
  ·
    refine ⟨56230322773070112857648815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74973763697426817143531753 56230322773070112857648815)
    ·
      refine ⟨84345484159605169286473223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56230322773070112857648815 84345484159605169286473223)
      ·
        refine ⟨126518226239407753929709835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84345484159605169286473223 126518226239407753929709835)
        ·
          refine ⟨189777339359111630894564753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126518226239407753929709835 189777339359111630894564753)
          ·
            refine ⟨142333004519333723170923565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189777339359111630894564753 142333004519333723170923565)
            ·
              refine ⟨53374876694750146189096337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142333004519333723170923565 53374876694750146189096337)
              ·
                refine ⟨40031157521062609641822253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53374876694750146189096337 40031157521062609641822253)
                ·
                  refine ⟨15011684070398478615683345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40031157521062609641822253 15011684070398478615683345)
                  ·
                    refine ⟨11258763052798858961762509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15011684070398478615683345 11258763052798858961762509)
                    ·
                      refine ⟨4222036144799572110660941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11258763052798858961762509 4222036144799572110660941)
                      ·
                        rfl

theorem cell23_8222386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_8222386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222386 prefixEnd_8222386 := by exact prefixLift 8222386
  have htrace : WordTrace (prefixWord ++ tailWord_8222386) baseStart_8222386 baseEnd_8222386 := by
    simpa [prefixWord, tailWord_8222386, baseEnd_8222386] using wordTrace_append hprefix tailTrace_8222386
  have hstable : (prefixWord ++ tailWord_8222386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222386).length < 2 ^ (prefixWord ++ tailWord_8222386).sum := by decide
  have hdescent : baseEnd_8222386 < baseStart_8222386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222396 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_8222396 : Nat := 118140960795 + 8222396 * 2 ^ 59
def prefixEnd_8222396 : Nat := 4983230072969 + 3 ^ 40 * 8222396 * 2
def baseEnd_8222396 : Nat := 4222041279606117071535895

theorem tailTrace_8222396 : CollatzResearch.WordTrace tailWord_8222396 prefixEnd_8222396 4222041279606117071535895 := by
  unfold tailWord_8222396
  simp only [CollatzResearch.WordTrace]
  refine ⟨149947709759835520140995521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199930279679780693521327361 149947709759835520140995521)
  ·
    refine ⟨112460782319876640105746641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149947709759835520140995521 112460782319876640105746641)
    ·
      refine ⟨84345586739907480079309981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112460782319876640105746641 84345586739907480079309981)
      ·
        refine ⟨31629595027465305029741243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84345586739907480079309981 31629595027465305029741243)
        ·
          refine ⟨47444392541197957544611865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31629595027465305029741243 47444392541197957544611865)
          ·
            refine ⟨35583294405898468158458899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47444392541197957544611865 35583294405898468158458899)
            ·
              refine ⟨53374941608847702237688349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35583294405898468158458899 53374941608847702237688349)
              ·
                refine ⟨20015603103317888339133131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53374941608847702237688349 20015603103317888339133131)
                ·
                  refine ⟨30023404654976832508699697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20015603103317888339133131 30023404654976832508699697)
                  ·
                    refine ⟨22517553491232624381524773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30023404654976832508699697 22517553491232624381524773)
                    ·
                      refine ⟨4222041279606117071535895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22517553491232624381524773 4222041279606117071535895)
                      ·
                        rfl

theorem cell23_8222396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_8222396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222396 prefixEnd_8222396 := by exact prefixLift 8222396
  have htrace : WordTrace (prefixWord ++ tailWord_8222396) baseStart_8222396 baseEnd_8222396 := by
    simpa [prefixWord, tailWord_8222396, baseEnd_8222396] using wordTrace_append hprefix tailTrace_8222396
  have hstable : (prefixWord ++ tailWord_8222396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222396).length < 2 ^ (prefixWord ++ tailWord_8222396).sum := by decide
  have hdescent : baseEnd_8222396 < baseStart_8222396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222417 : List Nat := [1, 2, 2, 1, 2, 5, 2, 3, 1, 2, 2]
def baseStart_8222417 : Nat := 118140960795 + 8222417 * 2 ^ 59
def prefixEnd_8222417 : Nat := 4983230072969 + 3 ^ 40 * 8222417 * 2
def baseEnd_8222417 : Nat := 4222052062699861489373299

theorem tailTrace_8222417 : CollatzResearch.WordTrace tailWord_8222417 prefixEnd_8222417 4222052062699861489373299 := by
  unfold tailWord_8222417
  simp only [CollatzResearch.WordTrace]
  refine ⟨299896185452594960868505505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199930790301729973912337003 299896185452594960868505505)
  ·
    refine ⟨224922139089446220651379129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299896185452594960868505505 224922139089446220651379129)
    ·
      refine ⟨168691604317084665488534347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224922139089446220651379129 168691604317084665488534347)
      ·
        refine ⟨253037406475626998232801521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168691604317084665488534347 253037406475626998232801521)
        ·
          refine ⟨189778054856720248674601141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253037406475626998232801521 189778054856720248674601141)
          ·
            refine ⟨17791692642817523313243857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189778054856720248674601141 17791692642817523313243857)
            ·
              refine ⟨13343769482113142484932893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17791692642817523313243857 13343769482113142484932893)
              ·
                refine ⟨5003913555792428431849835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13343769482113142484932893 5003913555792428431849835)
                ·
                  refine ⟨7505870333688642647774753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003913555792428431849835 7505870333688642647774753)
                  ·
                    refine ⟨5629402750266481985831065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7505870333688642647774753 5629402750266481985831065)
                    ·
                      refine ⟨4222052062699861489373299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629402750266481985831065 4222052062699861489373299)
                      ·
                        rfl

theorem cell23_8222417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 2, 2].length) (baseStart_8222417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222417 prefixEnd_8222417 := by exact prefixLift 8222417
  have htrace : WordTrace (prefixWord ++ tailWord_8222417) baseStart_8222417 baseEnd_8222417 := by
    simpa [prefixWord, tailWord_8222417, baseEnd_8222417] using wordTrace_append hprefix tailTrace_8222417
  have hstable : (prefixWord ++ tailWord_8222417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222417).length < 2 ^ (prefixWord ++ tailWord_8222417).sum := by decide
  have hdescent : baseEnd_8222417 < baseStart_8222417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222420 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_8222420 : Nat := 118140960795 + 8222420 * 2 ^ 59
def prefixEnd_8222420 : Nat := 4983230072969 + 3 ^ 40 * 8222420 * 2
def baseEnd_8222420 : Nat := 4222053603141824977635785

theorem tailTrace_8222420 : CollatzResearch.WordTrace tailWord_8222420 prefixEnd_8222420 4222053603141824977635785 := by
  unfold tailWord_8222420
  simp only [CollatzResearch.WordTrace]
  refine ⟨149948147435792046190432357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199930863247722728253909809 149948147435792046190432357)
  ·
    refine ⟨28115277644211008660706067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149948147435792046190432357 28115277644211008660706067)
    ·
      refine ⟨42172916466316512991059101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28115277644211008660706067 42172916466316512991059101)
      ·
        refine ⟨15814843674868692371647163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42172916466316512991059101 15814843674868692371647163)
        ·
          refine ⟨23722265512303038557470745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15814843674868692371647163 23722265512303038557470745)
          ·
            refine ⟨17791699134227278918103059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23722265512303038557470745 17791699134227278918103059)
            ·
              refine ⟨26687548701340918377154589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17791699134227278918103059 26687548701340918377154589)
              ·
                refine ⟨10007830763002844391432971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26687548701340918377154589 10007830763002844391432971)
                ·
                  refine ⟨15011746144504266587149457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10007830763002844391432971 15011746144504266587149457)
                  ·
                    refine ⟨11258809608378199940362093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15011746144504266587149457 11258809608378199940362093)
                    ·
                      refine ⟨4222053603141824977635785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11258809608378199940362093 4222053603141824977635785)
                      ·
                        rfl

theorem cell23_8222420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_8222420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222420 prefixEnd_8222420 := by exact prefixLift 8222420
  have htrace : WordTrace (prefixWord ++ tailWord_8222420) baseStart_8222420 baseEnd_8222420 := by
    simpa [prefixWord, tailWord_8222420, baseEnd_8222420] using wordTrace_append hprefix tailTrace_8222420
  have hstable : (prefixWord ++ tailWord_8222420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222420).length < 2 ^ (prefixWord ++ tailWord_8222420).sum := by decide
  have hdescent : baseEnd_8222420 < baseStart_8222420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222460 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_8222460 : Nat := 118140960795 + 8222460 * 2 ^ 59
def prefixEnd_8222460 : Nat := 4983230072969 + 3 ^ 40 * 8222460 * 2
def baseEnd_8222460 : Nat := 4222074142368004821135601

theorem tailTrace_8222460 : CollatzResearch.WordTrace tailWord_8222460 prefixEnd_8222460 4222074142368004821135601 := by
  unfold tailWord_8222460
  simp only [CollatzResearch.WordTrace]
  refine ⟨149948876895719589606160417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199931835860959452808213889 149948876895719589606160417)
  ·
    refine ⟨112461657671789692204620313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149948876895719589606160417 112461657671789692204620313)
    ·
      refine ⟨84346243253842269153465235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112461657671789692204620313 84346243253842269153465235)
      ·
        refine ⟨126519364880763403730197853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84346243253842269153465235 126519364880763403730197853)
        ·
          refine ⟨47444761830286276398824195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126519364880763403730197853 47444761830286276398824195)
          ·
            refine ⟨71167142745429414598236293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47444761830286276398824195 71167142745429414598236293)
            ·
              refine ⟨13343839264768015237169305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71167142745429414598236293 13343839264768015237169305)
              ·
                refine ⟨10007879448576011427876979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13343839264768015237169305 10007879448576011427876979)
                ·
                  refine ⟨15011819172864017141815469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10007879448576011427876979 15011819172864017141815469)
                  ·
                    refine ⟨5629432189824006428180801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15011819172864017141815469 5629432189824006428180801)
                    ·
                      refine ⟨4222074142368004821135601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629432189824006428180801 4222074142368004821135601)
                      ·
                        rfl

theorem cell23_8222460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_8222460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222460 prefixEnd_8222460 := by exact prefixLift 8222460
  have htrace : WordTrace (prefixWord ++ tailWord_8222460) baseStart_8222460 baseEnd_8222460 := by
    simpa [prefixWord, tailWord_8222460, baseEnd_8222460] using wordTrace_append hprefix tailTrace_8222460
  have hstable : (prefixWord ++ tailWord_8222460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222460).length < 2 ^ (prefixWord ++ tailWord_8222460).sum := by decide
  have hdescent : baseEnd_8222460 < baseStart_8222460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222490 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2]
def baseStart_8222490 : Nat := 118140960795 + 8222490 * 2 ^ 59
def prefixEnd_8222490 : Nat := 4983230072969 + 3 ^ 40 * 8222490 * 2
def baseEnd_8222490 : Nat := 4222089546787639703760463

theorem tailTrace_8222490 : CollatzResearch.WordTrace tailWord_8222490 prefixEnd_8222490 4222089546787639703760463 := by
  unfold tailWord_8222490
  simp only [CollatzResearch.WordTrace]
  refine ⟨74974711995332623583978231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199932565320886996223941949 74974711995332623583978231)
  ·
    refine ⟨112462067992998935375967347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74974711995332623583978231 112462067992998935375967347)
    ·
      refine ⟨168693101989498403063951021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112462067992998935375967347 168693101989498403063951021)
      ·
        refine ⟨63259913246061901148981633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168693101989498403063951021 63259913246061901148981633)
        ·
          refine ⟨47444934934546425861736225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63259913246061901148981633 47444934934546425861736225)
          ·
            refine ⟨35583701200909819396302169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47444934934546425861736225 35583701200909819396302169)
            ·
              refine ⟨26687775900682364547226627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35583701200909819396302169 26687775900682364547226627)
              ·
                refine ⟨40031663851023546820839941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26687775900682364547226627 40031663851023546820839941)
                ·
                  refine ⟨7505936972066915028907489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40031663851023546820839941 7505936972066915028907489)
                  ·
                    refine ⟨5629452729050186271680617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7505936972066915028907489 5629452729050186271680617)
                    ·
                      refine ⟨4222089546787639703760463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629452729050186271680617 4222089546787639703760463)
                      ·
                        rfl

theorem cell23_8222490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_8222490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222490 prefixEnd_8222490 := by exact prefixLift 8222490
  have htrace : WordTrace (prefixWord ++ tailWord_8222490) baseStart_8222490 baseEnd_8222490 := by
    simpa [prefixWord, tailWord_8222490, baseEnd_8222490] using wordTrace_append hprefix tailTrace_8222490
  have hstable : (prefixWord ++ tailWord_8222490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222490).length < 2 ^ (prefixWord ++ tailWord_8222490).sum := by decide
  have hdescent : baseEnd_8222490 < baseStart_8222490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222536 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_8222536 : Nat := 118140960795 + 8222536 * 2 ^ 59
def prefixEnd_8222536 : Nat := 4983230072969 + 3 ^ 40 * 8222536 * 2
def baseEnd_8222536 : Nat := 4222113166897746523785251

theorem tailTrace_8222536 : CollatzResearch.WordTrace tailWord_8222536 prefixEnd_8222536 4222113166897746523785251 := by
  unfold tailWord_8222536
  simp only [CollatzResearch.WordTrace]
  refine ⟨149950262869581922096043731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199933683826109229461391641 149950262869581922096043731)
  ·
    refine ⟨224925394304372883144065597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149950262869581922096043731 224925394304372883144065597)
    ·
      refine ⟨84347022864139831179024599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224925394304372883144065597 84347022864139831179024599)
      ·
        refine ⟨126520534296209746768536899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84347022864139831179024599 126520534296209746768536899)
        ·
          refine ⟨189780801444314620152805349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126520534296209746768536899 189780801444314620152805349)
          ·
            refine ⟨35583900270808991278651003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189780801444314620152805349 35583900270808991278651003)
            ·
              refine ⟨53375850406213486917976505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35583900270808991278651003 53375850406213486917976505)
              ·
                refine ⟨40031887804660115188482379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53375850406213486917976505 40031887804660115188482379)
                ·
                  refine ⟨60047831706990172782723569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40031887804660115188482379 60047831706990172782723569)
                  ·
                    refine ⟨45035873780242629587042677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60047831706990172782723569 45035873780242629587042677)
                    ·
                      refine ⟨4222113166897746523785251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45035873780242629587042677 4222113166897746523785251)
                      ·
                        rfl

theorem cell23_8222536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_8222536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222536 prefixEnd_8222536 := by exact prefixLift 8222536
  have htrace : WordTrace (prefixWord ++ tailWord_8222536) baseStart_8222536 baseEnd_8222536 := by
    simpa [prefixWord, tailWord_8222536, baseEnd_8222536] using wordTrace_append hprefix tailTrace_8222536
  have hstable : (prefixWord ++ tailWord_8222536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222536).length < 2 ^ (prefixWord ++ tailWord_8222536).sum := by decide
  have hdescent : baseEnd_8222536 < baseStart_8222536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222573 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_8222573 : Nat := 118140960795 + 8222573 * 2 ^ 59
def prefixEnd_8222573 : Nat := 4983230072969 + 3 ^ 40 * 8222573 * 2
def baseEnd_8222573 : Nat := 1407377388560654293007527

theorem tailTrace_8222573 : CollatzResearch.WordTrace tailWord_8222573 prefixEnd_8222573 1407377388560654293007527 := by
  unfold tailWord_8222573
  simp only [CollatzResearch.WordTrace]
  refine ⟨299901875240029799511184373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199934583493353199674122915 299901875240029799511184373)
  ·
    refine ⟨28115800803752793704173535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299901875240029799511184373 28115800803752793704173535)
    ·
      refine ⟨42173701205629190556260303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28115800803752793704173535 42173701205629190556260303)
      ·
        refine ⟨63260551808443785834390455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42173701205629190556260303 63260551808443785834390455)
        ·
          refine ⟨94890827712665678751585683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63260551808443785834390455 94890827712665678751585683)
          ·
            refine ⟨142336241568998518127378525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94890827712665678751585683 142336241568998518127378525)
            ·
              refine ⟨53376090588374444297766947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142336241568998518127378525 53376090588374444297766947)
              ·
                refine ⟨80064135882561666446650421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53376090588374444297766947 80064135882561666446650421)
                ·
                  refine ⟨7506012738990156229373477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80064135882561666446650421 7506012738990156229373477)
                  ·
                    refine ⟨1407377388560654293007527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7506012738990156229373477 1407377388560654293007527)
                    ·
                      rfl

theorem cell23_8222573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_8222573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222573 prefixEnd_8222573 := by exact prefixLift 8222573
  have htrace : WordTrace (prefixWord ++ tailWord_8222573) baseStart_8222573 baseEnd_8222573 := by
    simpa [prefixWord, tailWord_8222573, baseEnd_8222573] using wordTrace_append hprefix tailTrace_8222573
  have hstable : (prefixWord ++ tailWord_8222573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222573).length < 2 ^ (prefixWord ++ tailWord_8222573).sum := by decide
  have hdescent : baseEnd_8222573 < baseStart_8222573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222680 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 2, 4]
def baseStart_8222680 : Nat := 118140960795 + 8222680 * 2 ^ 59
def prefixEnd_8222680 : Nat := 4983230072969 + 3 ^ 40 * 8222680 * 2
def baseEnd_8222680 : Nat := 1407395702703997986794863

theorem tailTrace_8222680 : CollatzResearch.WordTrace tailWord_8222680 prefixEnd_8222680 1407395702703997986794863 := by
  unfold tailWord_8222680
  simp only [CollatzResearch.WordTrace]
  refine ⟨149952888925321078392664747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199937185233761437856886329 149952888925321078392664747)
  ·
    refine ⟨224929333387981617588997121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149952888925321078392664747 224929333387981617588997121)
    ·
      refine ⟨168697000040986213191747841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224929333387981617588997121 168697000040986213191747841)
      ·
        refine ⟨126522750030739659893810881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168697000040986213191747841 126522750030739659893810881)
        ·
          refine ⟨94892062523054744920358161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126522750030739659893810881 94892062523054744920358161)
          ·
            refine ⟨71169046892291058690268621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94892062523054744920358161 71169046892291058690268621)
            ·
              refine ⟨26688392584609147008850733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71169046892291058690268621 26688392584609147008850733)
              ·
                refine ⟨10008147219228430128319025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26688392584609147008850733 10008147219228430128319025)
                ·
                  refine ⟨7506110414421322596239269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10008147219228430128319025 7506110414421322596239269)
                  ·
                    refine ⟨1407395702703997986794863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7506110414421322596239269 1407395702703997986794863)
                    ·
                      rfl

theorem cell23_8222680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_8222680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222680 prefixEnd_8222680 := by exact prefixLift 8222680
  have htrace : WordTrace (prefixWord ++ tailWord_8222680) baseStart_8222680 baseEnd_8222680 := by
    simpa [prefixWord, tailWord_8222680, baseEnd_8222680] using wordTrace_append hprefix tailTrace_8222680
  have hstable : (prefixWord ++ tailWord_8222680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222680).length < 2 ^ (prefixWord ++ tailWord_8222680).sum := by decide
  have hdescent : baseEnd_8222680 < baseStart_8222680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222684 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_8222684 : Nat := 118140960795 + 8222684 * 2 ^ 59
def prefixEnd_8222684 : Nat := 4983230072969 + 3 ^ 40 * 8222684 * 2
def baseEnd_8222684 : Nat := 1407396387344870648244857

theorem tailTrace_8222684 : CollatzResearch.WordTrace tailWord_8222684 prefixEnd_8222684 1407396387344870648244857 := by
  unfold tailWord_8222684
  simp only [CollatzResearch.WordTrace]
  refine ⟨149952961871313832734237553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199937282495085110312316737 149952961871313832734237553)
  ·
    refine ⟨112464721403485374550678165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149952961871313832734237553 112464721403485374550678165)
    ·
      refine ⟨5271783815788376932063039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112464721403485374550678165 5271783815788376932063039)
      ·
        refine ⟨7907675723682565398094559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271783815788376932063039 7907675723682565398094559)
        ·
          refine ⟨11861513585523848097141839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907675723682565398094559 11861513585523848097141839)
          ·
            refine ⟨17792270378285772145712759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11861513585523848097141839 17792270378285772145712759)
            ·
              refine ⟨26688405567428658218569139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17792270378285772145712759 26688405567428658218569139)
              ·
                refine ⟨40032608351142987327853709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26688405567428658218569139 40032608351142987327853709)
                ·
                  refine ⟨15012228131678620247945141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40032608351142987327853709 15012228131678620247945141)
                  ·
                    refine ⟨1407396387344870648244857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15012228131678620247945141 1407396387344870648244857)
                    ·
                      rfl

theorem cell23_8222684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_8222684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222684 prefixEnd_8222684 := by exact prefixLift 8222684
  have htrace : WordTrace (prefixWord ++ tailWord_8222684) baseStart_8222684 baseEnd_8222684 := by
    simpa [prefixWord, tailWord_8222684, baseEnd_8222684] using wordTrace_append hprefix tailTrace_8222684
  have hstable : (prefixWord ++ tailWord_8222684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222684).length < 2 ^ (prefixWord ++ tailWord_8222684).sum := by decide
  have hdescent : baseEnd_8222684 < baseStart_8222684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222687 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 4]
def baseStart_8222687 : Nat := 118140960795 + 8222687 * 2 ^ 59
def prefixEnd_8222687 : Nat := 4983230072969 + 3 ^ 40 * 8222687 * 2
def baseEnd_8222687 : Nat := 4222190702476575432997057

theorem tailTrace_8222687 : CollatzResearch.WordTrace tailWord_8222687 prefixEnd_8222687 4222190702476575432997057 := by
  unfold tailWord_8222687
  simp only [CollatzResearch.WordTrace]
  refine ⟨299906033161616796980834315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199937355441077864653889543 299906033161616796980834315)
  ·
    refine ⟨449859049742425195471251473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299906033161616796980834315 449859049742425195471251473)
    ·
      refine ⟨337394287306818896603438605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449859049742425195471251473 337394287306818896603438605)
      ·
        refine ⟨126522857740057086226289477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337394287306818896603438605 126522857740057086226289477)
        ·
          refine ⟨23723035826260703667429277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126522857740057086226289477 23723035826260703667429277)
          ·
            refine ⟨8896138434847763875285979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23723035826260703667429277 8896138434847763875285979)
            ·
              refine ⟨13344207652271645812928969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8896138434847763875285979 13344207652271645812928969)
              ·
                refine ⟨10008155739203734359696727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13344207652271645812928969 10008155739203734359696727)
                ·
                  refine ⟨15012233608805601539545091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10008155739203734359696727 15012233608805601539545091)
                  ·
                    refine ⟨22518350413208402309317637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15012233608805601539545091 22518350413208402309317637)
                    ·
                      refine ⟨4222190702476575432997057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22518350413208402309317637 4222190702476575432997057)
                      ·
                        rfl

theorem cell23_8222687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_8222687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222687 prefixEnd_8222687 := by exact prefixLift 8222687
  have htrace : WordTrace (prefixWord ++ tailWord_8222687) baseStart_8222687 baseEnd_8222687 := by
    simpa [prefixWord, tailWord_8222687, baseEnd_8222687] using wordTrace_append hprefix tailTrace_8222687
  have hstable : (prefixWord ++ tailWord_8222687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222687).length < 2 ^ (prefixWord ++ tailWord_8222687).sum := by decide
  have hdescent : baseEnd_8222687 < baseStart_8222687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222710 : List Nat := [5, 1, 1, 1, 5, 10]
def baseStart_8222710 : Nat := 118140960795 + 8222710 * 2 ^ 59
def prefixEnd_8222710 : Nat := 4983230072969 + 3 ^ 40 * 8222710 * 2
def baseEnd_8222710 : Nat := 17375318981611641329257

theorem tailTrace_8222710 : CollatzResearch.WordTrace tailWord_8222710 prefixEnd_8222710 17375318981611641329257 := by
  unfold tailWord_8222710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18744179502533341994307599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199937914693688981272614389 18744179502533341994307599)
  ·
    refine ⟨28116269253800012991461399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18744179502533341994307599 28116269253800012991461399)
    ·
      refine ⟨42174403880700019487192099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28116269253800012991461399 42174403880700019487192099)
      ·
        refine ⟨63261605821050029230788149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42174403880700019487192099 63261605821050029230788149)
        ·
          refine ⟨5930775545723440240386389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63261605821050029230788149 5930775545723440240386389)
          ·
            refine ⟨17375318981611641329257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5930775545723440240386389 17375318981611641329257)
            ·
              rfl

theorem cell23_8222710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 10].length) (baseStart_8222710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222710 prefixEnd_8222710 := by exact prefixLift 8222710
  have htrace : WordTrace (prefixWord ++ tailWord_8222710) baseStart_8222710 baseEnd_8222710 := by
    simpa [prefixWord, tailWord_8222710, baseEnd_8222710] using wordTrace_append hprefix tailTrace_8222710
  have hstable : (prefixWord ++ tailWord_8222710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222710).length < 2 ^ (prefixWord ++ tailWord_8222710).sum := by decide
  have hdescent : baseEnd_8222710 < baseStart_8222710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222763 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 3]
def baseStart_8222763 : Nat := 118140960795 + 8222763 * 2 ^ 59
def prefixEnd_8222763 : Nat := 4983230072969 + 3 ^ 40 * 8222763 * 2
def baseEnd_8222763 : Nat := 4222229727006317135646707

theorem tailTrace_8222763 : CollatzResearch.WordTrace tailWord_8222763 prefixEnd_8222763 4222229727006317135646707 := by
  unfold tailWord_8222763
  simp only [CollatzResearch.WordTrace]
  refine ⟨299908805109341461960600943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199939203406227641307067295 299908805109341461960600943)
  ·
    refine ⟨449863207664012192940901415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299908805109341461960600943 449863207664012192940901415)
    ·
      refine ⟨674794811496018289411352123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449863207664012192940901415 674794811496018289411352123)
      ·
        refine ⟨1012192217244027434117028185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674794811496018289411352123 1012192217244027434117028185)
        ·
          refine ⟨759144162933020575587771139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012192217244027434117028185 759144162933020575587771139)
          ·
            refine ⟨1138716244399530863381656709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759144162933020575587771139 1138716244399530863381656709)
            ·
              refine ⟨213509295824912036884060633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1138716244399530863381656709 213509295824912036884060633)
              ·
                refine ⟨160131971868684027663045475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213509295824912036884060633 160131971868684027663045475)
                ·
                  refine ⟨240197957803026041494568213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160131971868684027663045475 240197957803026041494568213)
                  ·
                    refine ⟨11259279272016845695057885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 240197957803026041494568213 11259279272016845695057885)
                    ·
                      refine ⟨4222229727006317135646707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11259279272016845695057885 4222229727006317135646707)
                      ·
                        rfl

theorem cell23_8222763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 3].length) (baseStart_8222763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222763 prefixEnd_8222763 := by exact prefixLift 8222763
  have htrace : WordTrace (prefixWord ++ tailWord_8222763) baseStart_8222763 baseEnd_8222763 := by
    simpa [prefixWord, tailWord_8222763, baseEnd_8222763] using wordTrace_append hprefix tailTrace_8222763
  have hstable : (prefixWord ++ tailWord_8222763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222763).length < 2 ^ (prefixWord ++ tailWord_8222763).sum := by decide
  have hdescent : baseEnd_8222763 < baseStart_8222763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222783 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 7]
def baseStart_8222783 : Nat := 118140960795 + 8222783 * 2 ^ 59
def prefixEnd_8222783 : Nat := 4983230072969 + 3 ^ 40 * 8222783 * 2
def baseEnd_8222783 : Nat := 469137777402156339710735

theorem tailTrace_8222783 : CollatzResearch.WordTrace tailWord_8222783 prefixEnd_8222783 469137777402156339710735 := by
  unfold tailWord_8222783
  simp only [CollatzResearch.WordTrace]
  refine ⟨299909534569269005376329003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199939689712846003584219335 299909534569269005376329003)
  ·
    refine ⟨449864301853903508064493505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299909534569269005376329003 449864301853903508064493505)
    ·
      refine ⟨337398226390427631048370129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449864301853903508064493505 337398226390427631048370129)
      ·
        refine ⟨253048669792820723286277597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337398226390427631048370129 253048669792820723286277597)
        ·
          refine ⟨94893251172307771232354099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253048669792820723286277597 94893251172307771232354099)
          ·
            refine ⟨142339876758461656848531149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94893251172307771232354099 142339876758461656848531149)
            ·
              refine ⟨53377453784423121318199181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142339876758461656848531149 53377453784423121318199181)
              ·
                refine ⟨20016545169158670494324693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53377453784423121318199181 20016545169158670494324693)
                ·
                  refine ⟨469137777402156339710735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20016545169158670494324693 469137777402156339710735)
                  ·
                    rfl

theorem cell23_8222783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 7].length) (baseStart_8222783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222783 prefixEnd_8222783 := by exact prefixLift 8222783
  have htrace : WordTrace (prefixWord ++ tailWord_8222783) baseStart_8222783 baseEnd_8222783 := by
    simpa [prefixWord, tailWord_8222783, baseEnd_8222783] using wordTrace_append hprefix tailTrace_8222783
  have hstable : (prefixWord ++ tailWord_8222783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222783).length < 2 ^ (prefixWord ++ tailWord_8222783).sum := by decide
  have hdescent : baseEnd_8222783 < baseStart_8222783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222834 : List Nat := [3, 2, 1, 2, 2, 3, 3, 2, 5]
def baseStart_8222834 : Nat := 118140960795 + 8222834 * 2 ^ 59
def prefixEnd_8222834 : Nat := 4983230072969 + 3 ^ 40 * 8222834 * 2
def baseEnd_8222834 : Nat := 469140687125865150873209

theorem tailTrace_8222834 : CollatzResearch.WordTrace tailWord_8222834 prefixEnd_8222834 469140687125865150873209 := by
  unfold tailWord_8222834
  simp only [CollatzResearch.WordTrace]
  refine ⟨74977848673021060271608889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199940929794722827390957037 74977848673021060271608889)
  ·
    refine ⟨56233386504765795203706667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74977848673021060271608889 56233386504765795203706667)
    ·
      refine ⟨84350079757148692805560001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56233386504765795203706667 84350079757148692805560001)
      ·
        refine ⟨63262559817861519604170001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84350079757148692805560001 63262559817861519604170001)
        ·
          refine ⟨47446919863396139703127501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63262559817861519604170001 47446919863396139703127501)
          ·
            refine ⟨17792594948773552388672813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47446919863396139703127501 17792594948773552388672813)
            ·
              refine ⟨6672223105790082145752305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17792594948773552388672813 6672223105790082145752305)
              ·
                refine ⟨5004167329342561609314229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6672223105790082145752305 5004167329342561609314229)
                ·
                  refine ⟨469140687125865150873209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5004167329342561609314229 469140687125865150873209)
                  ·
                    rfl

theorem cell23_8222834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_8222834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222834 prefixEnd_8222834 := by exact prefixLift 8222834
  have htrace : WordTrace (prefixWord ++ tailWord_8222834) baseStart_8222834 baseEnd_8222834 := by
    simpa [prefixWord, tailWord_8222834, baseEnd_8222834] using wordTrace_append hprefix tailTrace_8222834
  have hstable : (prefixWord ++ tailWord_8222834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222834).length < 2 ^ (prefixWord ++ tailWord_8222834).sum := by decide
  have hdescent : baseEnd_8222834 < baseStart_8222834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222873 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 10]
def baseStart_8222873 : Nat := 118140960795 + 8222873 * 2 ^ 59
def prefixEnd_8222873 : Nat := 4983230072969 + 3 ^ 40 * 8222873 * 2
def baseEnd_8222873 : Nat := 469142912208701300585689

theorem tailTrace_8222873 : CollatzResearch.WordTrace tailWord_8222873 prefixEnd_8222873 469142912208701300585689 := by
  unfold tailWord_8222873
  simp only [CollatzResearch.WordTrace]
  refine ⟨299912817138942950747105273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199941878092628633831403515 299912817138942950747105273)
  ·
    refine ⟨224934612854207213060328955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299912817138942950747105273 224934612854207213060328955)
    ·
      refine ⟨337401919281310819590493433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224934612854207213060328955 337401919281310819590493433)
      ·
        refine ⟨253051439460983114692870075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337401919281310819590493433 253051439460983114692870075)
        ·
          refine ⟨379577159191474672039305113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253051439460983114692870075 379577159191474672039305113)
          ·
            refine ⟨284682869393606004029478835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379577159191474672039305113 284682869393606004029478835)
            ·
              refine ⟨427024304090409006044218253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284682869393606004029478835 427024304090409006044218253)
              ·
                refine ⟨160134114033903377266581845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427024304090409006044218253 160134114033903377266581845)
                ·
                  refine ⟨469142912208701300585689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 160134114033903377266581845 469142912208701300585689)
                  ·
                    rfl

theorem cell23_8222873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 10].length) (baseStart_8222873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222873 prefixEnd_8222873 := by exact prefixLift 8222873
  have htrace : WordTrace (prefixWord ++ tailWord_8222873) baseStart_8222873 baseEnd_8222873 := by
    simpa [prefixWord, tailWord_8222873, baseEnd_8222873] using wordTrace_append hprefix tailTrace_8222873
  have hstable : (prefixWord ++ tailWord_8222873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222873).length < 2 ^ (prefixWord ++ tailWord_8222873).sum := by decide
  have hdescent : baseEnd_8222873 < baseStart_8222873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222901 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_8222901 : Nat := 118140960795 + 8222901 * 2 ^ 59
def prefixEnd_8222901 : Nat := 4983230072969 + 3 ^ 40 * 8222901 * 2
def baseEnd_8222901 : Nat := 4222300587336637595721073

theorem tailTrace_8222901 : CollatzResearch.WordTrace tailWord_8222901 prefixEnd_8222901 4222300587336637595721073 := by
  unfold tailWord_8222901
  simp only [CollatzResearch.WordTrace]
  refine ⟨299913838382841511529124557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199942558921894341019416371 299913838382841511529124557)
  ·
    refine ⟨112467689393565566823421709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299913838382841511529124557 112467689393565566823421709)
    ·
      refine ⟨42175383522587087558783141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112467689393565566823421709 42175383522587087558783141)
      ·
        refine ⟨7907884410485078917271839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42175383522587087558783141 7907884410485078917271839)
        ·
          refine ⟨11861826615727618375907759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907884410485078917271839 11861826615727618375907759)
          ·
            refine ⟨17792739923591427563861639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11861826615727618375907759 17792739923591427563861639)
            ·
              refine ⟨26689109885387141345792459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17792739923591427563861639 26689109885387141345792459)
              ·
                refine ⟨40033664828080712018688689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26689109885387141345792459 40033664828080712018688689)
                ·
                  refine ⟨30025248621060534014016517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40033664828080712018688689 30025248621060534014016517)
                  ·
                    refine ⟨5629734116448850127628097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30025248621060534014016517 5629734116448850127628097)
                    ·
                      refine ⟨4222300587336637595721073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629734116448850127628097 4222300587336637595721073)
                      ·
                        rfl

theorem cell23_8222901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_8222901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222901 prefixEnd_8222901 := by exact prefixLift 8222901
  have htrace : WordTrace (prefixWord ++ tailWord_8222901) baseStart_8222901 baseEnd_8222901 := by
    simpa [prefixWord, tailWord_8222901, baseEnd_8222901] using wordTrace_append hprefix tailTrace_8222901
  have hstable : (prefixWord ++ tailWord_8222901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222901).length < 2 ^ (prefixWord ++ tailWord_8222901).sum := by decide
  have hdescent : baseEnd_8222901 < baseStart_8222901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222917 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 3]
def baseStart_8222917 : Nat := 118140960795 + 8222917 * 2 ^ 59
def prefixEnd_8222917 : Nat := 4983230072969 + 3 ^ 40 * 8222917 * 2
def baseEnd_8222917 : Nat := 4222308803027109533120999

theorem tailTrace_8222917 : CollatzResearch.WordTrace tailWord_8222917 prefixEnd_8222917 4222308803027109533120999 := by
  unfold tailWord_8222917
  simp only [CollatzResearch.WordTrace]
  refine ⟨299914421950783546261707005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199942947967189030841138003 299914421950783546261707005)
  ·
    refine ⟨112467908231543829848140127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299914421950783546261707005 112467908231543829848140127)
    ·
      refine ⟨168701862347315744772210191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112467908231543829848140127 168701862347315744772210191)
      ·
        refine ⟨253052793520973617158315287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168701862347315744772210191 253052793520973617158315287)
        ·
          refine ⟨379579190281460425737472931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253052793520973617158315287 379579190281460425737472931)
          ·
            refine ⟨569368785422190638606209397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379579190281460425737472931 569368785422190638606209397)
            ·
              refine ⟨53378323633330372369332131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 569368785422190638606209397 53378323633330372369332131)
              ·
                refine ⟨80067485449995558553998197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53378323633330372369332131 80067485449995558553998197)
                ·
                  refine ⟨7506326760937083614437331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80067485449995558553998197 7506326760937083614437331)
                  ·
                    refine ⟨11259490141405625421655997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7506326760937083614437331 11259490141405625421655997)
                    ·
                      refine ⟨4222308803027109533120999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11259490141405625421655997 4222308803027109533120999)
                      ·
                        rfl

theorem cell23_8222917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_8222917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222917 prefixEnd_8222917 := by exact prefixLift 8222917
  have htrace : WordTrace (prefixWord ++ tailWord_8222917) baseStart_8222917 baseEnd_8222917 := by
    simpa [prefixWord, tailWord_8222917, baseEnd_8222917] using wordTrace_append hprefix tailTrace_8222917
  have hstable : (prefixWord ++ tailWord_8222917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222917).length < 2 ^ (prefixWord ++ tailWord_8222917).sum := by decide
  have hdescent : baseEnd_8222917 < baseStart_8222917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222927 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 1, 5, 2]
def baseStart_8222927 : Nat := 118140960795 + 8222927 * 2 ^ 59
def prefixEnd_8222927 : Nat := 4983230072969 + 3 ^ 40 * 8222927 * 2
def baseEnd_8222927 : Nat := 4222313937833654493995953

theorem tailTrace_8222927 : CollatzResearch.WordTrace tailWord_8222927 prefixEnd_8222927 4222313937833654493995953 := by
  unfold tailWord_8222927
  simp only [CollatzResearch.WordTrace]
  refine ⟨299914786680747317969571035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199943191120498211979714023 299914786680747317969571035)
  ·
    refine ⟨449872180021120976954356553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299914786680747317969571035 449872180021120976954356553)
    ·
      refine ⟨337404135015840732715767415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449872180021120976954356553 337404135015840732715767415)
      ·
        refine ⟨506106202523761099073651123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337404135015840732715767415 506106202523761099073651123)
        ·
          refine ⟨759159303785641648610476685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506106202523761099073651123 759159303785641648610476685)
          ·
            refine ⟨284684738919615618228928757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759159303785641648610476685 284684738919615618228928757)
            ·
              refine ⟨26689194273713964208962071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284684738919615618228928757 26689194273713964208962071)
              ·
                refine ⟨40033791410570946313443107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26689194273713964208962071 40033791410570946313443107)
                ·
                  refine ⟨60050687115856419470164661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40033791410570946313443107 60050687115856419470164661)
                  ·
                    refine ⟨5629751917111539325327937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60050687115856419470164661 5629751917111539325327937)
                    ·
                      refine ⟨4222313937833654493995953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629751917111539325327937 4222313937833654493995953)
                      ·
                        rfl

theorem cell23_8222927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 5, 2].length) (baseStart_8222927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222927 prefixEnd_8222927 := by exact prefixLift 8222927
  have htrace : WordTrace (prefixWord ++ tailWord_8222927) baseStart_8222927 baseEnd_8222927 := by
    simpa [prefixWord, tailWord_8222927, baseEnd_8222927] using wordTrace_append hprefix tailTrace_8222927
  have hstable : (prefixWord ++ tailWord_8222927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222927).length < 2 ^ (prefixWord ++ tailWord_8222927).sum := by decide
  have hdescent : baseEnd_8222927 < baseStart_8222927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222951 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_8222951 : Nat := 118140960795 + 8222951 * 2 ^ 59
def prefixEnd_8222951 : Nat := 4983230072969 + 3 ^ 40 * 8222951 * 2
def baseEnd_8222951 : Nat := 4222326261369362400095843

theorem tailTrace_8222951 : CollatzResearch.WordTrace tailWord_8222951 prefixEnd_8222951 4222326261369362400095843 := by
  unfold tailWord_8222951
  simp only [CollatzResearch.WordTrace]
  refine ⟨299915662032660370068444707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199943774688440246712296471 299915662032660370068444707)
  ·
    refine ⟨449873493048990555102667061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299915662032660370068444707 449873493048990555102667061)
    ·
      refine ⟨42175639973342864540875037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449873493048990555102667061 42175639973342864540875037)
      ·
        refine ⟨15815864990003574202828139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42175639973342864540875037 15815864990003574202828139)
        ·
          refine ⟨23723797485005361304242209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15815864990003574202828139 23723797485005361304242209)
          ·
            refine ⟨17792848113754020978181657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23723797485005361304242209 17792848113754020978181657)
            ·
              refine ⟨13344636085315515733636243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17792848113754020978181657 13344636085315515733636243)
              ·
                refine ⟨20016954127973273600454365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13344636085315515733636243 20016954127973273600454365)
                ·
                  refine ⟨7506357797989977600170387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20016954127973273600454365 7506357797989977600170387)
                  ·
                    refine ⟨11259536696984966400255581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7506357797989977600170387 11259536696984966400255581)
                    ·
                      refine ⟨4222326261369362400095843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11259536696984966400255581 4222326261369362400095843)
                      ·
                        rfl

theorem cell23_8222951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_8222951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222951 prefixEnd_8222951 := by exact prefixLift 8222951
  have htrace : WordTrace (prefixWord ++ tailWord_8222951) baseStart_8222951 baseEnd_8222951 := by
    simpa [prefixWord, tailWord_8222951, baseEnd_8222951] using wordTrace_append hprefix tailTrace_8222951
  have hstable : (prefixWord ++ tailWord_8222951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222951).length < 2 ^ (prefixWord ++ tailWord_8222951).sum := by decide
  have hdescent : baseEnd_8222951 < baseStart_8222951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8222974 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_8222974 : Nat := 118140960795 + 8222974 * 2 ^ 59
def prefixEnd_8222974 : Nat := 4983230072969 + 3 ^ 40 * 8222974 * 2
def baseEnd_8222974 : Nat := 4222338071424415810108237

theorem tailTrace_8222974 : CollatzResearch.WordTrace tailWord_8222974 prefixEnd_8222974 4222338071424415810108237 := by
  unfold tailWord_8222974
  simp only [CollatzResearch.WordTrace]
  refine ⟨37489562613947130624566497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199944333941051363331021317 37489562613947130624566497)
  ·
    refine ⟨28117171960460347968424873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37489562613947130624566497 28117171960460347968424873)
    ·
      refine ⟨21087878970345260976318655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28117171960460347968424873 21087878970345260976318655)
      ·
        refine ⟨31631818455517891464477983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21087878970345260976318655 31631818455517891464477983)
        ·
          refine ⟨47447727683276837196716975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31631818455517891464477983 47447727683276837196716975)
          ·
            refine ⟨71171591524915255795075463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47447727683276837196716975 71171591524915255795075463)
            ·
              refine ⟨106757387287372883692613195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71171591524915255795075463 106757387287372883692613195)
              ·
                refine ⟨160136080931059325538919793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106757387287372883692613195 160136080931059325538919793)
                ·
                  refine ⟨120102060698294494154189845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160136080931059325538919793 120102060698294494154189845)
                  ·
                    refine ⟨5629784095232554413477649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120102060698294494154189845 5629784095232554413477649)
                    ·
                      refine ⟨4222338071424415810108237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629784095232554413477649 4222338071424415810108237)
                      ·
                        rfl

theorem cell23_8222974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_8222974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8222974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8222974 prefixEnd_8222974 := by exact prefixLift 8222974
  have htrace : WordTrace (prefixWord ++ tailWord_8222974) baseStart_8222974 baseEnd_8222974 := by
    simpa [prefixWord, tailWord_8222974, baseEnd_8222974] using wordTrace_append hprefix tailTrace_8222974
  have hstable : (prefixWord ++ tailWord_8222974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8222974).length < 2 ^ (prefixWord ++ tailWord_8222974).sum := by decide
  have hdescent : baseEnd_8222974 < baseStart_8222974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8222974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223008 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 3, 2, 2]
def baseStart_8223008 : Nat := 118140960795 + 8223008 * 2 ^ 59
def prefixEnd_8223008 : Nat := 4983230072969 + 3 ^ 40 * 8223008 * 2
def baseEnd_8223008 : Nat := 4222355529766668677083081

theorem tailTrace_8223008 : CollatzResearch.WordTrace tailWord_8223008 prefixEnd_8223008 4222355529766668677083081 := by
  unfold tailWord_8223008
  simp only [CollatzResearch.WordTrace]
  refine ⟨149958870496726934401634839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199945160662302579202179785 149958870496726934401634839)
  ·
    refine ⟨224938305745090401602452259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149958870496726934401634839 224938305745090401602452259)
    ·
      refine ⟨337407458617635602403678389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224938305745090401602452259 337407458617635602403678389)
      ·
        refine ⟨31631949245403337725344849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337407458617635602403678389 31631949245403337725344849)
        ·
          refine ⟨23723961934052503294008637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31631949245403337725344849 23723961934052503294008637)
          ·
            refine ⟨8896485725269688735253239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23723961934052503294008637 8896485725269688735253239)
            ·
              refine ⟨13344728587904533102879859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8896485725269688735253239 13344728587904533102879859)
              ·
                refine ⟨20017092881856799654319789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13344728587904533102879859 20017092881856799654319789)
                ·
                  refine ⟨7506409830696299870369921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20017092881856799654319789 7506409830696299870369921)
                  ·
                    refine ⟨5629807373022224902777441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7506409830696299870369921 5629807373022224902777441)
                    ·
                      refine ⟨4222355529766668677083081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629807373022224902777441 4222355529766668677083081)
                      ·
                        rfl

theorem cell23_8223008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_8223008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223008 prefixEnd_8223008 := by exact prefixLift 8223008
  have htrace : WordTrace (prefixWord ++ tailWord_8223008) baseStart_8223008 baseEnd_8223008 := by
    simpa [prefixWord, tailWord_8223008, baseEnd_8223008] using wordTrace_append hprefix tailTrace_8223008
  have hstable : (prefixWord ++ tailWord_8223008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223008).length < 2 ^ (prefixWord ++ tailWord_8223008).sum := by decide
  have hdescent : baseEnd_8223008 < baseStart_8223008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223028 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_8223028 : Nat := 118140960795 + 8223028 * 2 ^ 59
def prefixEnd_8223028 : Nat := 4983230072969 + 3 ^ 40 * 8223028 * 2
def baseEnd_8223028 : Nat := 4222365799379758598832989

theorem tailTrace_8223028 : CollatzResearch.WordTrace tailWord_8223028 prefixEnd_8223028 4222365799379758598832989 := by
  unfold tailWord_8223028
  simp only [CollatzResearch.WordTrace]
  refine ⟨149959235226690706109498869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199945646968920941479331825 149959235226690706109498869)
  ·
    refine ⟨14058678302502253697765519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149959235226690706109498869 14058678302502253697765519)
    ·
      refine ⟨21088017453753380546648279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14058678302502253697765519 21088017453753380546648279)
      ·
        refine ⟨31632026180630070819972419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21088017453753380546648279 31632026180630070819972419)
        ·
          refine ⟨47448039270945106229958629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31632026180630070819972419 47448039270945106229958629)
          ·
            refine ⟨8896507363302207418117243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47448039270945106229958629 8896507363302207418117243)
            ·
              refine ⟨13344761044953311127175865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8896507363302207418117243 13344761044953311127175865)
              ·
                refine ⟨10008570783714983345381899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13344761044953311127175865 10008570783714983345381899)
                ·
                  refine ⟨15012856175572475018072849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10008570783714983345381899 15012856175572475018072849)
                  ·
                    refine ⟨11259642131679356263554637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15012856175572475018072849 11259642131679356263554637)
                    ·
                      refine ⟨4222365799379758598832989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11259642131679356263554637 4222365799379758598832989)
                      ·
                        rfl

theorem cell23_8223028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_8223028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223028 prefixEnd_8223028 := by exact prefixLift 8223028
  have htrace : WordTrace (prefixWord ++ tailWord_8223028) baseStart_8223028 baseEnd_8223028 := by
    simpa [prefixWord, tailWord_8223028, baseEnd_8223028] using wordTrace_append hprefix tailTrace_8223028
  have hstable : (prefixWord ++ tailWord_8223028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223028).length < 2 ^ (prefixWord ++ tailWord_8223028).sum := by decide
  have hdescent : baseEnd_8223028 < baseStart_8223028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223040 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 3, 8]
def baseStart_8223040 : Nat := 118140960795 + 8223040 * 2 ^ 59
def prefixEnd_8223040 : Nat := 4983230072969 + 3 ^ 40 * 8223040 * 2
def baseEnd_8223040 : Nat := 1407457320382537517294311

theorem tailTrace_8223040 : CollatzResearch.WordTrace tailWord_8223040 prefixEnd_8223040 1407457320382537517294311 := by
  unfold tailWord_8223040
  simp only [CollatzResearch.WordTrace]
  refine ⟨149959454064668969134217287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199945938752891958845623049 149959454064668969134217287)
  ·
    refine ⟨224939181097003453701325931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149959454064668969134217287 224939181097003453701325931)
    ·
      refine ⟨337408771645505180551988897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224939181097003453701325931 337408771645505180551988897)
      ·
        refine ⟨253056578734128885413991673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337408771645505180551988897 253056578734128885413991673)
        ·
          refine ⟨189792434050596664060493755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253056578734128885413991673 189792434050596664060493755)
          ·
            refine ⟨284688651075894996090740633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189792434050596664060493755 284688651075894996090740633)
            ·
              refine ⟨213516488306921247068055475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284688651075894996090740633 213516488306921247068055475)
              ·
                refine ⟨320274732460381870602083213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213516488306921247068055475 320274732460381870602083213)
                ·
                  refine ⟨120103024672643201475781205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320274732460381870602083213 120103024672643201475781205)
                  ·
                    refine ⟨1407457320382537517294311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120103024672643201475781205 1407457320382537517294311)
                    ·
                      rfl

theorem cell23_8223040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_8223040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223040 prefixEnd_8223040 := by exact prefixLift 8223040
  have htrace : WordTrace (prefixWord ++ tailWord_8223040) baseStart_8223040 baseEnd_8223040 := by
    simpa [prefixWord, tailWord_8223040, baseEnd_8223040] using wordTrace_append hprefix tailTrace_8223040
  have hstable : (prefixWord ++ tailWord_8223040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223040).length < 2 ^ (prefixWord ++ tailWord_8223040).sum := by decide
  have hdescent : baseEnd_8223040 < baseStart_8223040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223041 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_8223041 : Nat := 118140960795 + 8223041 * 2 ^ 59
def prefixEnd_8223041 : Nat := 4983230072969 + 3 ^ 40 * 8223041 * 2
def baseEnd_8223041 : Nat := 4222372474628267047970429

theorem tailTrace_8223041 : CollatzResearch.WordTrace tailWord_8223041 prefixEnd_8223041 4222372474628267047970429 := by
  unfold tailWord_8223041
  simp only [CollatzResearch.WordTrace]
  refine ⟨299918944602334315439220977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199945963068222876959480651 299918944602334315439220977)
  ·
    refine ⟨224939208451750736579415733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299918944602334315439220977 224939208451750736579415733)
    ·
      refine ⟨21088050792351631554320225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224939208451750736579415733 21088050792351631554320225)
      ·
        refine ⟨15816038094263723665740169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21088050792351631554320225 15816038094263723665740169)
        ·
          refine ⟨11862028570697792749305127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15816038094263723665740169 11862028570697792749305127)
          ·
            refine ⟨17793042856046689123957691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11862028570697792749305127 17793042856046689123957691)
            ·
              refine ⟨26689564284070033685936537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17793042856046689123957691 26689564284070033685936537)
              ·
                refine ⟨20017173213052525264452403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26689564284070033685936537 20017173213052525264452403)
                ·
                  refine ⟨30025759819578787896678605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20017173213052525264452403 30025759819578787896678605)
                  ·
                    refine ⟨11259659932342045461254477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30025759819578787896678605 11259659932342045461254477)
                    ·
                      refine ⟨4222372474628267047970429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11259659932342045461254477 4222372474628267047970429)
                      ·
                        rfl

theorem cell23_8223041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_8223041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223041 prefixEnd_8223041 := by exact prefixLift 8223041
  have htrace : WordTrace (prefixWord ++ tailWord_8223041) baseStart_8223041 baseEnd_8223041 := by
    simpa [prefixWord, tailWord_8223041, baseEnd_8223041] using wordTrace_append hprefix tailTrace_8223041
  have hstable : (prefixWord ++ tailWord_8223041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223041).length < 2 ^ (prefixWord ++ tailWord_8223041).sum := by decide
  have hdescent : baseEnd_8223041 < baseStart_8223041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223074 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_8223074 : Nat := 118140960795 + 8223074 * 2 ^ 59
def prefixEnd_8223074 : Nat := 4983230072969 + 3 ^ 40 * 8223074 * 2
def baseEnd_8223074 : Nat := 1407463139829955139619259

theorem tailTrace_8223074 : CollatzResearch.WordTrace tailWord_8223074 prefixEnd_8223074 1407463139829955139619259 := by
  unfold tailWord_8223074
  simp only [CollatzResearch.WordTrace]
  refine ⟨74980037052803690518793069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199946765474143174716781517 74980037052803690518793069)
  ·
    refine ⟨28117513894801383944547401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74980037052803690518793069 28117513894801383944547401)
    ·
      refine ⟨21088135421101037958410551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28117513894801383944547401 21088135421101037958410551)
      ·
        refine ⟨31632203131651556937615827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21088135421101037958410551 31632203131651556937615827)
        ·
          refine ⟨47448304697477335406423741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31632203131651556937615827 47448304697477335406423741)
          ·
            refine ⟨17793114261554000777408903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47448304697477335406423741 17793114261554000777408903)
            ·
              refine ⟨26689671392331001166113355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17793114261554000777408903 26689671392331001166113355)
              ·
                refine ⟨40034507088496501749170033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26689671392331001166113355 40034507088496501749170033)
                ·
                  refine ⟨30025880316372376311877525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40034507088496501749170033 30025880316372376311877525)
                  ·
                    refine ⟨1407463139829955139619259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30025880316372376311877525 1407463139829955139619259)
                    ·
                      rfl

theorem cell23_8223074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_8223074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223074 prefixEnd_8223074 := by exact prefixLift 8223074
  have htrace : WordTrace (prefixWord ++ tailWord_8223074) baseStart_8223074 baseEnd_8223074 := by
    simpa [prefixWord, tailWord_8223074, baseEnd_8223074] using wordTrace_append hprefix tailTrace_8223074
  have hstable : (prefixWord ++ tailWord_8223074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223074).length < 2 ^ (prefixWord ++ tailWord_8223074).sum := by decide
  have hdescent : baseEnd_8223074 < baseStart_8223074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223077 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_8223077 : Nat := 118140960795 + 8223077 * 2 ^ 59
def prefixEnd_8223077 : Nat := 4983230072969 + 3 ^ 40 * 8223077 * 2
def baseEnd_8223077 : Nat := 4222390959931828907120263

theorem tailTrace_8223077 : CollatzResearch.WordTrace tailWord_8223077 prefixEnd_8223077 4222390959931828907120263 := by
  unfold tailWord_8223077
  simp only [CollatzResearch.WordTrace]
  refine ⟨299920257630203893587531485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199946838420135929058354323 299920257630203893587531485)
  ·
    refine ⟨112470096611326460095324307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299920257630203893587531485 112470096611326460095324307)
    ·
      refine ⟨168705144916989690142986461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112470096611326460095324307 168705144916989690142986461)
      ·
        refine ⟨63264429343871133803619923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168705144916989690142986461 63264429343871133803619923)
        ·
          refine ⟨94896644015806700705429885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63264429343871133803619923 94896644015806700705429885)
          ·
            refine ⟨35586241505927512764536207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94896644015806700705429885 35586241505927512764536207)
            ·
              refine ⟨53379362258891269146804311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35586241505927512764536207 53379362258891269146804311)
              ·
                refine ⟨80069043388336903720206467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53379362258891269146804311 80069043388336903720206467)
                ·
                  refine ⟨120103565082505355580309701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80069043388336903720206467 120103565082505355580309701)
                  ·
                    refine ⟨22519418452969754171308069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120103565082505355580309701 22519418452969754171308069)
                    ·
                      refine ⟨4222390959931828907120263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22519418452969754171308069 4222390959931828907120263)
                      ·
                        rfl

theorem cell23_8223077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_8223077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223077 prefixEnd_8223077 := by exact prefixLift 8223077
  have htrace : WordTrace (prefixWord ++ tailWord_8223077) baseStart_8223077 baseEnd_8223077 := by
    simpa [prefixWord, tailWord_8223077, baseEnd_8223077] using wordTrace_append hprefix tailTrace_8223077
  have hstable : (prefixWord ++ tailWord_8223077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223077).length < 2 ^ (prefixWord ++ tailWord_8223077).sum := by decide
  have hdescent : baseEnd_8223077 < baseStart_8223077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223081 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 2, 2, 2]
def baseStart_8223081 : Nat := 118140960795 + 8223081 * 2 ^ 59
def prefixEnd_8223081 : Nat := 4983230072969 + 3 ^ 40 * 8223081 * 2
def baseEnd_8223081 : Nat := 4222393013854446891470245

theorem tailTrace_8223081 : CollatzResearch.WordTrace tailWord_8223081 prefixEnd_8223081 4222393013854446891470245 := by
  unfold tailWord_8223081
  simp only [CollatzResearch.WordTrace]
  refine ⟨299920403522189402270677097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199946935681459601513784731 299920403522189402270677097)
  ·
    refine ⟨224940302641642051703007823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299920403522189402270677097 224940302641642051703007823)
    ·
      refine ⟨337410453962463077554511735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224940302641642051703007823 337410453962463077554511735)
      ·
        refine ⟨506115680943694616331767603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337410453962463077554511735 506115680943694616331767603)
        ·
          refine ⟨759173521415541924497651405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506115680943694616331767603 759173521415541924497651405)
          ·
            refine ⟨284690070530828221686619277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759173521415541924497651405 284690070530828221686619277)
            ·
              refine ⟨106758776449060583132482229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284690070530828221686619277 106758776449060583132482229)
              ·
                refine ⟨10008635292099429668670209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106758776449060583132482229 10008635292099429668670209)
                ·
                  refine ⟨7506476469074572251502657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10008635292099429668670209 7506476469074572251502657)
                  ·
                    refine ⟨5629857351805929188626993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7506476469074572251502657 5629857351805929188626993)
                    ·
                      refine ⟨4222393013854446891470245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629857351805929188626993 4222393013854446891470245)
                      ·
                        rfl

theorem cell23_8223081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 2, 2].length) (baseStart_8223081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223081 prefixEnd_8223081 := by exact prefixLift 8223081
  have htrace : WordTrace (prefixWord ++ tailWord_8223081) baseStart_8223081 baseEnd_8223081 := by
    simpa [prefixWord, tailWord_8223081, baseEnd_8223081] using wordTrace_append hprefix tailTrace_8223081
  have hstable : (prefixWord ++ tailWord_8223081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223081).length < 2 ^ (prefixWord ++ tailWord_8223081).sum := by decide
  have hdescent : baseEnd_8223081 < baseStart_8223081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223097 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 3]
def baseStart_8223097 : Nat := 118140960795 + 8223097 * 2 ^ 59
def prefixEnd_8223097 : Nat := 4983230072969 + 3 ^ 40 * 8223097 * 2
def baseEnd_8223097 : Nat := 4222401229544918828870171

theorem tailTrace_8223097 : CollatzResearch.WordTrace tailWord_8223097 prefixEnd_8223097 4222401229544918828870171 := by
  unfold tailWord_8223097
  simp only [CollatzResearch.WordTrace]
  refine ⟨299920987090131437003259545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199947324726754291335506363 299920987090131437003259545)
  ·
    refine ⟨224940740317598577752444659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299920987090131437003259545 224940740317598577752444659)
    ·
      refine ⟨337411110476397866628666989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224940740317598577752444659 337411110476397866628666989)
      ·
        refine ⟨126529166428649199985750121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337411110476397866628666989 126529166428649199985750121)
        ·
          refine ⟨94896874821486899989312591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126529166428649199985750121 94896874821486899989312591)
          ·
            refine ⟨142345312232230349983968887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94896874821486899989312591 142345312232230349983968887)
            ·
              refine ⟨213517968348345524975953331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142345312232230349983968887 213517968348345524975953331)
              ·
                refine ⟨320276952522518287463929997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213517968348345524975953331 320276952522518287463929997)
                ·
                  refine ⟨120103857195944357798973749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320276952522518287463929997 120103857195944357798973749)
                  ·
                    refine ⟨11259736612119783543653789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120103857195944357798973749 11259736612119783543653789)
                    ·
                      refine ⟨4222401229544918828870171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11259736612119783543653789 4222401229544918828870171)
                      ·
                        rfl

theorem cell23_8223097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_8223097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223097 prefixEnd_8223097 := by exact prefixLift 8223097
  have htrace : WordTrace (prefixWord ++ tailWord_8223097) baseStart_8223097 baseEnd_8223097 := by
    simpa [prefixWord, tailWord_8223097, baseEnd_8223097] using wordTrace_append hprefix tailTrace_8223097
  have hstable : (prefixWord ++ tailWord_8223097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223097).length < 2 ^ (prefixWord ++ tailWord_8223097).sum := by decide
  have hdescent : baseEnd_8223097 < baseStart_8223097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223127 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_8223127 : Nat := 118140960795 + 8223127 * 2 ^ 59
def prefixEnd_8223127 : Nat := 4983230072969 + 3 ^ 40 * 8223127 * 2
def baseEnd_8223127 : Nat := 4222416633964553711495033

theorem tailTrace_8223127 : CollatzResearch.WordTrace tailWord_8223127 prefixEnd_8223127 4222416633964553711495033 := by
  unfold tailWord_8223127
  simp only [CollatzResearch.WordTrace]
  refine ⟨299922081280022752126851635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199948054186681834751234423 299922081280022752126851635)
  ·
    refine ⟨449883121920034128190277453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299922081280022752126851635 449883121920034128190277453)
    ·
      refine ⟨168706170720012798071354045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449883121920034128190277453 168706170720012798071354045)
      ·
        refine ⟨63264814020004799276757767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168706170720012798071354045 63264814020004799276757767)
        ·
          refine ⟨94897221030007198915136651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63264814020004799276757767 94897221030007198915136651)
          ·
            refine ⟨142345831545010798372704977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94897221030007198915136651 142345831545010798372704977)
            ·
              refine ⟨106759373658758098779528733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142345831545010798372704977 106759373658758098779528733)
              ·
                refine ⟨40034765122034287042323275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106759373658758098779528733 40034765122034287042323275)
                ·
                  refine ⟨60052147683051430563484913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40034765122034287042323275 60052147683051430563484913)
                  ·
                    refine ⟨45039110762288572922613685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60052147683051430563484913 45039110762288572922613685)
                    ·
                      refine ⟨4222416633964553711495033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45039110762288572922613685 4222416633964553711495033)
                      ·
                        rfl

theorem cell23_8223127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_8223127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223127 prefixEnd_8223127 := by exact prefixLift 8223127
  have htrace : WordTrace (prefixWord ++ tailWord_8223127) baseStart_8223127 baseEnd_8223127 := by
    simpa [prefixWord, tailWord_8223127, baseEnd_8223127] using wordTrace_append hprefix tailTrace_8223127
  have hstable : (prefixWord ++ tailWord_8223127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223127).length < 2 ^ (prefixWord ++ tailWord_8223127).sum := by decide
  have hdescent : baseEnd_8223127 < baseStart_8223127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223154 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_8223154 : Nat := 118140960795 + 8223154 * 2 ^ 59
def prefixEnd_8223154 : Nat := 4983230072969 + 3 ^ 40 * 8223154 * 2
def baseEnd_8223154 : Nat := 4222430497942225105857409

theorem tailTrace_8223154 : CollatzResearch.WordTrace tailWord_8223154 prefixEnd_8223154 4222430497942225105857409 := by
  unfold tailWord_8223154
  simp only [CollatzResearch.WordTrace]
  refine ⟨74980766512731233934521129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199948710700616623825389677 74980766512731233934521129)
  ·
    refine ⟨56235574884548425450890847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74980766512731233934521129 56235574884548425450890847)
    ·
      refine ⟨84353362326822638176336271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56235574884548425450890847 84353362326822638176336271)
      ·
        refine ⟨126530043490233957264504407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84353362326822638176336271 126530043490233957264504407)
        ·
          refine ⟨189795065235350935896756611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126530043490233957264504407 189795065235350935896756611)
          ·
            refine ⟨284692597853026403845134917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189795065235350935896756611 284692597853026403845134917)
            ·
              refine ⟨53379862097442450720962797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284692597853026403845134917 53379862097442450720962797)
              ·
                refine ⟨20017448286540919020361049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53379862097442450720962797 20017448286540919020361049)
                ·
                  refine ⟨15013086214905689265270787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20017448286540919020361049 15013086214905689265270787)
                  ·
                    refine ⟨22519629322358533897906181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15013086214905689265270787 22519629322358533897906181)
                    ·
                      refine ⟨4222430497942225105857409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22519629322358533897906181 4222430497942225105857409)
                      ·
                        rfl

theorem cell23_8223154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_8223154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223154 prefixEnd_8223154 := by exact prefixLift 8223154
  have htrace : WordTrace (prefixWord ++ tailWord_8223154) baseStart_8223154 baseEnd_8223154 := by
    simpa [prefixWord, tailWord_8223154, baseEnd_8223154] using wordTrace_append hprefix tailTrace_8223154
  have hstable : (prefixWord ++ tailWord_8223154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223154).length < 2 ^ (prefixWord ++ tailWord_8223154).sum := by decide
  have hdescent : baseEnd_8223154 < baseStart_8223154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223177 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 8]
def baseStart_8223177 : Nat := 118140960795 + 8223177 * 2 ^ 59
def prefixEnd_8223177 : Nat := 4983230072969 + 3 ^ 40 * 8223177 * 2
def baseEnd_8223177 : Nat := 469160256444142057318867

theorem tailTrace_8223177 : CollatzResearch.WordTrace tailWord_8223177 prefixEnd_8223177 469160256444142057318867 := by
  unfold tailWord_8223177
  simp only [CollatzResearch.WordTrace]
  refine ⟨299923904929841610666171785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199949269953227740444114523 299923904929841610666171785)
  ·
    refine ⟨224942928697381207999628839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299923904929841610666171785 224942928697381207999628839)
    ·
      refine ⟨337414393046071811999443259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224942928697381207999628839 337414393046071811999443259)
      ·
        refine ⟨506121589569107717999164889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337414393046071811999443259 506121589569107717999164889)
        ·
          refine ⟨379591192176830788499373667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506121589569107717999164889 379591192176830788499373667)
          ·
            refine ⟨569386788265246182749060501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379591192176830788499373667 569386788265246182749060501)
            ·
              refine ⟨26690005699933414816362211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 569386788265246182749060501 26690005699933414816362211)
              ·
                refine ⟨40035008549900122224543317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26690005699933414816362211 40035008549900122224543317)
                ·
                  refine ⟨469160256444142057318867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40035008549900122224543317 469160256444142057318867)
                  ·
                    rfl

theorem cell23_8223177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 8].length) (baseStart_8223177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223177 prefixEnd_8223177 := by exact prefixLift 8223177
  have htrace : WordTrace (prefixWord ++ tailWord_8223177) baseStart_8223177 baseEnd_8223177 := by
    simpa [prefixWord, tailWord_8223177, baseEnd_8223177] using wordTrace_append hprefix tailTrace_8223177
  have hstable : (prefixWord ++ tailWord_8223177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223177).length < 2 ^ (prefixWord ++ tailWord_8223177).sum := by decide
  have hdescent : baseEnd_8223177 < baseStart_8223177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223194 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 6]
def baseStart_8223194 : Nat := 118140960795 + 8223194 * 2 ^ 59
def prefixEnd_8223194 : Nat := 4983230072969 + 3 ^ 40 * 8223194 * 2
def baseEnd_8223194 : Nat := 469161226352044994373025

theorem tailTrace_8223194 : CollatzResearch.WordTrace tailWord_8223194 prefixEnd_8223194 469161226352044994373025 := by
  unfold tailWord_8223194
  simp only [CollatzResearch.WordTrace]
  refine ⟨74981131242695005642385159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199949683313853348379693757 74981131242695005642385159)
  ·
    refine ⟨112471696864042508463577739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74981131242695005642385159 112471696864042508463577739)
    ·
      refine ⟨168707545296063762695366609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112471696864042508463577739 168707545296063762695366609)
      ·
        refine ⟨126530658972047822021524957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168707545296063762695366609 126530658972047822021524957)
        ·
          refine ⟨47448997114517933258071859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126530658972047822021524957 47448997114517933258071859)
          ·
            refine ⟨71173495671776899887107789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47448997114517933258071859 71173495671776899887107789)
            ·
              refine ⟨26690060876916337457665421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71173495671776899887107789 26690060876916337457665421)
              ·
                refine ⟨10008772828843626546624533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26690060876916337457665421 10008772828843626546624533)
                ·
                  refine ⟨469161226352044994373025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10008772828843626546624533 469161226352044994373025)
                  ·
                    rfl

theorem cell23_8223194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_8223194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223194 prefixEnd_8223194 := by exact prefixLift 8223194
  have htrace : WordTrace (prefixWord ++ tailWord_8223194) baseStart_8223194 baseEnd_8223194 := by
    simpa [prefixWord, tailWord_8223194, baseEnd_8223194] using wordTrace_append hprefix tailTrace_8223194
  have hstable : (prefixWord ++ tailWord_8223194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223194).length < 2 ^ (prefixWord ++ tailWord_8223194).sum := by decide
  have hdescent : baseEnd_8223194 < baseStart_8223194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223231 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 2, 3, 2]
def baseStart_8223231 : Nat := 118140960795 + 8223231 * 2 ^ 59
def prefixEnd_8223231 : Nat := 4983230072969 + 3 ^ 40 * 8223231 * 2
def baseEnd_8223231 : Nat := 4222470035952621304594555

theorem tailTrace_8223231 : CollatzResearch.WordTrace tailWord_8223231 prefixEnd_8223231 4222470035952621304594555 := by
  unfold tailWord_8223231
  simp only [CollatzResearch.WordTrace]
  refine ⟨299925874471645977888637547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199950582981097318592425031 299925874471645977888637547)
  ·
    refine ⟨449888811707468966832956321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299925874471645977888637547 449888811707468966832956321)
    ·
      refine ⟨337416608780601725124717241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449888811707468966832956321 337416608780601725124717241)
      ·
        refine ⟨253062456585451293843537931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337416608780601725124717241 253062456585451293843537931)
        ·
          refine ⟨379593684878176940765306897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253062456585451293843537931 379593684878176940765306897)
          ·
            refine ⟨284695263658632705573980173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379593684878176940765306897 284695263658632705573980173)
            ·
              refine ⟨106760723871987264590242565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284695263658632705573980173 106760723871987264590242565)
              ·
                refine ⟨20017635725997612110670481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106760723871987264590242565 20017635725997612110670481)
                ·
                  refine ⟨15013226794498209083002861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20017635725997612110670481 15013226794498209083002861)
                  ·
                    refine ⟨5629960047936828406126073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15013226794498209083002861 5629960047936828406126073)
                    ·
                      refine ⟨4222470035952621304594555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5629960047936828406126073 4222470035952621304594555)
                      ·
                        rfl

theorem cell23_8223231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_8223231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223231 prefixEnd_8223231 := by exact prefixLift 8223231
  have htrace : WordTrace (prefixWord ++ tailWord_8223231) baseStart_8223231 baseEnd_8223231 := by
    simpa [prefixWord, tailWord_8223231, baseEnd_8223231] using wordTrace_append hprefix tailTrace_8223231
  have hstable : (prefixWord ++ tailWord_8223231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223231).length < 2 ^ (prefixWord ++ tailWord_8223231).sum := by decide
  have hdescent : baseEnd_8223231 < baseStart_8223231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223255 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 3]
def baseStart_8223255 : Nat := 118140960795 + 8223255 * 2 ^ 59
def prefixEnd_8223255 : Nat := 4983230072969 + 3 ^ 40 * 8223255 * 2
def baseEnd_8223255 : Nat := 4222482359488329210694445

theorem tailTrace_8223255 : CollatzResearch.WordTrace tailWord_8223255 prefixEnd_8223255 4222482359488329210694445 := by
  unfold tailWord_8223255
  simp only [CollatzResearch.WordTrace]
  refine ⟨299926749823559029987511219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199951166549039353325007479 299926749823559029987511219)
  ·
    refine ⟨449890124735338544981266829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299926749823559029987511219 449890124735338544981266829)
    ·
      refine ⟨168708796775751954367975061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449890124735338544981266829 168708796775751954367975061)
      ·
        refine ⟨7908224848863372860998831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168708796775751954367975061 7908224848863372860998831)
        ·
          refine ⟨11862337273295059291498247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7908224848863372860998831 11862337273295059291498247)
          ·
            refine ⟨17793505909942588937247371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11862337273295059291498247 17793505909942588937247371)
            ·
              refine ⟨26690258864913883405871057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17793505909942588937247371 26690258864913883405871057)
              ·
                refine ⟨20017694148685412554403293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26690258864913883405871057 20017694148685412554403293)
                ·
                  refine ⟨7506635305757029707901235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20017694148685412554403293 7506635305757029707901235)
                  ·
                    refine ⟨11259952958635544561851853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7506635305757029707901235 11259952958635544561851853)
                    ·
                      refine ⟨4222482359488329210694445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11259952958635544561851853 4222482359488329210694445)
                      ·
                        rfl

theorem cell23_8223255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_8223255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223255 prefixEnd_8223255 := by exact prefixLift 8223255
  have htrace : WordTrace (prefixWord ++ tailWord_8223255) baseStart_8223255 baseEnd_8223255 := by
    simpa [prefixWord, tailWord_8223255, baseEnd_8223255] using wordTrace_append hprefix tailTrace_8223255
  have hstable : (prefixWord ++ tailWord_8223255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223255).length < 2 ^ (prefixWord ++ tailWord_8223255).sum := by decide
  have hdescent : baseEnd_8223255 < baseStart_8223255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223261 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_8223261 : Nat := 118140960795 + 8223261 * 2 ^ 59
def prefixEnd_8223261 : Nat := 4983230072969 + 3 ^ 40 * 8223261 * 2
def baseEnd_8223261 : Nat := 4222485440372256187219417

theorem tailTrace_8223261 : CollatzResearch.WordTrace tailWord_8223261 prefixEnd_8223261 4222485440372256187219417 := by
  unfold tailWord_8223261
  simp only [CollatzResearch.WordTrace]
  refine ⟨299926968661537293012229637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199951312441024862008153091 299926968661537293012229637)
  ·
    refine ⟨56236306624038242439793057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299926968661537293012229637 56236306624038242439793057)
    ·
      refine ⟨42177229968028681829844793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56236306624038242439793057 42177229968028681829844793)
      ·
        refine ⟨31632922476021511372383595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42177229968028681829844793 31632922476021511372383595)
        ·
          refine ⟨47449383714032267058575393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31632922476021511372383595 47449383714032267058575393)
          ·
            refine ⟨35587037785524200293931545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47449383714032267058575393 35587037785524200293931545)
            ·
              refine ⟨26690278339143150220448659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35587037785524200293931545 26690278339143150220448659)
              ·
                refine ⟨40035417508714725330672989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26690278339143150220448659 40035417508714725330672989)
                ·
                  refine ⟨15013281565768021999002371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40035417508714725330672989 15013281565768021999002371)
                  ·
                    refine ⟨22519922348652032998503557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15013281565768021999002371 22519922348652032998503557)
                    ·
                      refine ⟨4222485440372256187219417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22519922348652032998503557 4222485440372256187219417)
                      ·
                        rfl

theorem cell23_8223261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_8223261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223261 prefixEnd_8223261 := by exact prefixLift 8223261
  have htrace : WordTrace (prefixWord ++ tailWord_8223261) baseStart_8223261 baseEnd_8223261 := by
    simpa [prefixWord, tailWord_8223261, baseEnd_8223261] using wordTrace_append hprefix tailTrace_8223261
  have hstable : (prefixWord ++ tailWord_8223261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223261).length < 2 ^ (prefixWord ++ tailWord_8223261).sum := by decide
  have hdescent : baseEnd_8223261 < baseStart_8223261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223272 : List Nat := [2, 1, 5, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_8223272 : Nat := 118140960795 + 8223272 * 2 ^ 59
def prefixEnd_8223272 : Nat := 4983230072969 + 3 ^ 40 * 8223272 * 2
def baseEnd_8223272 : Nat := 4222491088659455644181867

theorem tailTrace_8223272 : CollatzResearch.WordTrace tailWord_8223272 prefixEnd_8223272 4222491088659455644181867 := by
  unfold tailWord_8223272
  simp only [CollatzResearch.WordTrace]
  refine ⟨149963684932248720945440035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199951579909664961260586713 149963684932248720945440035)
  ·
    refine ⟨224945527398373081418160053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149963684932248720945440035 224945527398373081418160053)
    ·
      refine ⟨21088643193597476382952505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224945527398373081418160053 21088643193597476382952505)
      ·
        refine ⟨15816482395198107287214379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21088643193597476382952505 15816482395198107287214379)
        ·
          refine ⟨23724723592797160930821569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15816482395198107287214379 23724723592797160930821569)
          ·
            refine ⟨17793542694597870698116177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23724723592797160930821569 17793542694597870698116177)
            ·
              refine ⟨13345157020948403023587133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17793542694597870698116177 13345157020948403023587133)
              ·
                refine ⟨5004433882855651133845175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13345157020948403023587133 5004433882855651133845175)
                ·
                  refine ⟨7506650824283476700767763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5004433882855651133845175 7506650824283476700767763)
                  ·
                    refine ⟨11259976236425215051151645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7506650824283476700767763 11259976236425215051151645)
                    ·
                      refine ⟨4222491088659455644181867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11259976236425215051151645 4222491088659455644181867)
                      ·
                        rfl

theorem cell23_8223272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_8223272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223272 prefixEnd_8223272 := by exact prefixLift 8223272
  have htrace : WordTrace (prefixWord ++ tailWord_8223272) baseStart_8223272 baseEnd_8223272 := by
    simpa [prefixWord, tailWord_8223272, baseEnd_8223272] using wordTrace_append hprefix tailTrace_8223272
  have hstable : (prefixWord ++ tailWord_8223272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223272).length < 2 ^ (prefixWord ++ tailWord_8223272).sum := by decide
  have hdescent : baseEnd_8223272 < baseStart_8223272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223295 : List Nat := [1, 1, 2, 2, 3, 2, 1, 6, 1, 2, 2]
def baseStart_8223295 : Nat := 118140960795 + 8223295 * 2 ^ 59
def prefixEnd_8223295 : Nat := 4983230072969 + 3 ^ 40 * 8223295 * 2
def baseEnd_8223295 : Nat := 4222502898714509054194261

theorem tailTrace_8223295 : CollatzResearch.WordTrace tailWord_8223295 prefixEnd_8223295 4222502898714509054194261 := by
  unfold tailWord_8223295
  simp only [CollatzResearch.WordTrace]
  refine ⟨299928208743414116818967339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199952139162276077879311559 299928208743414116818967339)
  ·
    refine ⟨449892313115121175228451009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299928208743414116818967339 449892313115121175228451009)
    ·
      refine ⟨337419234836340881421338257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449892313115121175228451009 337419234836340881421338257)
      ·
        refine ⟨253064426127255661066003693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337419234836340881421338257 253064426127255661066003693)
        ·
          refine ⟨94899159797720872899751385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253064426127255661066003693 94899159797720872899751385)
          ·
            refine ⟨71174369848290654674813539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94899159797720872899751385 71174369848290654674813539)
            ·
              refine ⟨106761554772435982012220309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71174369848290654674813539 106761554772435982012220309)
              ·
                refine ⟨5004447879957936656822827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106761554772435982012220309 5004447879957936656822827)
                ·
                  refine ⟨7506671819936904985234241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5004447879957936656822827 7506671819936904985234241)
                  ·
                    refine ⟨5630003864952678738925681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7506671819936904985234241 5630003864952678738925681)
                    ·
                      refine ⟨4222502898714509054194261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630003864952678738925681 4222502898714509054194261)
                      ·
                        rfl

theorem cell23_8223295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 2, 2].length) (baseStart_8223295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223295 prefixEnd_8223295 := by exact prefixLift 8223295
  have htrace : WordTrace (prefixWord ++ tailWord_8223295) baseStart_8223295 baseEnd_8223295 := by
    simpa [prefixWord, tailWord_8223295, baseEnd_8223295] using wordTrace_append hprefix tailTrace_8223295
  have hstable : (prefixWord ++ tailWord_8223295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223295).length < 2 ^ (prefixWord ++ tailWord_8223295).sum := by decide
  have hdescent : baseEnd_8223295 < baseStart_8223295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223311 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 3]
def baseStart_8223311 : Nat := 118140960795 + 8223311 * 2 ^ 59
def prefixEnd_8223311 : Nat := 4983230072969 + 3 ^ 40 * 8223311 * 2
def baseEnd_8223311 : Nat := 4222511114404980991594187

theorem tailTrace_8223311 : CollatzResearch.WordTrace tailWord_8223311 prefixEnd_8223311 4222511114404980991594187 := by
  unfold tailWord_8223311
  simp only [CollatzResearch.WordTrace]
  refine ⟨299928792311356151551549787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199952528207570767701033191 299928792311356151551549787)
  ·
    refine ⟨449893188467034227327324681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299928792311356151551549787 449893188467034227327324681)
    ·
      refine ⟨337419891350275670495493511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449893188467034227327324681 337419891350275670495493511)
      ·
        refine ⟨506129837025413505743240267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337419891350275670495493511 506129837025413505743240267)
        ·
          refine ⟨759194755538120258614860401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506129837025413505743240267 759194755538120258614860401)
          ·
            refine ⟨569396066653590193961145301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759194755538120258614860401 569396066653590193961145301)
            ·
              refine ⟨13345220312193520170964343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 569396066653590193961145301 13345220312193520170964343)
              ·
                refine ⟨20017830468290280256446515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13345220312193520170964343 20017830468290280256446515)
                ·
                  refine ⟨30026745702435420384669773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20017830468290280256446515 30026745702435420384669773)
                  ·
                    refine ⟨11260029638413282644251165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30026745702435420384669773 11260029638413282644251165)
                    ·
                      refine ⟨4222511114404980991594187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11260029638413282644251165 4222511114404980991594187)
                      ·
                        rfl

theorem cell23_8223311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_8223311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223311 prefixEnd_8223311 := by exact prefixLift 8223311
  have htrace : WordTrace (prefixWord ++ tailWord_8223311) baseStart_8223311 baseEnd_8223311 := by
    simpa [prefixWord, tailWord_8223311, baseEnd_8223311] using wordTrace_append hprefix tailTrace_8223311
  have hstable : (prefixWord ++ tailWord_8223311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223311).length < 2 ^ (prefixWord ++ tailWord_8223311).sum := by decide
  have hdescent : baseEnd_8223311 < baseStart_8223311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223425 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 7]
def baseStart_8223425 : Nat := 118140960795 + 8223425 * 2 ^ 59
def prefixEnd_8223425 : Nat := 4983230072969 + 3 ^ 40 * 8223425 * 2
def baseEnd_8223425 : Nat := 469174405688843727285407

theorem tailTrace_8223425 : CollatzResearch.WordTrace tailWord_8223425 prefixEnd_8223425 469174405688843727285407 := by
  unfold tailWord_8223425
  simp only [CollatzResearch.WordTrace]
  refine ⟨299932950232943149021199729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199955300155295432680799819 299932950232943149021199729)
  ·
    refine ⟨224949712674707361765899797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299932950232943149021199729 224949712674707361765899797)
    ·
      refine ⟨10544517781626907582776553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224949712674707361765899797 10544517781626907582776553)
      ·
        refine ⟨7908388336220180687082415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10544517781626907582776553 7908388336220180687082415)
        ·
          refine ⟨11862582504330271030623623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7908388336220180687082415 11862582504330271030623623)
          ·
            refine ⟨17793873756495406545935435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11862582504330271030623623 17793873756495406545935435)
            ·
              refine ⟨26690810634743109818903153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17793873756495406545935435 26690810634743109818903153)
              ·
                refine ⟨20018107976057332364177365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26690810634743109818903153 20018107976057332364177365)
                ·
                  refine ⟨469174405688843727285407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20018107976057332364177365 469174405688843727285407)
                  ·
                    rfl

theorem cell23_8223425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 7].length) (baseStart_8223425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223425 prefixEnd_8223425 := by exact prefixLift 8223425
  have htrace : WordTrace (prefixWord ++ tailWord_8223425) baseStart_8223425 baseEnd_8223425 := by
    simpa [prefixWord, tailWord_8223425, baseEnd_8223425] using wordTrace_append hprefix tailTrace_8223425
  have hstable : (prefixWord ++ tailWord_8223425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223425).length < 2 ^ (prefixWord ++ tailWord_8223425).sum := by decide
  have hdescent : baseEnd_8223425 < baseStart_8223425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223438 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_8223438 : Nat := 118140960795 + 8223438 * 2 ^ 59
def prefixEnd_8223438 : Nat := 4983230072969 + 3 ^ 40 * 8223438 * 2
def baseEnd_8223438 : Nat := 1407525442149367331568701

theorem tailTrace_8223438 : CollatzResearch.WordTrace tailWord_8223438 prefixEnd_8223438 1407525442149367331568701 := by
  unfold tailWord_8223438
  simp only [CollatzResearch.WordTrace]
  refine ⟨37491678047737006530177871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199955616254597368160948645 37491678047737006530177871)
  ·
    refine ⟨56237517071605509795266807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37491678047737006530177871 56237517071605509795266807)
    ·
      refine ⟨84356275607408264692900211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56237517071605509795266807 84356275607408264692900211)
      ·
        refine ⟨126534413411112397039350317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84356275607408264692900211 126534413411112397039350317)
        ·
          refine ⟨47450405029167148889756369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126534413411112397039350317 47450405029167148889756369)
          ·
            refine ⟨35587803771875361667317277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47450405029167148889756369 35587803771875361667317277)
            ·
              refine ⟨13345426414453260625243979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35587803771875361667317277 13345426414453260625243979)
              ·
                refine ⟨20018139621679890937865969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13345426414453260625243979 20018139621679890937865969)
                ·
                  refine ⟨15013604716259918203399477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20018139621679890937865969 15013604716259918203399477)
                  ·
                    refine ⟨1407525442149367331568701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15013604716259918203399477 1407525442149367331568701)
                    ·
                      rfl

theorem cell23_8223438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_8223438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223438 prefixEnd_8223438 := by exact prefixLift 8223438
  have htrace : WordTrace (prefixWord ++ tailWord_8223438) baseStart_8223438 baseEnd_8223438 := by
    simpa [prefixWord, tailWord_8223438, baseEnd_8223438] using wordTrace_append hprefix tailTrace_8223438
  have hstable : (prefixWord ++ tailWord_8223438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223438).length < 2 ^ (prefixWord ++ tailWord_8223438).sum := by decide
  have hdescent : baseEnd_8223438 < baseStart_8223438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223441 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_8223441 : Nat := 118140960795 + 8223441 * 2 ^ 59
def prefixEnd_8223441 : Nat := 4983230072969 + 3 ^ 40 * 8223441 * 2
def baseEnd_8223441 : Nat := 4222577866890065482968589

theorem tailTrace_8223441 : CollatzResearch.WordTrace tailWord_8223441 prefixEnd_8223441 4222577866890065482968589 := by
  unfold tailWord_8223441
  simp only [CollatzResearch.WordTrace]
  refine ⟨299933533800885183753782177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199955689200590122502521451 299933533800885183753782177)
  ·
    refine ⟨224950150350663887815336633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299933533800885183753782177 224950150350663887815336633)
    ·
      refine ⟨168712612762997915861502475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224950150350663887815336633 168712612762997915861502475)
      ·
        refine ⟨253068919144496873792253713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168712612762997915861502475 253068919144496873792253713)
        ·
          refine ⟨189801689358372655344190285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253068919144496873792253713 189801689358372655344190285)
          ·
            refine ⟨71175633509389745754071357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189801689358372655344190285 71175633509389745754071357)
            ·
              refine ⟨26690862566021154657776759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71175633509389745754071357 26690862566021154657776759)
              ·
                refine ⟨40036293849031731986665139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26690862566021154657776759 40036293849031731986665139)
                ·
                  refine ⟨60054440773547597979997709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40036293849031731986665139 60054440773547597979997709)
                  ·
                    refine ⟨22520415290080349242499141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60054440773547597979997709 22520415290080349242499141)
                    ·
                      refine ⟨4222577866890065482968589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22520415290080349242499141 4222577866890065482968589)
                      ·
                        rfl

theorem cell23_8223441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_8223441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223441 prefixEnd_8223441 := by exact prefixLift 8223441
  have htrace : WordTrace (prefixWord ++ tailWord_8223441) baseStart_8223441 baseEnd_8223441 := by
    simpa [prefixWord, tailWord_8223441, baseEnd_8223441] using wordTrace_append hprefix tailTrace_8223441
  have hstable : (prefixWord ++ tailWord_8223441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223441).length < 2 ^ (prefixWord ++ tailWord_8223441).sum := by decide
  have hdescent : baseEnd_8223441 < baseStart_8223441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223478 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_8223478 : Nat := 118140960795 + 8223478 * 2 ^ 59
def prefixEnd_8223478 : Nat := 4983230072969 + 3 ^ 40 * 8223478 * 2
def baseEnd_8223478 : Nat := 4222596865674281838205919

theorem tailTrace_8223478 : CollatzResearch.WordTrace tailWord_8223478 prefixEnd_8223478 4222596865674281838205919 := by
  unfold tailWord_8223478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18745930206359446192054943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199956588867834092715252725 18745930206359446192054943)
  ·
    refine ⟨28118895309539169288082415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18745930206359446192054943 28118895309539169288082415)
    ·
      refine ⟨42178342964308753932123623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28118895309539169288082415 42178342964308753932123623)
      ·
        refine ⟨63267514446463130898185435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42178342964308753932123623 63267514446463130898185435)
        ·
          refine ⟨94901271669694696347278153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63267514446463130898185435 94901271669694696347278153)
          ·
            refine ⟨71175953752271022260458615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94901271669694696347278153 71175953752271022260458615)
            ·
              refine ⟨106763930628406533390687923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71175953752271022260458615 106763930628406533390687923)
              ·
                refine ⟨160145895942609800086031885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106763930628406533390687923 160145895942609800086031885)
                ·
                  refine ⟨60054710978478675032261957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160145895942609800086031885 60054710978478675032261957)
                  ·
                    refine ⟨11260258308464751568549117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60054710978478675032261957 11260258308464751568549117)
                    ·
                      refine ⟨4222596865674281838205919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11260258308464751568549117 4222596865674281838205919)
                      ·
                        rfl

theorem cell23_8223478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_8223478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223478 prefixEnd_8223478 := by exact prefixLift 8223478
  have htrace : WordTrace (prefixWord ++ tailWord_8223478) baseStart_8223478 baseEnd_8223478 := by
    simpa [prefixWord, tailWord_8223478, baseEnd_8223478] using wordTrace_append hprefix tailTrace_8223478
  have hstable : (prefixWord ++ tailWord_8223478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223478).length < 2 ^ (prefixWord ++ tailWord_8223478).sum := by decide
  have hdescent : baseEnd_8223478 < baseStart_8223478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223481 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 6]
def baseStart_8223481 : Nat := 118140960795 + 8223481 * 2 ^ 59
def prefixEnd_8223481 : Nat := 4983230072969 + 3 ^ 40 * 8223481 * 2
def baseEnd_8223481 : Nat := 469177600679582814052045

theorem tailTrace_8223481 : CollatzResearch.WordTrace tailWord_8223481 prefixEnd_8223481 469177600679582814052045 := by
  unfold tailWord_8223481
  simp only [CollatzResearch.WordTrace]
  refine ⟨299934992720740270585238297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199956661813826847056825531 299934992720740270585238297)
  ·
    refine ⟨224951244540555202938928723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299934992720740270585238297 224951244540555202938928723)
    ·
      refine ⟨337426866810832804408393085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224951244540555202938928723 337426866810832804408393085)
      ·
        refine ⟨126535075054062301653147407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337426866810832804408393085 126535075054062301653147407)
        ·
          refine ⟨189802612581093452479721111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126535075054062301653147407 189802612581093452479721111)
          ·
            refine ⟨284703918871640178719581667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189802612581093452479721111 284703918871640178719581667)
            ·
              refine ⟨427055878307460268079372501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284703918871640178719581667 427055878307460268079372501)
              ·
                refine ⟨10009122147831100033110293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 427055878307460268079372501 10009122147831100033110293)
                ·
                  refine ⟨469177600679582814052045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10009122147831100033110293 469177600679582814052045)
                  ·
                    rfl

theorem cell23_8223481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 6].length) (baseStart_8223481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223481 prefixEnd_8223481 := by exact prefixLift 8223481
  have htrace : WordTrace (prefixWord ++ tailWord_8223481) baseStart_8223481 baseEnd_8223481 := by
    simpa [prefixWord, tailWord_8223481, baseEnd_8223481] using wordTrace_append hprefix tailTrace_8223481
  have hstable : (prefixWord ++ tailWord_8223481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223481).length < 2 ^ (prefixWord ++ tailWord_8223481).sum := by decide
  have hdescent : baseEnd_8223481 < baseStart_8223481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223491 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 3]
def baseStart_8223491 : Nat := 118140960795 + 8223491 * 2 ^ 59
def prefixEnd_8223491 : Nat := 4983230072969 + 3 ^ 40 * 8223491 * 2
def baseEnd_8223491 : Nat := 4222603540922790287343359

theorem tailTrace_8223491 : CollatzResearch.WordTrace tailWord_8223491 prefixEnd_8223491 4222603540922790287343359 := by
  unfold tailWord_8223491
  simp only [CollatzResearch.WordTrace]
  refine ⟨299935357450704042293102327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199956904967136028195401551 299935357450704042293102327)
  ·
    refine ⟨449903036176056063439653491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299935357450704042293102327 449903036176056063439653491)
    ·
      refine ⟨674854554264084095159480237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449903036176056063439653491 674854554264084095159480237)
      ·
        refine ⟨253070457849031535684805089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674854554264084095159480237 253070457849031535684805089)
        ·
          refine ⟨189802843386773651763603817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253070457849031535684805089 189802843386773651763603817)
          ·
            refine ⟨142352132540080238822702863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189802843386773651763603817 142352132540080238822702863)
            ·
              refine ⟨213528198810120358234054295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142352132540080238822702863 213528198810120358234054295)
              ·
                refine ⟨320292298215180537351081443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213528198810120358234054295 320292298215180537351081443)
                ·
                  refine ⟨480438447322770806026622165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320292298215180537351081443 480438447322770806026622165)
                  ·
                    refine ⟨11260276109127440766248957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 480438447322770806026622165 11260276109127440766248957)
                    ·
                      refine ⟨4222603540922790287343359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11260276109127440766248957 4222603540922790287343359)
                      ·
                        rfl

theorem cell23_8223491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_8223491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223491 prefixEnd_8223491 := by exact prefixLift 8223491
  have htrace : WordTrace (prefixWord ++ tailWord_8223491) baseStart_8223491 baseEnd_8223491 := by
    simpa [prefixWord, tailWord_8223491, baseEnd_8223491] using wordTrace_append hprefix tailTrace_8223491
  have hstable : (prefixWord ++ tailWord_8223491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223491).length < 2 ^ (prefixWord ++ tailWord_8223491).sum := by decide
  have hdescent : baseEnd_8223491 < baseStart_8223491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223528 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 3, 5]
def baseStart_8223528 : Nat := 118140960795 + 8223528 * 2 ^ 59
def prefixEnd_8223528 : Nat := 4983230072969 + 3 ^ 40 * 8223528 * 2
def baseEnd_8223528 : Nat := 1407540846569002214193563

theorem tailTrace_8223528 : CollatzResearch.WordTrace tailWord_8223528 prefixEnd_8223528 1407540846569002214193563 := by
  unfold tailWord_8223528
  simp only [CollatzResearch.WordTrace]
  refine ⟨149968353475784998806099619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199957804634379998408132825 149968353475784998806099619)
  ·
    refine ⟨224952530213677498209149429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149968353475784998806099619 224952530213677498209149429)
    ·
      refine ⟨21089299707532265457107759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224952530213677498209149429 21089299707532265457107759)
      ·
        refine ⟨31633949561298398185661639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21089299707532265457107759 31633949561298398185661639)
        ·
          refine ⟨47450924341947597278492459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31633949561298398185661639 47450924341947597278492459)
          ·
            refine ⟨71176386512921395917738689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47450924341947597278492459 71176386512921395917738689)
            ·
              refine ⟨53382289884691046938304017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71176386512921395917738689 53382289884691046938304017)
              ·
                refine ⟨40036717413518285203728013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53382289884691046938304017 40036717413518285203728013)
                ·
                  refine ⟨15013769030069356951398005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40036717413518285203728013 15013769030069356951398005)
                  ·
                    refine ⟨1407540846569002214193563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15013769030069356951398005 1407540846569002214193563)
                    ·
                      rfl

theorem cell23_8223528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_8223528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223528 prefixEnd_8223528 := by exact prefixLift 8223528
  have htrace : WordTrace (prefixWord ++ tailWord_8223528) baseStart_8223528 baseEnd_8223528 := by
    simpa [prefixWord, tailWord_8223528, baseEnd_8223528] using wordTrace_append hprefix tailTrace_8223528
  have hstable : (prefixWord ++ tailWord_8223528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223528).length < 2 ^ (prefixWord ++ tailWord_8223528).sum := by decide
  have hdescent : baseEnd_8223528 < baseStart_8223528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223568 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 5]
def baseStart_8223568 : Nat := 118140960795 + 8223568 * 2 ^ 59
def prefixEnd_8223568 : Nat := 4983230072969 + 3 ^ 40 * 8223568 * 2
def baseEnd_8223568 : Nat := 4222643078933186486080505

theorem tailTrace_8223568 : CollatzResearch.WordTrace tailWord_8223568 prefixEnd_8223568 4222643078933186486080505 := by
  unfold tailWord_8223568
  simp only [CollatzResearch.WordTrace]
  refine ⟨149969082935712542221827679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199958777247616722962436905 149969082935712542221827679)
  ·
    refine ⟨224953624403568813332741519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149969082935712542221827679 224953624403568813332741519)
    ·
      refine ⟨337430436605353219999112279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224953624403568813332741519 337430436605353219999112279)
      ·
        refine ⟨506145654908029829998668419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337430436605353219999112279 506145654908029829998668419)
        ·
          refine ⟨759218482362044744998002629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506145654908029829998668419 759218482362044744998002629)
          ·
            refine ⟨142353465442883389687125493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 759218482362044744998002629 142353465442883389687125493)
            ·
              refine ⟨13345637385270317783168015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142353465442883389687125493 13345637385270317783168015)
              ·
                refine ⟨20018456077905476674752023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13345637385270317783168015 20018456077905476674752023)
                ·
                  refine ⟨30027684116858215012128035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20018456077905476674752023 30027684116858215012128035)
                  ·
                    refine ⟨45041526175287322518192053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30027684116858215012128035 45041526175287322518192053)
                    ·
                      refine ⟨4222643078933186486080505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45041526175287322518192053 4222643078933186486080505)
                      ·
                        rfl

theorem cell23_8223568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_8223568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223568 prefixEnd_8223568 := by exact prefixLift 8223568
  have htrace : WordTrace (prefixWord ++ tailWord_8223568) baseStart_8223568 baseEnd_8223568 := by
    simpa [prefixWord, tailWord_8223568, baseEnd_8223568] using wordTrace_append hprefix tailTrace_8223568
  have hstable : (prefixWord ++ tailWord_8223568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223568).length < 2 ^ (prefixWord ++ tailWord_8223568).sum := by decide
  have hdescent : baseEnd_8223568 < baseStart_8223568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223575 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 2, 4]
def baseStart_8223575 : Nat := 118140960795 + 8223575 * 2 ^ 59
def prefixEnd_8223575 : Nat := 4983230072969 + 3 ^ 40 * 8223575 * 2
def baseEnd_8223575 : Nat := 1407548891099255986230991

theorem tailTrace_8223575 : CollatzResearch.WordTrace tailWord_8223575 prefixEnd_8223575 1407548891099255986230991 := by
  unfold tailWord_8223575
  simp only [CollatzResearch.WordTrace]
  refine ⟨299938421182399724639160179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199958947454933149759440119 299938421182399724639160179)
  ·
    refine ⟨449907631773599586958740269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299938421182399724639160179 449907631773599586958740269)
    ·
      refine ⟨168715361915099845109527601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449907631773599586958740269 168715361915099845109527601)
      ·
        refine ⟨126536521436324883832145701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168715361915099845109527601 126536521436324883832145701)
        ·
          refine ⟨23725597769310915718527319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126536521436324883832145701 23725597769310915718527319)
          ·
            refine ⟨35588396653966373577790979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23725597769310915718527319 35588396653966373577790979)
            ·
              refine ⟨53382594980949560366686469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35588396653966373577790979 53382594980949560366686469)
              ·
                refine ⟨10009236558928042568753713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53382594980949560366686469 10009236558928042568753713)
                ·
                  refine ⟨7506927419196031926565285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10009236558928042568753713 7506927419196031926565285)
                  ·
                    refine ⟨1407548891099255986230991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7506927419196031926565285 1407548891099255986230991)
                    ·
                      rfl

theorem cell23_8223575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_8223575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223575 prefixEnd_8223575 := by exact prefixLift 8223575
  have htrace : WordTrace (prefixWord ++ tailWord_8223575) baseStart_8223575 baseEnd_8223575 := by
    simpa [prefixWord, tailWord_8223575, baseEnd_8223575] using wordTrace_append hprefix tailTrace_8223575
  have hstable : (prefixWord ++ tailWord_8223575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223575).length < 2 ^ (prefixWord ++ tailWord_8223575).sum := by decide
  have hdescent : baseEnd_8223575 < baseStart_8223575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223588 : List Nat := [2, 3, 1, 1, 4, 1, 3, 8]
def baseStart_8223588 : Nat := 118140960795 + 8223588 * 2 ^ 59
def prefixEnd_8223588 : Nat := 4983230072969 + 3 ^ 40 * 8223588 * 2
def baseEnd_8223588 : Nat := 156394568464676903993719

theorem tailTrace_8223588 : CollatzResearch.WordTrace tailWord_8223588 prefixEnd_8223588 156394568464676903993719 := by
  unfold tailWord_8223588
  simp only [CollatzResearch.WordTrace]
  refine ⟨149969447665676313929691709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199959263554235085239588945 149969447665676313929691709)
  ·
    refine ⟨56238542874628617723634391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149969447665676313929691709 56238542874628617723634391)
    ·
      refine ⟨84357814311942926585451587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56238542874628617723634391 84357814311942926585451587)
      ·
        refine ⟨126536721467914389878177381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84357814311942926585451587 126536721467914389878177381)
        ·
          refine ⟨23725635275233948102158259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126536721467914389878177381 23725635275233948102158259)
          ·
            refine ⟨35588452912850922153237389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23725635275233948102158259 35588452912850922153237389)
            ·
              refine ⟨13345669842319095807464021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35588452912850922153237389 13345669842319095807464021)
              ·
                refine ⟨156394568464676903993719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13345669842319095807464021 156394568464676903993719)
                ·
                  rfl

theorem cell23_8223588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 8].length) (baseStart_8223588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223588 prefixEnd_8223588 := by exact prefixLift 8223588
  have htrace : WordTrace (prefixWord ++ tailWord_8223588) baseStart_8223588 baseEnd_8223588 := by
    simpa [prefixWord, tailWord_8223588, baseEnd_8223588] using wordTrace_append hprefix tailTrace_8223588
  have hstable : (prefixWord ++ tailWord_8223588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223588).length < 2 ^ (prefixWord ++ tailWord_8223588).sum := by decide
  have hdescent : baseEnd_8223588 < baseStart_8223588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223605 : List Nat := [1, 3, 4, 1, 1, 3, 3, 7]
def baseStart_8223605 : Nat := 118140960795 + 8223605 * 2 ^ 59
def prefixEnd_8223605 : Nat := 4983230072969 + 3 ^ 40 * 8223605 * 2
def baseEnd_8223605 : Nat := 156394891767311216345105

theorem tailTrace_8223605 : CollatzResearch.WordTrace tailWord_8223605 prefixEnd_8223605 156394891767311216345105 := by
  unfold tailWord_8223605
  simp only [CollatzResearch.WordTrace]
  refine ⟨299939515372291039762752269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199959676914860693175168179 299939515372291039762752269)
  ·
    refine ⟨112477318264609139911032101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299939515372291039762752269 112477318264609139911032101)
    ·
      refine ⟨21089497174614213733318519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112477318264609139911032101 21089497174614213733318519)
      ·
        refine ⟨31634245761921320599977779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21089497174614213733318519 31634245761921320599977779)
        ·
          refine ⟨47451368642881980899966669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31634245761921320599977779 47451368642881980899966669)
          ·
            refine ⟨17794263241080742837487501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47451368642881980899966669 17794263241080742837487501)
            ·
              refine ⟨6672848715405278564057813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17794263241080742837487501 6672848715405278564057813)
              ·
                refine ⟨156394891767311216345105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6672848715405278564057813 156394891767311216345105)
                ·
                  rfl

theorem cell23_8223605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 7].length) (baseStart_8223605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223605 prefixEnd_8223605 := by exact prefixLift 8223605
  have htrace : WordTrace (prefixWord ++ tailWord_8223605) baseStart_8223605 baseEnd_8223605 := by
    simpa [prefixWord, tailWord_8223605, baseEnd_8223605] using wordTrace_append hprefix tailTrace_8223605
  have hstable : (prefixWord ++ tailWord_8223605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223605).length < 2 ^ (prefixWord ++ tailWord_8223605).sum := by decide
  have hdescent : baseEnd_8223605 < baseStart_8223605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223631 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 12]
def baseStart_8223631 : Nat := 118140960795 + 8223631 * 2 ^ 59
def prefixEnd_8223631 : Nat := 4983230072969 + 3 ^ 40 * 8223631 * 2
def baseEnd_8223631 : Nat := 1407558476071473246530905

theorem tailTrace_8223631 : CollatzResearch.WordTrace tailWord_8223631 prefixEnd_8223631 1407558476071473246530905 := by
  unfold tailWord_8223631
  simp only [CollatzResearch.WordTrace]
  refine ⟨299940463670196846203198747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199960309113464564135465831 299940463670196846203198747)
  ·
    refine ⟨449910695505295269304798121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299940463670196846203198747 449910695505295269304798121)
    ·
      refine ⟨337433021628971451978598591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449910695505295269304798121 337433021628971451978598591)
      ·
        refine ⟨506149532443457177967897887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337433021628971451978598591 506149532443457177967897887)
        ·
          refine ⟨759224298665185766951846831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506149532443457177967897887 759224298665185766951846831)
          ·
            refine ⟨1138836447997778650427770247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759224298665185766951846831 1138836447997778650427770247)
            ·
              refine ⟨1708254671996667975641655371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138836447997778650427770247 1708254671996667975641655371)
              ·
                refine ⟨2562382007995001963462483057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708254671996667975641655371 2562382007995001963462483057)
                ·
                  refine ⟨1921786505996251472596862293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2562382007995001963462483057 1921786505996251472596862293)
                  ·
                    refine ⟨1407558476071473246530905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1921786505996251472596862293 1407558476071473246530905)
                    ·
                      rfl

theorem cell23_8223631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_8223631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223631 prefixEnd_8223631 := by exact prefixLift 8223631
  have htrace : WordTrace (prefixWord ++ tailWord_8223631) baseStart_8223631 baseEnd_8223631 := by
    simpa [prefixWord, tailWord_8223631, baseEnd_8223631] using wordTrace_append hprefix tailTrace_8223631
  have hstable : (prefixWord ++ tailWord_8223631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223631).length < 2 ^ (prefixWord ++ tailWord_8223631).sum := by decide
  have hdescent : baseEnd_8223631 < baseStart_8223631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223648 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 2, 6]
def baseStart_8223648 : Nat := 118140960795 + 8223648 * 2 ^ 59
def prefixEnd_8223648 : Nat := 4983230072969 + 3 ^ 40 * 8223648 * 2
def baseEnd_8223648 : Nat := 1407561385795182057693379

theorem tailTrace_8223648 : CollatzResearch.WordTrace tailWord_8223648 prefixEnd_8223648 1407561385795182057693379 := by
  unfold tailWord_8223648
  simp only [CollatzResearch.WordTrace]
  refine ⟨149970541855567629053283799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199960722474090172071045065 149970541855567629053283799)
  ·
    refine ⟨224955812783351443579925699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149970541855567629053283799 224955812783351443579925699)
    ·
      refine ⟨337433719175027165369888549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224955812783351443579925699 337433719175027165369888549)
      ·
        refine ⟨63268822345317593506854103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337433719175027165369888549 63268822345317593506854103)
        ·
          refine ⟨94903233517976390260281155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63268822345317593506854103 94903233517976390260281155)
          ·
            refine ⟨142354850276964585390421733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94903233517976390260281155 142354850276964585390421733)
            ·
              refine ⟨26691534426930859760704075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142354850276964585390421733 26691534426930859760704075)
              ·
                refine ⟨40037301640396289641056113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26691534426930859760704075 40037301640396289641056113)
                ·
                  refine ⟨30027976230297217230792085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40037301640396289641056113 30027976230297217230792085)
                  ·
                    refine ⟨1407561385795182057693379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30027976230297217230792085 1407561385795182057693379)
                    ·
                      rfl

theorem cell23_8223648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_8223648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223648 prefixEnd_8223648 := by exact prefixLift 8223648
  have htrace : WordTrace (prefixWord ++ tailWord_8223648) baseStart_8223648 baseEnd_8223648 := by
    simpa [prefixWord, tailWord_8223648, baseEnd_8223648] using wordTrace_append hprefix tailTrace_8223648
  have hstable : (prefixWord ++ tailWord_8223648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223648).length < 2 ^ (prefixWord ++ tailWord_8223648).sum := by decide
  have hdescent : baseEnd_8223648 < baseStart_8223648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223672 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 4, 2, 2]
def baseStart_8223672 : Nat := 118140960795 + 8223672 * 2 ^ 59
def prefixEnd_8223672 : Nat := 4983230072969 + 3 ^ 40 * 8223672 * 2
def baseEnd_8223672 : Nat := 4222696480921254079180027

theorem tailTrace_8223672 : CollatzResearch.WordTrace tailWord_8223672 prefixEnd_8223672 4222696480921254079180027 := by
  unfold tailWord_8223672
  simp only [CollatzResearch.WordTrace]
  refine ⟨149970979531524155102720635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199961306042032206803627513 149970979531524155102720635)
  ·
    refine ⟨224956469297286232654080953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149970979531524155102720635 224956469297286232654080953)
    ·
      refine ⟨168717351972964674490560715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224956469297286232654080953 168717351972964674490560715)
      ·
        refine ⟨253076027959447011735841073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168717351972964674490560715 253076027959447011735841073)
        ·
          refine ⟨189807020969585258801880805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253076027959447011735841073 189807020969585258801880805)
          ·
            refine ⟨35588816431797236025352651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189807020969585258801880805 35588816431797236025352651)
            ·
              refine ⟨53383224647695854038028977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35588816431797236025352651 53383224647695854038028977)
              ·
                refine ⟨40037418485771890528521733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53383224647695854038028977 40037418485771890528521733)
                ·
                  refine ⟨7507015966082229474097825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40037418485771890528521733 7507015966082229474097825)
                  ·
                    refine ⟨5630261974561672105573369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7507015966082229474097825 5630261974561672105573369)
                    ·
                      refine ⟨4222696480921254079180027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630261974561672105573369 4222696480921254079180027)
                      ·
                        rfl

theorem cell23_8223672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_8223672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223672 prefixEnd_8223672 := by exact prefixLift 8223672
  have htrace : WordTrace (prefixWord ++ tailWord_8223672) baseStart_8223672 baseEnd_8223672 := by
    simpa [prefixWord, tailWord_8223672, baseEnd_8223672] using wordTrace_append hprefix tailTrace_8223672
  have hstable : (prefixWord ++ tailWord_8223672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223672).length < 2 ^ (prefixWord ++ tailWord_8223672).sum := by decide
  have hdescent : baseEnd_8223672 < baseStart_8223672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223695 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 7]
def baseStart_8223695 : Nat := 118140960795 + 8223695 * 2 ^ 59
def prefixEnd_8223695 : Nat := 4983230072969 + 3 ^ 40 * 8223695 * 2
def baseEnd_8223695 : Nat := 469189810108478609910269

theorem tailTrace_8223695 : CollatzResearch.WordTrace tailWord_8223695 prefixEnd_8223695 469189810108478609910269 := by
  unfold tailWord_8223695
  simp only [CollatzResearch.WordTrace]
  refine ⟨299942797941964985133528539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199961865294643323422352359 299942797941964985133528539)
  ·
    refine ⟨449914196912947477700292809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299942797941964985133528539 449914196912947477700292809)
    ·
      refine ⟨337435647684710608275219607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449914196912947477700292809 337435647684710608275219607)
      ·
        refine ⟨506153471527065912412829411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337435647684710608275219607 506153471527065912412829411)
        ·
          refine ⟨759230207290598868619244117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506153471527065912412829411 759230207290598868619244117)
          ·
            refine ⟨8897228991686705491631767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 759230207290598868619244117 8897228991686705491631767)
            ·
              refine ⟨13345843487530058237447651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8897228991686705491631767 13345843487530058237447651)
              ·
                refine ⟨20018765231295087356171477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13345843487530058237447651 20018765231295087356171477)
                ·
                  refine ⟨469189810108478609910269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20018765231295087356171477 469189810108478609910269)
                  ·
                    rfl

theorem cell23_8223695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 7].length) (baseStart_8223695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223695 prefixEnd_8223695 := by exact prefixLift 8223695
  have htrace : WordTrace (prefixWord ++ tailWord_8223695) baseStart_8223695 baseEnd_8223695 := by
    simpa [prefixWord, tailWord_8223695, baseEnd_8223695] using wordTrace_append hprefix tailTrace_8223695
  have hstable : (prefixWord ++ tailWord_8223695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223695).length < 2 ^ (prefixWord ++ tailWord_8223695).sum := by decide
  have hdescent : baseEnd_8223695 < baseStart_8223695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223706 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2]
def baseStart_8223706 : Nat := 118140960795 + 8223706 * 2 ^ 59
def prefixEnd_8223706 : Nat := 4983230072969 + 3 ^ 40 * 8223706 * 2
def baseEnd_8223706 : Nat := 4222713939263506946154871

theorem tailTrace_8223706 : CollatzResearch.WordTrace tailWord_8223706 prefixEnd_8223706 4222713939263506946154871 := by
  unfold tailWord_8223706
  simp only [CollatzResearch.WordTrace]
  refine ⟨74985799786231283503044743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199962132763283422674785981 74985799786231283503044743)
  ·
    refine ⟨112478699679346925254567115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74985799786231283503044743 112478699679346925254567115)
    ·
      refine ⟨168718049519020387881850673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112478699679346925254567115 168718049519020387881850673)
      ·
        refine ⟨126538537139265290911388005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168718049519020387881850673 126538537139265290911388005)
        ·
          refine ⟨23725975713612242045885251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126538537139265290911388005 23725975713612242045885251)
          ·
            refine ⟨35588963570418363068827877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23725975713612242045885251 35588963570418363068827877)
            ·
              refine ⟨6672930669453443075405227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35588963570418363068827877 6672930669453443075405227)
              ·
                refine ⟨10009396004180164613107841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672930669453443075405227 10009396004180164613107841)
                ·
                  refine ⟨7507047003135123459830881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10009396004180164613107841 7507047003135123459830881)
                  ·
                    refine ⟨5630285252351342594873161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7507047003135123459830881 5630285252351342594873161)
                    ·
                      refine ⟨4222713939263506946154871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630285252351342594873161 4222713939263506946154871)
                      ·
                        rfl

theorem cell23_8223706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_8223706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223706 prefixEnd_8223706 := by exact prefixLift 8223706
  have htrace : WordTrace (prefixWord ++ tailWord_8223706) baseStart_8223706 baseEnd_8223706 := by
    simpa [prefixWord, tailWord_8223706, baseEnd_8223706] using wordTrace_append hprefix tailTrace_8223706
  have hstable : (prefixWord ++ tailWord_8223706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223706).length < 2 ^ (prefixWord ++ tailWord_8223706).sum := by decide
  have hdescent : baseEnd_8223706 < baseStart_8223706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223746 : List Nat := [3, 4, 1, 3, 1, 1, 1, 4, 5]
def baseStart_8223746 : Nat := 118140960795 + 8223746 * 2 ^ 59
def prefixEnd_8223746 : Nat := 4983230072969 + 3 ^ 40 * 8223746 * 2
def baseEnd_8223746 : Nat := 469192719832187421072743

theorem tailTrace_8223746 : CollatzResearch.WordTrace tailWord_8223746 prefixEnd_8223746 469192719832187421072743 := by
  unfold tailWord_8223746
  simp only [CollatzResearch.WordTrace]
  refine ⟨74986164516195055210908773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199963105376520147229090061 74986164516195055210908773)
  ·
    refine ⟨14059905846786572852045395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74986164516195055210908773 14059905846786572852045395)
    ·
      refine ⟨21089858770179859278068093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14059905846786572852045395 21089858770179859278068093)
      ·
        refine ⟨7908697038817447229275535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21089858770179859278068093 7908697038817447229275535)
        ·
          refine ⟨11863045558226170843913303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7908697038817447229275535 11863045558226170843913303)
          ·
            refine ⟨17794568337339256265869955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11863045558226170843913303 17794568337339256265869955)
            ·
              refine ⟨26691852506008884398804933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17794568337339256265869955 26691852506008884398804933)
              ·
                refine ⟨5004722344876665824775925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26691852506008884398804933 5004722344876665824775925)
                ·
                  refine ⟨469192719832187421072743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5004722344876665824775925 469192719832187421072743)
                  ·
                    rfl

theorem cell23_8223746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_8223746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223746 prefixEnd_8223746 := by exact prefixLift 8223746
  have htrace : WordTrace (prefixWord ++ tailWord_8223746) baseStart_8223746 baseEnd_8223746 := by
    simpa [prefixWord, tailWord_8223746, baseEnd_8223746] using wordTrace_append hprefix tailTrace_8223746
  have hstable : (prefixWord ++ tailWord_8223746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223746).length < 2 ^ (prefixWord ++ tailWord_8223746).sum := by decide
  have hdescent : baseEnd_8223746 < baseStart_8223746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223776 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 2, 5]
def baseStart_8223776 : Nat := 118140960795 + 8223776 * 2 ^ 59
def prefixEnd_8223776 : Nat := 4983230072969 + 3 ^ 40 * 8223776 * 2
def baseEnd_8223776 : Nat := 1407583294303107224093183

theorem tailTrace_8223776 : CollatzResearch.WordTrace tailWord_8223776 prefixEnd_8223776 1407583294303107224093183 := by
  unfold tailWord_8223776
  simp only [CollatzResearch.WordTrace]
  refine ⟨149972876127335767983613591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199963834836447690644818121 149972876127335767983613591)
  ·
    refine ⟨224959314191003651975420387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149972876127335767983613591 224959314191003651975420387)
    ·
      refine ⟨337438971286505477963130581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224959314191003651975420387 337438971286505477963130581)
      ·
        refine ⟨7908725889527472139760873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 337438971286505477963130581 7908725889527472139760873)
        ·
          refine ⟨5931544417145604104820655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7908725889527472139760873 5931544417145604104820655)
          ·
            refine ⟨8897316625718406157230983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931544417145604104820655 8897316625718406157230983)
            ·
              refine ⟨13345974938577609235846475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8897316625718406157230983 13345974938577609235846475)
              ·
                refine ⟨20018962407866413853769713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13345974938577609235846475 20018962407866413853769713)
                ·
                  refine ⟨15014221805899810390327285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20018962407866413853769713 15014221805899810390327285)
                  ·
                    refine ⟨1407583294303107224093183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15014221805899810390327285 1407583294303107224093183)
                    ·
                      rfl

theorem cell23_8223776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 5].length) (baseStart_8223776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223776 prefixEnd_8223776 := by exact prefixLift 8223776
  have htrace : WordTrace (prefixWord ++ tailWord_8223776) baseStart_8223776 baseEnd_8223776 := by
    simpa [prefixWord, tailWord_8223776, baseEnd_8223776] using wordTrace_append hprefix tailTrace_8223776
  have hstable : (prefixWord ++ tailWord_8223776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223776).length < 2 ^ (prefixWord ++ tailWord_8223776).sum := by decide
  have hdescent : baseEnd_8223776 < baseStart_8223776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223805 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_8223805 : Nat := 118140960795 + 8223805 * 2 ^ 59
def prefixEnd_8223805 : Nat := 4983230072969 + 3 ^ 40 * 8223805 * 2
def baseEnd_8223805 : Nat := 4222764773848302058816915

theorem tailTrace_8223805 : CollatzResearch.WordTrace tailWord_8223805 prefixEnd_8223805 4222764773848302058816915 := by
  unfold tailWord_8223805
  simp only [CollatzResearch.WordTrace]
  refine ⟨299946809971566473920032869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199964539981044315946688579 299946809971566473920032869)
  ·
    refine ⟨56240026869668713860006163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299946809971566473920032869 56240026869668713860006163)
    ·
      refine ⟨84360040304503070790009245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56240026869668713860006163 84360040304503070790009245)
      ·
        refine ⟨31635015114188651546253467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84360040304503070790009245 31635015114188651546253467)
        ·
          refine ⟨47452522671282977319380201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31635015114188651546253467 47452522671282977319380201)
          ·
            refine ⟨35589392003462232989535151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47452522671282977319380201 35589392003462232989535151)
            ·
              refine ⟨53384088005193349484302727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35589392003462232989535151 53384088005193349484302727)
              ·
                refine ⟨80076132007790024226454091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53384088005193349484302727 80076132007790024226454091)
                ·
                  refine ⟨120114198011685036339681137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80076132007790024226454091 120114198011685036339681137)
                  ·
                    refine ⟨90085648508763777254760853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120114198011685036339681137 90085648508763777254760853)
                    ·
                      refine ⟨4222764773848302058816915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90085648508763777254760853 4222764773848302058816915)
                      ·
                        rfl

theorem cell23_8223805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_8223805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223805 prefixEnd_8223805 := by exact prefixLift 8223805
  have htrace : WordTrace (prefixWord ++ tailWord_8223805) baseStart_8223805 baseEnd_8223805 := by
    simpa [prefixWord, tailWord_8223805, baseEnd_8223805] using wordTrace_append hprefix tailTrace_8223805
  have hstable : (prefixWord ++ tailWord_8223805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223805).length < 2 ^ (prefixWord ++ tailWord_8223805).sum := by decide
  have hdescent : baseEnd_8223805 < baseStart_8223805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223806 : List Nat := [4, 2, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_8223806 : Nat := 118140960795 + 8223806 * 2 ^ 59
def prefixEnd_8223806 : Nat := 4983230072969 + 3 ^ 40 * 8223806 * 2
def baseEnd_8223806 : Nat := 1407588429109652184968137

theorem tailTrace_8223806 : CollatzResearch.WordTrace tailWord_8223806 prefixEnd_8223806 1407588429109652184968137 := by
  unfold tailWord_8223806
  simp only [CollatzResearch.WordTrace]
  refine ⟨37493355805570356386352409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199964564296375234060546181 37493355805570356386352409)
  ·
    refine ⟨28120016854177767289764307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37493355805570356386352409 28120016854177767289764307)
    ·
      refine ⟨42180025281266650934646461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28120016854177767289764307 42180025281266650934646461)
      ·
        refine ⟨15817509480474994100492423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42180025281266650934646461 15817509480474994100492423)
        ·
          refine ⟨23726264220712491150738635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15817509480474994100492423 23726264220712491150738635)
          ·
            refine ⟨35589396331068736726107953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23726264220712491150738635 35589396331068736726107953)
            ·
              refine ⟨26692047248301552544580965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35589396331068736726107953 26692047248301552544580965)
              ·
                refine ⟨5004758859056541102108931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26692047248301552544580965 5004758859056541102108931)
                ·
                  refine ⟨7507138288584811653163397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5004758859056541102108931 7507138288584811653163397)
                  ·
                    refine ⟨1407588429109652184968137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7507138288584811653163397 1407588429109652184968137)
                    ·
                      rfl

theorem cell23_8223806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_8223806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223806 prefixEnd_8223806 := by exact prefixLift 8223806
  have htrace : WordTrace (prefixWord ++ tailWord_8223806) baseStart_8223806 baseEnd_8223806 := by
    simpa [prefixWord, tailWord_8223806, baseEnd_8223806] using wordTrace_append hprefix tailTrace_8223806
  have hstable : (prefixWord ++ tailWord_8223806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223806).length < 2 ^ (prefixWord ++ tailWord_8223806).sum := by decide
  have hdescent : baseEnd_8223806 < baseStart_8223806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223822 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_8223822 : Nat := 118140960795 + 8223822 * 2 ^ 59
def prefixEnd_8223822 : Nat := 4983230072969 + 3 ^ 40 * 8223822 * 2
def baseEnd_8223822 : Nat := 4222773503019428492304337

theorem tailTrace_8223822 : CollatzResearch.WordTrace tailWord_8223822 prefixEnd_8223822 4222773503019428492304337 := by
  unfold tailWord_8223822
  simp only [CollatzResearch.WordTrace]
  refine ⟨37493428751563110727925215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199964953341669923882267813 37493428751563110727925215)
  ·
    refine ⟨56240143127344666091887823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37493428751563110727925215 56240143127344666091887823)
    ·
      refine ⟨84360214691016999137831735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56240143127344666091887823 84360214691016999137831735)
      ·
        refine ⟨126540322036525498706747603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84360214691016999137831735 126540322036525498706747603)
        ·
          refine ⟨189810483054788248060121405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126540322036525498706747603 189810483054788248060121405)
          ·
            refine ⟨71178931145545593022545527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189810483054788248060121405 71178931145545593022545527)
            ·
              refine ⟨106768396718318389533818291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71178931145545593022545527 106768396718318389533818291)
              ·
                refine ⟨160152595077477584300727437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106768396718318389533818291 160152595077477584300727437)
                ·
                  refine ⟨60057223154054094112772789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160152595077477584300727437 60057223154054094112772789)
                  ·
                    refine ⟨5630364670692571323072449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60057223154054094112772789 5630364670692571323072449)
                    ·
                      refine ⟨4222773503019428492304337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630364670692571323072449 4222773503019428492304337)
                      ·
                        rfl

theorem cell23_8223822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_8223822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223822 prefixEnd_8223822 := by exact prefixLift 8223822
  have htrace : WordTrace (prefixWord ++ tailWord_8223822) baseStart_8223822 baseEnd_8223822 := by
    simpa [prefixWord, tailWord_8223822, baseEnd_8223822] using wordTrace_append hprefix tailTrace_8223822
  have hstable : (prefixWord ++ tailWord_8223822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223822).length < 2 ^ (prefixWord ++ tailWord_8223822).sum := by decide
  have hdescent : baseEnd_8223822 < baseStart_8223822 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223832 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 1, 5]
def baseStart_8223832 : Nat := 118140960795 + 8223832 * 2 ^ 59
def prefixEnd_8223832 : Nat := 4983230072969 + 3 ^ 40 * 8223832 * 2
def baseEnd_8223832 : Nat := 1407592879275324484393097

theorem tailTrace_8223832 : CollatzResearch.WordTrace tailWord_8223832 prefixEnd_8223832 1407592879275324484393097 := by
  unfold tailWord_8223832
  simp only [CollatzResearch.WordTrace]
  refine ⟨149973897371234328765632875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199965196494979105020843833 149973897371234328765632875)
  ·
    refine ⟨224960846056851493148449313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149973897371234328765632875 224960846056851493148449313)
    ·
      refine ⟨168720634542638619861336985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224960846056851493148449313 168720634542638619861336985)
      ·
        refine ⟨126540475906978964896002739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168720634542638619861336985 126540475906978964896002739)
        ·
          refine ⟨189810713860468447344004109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126540475906978964896002739 189810713860468447344004109)
          ·
            refine ⟨71179017697675667754001541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189810713860468447344004109 71179017697675667754001541)
            ·
              refine ⟨13346065818314187703875289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71179017697675667754001541 13346065818314187703875289)
              ·
                refine ⟨10009549363735640777906467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13346065818314187703875289 10009549363735640777906467)
                ·
                  refine ⟨15014324045603461166859701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10009549363735640777906467 15014324045603461166859701)
                  ·
                    refine ⟨1407592879275324484393097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15014324045603461166859701 1407592879275324484393097)
                    ·
                      rfl

theorem cell23_8223832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_8223832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223832 prefixEnd_8223832 := by exact prefixLift 8223832
  have htrace : WordTrace (prefixWord ++ tailWord_8223832) baseStart_8223832 baseEnd_8223832 := by
    simpa [prefixWord, tailWord_8223832, baseEnd_8223832] using wordTrace_append hprefix tailTrace_8223832
  have hstable : (prefixWord ++ tailWord_8223832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223832).length < 2 ^ (prefixWord ++ tailWord_8223832).sum := by decide
  have hdescent : baseEnd_8223832 < baseStart_8223832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223845 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_8223845 : Nat := 118140960795 + 8223845 * 2 ^ 59
def prefixEnd_8223845 : Nat := 4983230072969 + 3 ^ 40 * 8223845 * 2
def baseEnd_8223845 : Nat := 1407595104358160634105577

theorem tailTrace_8223845 : CollatzResearch.WordTrace tailWord_8223845 prefixEnd_8223845 1407595104358160634105577 := by
  unfold tailWord_8223845
  simp only [CollatzResearch.WordTrace]
  refine ⟨299948268891421560751488989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199965512594281040500992659 299948268891421560751488989)
  ·
    refine ⟨112480600834283085281808371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299948268891421560751488989 112480600834283085281808371)
    ·
      refine ⟨168720901251424627922712557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112480600834283085281808371 168720901251424627922712557)
      ·
        refine ⟨63270337969284235471017209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168720901251424627922712557 63270337969284235471017209)
        ·
          refine ⟨47452753476963176603262907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63270337969284235471017209 47452753476963176603262907)
          ·
            refine ⟨71179130215444764904894361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47452753476963176603262907 71179130215444764904894361)
            ·
              refine ⟨53384347661583573678670771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71179130215444764904894361 53384347661583573678670771)
              ·
                refine ⟨80076521492375360518006157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53384347661583573678670771 80076521492375360518006157)
                ·
                  refine ⟨30028695559640760194252309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80076521492375360518006157 30028695559640760194252309)
                  ·
                    refine ⟨1407595104358160634105577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30028695559640760194252309 1407595104358160634105577)
                    ·
                      rfl

theorem cell23_8223845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_8223845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223845 prefixEnd_8223845 := by exact prefixLift 8223845
  have htrace : WordTrace (prefixWord ++ tailWord_8223845) baseStart_8223845 baseEnd_8223845 := by
    simpa [prefixWord, tailWord_8223845, baseEnd_8223845] using wordTrace_append hprefix tailTrace_8223845
  have hstable : (prefixWord ++ tailWord_8223845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223845).length < 2 ^ (prefixWord ++ tailWord_8223845).sum := by decide
  have hdescent : baseEnd_8223845 < baseStart_8223845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223852 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 4]
def baseStart_8223852 : Nat := 118140960795 + 8223852 * 2 ^ 59
def prefixEnd_8223852 : Nat := 4983230072969 + 3 ^ 40 * 8223852 * 2
def baseEnd_8223852 : Nat := 4222788907439063374929199

theorem tailTrace_8223852 : CollatzResearch.WordTrace tailWord_8223852 prefixEnd_8223852 4222788907439063374929199 := by
  unfold tailWord_8223852
  simp only [CollatzResearch.WordTrace]
  refine ⟨149974262101198100473496905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199965682801597467297995873 149974262101198100473496905)
  ·
    refine ⟨112480696575898575355122679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149974262101198100473496905 112480696575898575355122679)
    ·
      refine ⟨168721044863847863032684019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112480696575898575355122679 168721044863847863032684019)
      ·
        refine ⟨253081567295771794549026029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168721044863847863032684019 253081567295771794549026029)
        ·
          refine ⟨94905587735914422955884761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253081567295771794549026029 94905587735914422955884761)
          ·
            refine ⟨71179190801935817216913571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94905587735914422955884761 71179190801935817216913571)
            ·
              refine ⟨106768786202903725825370357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71179190801935817216913571 106768786202903725825370357)
              ·
                refine ⟨10009573706522224296128471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106768786202903725825370357 10009573706522224296128471)
                ·
                  refine ⟨15014360559783336444192707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10009573706522224296128471 15014360559783336444192707)
                  ·
                    refine ⟨22521540839675004666289061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15014360559783336444192707 22521540839675004666289061)
                    ·
                      refine ⟨4222788907439063374929199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22521540839675004666289061 4222788907439063374929199)
                      ·
                        rfl

theorem cell23_8223852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_8223852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223852 prefixEnd_8223852 := by exact prefixLift 8223852
  have htrace : WordTrace (prefixWord ++ tailWord_8223852) baseStart_8223852 baseEnd_8223852 := by
    simpa [prefixWord, tailWord_8223852, baseEnd_8223852] using wordTrace_append hprefix tailTrace_8223852
  have hstable : (prefixWord ++ tailWord_8223852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223852).length < 2 ^ (prefixWord ++ tailWord_8223852).sum := by decide
  have hdescent : baseEnd_8223852 < baseStart_8223852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223870 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_8223870 : Nat := 118140960795 + 8223870 * 2 ^ 59
def prefixEnd_8223870 : Nat := 4983230072969 + 3 ^ 40 * 8223870 * 2
def baseEnd_8223870 : Nat := 469199794454538256056013

theorem tailTrace_8223870 : CollatzResearch.WordTrace tailWord_8223870 prefixEnd_8223870 469199794454538256056013 := by
  unfold tailWord_8223870
  simp only [CollatzResearch.WordTrace]
  refine ⟨37493647589541373752643633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199966120477553993347432709 37493647589541373752643633)
  ·
    refine ⟨28120235692156030314482725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37493647589541373752643633 28120235692156030314482725)
    ·
      refine ⟨5272544192279255683965511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28120235692156030314482725 5272544192279255683965511)
      ·
        refine ⟨7908816288418883525948267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5272544192279255683965511 7908816288418883525948267)
        ·
          refine ⟨11863224432628325288922401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7908816288418883525948267 11863224432628325288922401)
          ·
            refine ⟨8897418324471243966691801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11863224432628325288922401 8897418324471243966691801)
            ·
              refine ⟨6673063743353432975018851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8897418324471243966691801 6673063743353432975018851)
              ·
                refine ⟨10009595615030149462528277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673063743353432975018851 10009595615030149462528277)
                ·
                  refine ⟨469199794454538256056013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10009595615030149462528277 469199794454538256056013)
                  ·
                    rfl

theorem cell23_8223870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_8223870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223870 prefixEnd_8223870 := by exact prefixLift 8223870
  have htrace : WordTrace (prefixWord ++ tailWord_8223870) baseStart_8223870 baseEnd_8223870 := by
    simpa [prefixWord, tailWord_8223870, baseEnd_8223870] using wordTrace_append hprefix tailTrace_8223870
  have hstable : (prefixWord ++ tailWord_8223870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223870).length < 2 ^ (prefixWord ++ tailWord_8223870).sum := by decide
  have hdescent : baseEnd_8223870 < baseStart_8223870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223875 : List Nat := [1, 1, 1, 3, 3, 2, 4, 8]
def baseStart_8223875 : Nat := 118140960795 + 8223875 * 2 ^ 59
def prefixEnd_8223875 : Nat := 4983230072969 + 3 ^ 40 * 8223875 * 2
def baseEnd_8223875 : Nat := 156400026573856177220059

theorem tailTrace_8223875 : CollatzResearch.WordTrace tailWord_8223875 prefixEnd_8223875 156400026573856177220059 := by
  unfold tailWord_8223875
  simp only [CollatzResearch.WordTrace]
  refine ⟨299949363081312875875081079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199966242054208583916720719 299949363081312875875081079)
  ·
    refine ⟨449924044621969313812621619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299949363081312875875081079 449924044621969313812621619)
    ·
      refine ⟨674886066932953970718932429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449924044621969313812621619 674886066932953970718932429)
      ·
        refine ⟨253082275099857739019599661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674886066932953970718932429 253082275099857739019599661)
        ·
          refine ⟨94905853162446652132349873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253082275099857739019599661 94905853162446652132349873)
          ·
            refine ⟨71179389871834989099262405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94905853162446652132349873 71179389871834989099262405)
            ·
              refine ⟨13346135600969060456111701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71179389871834989099262405 13346135600969060456111701)
              ·
                refine ⟨156400026573856177220059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13346135600969060456111701 156400026573856177220059)
                ·
                  rfl

theorem cell23_8223875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 8].length) (baseStart_8223875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223875 prefixEnd_8223875 := by exact prefixLift 8223875
  have htrace : WordTrace (prefixWord ++ tailWord_8223875) baseStart_8223875 baseEnd_8223875 := by
    simpa [prefixWord, tailWord_8223875, baseEnd_8223875] using wordTrace_append hprefix tailTrace_8223875
  have hstable : (prefixWord ++ tailWord_8223875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223875).length < 2 ^ (prefixWord ++ tailWord_8223875).sum := by decide
  have hdescent : baseEnd_8223875 < baseStart_8223875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223882 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_8223882 : Nat := 118140960795 + 8223882 * 2 ^ 59
def prefixEnd_8223882 : Nat := 4983230072969 + 3 ^ 40 * 8223882 * 2
def baseEnd_8223882 : Nat := 4222804311858698257554061

theorem tailTrace_8223882 : CollatzResearch.WordTrace tailWord_8223882 prefixEnd_8223882 4222804311858698257554061 := by
  unfold tailWord_8223882
  simp only [CollatzResearch.WordTrace]
  refine ⟨74987404598071879017646475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199966412261525010713723933 74987404598071879017646475)
  ·
    refine ⟨112481106897107818526469713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74987404598071879017646475 112481106897107818526469713)
    ·
      refine ⟨84360830172830863894852285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112481106897107818526469713 84360830172830863894852285)
      ·
        refine ⟨31635311314811573960569607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84360830172830863894852285 31635311314811573960569607)
        ·
          refine ⟨47452966972217360940854411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31635311314811573960569607 47452966972217360940854411)
          ·
            refine ⟨71179450458326041411281617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47452966972217360940854411 71179450458326041411281617)
            ·
              refine ⟨53384587843744531058461213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71179450458326041411281617 53384587843744531058461213)
              ·
                refine ⟨20019220441404199146922955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53384587843744531058461213 20019220441404199146922955)
                ·
                  refine ⟨30028830662106298720384433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20019220441404199146922955 30028830662106298720384433)
                  ·
                    refine ⟨22521622996579724040288325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30028830662106298720384433 22521622996579724040288325)
                    ·
                      refine ⟨4222804311858698257554061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22521622996579724040288325 4222804311858698257554061)
                      ·
                        rfl

theorem cell23_8223882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_8223882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223882 prefixEnd_8223882 := by exact prefixLift 8223882
  have htrace : WordTrace (prefixWord ++ tailWord_8223882) baseStart_8223882 baseEnd_8223882 := by
    simpa [prefixWord, tailWord_8223882, baseEnd_8223882] using wordTrace_append hprefix tailTrace_8223882
  have hstable : (prefixWord ++ tailWord_8223882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223882).length < 2 ^ (prefixWord ++ tailWord_8223882).sum := by decide
  have hdescent : baseEnd_8223882 < baseStart_8223882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223886 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_8223886 : Nat := 118140960795 + 8223886 * 2 ^ 59
def prefixEnd_8223886 : Nat := 4983230072969 + 3 ^ 40 * 8223886 * 2
def baseEnd_8223886 : Nat := 4222806365781316241904043

theorem tailTrace_8223886 : CollatzResearch.WordTrace tailWord_8223886 prefixEnd_8223886 4222806365781316241904043 := by
  unfold tailWord_8223886
  simp only [CollatzResearch.WordTrace]
  refine ⟨37493720535534128094216439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199966509522848683169154341 37493720535534128094216439)
  ·
    refine ⟨56240580803301192141324659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37493720535534128094216439 56240580803301192141324659)
    ·
      refine ⟨84360871204951788211986989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56240580803301192141324659 84360871204951788211986989)
      ·
        refine ⟨31635326701856920579495121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84360871204951788211986989 31635326701856920579495121)
        ·
          refine ⟨23726495026392690434621341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31635326701856920579495121 23726495026392690434621341)
          ·
            refine ⟨8897435634897258912983003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23726495026392690434621341 8897435634897258912983003)
            ·
              refine ⟨13346153452345888369474505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8897435634897258912983003 13346153452345888369474505)
              ·
                refine ⟨10009615089259416277105879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13346153452345888369474505 10009615089259416277105879)
                ·
                  refine ⟨15014422633889124415658819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10009615089259416277105879 15014422633889124415658819)
                  ·
                    refine ⟨22521633950833686623488229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15014422633889124415658819 22521633950833686623488229)
                    ·
                      refine ⟨4222806365781316241904043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22521633950833686623488229 4222806365781316241904043)
                      ·
                        rfl

theorem cell23_8223886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_8223886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223886 prefixEnd_8223886 := by exact prefixLift 8223886
  have htrace : WordTrace (prefixWord ++ tailWord_8223886) baseStart_8223886 baseEnd_8223886 := by
    simpa [prefixWord, tailWord_8223886, baseEnd_8223886] using wordTrace_append hprefix tailTrace_8223886
  have hstable : (prefixWord ++ tailWord_8223886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223886).length < 2 ^ (prefixWord ++ tailWord_8223886).sum := by decide
  have hdescent : baseEnd_8223886 < baseStart_8223886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223906 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_8223906 : Nat := 118140960795 + 8223906 * 2 ^ 59
def prefixEnd_8223906 : Nat := 4983230072969 + 3 ^ 40 * 8223906 * 2
def baseEnd_8223906 : Nat := 4222816635394406163653951

theorem tailTrace_8223906 : CollatzResearch.WordTrace tailWord_8223906 prefixEnd_8223906 4222816635394406163653951 := by
  unfold tailWord_8223906
  simp only [CollatzResearch.WordTrace]
  refine ⟨74987623436050142042364893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199966995829467045446306381 74987623436050142042364893)
  ·
    refine ⟨28120358788518803265886835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74987623436050142042364893 28120358788518803265886835)
    ·
      refine ⟨42180538182778204898830253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28120358788518803265886835 42180538182778204898830253)
      ·
        refine ⟨15817701818541826837061345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42180538182778204898830253 15817701818541826837061345)
        ·
          refine ⟨11863276363906370127796009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15817701818541826837061345 11863276363906370127796009)
          ·
            refine ⟨8897457272929777595847007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11863276363906370127796009 8897457272929777595847007)
            ·
              refine ⟨13346185909394666393770511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8897457272929777595847007 13346185909394666393770511)
              ·
                refine ⟨20019278864091999590655767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13346185909394666393770511 20019278864091999590655767)
                ·
                  refine ⟨30028918296137999385983651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20019278864091999590655767 30028918296137999385983651)
                  ·
                    refine ⟨45043377444206999078975477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30028918296137999385983651 45043377444206999078975477)
                    ·
                      refine ⟨4222816635394406163653951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45043377444206999078975477 4222816635394406163653951)
                      ·
                        rfl

theorem cell23_8223906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_8223906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223906 prefixEnd_8223906 := by exact prefixLift 8223906
  have htrace : WordTrace (prefixWord ++ tailWord_8223906) baseStart_8223906 baseEnd_8223906 := by
    simpa [prefixWord, tailWord_8223906, baseEnd_8223906] using wordTrace_append hprefix tailTrace_8223906
  have hstable : (prefixWord ++ tailWord_8223906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223906).length < 2 ^ (prefixWord ++ tailWord_8223906).sum := by decide
  have hdescent : baseEnd_8223906 < baseStart_8223906 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223919 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 3]
def baseStart_8223919 : Nat := 118140960795 + 8223919 * 2 ^ 59
def prefixEnd_8223919 : Nat := 4983230072969 + 3 ^ 40 * 8223919 * 2
def baseEnd_8223919 : Nat := 4222823310642914612791391

theorem tailTrace_8223919 : CollatzResearch.WordTrace tailWord_8223919 prefixEnd_8223919 4222823310642914612791391 := by
  unfold tailWord_8223919
  simp only [CollatzResearch.WordTrace]
  refine ⟨299950967893153471389682811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199967311928768980926455207 299950967893153471389682811)
  ·
    refine ⟨449926451839730207084524217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299950967893153471389682811 449926451839730207084524217)
    ·
      refine ⟨337444838879797655313393163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449926451839730207084524217 337444838879797655313393163)
      ·
        refine ⟨506167258319696482970089745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337444838879797655313393163 506167258319696482970089745)
        ·
          refine ⟨379625443739772362227567309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506167258319696482970089745 379625443739772362227567309)
          ·
            refine ⟨142359541402414635835337741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379625443739772362227567309 142359541402414635835337741)
            ·
              refine ⟨53384828025905488438251653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142359541402414635835337741 53384828025905488438251653)
              ·
                refine ⟨10009655254857279082172185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53384828025905488438251653 10009655254857279082172185)
                ·
                  refine ⟨7507241441142959311629139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10009655254857279082172185 7507241441142959311629139)
                  ·
                    refine ⟨11260862161714438967443709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7507241441142959311629139 11260862161714438967443709)
                    ·
                      refine ⟨4222823310642914612791391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11260862161714438967443709 4222823310642914612791391)
                      ·
                        rfl

theorem cell23_8223919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 3].length) (baseStart_8223919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223919 prefixEnd_8223919 := by exact prefixLift 8223919
  have htrace : WordTrace (prefixWord ++ tailWord_8223919) baseStart_8223919 baseEnd_8223919 := by
    simpa [prefixWord, tailWord_8223919, baseEnd_8223919] using wordTrace_append hprefix tailTrace_8223919
  have hstable : (prefixWord ++ tailWord_8223919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223919).length < 2 ^ (prefixWord ++ tailWord_8223919).sum := by decide
  have hdescent : baseEnd_8223919 < baseStart_8223919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223929 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 3, 3, 2]
def baseStart_8223929 : Nat := 118140960795 + 8223929 * 2 ^ 59
def prefixEnd_8223929 : Nat := 4983230072969 + 3 ^ 40 * 8223929 * 2
def baseEnd_8223929 : Nat := 4222828445449459573666345

theorem tailTrace_8223929 : CollatzResearch.WordTrace tailWord_8223929 prefixEnd_8223929 4222828445449459573666345 := by
  unfold tailWord_8223929
  simp only [CollatzResearch.WordTrace]
  refine ⟨299951332623117243097546841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199967555082078162065031227 299951332623117243097546841)
  ·
    refine ⟨224963499467337932323160131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299951332623117243097546841 224963499467337932323160131)
    ·
      refine ⟨337445249201006898484740197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224963499467337932323160131 337445249201006898484740197)
      ·
        refine ⟨63270984225188793465888787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337445249201006898484740197 63270984225188793465888787)
        ·
          refine ⟨94906476337783190198833181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63270984225188793465888787 94906476337783190198833181)
          ·
            refine ⟨35589928626668696324562443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94906476337783190198833181 35589928626668696324562443)
            ·
              refine ⟨53384892940003044486843665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35589928626668696324562443 53384892940003044486843665)
              ·
                refine ⟨40038669705002283365132749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53384892940003044486843665 40038669705002283365132749)
                ·
                  refine ⟨15014501139375856261924781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40038669705002283365132749 15014501139375856261924781)
                  ·
                    refine ⟨5630437927265946098221793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15014501139375856261924781 5630437927265946098221793)
                    ·
                      refine ⟨4222828445449459573666345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630437927265946098221793 4222828445449459573666345)
                      ·
                        rfl

theorem cell23_8223929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_8223929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223929 prefixEnd_8223929 := by exact prefixLift 8223929
  have htrace : WordTrace (prefixWord ++ tailWord_8223929) baseStart_8223929 baseEnd_8223929 := by
    simpa [prefixWord, tailWord_8223929, baseEnd_8223929] using wordTrace_append hprefix tailTrace_8223929
  have hstable : (prefixWord ++ tailWord_8223929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223929).length < 2 ^ (prefixWord ++ tailWord_8223929).sum := by decide
  have hdescent : baseEnd_8223929 < baseStart_8223929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223935 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 1, 8]
def baseStart_8223935 : Nat := 118140960795 + 8223935 * 2 ^ 59
def prefixEnd_8223935 : Nat := 4983230072969 + 3 ^ 40 * 8223935 * 2
def baseEnd_8223935 : Nat := 1407610508777795516730439

theorem tailTrace_8223935 : CollatzResearch.WordTrace tailWord_8223935 prefixEnd_8223935 1407610508777795516730439 := by
  unfold tailWord_8223935
  simp only [CollatzResearch.WordTrace]
  refine ⟨299951551461095506122265259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199967700974063670748176839 299951551461095506122265259)
  ·
    refine ⟨449927327191643259183397889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299951551461095506122265259 449927327191643259183397889)
    ·
      refine ⟨337445495393732444387548417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449927327191643259183397889 337445495393732444387548417)
      ·
        refine ⟨253084121545299333290661313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337445495393732444387548417 253084121545299333290661313)
        ·
          refine ⟨189813091158974499967995985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253084121545299333290661313 189813091158974499967995985)
          ·
            refine ⟨142359818369230874975996989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189813091158974499967995985 142359818369230874975996989)
            ·
              refine ⟨53384931888461578115998871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142359818369230874975996989 53384931888461578115998871)
              ·
                refine ⟨80077397832692367173998307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53384931888461578115998871 80077397832692367173998307)
                ·
                  refine ⟨120116096749038550760997461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80077397832692367173998307 120116096749038550760997461)
                  ·
                    refine ⟨1407610508777795516730439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120116096749038550760997461 1407610508777795516730439)
                    ·
                      rfl

theorem cell23_8223935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_8223935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223935 prefixEnd_8223935 := by exact prefixLift 8223935
  have htrace : WordTrace (prefixWord ++ tailWord_8223935) baseStart_8223935 baseEnd_8223935 := by
    simpa [prefixWord, tailWord_8223935, baseEnd_8223935] using wordTrace_append hprefix tailTrace_8223935
  have hstable : (prefixWord ++ tailWord_8223935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223935).length < 2 ^ (prefixWord ++ tailWord_8223935).sum := by decide
  have hdescent : baseEnd_8223935 < baseStart_8223935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223959 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 1, 4, 2]
def baseStart_8223959 : Nat := 118140960795 + 8223959 * 2 ^ 59
def prefixEnd_8223959 : Nat := 4983230072969 + 3 ^ 40 * 8223959 * 2
def baseEnd_8223959 : Nat := 4222843849869094456291207

theorem tailTrace_8223959 : CollatzResearch.WordTrace tailWord_8223959 prefixEnd_8223959 4222843849869094456291207 := by
  unfold tailWord_8223959
  simp only [CollatzResearch.WordTrace]
  refine ⟨299952426813008558221138931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199968284542005705480759287 299952426813008558221138931)
  ·
    refine ⟨449928640219512837331708397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299952426813008558221138931 449928640219512837331708397)
    ·
      refine ⟨168723240082317313999390649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449928640219512837331708397 168723240082317313999390649)
      ·
        refine ⟨126542430061737985499542987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168723240082317313999390649 126542430061737985499542987)
        ·
          refine ⟨189813645092606978249314481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126542430061737985499542987 189813645092606978249314481)
          ·
            refine ⟨142360233819455233686985861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189813645092606978249314481 142360233819455233686985861)
            ·
              refine ⟨26692543841147856316309849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142360233819455233686985861 26692543841147856316309849)
              ·
                refine ⟨20019407880860892237232387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26692543841147856316309849 20019407880860892237232387)
                ·
                  refine ⟨30029111821291338355848581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20019407880860892237232387 30029111821291338355848581)
                  ·
                    refine ⟨5630458466492125941721609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30029111821291338355848581 5630458466492125941721609)
                    ·
                      refine ⟨4222843849869094456291207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630458466492125941721609 4222843849869094456291207)
                      ·
                        rfl

theorem cell23_8223959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_8223959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223959 prefixEnd_8223959 := by exact prefixLift 8223959
  have htrace : WordTrace (prefixWord ++ tailWord_8223959) baseStart_8223959 baseEnd_8223959 := by
    simpa [prefixWord, tailWord_8223959, baseEnd_8223959] using wordTrace_append hprefix tailTrace_8223959
  have hstable : (prefixWord ++ tailWord_8223959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223959).length < 2 ^ (prefixWord ++ tailWord_8223959).sum := by decide
  have hdescent : baseEnd_8223959 < baseStart_8223959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223972 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_8223972 : Nat := 118140960795 + 8223972 * 2 ^ 59
def prefixEnd_8223972 : Nat := 4983230072969 + 3 ^ 40 * 8223972 * 2
def baseEnd_8223972 : Nat := 4222850525117602905428647

theorem tailTrace_8223972 : CollatzResearch.WordTrace tailWord_8223972 prefixEnd_8223972 4222850525117602905428647 := by
  unfold tailWord_8223972
  simp only [CollatzResearch.WordTrace]
  refine ⟨149976450480980730720681085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199968600641307640960908113 149976450480980730720681085)
  ·
    refine ⟨56241168930367774020255407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149976450480980730720681085 56241168930367774020255407)
    ·
      refine ⟨84361753395551661030383111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56241168930367774020255407 84361753395551661030383111)
      ·
        refine ⟨126542630093327491545574667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84361753395551661030383111 126542630093327491545574667)
        ·
          refine ⟨189813945139991237318362001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126542630093327491545574667 189813945139991237318362001)
          ·
            refine ⟨142360458854993427988771501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189813945139991237318362001 142360458854993427988771501)
            ·
              refine ⟨53385172070622535495789313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142360458854993427988771501 53385172070622535495789313)
              ·
                refine ⟨40038879052966901621841985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53385172070622535495789313 40038879052966901621841985)
                ·
                  refine ⟨30029159289725176216381489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40038879052966901621841985 30029159289725176216381489)
                  ·
                    refine ⟨22521869467293882162286117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30029159289725176216381489 22521869467293882162286117)
                    ·
                      refine ⟨4222850525117602905428647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22521869467293882162286117 4222850525117602905428647)
                      ·
                        rfl

theorem cell23_8223972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_8223972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223972 prefixEnd_8223972 := by exact prefixLift 8223972
  have htrace : WordTrace (prefixWord ++ tailWord_8223972) baseStart_8223972 baseEnd_8223972 := by
    simpa [prefixWord, tailWord_8223972, baseEnd_8223972] using wordTrace_append hprefix tailTrace_8223972
  have hstable : (prefixWord ++ tailWord_8223972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223972).length < 2 ^ (prefixWord ++ tailWord_8223972).sum := by decide
  have hdescent : baseEnd_8223972 < baseStart_8223972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223976 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_8223976 : Nat := 118140960795 + 8223976 * 2 ^ 59
def prefixEnd_8223976 : Nat := 4983230072969 + 3 ^ 40 * 8223976 * 2
def baseEnd_8223976 : Nat := 4222852579040220889778629

theorem tailTrace_8223976 : CollatzResearch.WordTrace tailWord_8223976 prefixEnd_8223976 4222852579040220889778629 := by
  unfold tailWord_8223976
  simp only [CollatzResearch.WordTrace]
  refine ⟨149976523426973485062253891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199968697902631313416338521 149976523426973485062253891)
  ·
    refine ⟨224964785140460227593380837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149976523426973485062253891 224964785140460227593380837)
    ·
      refine ⟨42180897213836292673758907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224964785140460227593380837 42180897213836292673758907)
      ·
        refine ⟨63271345820754439010638361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42180897213836292673758907 63271345820754439010638361)
        ·
          refine ⟨47453509365565829257978771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63271345820754439010638361 47453509365565829257978771)
          ·
            refine ⟨71180264048348743886968157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47453509365565829257978771 71180264048348743886968157)
            ·
              refine ⟨26692599018130778957613059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71180264048348743886968157 26692599018130778957613059)
              ·
                refine ⟨40038898527196168436419589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26692599018130778957613059 40038898527196168436419589)
                ·
                  refine ⟨7507293473849281581828673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40038898527196168436419589 7507293473849281581828673)
                  ·
                    refine ⟨5630470105386961186371505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7507293473849281581828673 5630470105386961186371505)
                    ·
                      refine ⟨4222852579040220889778629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630470105386961186371505 4222852579040220889778629)
                      ·
                        rfl

theorem cell23_8223976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_8223976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223976 prefixEnd_8223976 := by exact prefixLift 8223976
  have htrace : WordTrace (prefixWord ++ tailWord_8223976) baseStart_8223976 baseEnd_8223976 := by
    simpa [prefixWord, tailWord_8223976, baseEnd_8223976] using wordTrace_append hprefix tailTrace_8223976
  have hstable : (prefixWord ++ tailWord_8223976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223976).length < 2 ^ (prefixWord ++ tailWord_8223976).sum := by decide
  have hdescent : baseEnd_8223976 < baseStart_8223976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223982 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_8223982 : Nat := 118140960795 + 8223982 * 2 ^ 59
def prefixEnd_8223982 : Nat := 4983230072969 + 3 ^ 40 * 8223982 * 2
def baseEnd_8223982 : Nat := 469206184436016429589289

theorem tailTrace_8223982 : CollatzResearch.WordTrace tailWord_8223982 prefixEnd_8223982 469206184436016429589289 := by
  unfold tailWord_8223982
  simp only [CollatzResearch.WordTrace]
  refine ⟨37494158211490654143653275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199968843794616822099484133 37494158211490654143653275)
  ·
    refine ⟨56241237317235981215479913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37494158211490654143653275 56241237317235981215479913)
    ·
      refine ⟨42180927987926985911609935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56241237317235981215479913 42180927987926985911609935)
      ·
        refine ⟨63271391981890478867414903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42180927987926985911609935 63271391981890478867414903)
        ·
          refine ⟨94907087972835718301122355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63271391981890478867414903 94907087972835718301122355)
          ·
            refine ⟨142360631959253577451683533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94907087972835718301122355 142360631959253577451683533)
            ·
              refine ⟨53385236984720091544381325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142360631959253577451683533 53385236984720091544381325)
              ·
                refine ⟨20019463869270034329142997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53385236984720091544381325 20019463869270034329142997)
                ·
                  refine ⟨469206184436016429589289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20019463869270034329142997 469206184436016429589289)
                  ·
                    rfl

theorem cell23_8223982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_8223982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223982 prefixEnd_8223982 := by exact prefixLift 8223982
  have htrace : WordTrace (prefixWord ++ tailWord_8223982) baseStart_8223982 baseEnd_8223982 := by
    simpa [prefixWord, tailWord_8223982, baseEnd_8223982] using wordTrace_append hprefix tailTrace_8223982
  have hstable : (prefixWord ++ tailWord_8223982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223982).length < 2 ^ (prefixWord ++ tailWord_8223982).sum := by decide
  have hdescent : baseEnd_8223982 < baseStart_8223982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223993 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 2, 2, 2]
def baseStart_8223993 : Nat := 118140960795 + 8223993 * 2 ^ 59
def prefixEnd_8223993 : Nat := 4983230072969 + 3 ^ 40 * 8223993 * 2
def baseEnd_8223993 : Nat := 4222861308211347323266051

theorem tailTrace_8223993 : CollatzResearch.WordTrace tailWord_8223993 prefixEnd_8223993 4222861308211347323266051 := by
  unfold tailWord_8223993
  simp only [CollatzResearch.WordTrace]
  refine ⟨299953666894885382027876633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199969111263256921351917755 299953666894885382027876633)
  ·
    refine ⟨224965250171164036520907475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299953666894885382027876633 224965250171164036520907475)
    ·
      refine ⟨337447875256746054781361213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224965250171164036520907475 337447875256746054781361213)
      ·
        refine ⟨126542953221279770543010455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337447875256746054781361213 126542953221279770543010455)
        ·
          refine ⟨189814429831919655814515683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126542953221279770543010455 189814429831919655814515683)
          ·
            refine ⟨284721644747879483721773525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189814429831919655814515683 284721644747879483721773525)
            ·
              refine ⟨6673163548778425399729067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 284721644747879483721773525 6673163548778425399729067)
              ·
                refine ⟨10009745323167638099593601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673163548778425399729067 10009745323167638099593601)
                ·
                  refine ⟨7507308992375728574695201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10009745323167638099593601 7507308992375728574695201)
                  ·
                    refine ⟨5630481744281796431021401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7507308992375728574695201 5630481744281796431021401)
                    ·
                      refine ⟨4222861308211347323266051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630481744281796431021401 4222861308211347323266051)
                      ·
                        rfl

theorem cell23_8223993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_8223993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223993 prefixEnd_8223993 := by exact prefixLift 8223993
  have htrace : WordTrace (prefixWord ++ tailWord_8223993) baseStart_8223993 baseEnd_8223993 := by
    simpa [prefixWord, tailWord_8223993, baseEnd_8223993] using wordTrace_append hprefix tailTrace_8223993
  have hstable : (prefixWord ++ tailWord_8223993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223993).length < 2 ^ (prefixWord ++ tailWord_8223993).sum := by decide
  have hdescent : baseEnd_8223993 < baseStart_8223993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224012 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_8224012 : Nat := 118140960795 + 8224012 * 2 ^ 59
def prefixEnd_8224012 : Nat := 4983230072969 + 3 ^ 40 * 8224012 * 2
def baseEnd_8224012 : Nat := 1407623688114594249642821

theorem tailTrace_8224012 : CollatzResearch.WordTrace tailWord_8224012 prefixEnd_8224012 1407623688114594249642821 := by
  unfold tailWord_8224012
  simp only [CollatzResearch.WordTrace]
  refine ⟨149977179940908274136409145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199969573254544365515212193 149977179940908274136409145)
  ·
    refine ⟨112482884955681205602306859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149977179940908274136409145 112482884955681205602306859)
    ·
      refine ⟨168724327433521808403460289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112482884955681205602306859 168724327433521808403460289)
      ·
        refine ⟨126543245575141356302595217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168724327433521808403460289 126543245575141356302595217)
        ·
          refine ⟨94907434181356017226946413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126543245575141356302595217 94907434181356017226946413)
          ·
            refine ⟨35590287818008506460104905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94907434181356017226946413 35590287818008506460104905)
            ·
              refine ⟨26692715863506379845078679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35590287818008506460104905 26692715863506379845078679)
              ·
                refine ⟨40039073795259569767618019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26692715863506379845078679 40039073795259569767618019)
                ·
                  refine ⟨60058610692889354651427029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40039073795259569767618019 60058610692889354651427029)
                  ·
                    refine ⟨1407623688114594249642821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60058610692889354651427029 1407623688114594249642821)
                    ·
                      rfl

theorem cell23_8224012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_8224012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224012 prefixEnd_8224012 := by exact prefixLift 8224012
  have htrace : WordTrace (prefixWord ++ tailWord_8224012) baseStart_8224012 baseEnd_8224012 := by
    simpa [prefixWord, tailWord_8224012, baseEnd_8224012] using wordTrace_append hprefix tailTrace_8224012
  have hstable : (prefixWord ++ tailWord_8224012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224012).length < 2 ^ (prefixWord ++ tailWord_8224012).sum := by decide
  have hdescent : baseEnd_8224012 < baseStart_8224012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224029 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_8224029 : Nat := 118140960795 + 8224029 * 2 ^ 59
def prefixEnd_8224029 : Nat := 4983230072969 + 3 ^ 40 * 8224029 * 2
def baseEnd_8224029 : Nat := 1407626597838303060805295

theorem tailTrace_8224029 : CollatzResearch.WordTrace tailWord_8224029 prefixEnd_8224029 1407626597838303060805295 := by
  unfold tailWord_8224029
  simp only [CollatzResearch.WordTrace]
  refine ⟨299954979922754960176187141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199969986615169973450791427 299954979922754960176187141)
  ·
    refine ⟨56241558735516555033035089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299954979922754960176187141 56241558735516555033035089)
    ·
      refine ⟨42181169051637416274776317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56241558735516555033035089 42181169051637416274776317)
      ·
        refine ⟨15817938394364031103041119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42181169051637416274776317 15817938394364031103041119)
        ·
          refine ⟨23726907591546046654561679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15817938394364031103041119 23726907591546046654561679)
          ·
            refine ⟨35590361387319069981842519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23726907591546046654561679 35590361387319069981842519)
            ·
              refine ⟨53385542080978604972763779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35590361387319069981842519 53385542080978604972763779)
              ·
                refine ⟨80078313121467907459145669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53385542080978604972763779 80078313121467907459145669)
                ·
                  refine ⟨15014683710275232648589813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80078313121467907459145669 15014683710275232648589813)
                  ·
                    refine ⟨1407626597838303060805295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15014683710275232648589813 1407626597838303060805295)
                    ·
                      rfl

theorem cell23_8224029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_8224029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224029 prefixEnd_8224029 := by exact prefixLift 8224029
  have htrace : WordTrace (prefixWord ++ tailWord_8224029) baseStart_8224029 baseEnd_8224029 := by
    simpa [prefixWord, tailWord_8224029, baseEnd_8224029] using wordTrace_append hprefix tailTrace_8224029
  have hstable : (prefixWord ++ tailWord_8224029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224029).length < 2 ^ (prefixWord ++ tailWord_8224029).sum := by decide
  have hdescent : baseEnd_8224029 < baseStart_8224029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224112 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_8224112 : Nat := 118140960795 + 8224112 * 2 ^ 59
def prefixEnd_8224112 : Nat := 4983230072969 + 3 ^ 40 * 8224112 * 2
def baseEnd_8224112 : Nat := 4222922412409232357678003

theorem tailTrace_8224112 : CollatzResearch.WordTrace tailWord_8224112 prefixEnd_8224112 4222922412409232357678003 := by
  unfold tailWord_8224112
  simp only [CollatzResearch.WordTrace]
  refine ⟨149979003590727132675729295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199972004787636176900972393 149979003590727132675729295)
  ·
    refine ⟨224968505386090699013593943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149979003590727132675729295 224968505386090699013593943)
    ·
      refine ⟨337452758079136048520390915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224968505386090699013593943 337452758079136048520390915)
      ·
        refine ⟨506179137118704072780586373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337452758079136048520390915 506179137118704072780586373)
        ·
          refine ⟨94908588209757013646359945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 506179137118704072780586373 94908588209757013646359945)
          ·
            refine ⟨71181441157317760234769959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94908588209757013646359945 71181441157317760234769959)
            ·
              refine ⟨106772161735976640352154939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71181441157317760234769959 106772161735976640352154939)
              ·
                refine ⟨160158242603964960528232409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106772161735976640352154939 160158242603964960528232409)
                ·
                  refine ⟨120118681952973720396174307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160158242603964960528232409 120118681952973720396174307)
                  ·
                    refine ⟨180178022929460580594261461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120118681952973720396174307 180178022929460580594261461)
                    ·
                      refine ⟨4222922412409232357678003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180178022929460580594261461 4222922412409232357678003)
                      ·
                        rfl

theorem cell23_8224112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_8224112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224112 prefixEnd_8224112 := by exact prefixLift 8224112
  have htrace : WordTrace (prefixWord ++ tailWord_8224112) baseStart_8224112 baseEnd_8224112 := by
    simpa [prefixWord, tailWord_8224112, baseEnd_8224112] using wordTrace_append hprefix tailTrace_8224112
  have hstable : (prefixWord ++ tailWord_8224112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224112).length < 2 ^ (prefixWord ++ tailWord_8224112).sum := by decide
  have hdescent : baseEnd_8224112 < baseStart_8224112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224119 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 1, 5]
def baseStart_8224119 : Nat := 118140960795 + 8224119 * 2 ^ 59
def prefixEnd_8224119 : Nat := 4983230072969 + 3 ^ 40 * 8224119 * 2
def baseEnd_8224119 : Nat := 1407642002257937943430157

theorem tailTrace_8224119 : CollatzResearch.WordTrace tailWord_8224119 prefixEnd_8224119 1407642002257937943430157 := by
  unfold tailWord_8224119
  simp only [CollatzResearch.WordTrace]
  refine ⟨299958262492428905546963411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199972174994952603697975607 299958262492428905546963411)
  ·
    refine ⟨449937393738643358320445117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299958262492428905546963411 449937393738643358320445117)
    ·
      refine ⟨168726522651991259370166919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449937393738643358320445117 168726522651991259370166919)
      ·
        refine ⟨253089783977986889055250379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168726522651991259370166919 253089783977986889055250379)
        ·
          refine ⟨379634675966980333582875569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253089783977986889055250379 379634675966980333582875569)
          ·
            refine ⟨284726006975235250187156677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379634675966980333582875569 284726006975235250187156677)
            ·
              refine ⟨53386126307856609410091877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284726006975235250187156677 53386126307856609410091877)
              ·
                refine ⟨10009898682723114264392227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53386126307856609410091877 10009898682723114264392227)
                ·
                  refine ⟨15014848024084671396588341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10009898682723114264392227 15014848024084671396588341)
                  ·
                    refine ⟨1407642002257937943430157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15014848024084671396588341 1407642002257937943430157)
                    ·
                      rfl

theorem cell23_8224119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_8224119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224119 prefixEnd_8224119 := by exact prefixLift 8224119
  have htrace : WordTrace (prefixWord ++ tailWord_8224119) baseStart_8224119 baseEnd_8224119 := by
    simpa [prefixWord, tailWord_8224119, baseEnd_8224119] using wordTrace_append hprefix tailTrace_8224119
  have hstable : (prefixWord ++ tailWord_8224119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224119).length < 2 ^ (prefixWord ++ tailWord_8224119).sum := by decide
  have hdescent : baseEnd_8224119 < baseStart_8224119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224133 : List Nat := [1, 3, 1, 1, 3, 1, 3, 5, 1, 1, 3]
def baseStart_8224133 : Nat := 118140960795 + 8224133 * 2 ^ 59
def prefixEnd_8224133 : Nat := 4983230072969 + 3 ^ 40 * 8224133 * 2
def baseEnd_8224133 : Nat := 4222933195502976775515407

theorem tailTrace_8224133 : CollatzResearch.WordTrace tailWord_8224133 prefixEnd_8224133 4222933195502976775515407 := by
  unfold tailWord_8224133
  simp only [CollatzResearch.WordTrace]
  refine ⟨299958773114378185937973053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199972515409585457291982035 299958773114378185937973053)
  ·
    refine ⟨112484539917891819726739895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299958773114378185937973053 112484539917891819726739895)
    ·
      refine ⟨168726809876837729590109843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112484539917891819726739895 168726809876837729590109843)
      ·
        refine ⟨253090214815256594385164765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168726809876837729590109843 253090214815256594385164765)
        ·
          refine ⟨94908830555721222894436787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253090214815256594385164765 94908830555721222894436787)
          ·
            refine ⟨142363245833581834341655181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94908830555721222894436787 142363245833581834341655181)
            ·
              refine ⟨53386217187593187878120693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142363245833581834341655181 53386217187593187878120693)
              ·
                refine ⟨5004957861336861363573815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53386217187593187878120693 5004957861336861363573815)
                ·
                  refine ⟨7507436792005292045360723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5004957861336861363573815 7507436792005292045360723)
                  ·
                    refine ⟨11261155188007938068041085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7507436792005292045360723 11261155188007938068041085)
                    ·
                      refine ⟨4222933195502976775515407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11261155188007938068041085 4222933195502976775515407)
                      ·
                        rfl

theorem cell23_8224133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 1, 3].length) (baseStart_8224133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224133 prefixEnd_8224133 := by exact prefixLift 8224133
  have htrace : WordTrace (prefixWord ++ tailWord_8224133) baseStart_8224133 baseEnd_8224133 := by
    simpa [prefixWord, tailWord_8224133, baseEnd_8224133] using wordTrace_append hprefix tailTrace_8224133
  have hstable : (prefixWord ++ tailWord_8224133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224133).length < 2 ^ (prefixWord ++ tailWord_8224133).sum := by decide
  have hdescent : baseEnd_8224133 < baseStart_8224133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224136 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 1, 5]
def baseStart_8224136 : Nat := 118140960795 + 8224136 * 2 ^ 59
def prefixEnd_8224136 : Nat := 4983230072969 + 3 ^ 40 * 8224136 * 2
def baseEnd_8224136 : Nat := 1407644911981646754592631

theorem tailTrace_8224136 : CollatzResearch.WordTrace tailWord_8224136 prefixEnd_8224136 1407644911981646754592631 := by
  unfold tailWord_8224136
  simp only [CollatzResearch.WordTrace]
  refine ⟨149979441266683658725166131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199972588355578211633554841 149979441266683658725166131)
  ·
    refine ⟨224969161900025488087749197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149979441266683658725166131 224969161900025488087749197)
    ·
      refine ⟨84363435712509558032905949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224969161900025488087749197 84363435712509558032905949)
      ·
        refine ⟨31636288392191084262339731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84363435712509558032905949 31636288392191084262339731)
        ·
          refine ⟨47454432588286626393509597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31636288392191084262339731 47454432588286626393509597)
          ·
            refine ⟨17795412220607484897566099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47454432588286626393509597 17795412220607484897566099)
            ·
              refine ⟨26693118330911227346349149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17795412220607484897566099 26693118330911227346349149)
              ·
                refine ⟨10009919374091710254880931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26693118330911227346349149 10009919374091710254880931)
                ·
                  refine ⟨15014879061137565382321397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10009919374091710254880931 15014879061137565382321397)
                  ·
                    refine ⟨1407644911981646754592631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15014879061137565382321397 1407644911981646754592631)
                    ·
                      rfl

theorem cell23_8224136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_8224136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224136 prefixEnd_8224136 := by exact prefixLift 8224136
  have htrace : WordTrace (prefixWord ++ tailWord_8224136) baseStart_8224136 baseEnd_8224136 := by
    simpa [prefixWord, tailWord_8224136, baseEnd_8224136] using wordTrace_append hprefix tailTrace_8224136
  have hstable : (prefixWord ++ tailWord_8224136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224136).length < 2 ^ (prefixWord ++ tailWord_8224136).sum := by decide
  have hdescent : baseEnd_8224136 < baseStart_8224136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224159 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_8224159 : Nat := 118140960795 + 8224159 * 2 ^ 59
def prefixEnd_8224159 : Nat := 4983230072969 + 3 ^ 40 * 8224159 * 2
def baseEnd_8224159 : Nat := 4222946545999993673790287

theorem tailTrace_8224159 : CollatzResearch.WordTrace tailWord_8224159 prefixEnd_8224159 4222946545999993673790287 := by
  unfold tailWord_8224159
  simp only [CollatzResearch.WordTrace]
  refine ⟨299959721412283992378419531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199973147608189328252279687 299959721412283992378419531)
  ·
    refine ⟨449939582118425988567629297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299959721412283992378419531 449939582118425988567629297)
    ·
      refine ⟨337454686588819491425721973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449939582118425988567629297 337454686588819491425721973)
      ·
        refine ⟨31636376867701827321161435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337454686588819491425721973 31636376867701827321161435)
        ·
          refine ⟨47454565301552740981742153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31636376867701827321161435 47454565301552740981742153)
          ·
            refine ⟨35590923976164555736306615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47454565301552740981742153 35590923976164555736306615)
            ·
              refine ⟨53386385964246833604459923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35590923976164555736306615 53386385964246833604459923)
              ·
                refine ⟨80079578946370250406689885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53386385964246833604459923 80079578946370250406689885)
                ·
                  refine ⟨30029842104888843902508707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80079578946370250406689885 30029842104888843902508707)
                  ·
                    refine ⟨45044763157333265853763061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30029842104888843902508707 45044763157333265853763061)
                    ·
                      refine ⟨4222946545999993673790287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45044763157333265853763061 4222946545999993673790287)
                      ·
                        rfl

theorem cell23_8224159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_8224159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224159 prefixEnd_8224159 := by exact prefixLift 8224159
  have htrace : WordTrace (prefixWord ++ tailWord_8224159) baseStart_8224159 baseEnd_8224159 := by
    simpa [prefixWord, tailWord_8224159, baseEnd_8224159] using wordTrace_append hprefix tailTrace_8224159
  have hstable : (prefixWord ++ tailWord_8224159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224159).length < 2 ^ (prefixWord ++ tailWord_8224159).sum := by decide
  have hdescent : baseEnd_8224159 < baseStart_8224159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224173 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_8224173 : Nat := 118140960795 + 8224173 * 2 ^ 59
def prefixEnd_8224173 : Nat := 4983230072969 + 3 ^ 40 * 8224173 * 2
def baseEnd_8224173 : Nat := 4222953734729156619015223

theorem tailTrace_8224173 : CollatzResearch.WordTrace tailWord_8224173 prefixEnd_8224173 4222953734729156619015223 := by
  unfold tailWord_8224173
  simp only [CollatzResearch.WordTrace]
  refine ⟨299960232034233272769429173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199973488022822181846286115 299960232034233272769429173)
  ·
    refine ⟨28121271753209369322133985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299960232034233272769429173 28121271753209369322133985)
    ·
      refine ⟨21090953814907026991600489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28121271753209369322133985 21090953814907026991600489)
      ·
        refine ⟨15818215361180270243700367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21090953814907026991600489 15818215361180270243700367)
        ·
          refine ⟨23727323041770405365550551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15818215361180270243700367 23727323041770405365550551)
          ·
            refine ⟨35590984562655608048325827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23727323041770405365550551 35590984562655608048325827)
            ·
              refine ⟨53386476843983412072488741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35590984562655608048325827 53386476843983412072488741)
              ·
                refine ⟨10009964408246889763591639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53386476843983412072488741 10009964408246889763591639)
                ·
                  refine ⟨15014946612370334645387459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10009964408246889763591639 15014946612370334645387459)
                  ·
                    refine ⟨22522419918555501968081189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15014946612370334645387459 22522419918555501968081189)
                    ·
                      refine ⟨4222953734729156619015223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22522419918555501968081189 4222953734729156619015223)
                      ·
                        rfl

theorem cell23_8224173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_8224173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224173 prefixEnd_8224173 := by exact prefixLift 8224173
  have htrace : WordTrace (prefixWord ++ tailWord_8224173) baseStart_8224173 baseEnd_8224173 := by
    simpa [prefixWord, tailWord_8224173, baseEnd_8224173] using wordTrace_append hprefix tailTrace_8224173
  have hstable : (prefixWord ++ tailWord_8224173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224173).length < 2 ^ (prefixWord ++ tailWord_8224173).sum := by decide
  have hdescent : baseEnd_8224173 < baseStart_8224173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224196 : List Nat := [2, 3, 3, 2, 1, 3, 9]
def baseStart_8224196 : Nat := 118140960795 + 8224196 * 2 ^ 59
def prefixEnd_8224196 : Nat := 4983230072969 + 3 ^ 40 * 8224196 * 2
def baseEnd_8224196 : Nat := 52135377096101358383057

theorem tailTrace_8224196 : CollatzResearch.WordTrace tailWord_8224196 prefixEnd_8224196 52135377096101358383057 := by
  unfold tailWord_8224196
  simp only [CollatzResearch.WordTrace]
  refine ⟨149980535456574973848758221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199974047275433298465010961 149980535456574973848758221)
  ·
    refine ⟨56242700796215615193284333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149980535456574973848758221 56242700796215615193284333)
    ·
      refine ⟨21091012798580855697481625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56242700796215615193284333 21091012798580855697481625)
      ·
        refine ⟨15818259598935641773111219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21091012798580855697481625 15818259598935641773111219)
        ·
          refine ⟨23727389398403462659666829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15818259598935641773111219 23727389398403462659666829)
          ·
            refine ⟨8897771024401298497375061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23727389398403462659666829 8897771024401298497375061)
            ·
              refine ⟨52135377096101358383057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8897771024401298497375061 52135377096101358383057)
              ·
                rfl

theorem cell23_8224196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 9].length) (baseStart_8224196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224196 prefixEnd_8224196 := by exact prefixLift 8224196
  have htrace : WordTrace (prefixWord ++ tailWord_8224196) baseStart_8224196 baseEnd_8224196 := by
    simpa [prefixWord, tailWord_8224196, baseEnd_8224196] using wordTrace_append hprefix tailTrace_8224196
  have hstable : (prefixWord ++ tailWord_8224196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224196).length < 2 ^ (prefixWord ++ tailWord_8224196).sum := by decide
  have hdescent : baseEnd_8224196 < baseStart_8224196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224223 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 3]
def baseStart_8224223 : Nat := 118140960795 + 8224223 * 2 ^ 59
def prefixEnd_8224223 : Nat := 4983230072969 + 3 ^ 40 * 8224223 * 2
def baseEnd_8224223 : Nat := 4222979408761881423389993

theorem tailTrace_8224223 : CollatzResearch.WordTrace tailWord_8224223 prefixEnd_8224223 4222979408761881423389993 := by
  unfold tailWord_8224223
  simp only [CollatzResearch.WordTrace]
  refine ⟨299962055684052131308749323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199974703789368087539166215 299962055684052131308749323)
  ·
    refine ⟨449943083526078196963123985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299962055684052131308749323 449943083526078196963123985)
    ·
      refine ⟨337457312644558647722342989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449943083526078196963123985 337457312644558647722342989)
      ·
        refine ⟨126546492241709492895878621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337457312644558647722342989 126546492241709492895878621)
        ·
          refine ⟨47454934590641059835954483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126546492241709492895878621 47454934590641059835954483)
          ·
            refine ⟨71182401885961589753931725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47454934590641059835954483 71182401885961589753931725)
            ·
              refine ⟨26693400707235596157724397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71182401885961589753931725 26693400707235596157724397)
              ·
                refine ⟨10010025265213348559146649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26693400707235596157724397 10010025265213348559146649)
                ·
                  refine ⟨7507518948910011419359987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10010025265213348559146649 7507518948910011419359987)
                  ·
                    refine ⟨11261278423365017129039981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7507518948910011419359987 11261278423365017129039981)
                    ·
                      refine ⟨4222979408761881423389993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11261278423365017129039981 4222979408761881423389993)
                      ·
                        rfl

theorem cell23_8224223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_8224223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224223 prefixEnd_8224223 := by exact prefixLift 8224223
  have htrace : WordTrace (prefixWord ++ tailWord_8224223) baseStart_8224223 baseEnd_8224223 := by
    simpa [prefixWord, tailWord_8224223, baseEnd_8224223] using wordTrace_append hprefix tailTrace_8224223
  have hstable : (prefixWord ++ tailWord_8224223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224223).length < 2 ^ (prefixWord ++ tailWord_8224223).sum := by decide
  have hdescent : baseEnd_8224223 < baseStart_8224223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224250 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2]
def baseStart_8224250 : Nat := 118140960795 + 8224250 * 2 ^ 59
def prefixEnd_8224250 : Nat := 4983230072969 + 3 ^ 40 * 8224250 * 2
def baseEnd_8224250 : Nat := 4222993272739552817752369

theorem tailTrace_8224250 : CollatzResearch.WordTrace tailWord_8224250 prefixEnd_8224250 4222993272739552817752369 := by
  unfold tailWord_8224250
  simp only [CollatzResearch.WordTrace]
  refine ⟨74990760113738578729995551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199975360303302876613321469 74990760113738578729995551)
  ·
    refine ⟨112486140170607868094993327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74990760113738578729995551 112486140170607868094993327)
    ·
      refine ⟨168729210255911802142489991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112486140170607868094993327 168729210255911802142489991)
      ·
        refine ⟨253093815383867703213734987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168729210255911802142489991 253093815383867703213734987)
        ·
          refine ⟨379640723075801554820602481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253093815383867703213734987 379640723075801554820602481)
          ·
            refine ⟨284730542306851166115451861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379640723075801554820602481 284730542306851166115451861)
            ·
              refine ⟨6673372085316824205830903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 284730542306851166115451861 6673372085316824205830903)
              ·
                refine ⟨10010058127975236308746355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673372085316824205830903 10010058127975236308746355)
                ·
                  refine ⟨15015087191962854463119533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10010058127975236308746355 15015087191962854463119533)
                  ·
                    refine ⟨5630657696986070423669825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15015087191962854463119533 5630657696986070423669825)
                    ·
                      refine ⟨4222993272739552817752369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630657696986070423669825 4222993272739552817752369)
                      ·
                        rfl

theorem cell23_8224250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_8224250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224250 prefixEnd_8224250 := by exact prefixLift 8224250
  have htrace : WordTrace (prefixWord ++ tailWord_8224250) baseStart_8224250 baseEnd_8224250 := by
    simpa [prefixWord, tailWord_8224250, baseEnd_8224250] using wordTrace_append hprefix tailTrace_8224250
  have hstable : (prefixWord ++ tailWord_8224250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224250).length < 2 ^ (prefixWord ++ tailWord_8224250).sum := by decide
  have hdescent : baseEnd_8224250 < baseStart_8224250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224266 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_8224266 : Nat := 118140960795 + 8224266 * 2 ^ 59
def prefixEnd_8224266 : Nat := 4983230072969 + 3 ^ 40 * 8224266 * 2
def baseEnd_8224266 : Nat := 4223001488430024755152295

theorem tailTrace_8224266 : CollatzResearch.WordTrace tailWord_8224266 prefixEnd_8224266 4223001488430024755152295 := by
  unfold tailWord_8224266
  simp only [CollatzResearch.WordTrace]
  refine ⟨74990906005724087413141163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199975749348597566435043101 74990906005724087413141163)
  ·
    refine ⟨112486359008586131119711745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74990906005724087413141163 112486359008586131119711745)
    ·
      refine ⟨84364769256439598339783809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112486359008586131119711745 84364769256439598339783809)
      ·
        refine ⟨63273576942329698754837857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84364769256439598339783809 63273576942329698754837857)
        ·
          refine ⟨47455182706747274066128393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63273576942329698754837857 47455182706747274066128393)
          ·
            refine ⟨35591387030060455549596295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47455182706747274066128393 35591387030060455549596295)
            ·
              refine ⟨53387080545090683324394443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35591387030060455549596295 53387080545090683324394443)
              ·
                refine ⟨80080620817636024986591665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53387080545090683324394443 80080620817636024986591665)
                ·
                  refine ⟨60060465613227018739943749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80080620817636024986591665 60060465613227018739943749)
                  ·
                    refine ⟨11261337302480066013739453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60060465613227018739943749 11261337302480066013739453)
                    ·
                      refine ⟨4223001488430024755152295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11261337302480066013739453 4223001488430024755152295)
                      ·
                        rfl

theorem cell23_8224266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_8224266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224266 prefixEnd_8224266 := by exact prefixLift 8224266
  have htrace : WordTrace (prefixWord ++ tailWord_8224266) baseStart_8224266 baseEnd_8224266 := by
    simpa [prefixWord, tailWord_8224266, baseEnd_8224266] using wordTrace_append hprefix tailTrace_8224266
  have hstable : (prefixWord ++ tailWord_8224266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224266).length < 2 ^ (prefixWord ++ tailWord_8224266).sum := by decide
  have hdescent : baseEnd_8224266 < baseStart_8224266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224280 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 1, 4, 2]
def baseStart_8224280 : Nat := 118140960795 + 8224280 * 2 ^ 59
def prefixEnd_8224280 : Nat := 4983230072969 + 3 ^ 40 * 8224280 * 2
def baseEnd_8224280 : Nat := 4223008677159187700377231

theorem tailTrace_8224280 : CollatzResearch.WordTrace tailWord_8224280 prefixEnd_8224280 4223008677159187700377231 := by
  unfold tailWord_8224280
  simp only [CollatzResearch.WordTrace]
  refine ⟨149982067322422815021787147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199976089763230420029049529 149982067322422815021787147)
  ·
    refine ⟨224973100983634222532680721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149982067322422815021787147 224973100983634222532680721)
    ·
      refine ⟨168729825737725666899510541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224973100983634222532680721 168729825737725666899510541)
      ·
        refine ⟨63273684651647125087316453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168729825737725666899510541 63273684651647125087316453)
        ·
          refine ⟨11863815872183835953871835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63273684651647125087316453 11863815872183835953871835)
          ·
            refine ⟨17795723808275753930807753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11863815872183835953871835 17795723808275753930807753)
            ·
              refine ⟨13346792856206815448105815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17795723808275753930807753 13346792856206815448105815)
              ·
                refine ⟨20020189284310223172158723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13346792856206815448105815 20020189284310223172158723)
                ·
                  refine ⟨30030283926465334758238085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20020189284310223172158723 30030283926465334758238085)
                  ·
                    refine ⟨5630678236212250267169641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30030283926465334758238085 5630678236212250267169641)
                    ·
                      refine ⟨4223008677159187700377231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630678236212250267169641 4223008677159187700377231)
                      ·
                        rfl

theorem cell23_8224280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_8224280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224280 prefixEnd_8224280 := by exact prefixLift 8224280
  have htrace : WordTrace (prefixWord ++ tailWord_8224280) baseStart_8224280 baseEnd_8224280 := by
    simpa [prefixWord, tailWord_8224280, baseEnd_8224280] using wordTrace_append hprefix tailTrace_8224280
  have hstable : (prefixWord ++ tailWord_8224280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224280).length < 2 ^ (prefixWord ++ tailWord_8224280).sum := by decide
  have hdescent : baseEnd_8224280 < baseStart_8224280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224339 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 5]
def baseStart_8224339 : Nat := 118140960795 + 8224339 * 2 ^ 59
def prefixEnd_8224339 : Nat := 4983230072969 + 3 ^ 40 * 8224339 * 2
def baseEnd_8224339 : Nat := 4223038972517802969539459

theorem tailTrace_8224339 : CollatzResearch.WordTrace tailWord_8224339 prefixEnd_8224339 4223038972517802969539459 := by
  unfold tailWord_8224339
  simp only [CollatzResearch.WordTrace]
  refine ⟨299966286551631883119972071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199977524367754588746648047 299966286551631883119972071)
  ·
    refine ⟨449949429827447824679958107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299966286551631883119972071 449949429827447824679958107)
    ·
      refine ⟨674924144741171737019937161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449949429827447824679958107 674924144741171737019937161)
      ·
        refine ⟨506193108555878802764952871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674924144741171737019937161 506193108555878802764952871)
        ·
          refine ⟨759289662833818204147429307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506193108555878802764952871 759289662833818204147429307)
          ·
            refine ⟨1138934494250727306221143961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759289662833818204147429307 1138934494250727306221143961)
            ·
              refine ⟨854200870688045479665857971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138934494250727306221143961 854200870688045479665857971)
              ·
                refine ⟨1281301306032068219498786957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854200870688045479665857971 1281301306032068219498786957)
                ·
                  refine ⟨480487989762025582312045109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1281301306032068219498786957 480487989762025582312045109)
                  ·
                    refine ⟨45045749040189898341754229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 480487989762025582312045109 45045749040189898341754229)
                    ·
                      refine ⟨4223038972517802969539459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45045749040189898341754229 4223038972517802969539459)
                      ·
                        rfl

theorem cell23_8224339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_8224339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224339 prefixEnd_8224339 := by exact prefixLift 8224339
  have htrace : WordTrace (prefixWord ++ tailWord_8224339) baseStart_8224339 baseEnd_8224339 := by
    simpa [prefixWord, tailWord_8224339, baseEnd_8224339] using wordTrace_append hprefix tailTrace_8224339
  have hstable : (prefixWord ++ tailWord_8224339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224339).length < 2 ^ (prefixWord ++ tailWord_8224339).sum := by decide
  have hdescent : baseEnd_8224339 < baseStart_8224339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224393 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 6]
def baseStart_8224393 : Nat := 118140960795 + 8224393 * 2 ^ 59
def prefixEnd_8224393 : Nat := 4983230072969 + 3 ^ 40 * 8224393 * 2
def baseEnd_8224393 : Nat := 469229633385905084251579

theorem tailTrace_8224393 : CollatzResearch.WordTrace tailWord_8224393 prefixEnd_8224393 469229633385905084251579 := by
  unfold tailWord_8224393
  simp only [CollatzResearch.WordTrace]
  refine ⟨299968256093436250342437833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199978837395624166894958555 299968256093436250342437833)
  ·
    refine ⟨224976192070077187756828375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299968256093436250342437833 224976192070077187756828375)
    ·
      refine ⟨337464288105115781635242563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224976192070077187756828375 337464288105115781635242563)
      ·
        refine ⟨506196432157673672452863845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337464288105115781635242563 506196432157673672452863845)
        ·
          refine ⟨94911831029563813584911971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 506196432157673672452863845 94911831029563813584911971)
          ·
            refine ⟨142367746544345720377367957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94911831029563813584911971 142367746544345720377367957)
            ·
              refine ⟨6673488119266205642689123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142367746544345720377367957 6673488119266205642689123)
              ·
                refine ⟨10010232178899308464033685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673488119266205642689123 10010232178899308464033685)
                ·
                  refine ⟨469229633385905084251579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10010232178899308464033685 469229633385905084251579)
                  ·
                    rfl

theorem cell23_8224393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 6].length) (baseStart_8224393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224393 prefixEnd_8224393 := by exact prefixLift 8224393
  have htrace : WordTrace (prefixWord ++ tailWord_8224393) baseStart_8224393 baseEnd_8224393 := by
    simpa [prefixWord, tailWord_8224393, baseEnd_8224393] using wordTrace_append hprefix tailTrace_8224393
  have hstable : (prefixWord ++ tailWord_8224393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224393).length < 2 ^ (prefixWord ++ tailWord_8224393).sum := by decide
  have hdescent : baseEnd_8224393 < baseStart_8224393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224454 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_8224454 : Nat := 118140960795 + 8224454 * 2 ^ 59
def prefixEnd_8224454 : Nat := 4983230072969 + 3 ^ 40 * 8224454 * 2
def baseEnd_8224454 : Nat := 4223098022793070019601431

theorem tailTrace_8224454 : CollatzResearch.WordTrace tailWord_8224454 prefixEnd_8224454 4223098022793070019601431 := by
  unfold tailWord_8224454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9374077529569226805012763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199980320630810171840272277 9374077529569226805012763)
  ·
    refine ⟨14061116294353840207519145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9374077529569226805012763 14061116294353840207519145)
    ·
      refine ⟨10545837220765380155639359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14061116294353840207519145 10545837220765380155639359)
      ·
        refine ⟨15818755831148070233459039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10545837220765380155639359 15818755831148070233459039)
        ·
          refine ⟨23728133746722105350188559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15818755831148070233459039 23728133746722105350188559)
          ·
            refine ⟨35592200620083158025282839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23728133746722105350188559 35592200620083158025282839)
            ·
              refine ⟨53388300930124737037924259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35592200620083158025282839 53388300930124737037924259)
              ·
                refine ⟨80082451395187105556886389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53388300930124737037924259 80082451395187105556886389)
                ·
                  refine ⟨7507729818298791145958099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80082451395187105556886389 7507729818298791145958099)
                  ·
                    refine ⟨11261594727448186718937149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7507729818298791145958099 11261594727448186718937149)
                    ·
                      refine ⟨4223098022793070019601431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11261594727448186718937149 4223098022793070019601431)
                      ·
                        rfl

theorem cell23_8224454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_8224454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224454 prefixEnd_8224454 := by exact prefixLift 8224454
  have htrace : WordTrace (prefixWord ++ tailWord_8224454) baseStart_8224454 baseEnd_8224454 := by
    simpa [prefixWord, tailWord_8224454, baseEnd_8224454] using wordTrace_append hprefix tailTrace_8224454
  have hstable : (prefixWord ++ tailWord_8224454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224454).length < 2 ^ (prefixWord ++ tailWord_8224454).sum := by decide
  have hdescent : baseEnd_8224454 < baseStart_8224454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224473 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_8224473 : Nat := 118140960795 + 8224473 * 2 ^ 59
def prefixEnd_8224473 : Nat := 4983230072969 + 3 ^ 40 * 8224473 * 2
def baseEnd_8224473 : Nat := 4223107778925505445263843

theorem tailTrace_8224473 : CollatzResearch.WordTrace tailWord_8224473 prefixEnd_8224473 4223107778925505445263843 := by
  unfold tailWord_8224473
  simp only [CollatzResearch.WordTrace]
  refine ⟨299971173933146424005350073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199980782622097616003566715 299971173933146424005350073)
  ·
    refine ⟨224978380449859818004012555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299971173933146424005350073 224978380449859818004012555)
    ·
      refine ⟨337467570674789727006018833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224978380449859818004012555 337467570674789727006018833)
      ·
        refine ⟨253100678006092295254514125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337467570674789727006018833 253100678006092295254514125)
        ·
          refine ⟨94912754252284610720442797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253100678006092295254514125 94912754252284610720442797)
          ·
            refine ⟨35592282844606729020166049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94912754252284610720442797 35592282844606729020166049)
            ·
              refine ⟨26694212133455046765124537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35592282844606729020166049 26694212133455046765124537)
              ·
                refine ⟨20020659100091285073843403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26694212133455046765124537 20020659100091285073843403)
                ·
                  refine ⟨30030988650136927610765105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20020659100091285073843403 30030988650136927610765105)
                  ·
                    refine ⟨22523241487602695708073829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30030988650136927610765105 22523241487602695708073829)
                    ·
                      refine ⟨4223107778925505445263843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22523241487602695708073829 4223107778925505445263843)
                      ·
                        rfl

theorem cell23_8224473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_8224473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224473 prefixEnd_8224473 := by exact prefixLift 8224473
  have htrace : WordTrace (prefixWord ++ tailWord_8224473) baseStart_8224473 baseEnd_8224473 := by
    simpa [prefixWord, tailWord_8224473, baseEnd_8224473] using wordTrace_append hprefix tailTrace_8224473
  have hstable : (prefixWord ++ tailWord_8224473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224473).length < 2 ^ (prefixWord ++ tailWord_8224473).sum := by decide
  have hdescent : baseEnd_8224473 < baseStart_8224473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224483 : List Nat := [1, 1, 1, 7, 2, 1, 10]
def baseStart_8224483 : Nat := 118140960795 + 8224483 * 2 ^ 59
def prefixEnd_8224483 : Nat := 4983230072969 + 3 ^ 40 * 8224483 * 2
def baseEnd_8224483 : Nat := 52137196465827782791837

theorem tailTrace_8224483 : CollatzResearch.WordTrace tailWord_8224483 prefixEnd_8224483 52137196465827782791837 := by
  unfold tailWord_8224483
  simp only [CollatzResearch.WordTrace]
  refine ⟨299971538663110195713214103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199981025775406797142142735 299971538663110195713214103)
  ·
    refine ⟨449957307994665293569821155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299971538663110195713214103 449957307994665293569821155)
    ·
      refine ⟨674935961991997940354731733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449957307994665293569821155 674935961991997940354731733)
      ·
        refine ⟨15818811609187451727064025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 674935961991997940354731733 15818811609187451727064025)
        ·
          refine ⟨11864108706890588795298019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15818811609187451727064025 11864108706890588795298019)
          ·
            refine ⟨17796163060335883192947029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11864108706890588795298019 17796163060335883192947029)
            ·
              refine ⟨52137196465827782791837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17796163060335883192947029 52137196465827782791837)
              ·
                rfl

theorem cell23_8224483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 10].length) (baseStart_8224483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224483 prefixEnd_8224483 := by exact prefixLift 8224483
  have htrace : WordTrace (prefixWord ++ tailWord_8224483) baseStart_8224483 baseEnd_8224483 := by
    simpa [prefixWord, tailWord_8224483, baseEnd_8224483] using wordTrace_append hprefix tailTrace_8224483
  have hstable : (prefixWord ++ tailWord_8224483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224483).length < 2 ^ (prefixWord ++ tailWord_8224483).sum := by decide
  have hdescent : baseEnd_8224483 < baseStart_8224483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224487 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 4, 4]
def baseStart_8224487 : Nat := 118140960795 + 8224487 * 2 ^ 59
def prefixEnd_8224487 : Nat := 4983230072969 + 3 ^ 40 * 8224487 * 2
def baseEnd_8224487 : Nat := 1407704989218222796829593

theorem tailTrace_8224487 : CollatzResearch.WordTrace tailWord_8224487 prefixEnd_8224487 1407704989218222796829593 := by
  unfold tailWord_8224487
  simp only [CollatzResearch.WordTrace]
  refine ⟨299971684555095704396359715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199981123036730469597573143 299971684555095704396359715)
  ·
    refine ⟨449957526832643556594539573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299971684555095704396359715 449957526832643556594539573)
    ·
      refine ⟨42183518140560333430738085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449957526832643556594539573 42183518140560333430738085)
      ·
        refine ⟨7909409651355062518263391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42183518140560333430738085 7909409651355062518263391)
        ·
          refine ⟨11864114477032593777395087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7909409651355062518263391 11864114477032593777395087)
          ·
            refine ⟨17796171715548890666092631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11864114477032593777395087 17796171715548890666092631)
            ·
              refine ⟨26694257573323335999138947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17796171715548890666092631 26694257573323335999138947)
              ·
                refine ⟨40041386359985003998708421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26694257573323335999138947 40041386359985003998708421)
                ·
                  refine ⟨7507759942497188249757829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40041386359985003998708421 7507759942497188249757829)
                  ·
                    refine ⟨1407704989218222796829593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7507759942497188249757829 1407704989218222796829593)
                    ·
                      rfl

theorem cell23_8224487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_8224487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224487 prefixEnd_8224487 := by exact prefixLift 8224487
  have htrace : WordTrace (prefixWord ++ tailWord_8224487) baseStart_8224487 baseEnd_8224487 := by
    simpa [prefixWord, tailWord_8224487, baseEnd_8224487] using wordTrace_append hprefix tailTrace_8224487
  have hstable : (prefixWord ++ tailWord_8224487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224487).length < 2 ^ (prefixWord ++ tailWord_8224487).sum := by decide
  have hdescent : baseEnd_8224487 < baseStart_8224487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224494 : List Nat := [4, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_8224494 : Nat := 118140960795 + 8224494 * 2 ^ 59
def prefixEnd_8224494 : Nat := 4983230072969 + 3 ^ 40 * 8224494 * 2
def baseEnd_8224494 : Nat := 4223118562019249863101247

theorem tailTrace_8224494 : CollatzResearch.WordTrace tailWord_8224494 prefixEnd_8224494 4223118562019249863101247 := by
  unfold tailWord_8224494
  simp only [CollatzResearch.WordTrace]
  refine ⟨37496492483258793073983067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199981293244046896394576357 37496492483258793073983067)
  ·
    refine ⟨56244738724888189610974601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37496492483258793073983067 56244738724888189610974601)
    ·
      refine ⟨42183554043666142208230951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56244738724888189610974601 42183554043666142208230951)
      ·
        refine ⟨63275331065499213312346427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42183554043666142208230951 63275331065499213312346427)
        ·
          refine ⟨94912996598248819968519641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63275331065499213312346427 94912996598248819968519641)
          ·
            refine ⟨71184747448686614976389731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94912996598248819968519641 71184747448686614976389731)
            ·
              refine ⟨106777121173029922464584597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71184747448686614976389731 106777121173029922464584597)
              ·
                refine ⟨5005177554985777615527403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106777121173029922464584597 5005177554985777615527403)
                ·
                  refine ⟨7507766332478666423291105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005177554985777615527403 7507766332478666423291105)
                  ·
                    refine ⟨5630824749358999817468329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7507766332478666423291105 5630824749358999817468329)
                    ·
                      refine ⟨4223118562019249863101247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630824749358999817468329 4223118562019249863101247)
                      ·
                        rfl

theorem cell23_8224494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_8224494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224494 prefixEnd_8224494 := by exact prefixLift 8224494
  have htrace : WordTrace (prefixWord ++ tailWord_8224494) baseStart_8224494 baseEnd_8224494 := by
    simpa [prefixWord, tailWord_8224494, baseEnd_8224494] using wordTrace_append hprefix tailTrace_8224494
  have hstable : (prefixWord ++ tailWord_8224494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224494).length < 2 ^ (prefixWord ++ tailWord_8224494).sum := by decide
  have hdescent : baseEnd_8224494 < baseStart_8224494 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224496 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 2, 7]
def baseStart_8224496 : Nat := 118140960795 + 8224496 * 2 ^ 59
def prefixEnd_8224496 : Nat := 4983230072969 + 3 ^ 40 * 8224496 * 2
def baseEnd_8224496 : Nat := 1407706529660186285092079

theorem tailTrace_8224496 : CollatzResearch.WordTrace tailWord_8224496 prefixEnd_8224496 1407706529660186285092079 := by
  unfold tailWord_8224496
  simp only [CollatzResearch.WordTrace]
  refine ⟨149986006406031549466718671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199981341874708732622291561 149986006406031549466718671)
  ·
    refine ⟨224979009609047324200078007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149986006406031549466718671 224979009609047324200078007)
    ·
      refine ⟨337468514413570986300117011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224979009609047324200078007 337468514413570986300117011)
      ·
        refine ⟨506202771620356479450175517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337468514413570986300117011 506202771620356479450175517)
        ·
          refine ⟨189826039357633679793815819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506202771620356479450175517 189826039357633679793815819)
          ·
            refine ⟨284739059036450519690723729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189826039357633679793815819 284739059036450519690723729)
            ·
              refine ⟨213554294277337889768042797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284739059036450519690723729 213554294277337889768042797)
              ·
                refine ⟨80082860354001708663016049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213554294277337889768042797 80082860354001708663016049)
                ·
                  refine ⟨60062145265501281497262037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80082860354001708663016049 60062145265501281497262037)
                  ·
                    refine ⟨1407706529660186285092079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60062145265501281497262037 1407706529660186285092079)
                    ·
                      rfl

theorem cell23_8224496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_8224496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224496 prefixEnd_8224496 := by exact prefixLift 8224496
  have htrace : WordTrace (prefixWord ++ tailWord_8224496) baseStart_8224496 baseEnd_8224496 := by
    simpa [prefixWord, tailWord_8224496, baseEnd_8224496] using wordTrace_append hprefix tailTrace_8224496
  have hstable : (prefixWord ++ tailWord_8224496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224496).length < 2 ^ (prefixWord ++ tailWord_8224496).sum := by decide
  have hdescent : baseEnd_8224496 < baseStart_8224496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224607 : List Nat := [1, 1, 2, 3, 1, 4, 4, 2, 5]
def baseStart_8224607 : Nat := 118140960795 + 8224607 * 2 ^ 59
def prefixEnd_8224607 : Nat := 4983230072969 + 3 ^ 40 * 8224607 * 2
def baseEnd_8224607 : Nat := 469241842814800880109803

theorem tailTrace_8224607 : CollatzResearch.WordTrace tailWord_8224607 prefixEnd_8224607 469241842814800880109803 := by
  unfold tailWord_8224607
  simp only [CollatzResearch.WordTrace]
  refine ⟨299976061314660964890728075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199984040876440643260485383 299976061314660964890728075)
  ·
    refine ⟨449964091971991447336092113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299976061314660964890728075 449964091971991447336092113)
    ·
      refine ⟨337473068978993585502069085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449964091971991447336092113 337473068978993585502069085)
      ·
        refine ⟨126552400867122594563275907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337473068978993585502069085 126552400867122594563275907)
        ·
          refine ⟨189828601300683891844913861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126552400867122594563275907 189828601300683891844913861)
          ·
            refine ⟨35592862743878229720921349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189828601300683891844913861 35592862743878229720921349)
            ·
              refine ⟨6673661764477168072672753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35592862743878229720921349 6673661764477168072672753)
              ·
                refine ⟨5005246323357876054504565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6673661764477168072672753 5005246323357876054504565)
                ·
                  refine ⟨469241842814800880109803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5005246323357876054504565 469241842814800880109803)
                  ·
                    rfl

theorem cell23_8224607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 5].length) (baseStart_8224607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224607 prefixEnd_8224607 := by exact prefixLift 8224607
  have htrace : WordTrace (prefixWord ++ tailWord_8224607) baseStart_8224607 baseEnd_8224607 := by
    simpa [prefixWord, tailWord_8224607, baseEnd_8224607] using wordTrace_append hprefix tailTrace_8224607
  have hstable : (prefixWord ++ tailWord_8224607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224607).length < 2 ^ (prefixWord ++ tailWord_8224607).sum := by decide
  have hdescent : baseEnd_8224607 < baseStart_8224607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224640 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 1, 6, 2]
def baseStart_8224640 : Nat := 118140960795 + 8224640 * 2 ^ 59
def prefixEnd_8224640 : Nat := 4983230072969 + 3 ^ 40 * 8224640 * 2
def baseEnd_8224640 : Nat := 4223193530194806291875575

theorem tailTrace_8224640 : CollatzResearch.WordTrace tailWord_8224640 prefixEnd_8224640 4223193530194806291875575 := by
  unfold tailWord_8224640
  simp only [CollatzResearch.WordTrace]
  refine ⟨149988632461770705763339687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199984843282360941017786249 149988632461770705763339687)
  ·
    refine ⟨224982948692656058645009531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149988632461770705763339687 224982948692656058645009531)
    ·
      refine ⟨337474423038984087967514297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224982948692656058645009531 337474423038984087967514297)
      ·
        refine ⟨253105817279238065975635723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337474423038984087967514297 253105817279238065975635723)
        ·
          refine ⟨379658725918857098963453585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253105817279238065975635723 379658725918857098963453585)
          ·
            refine ⟨284744044439142824222590189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379658725918857098963453585 284744044439142824222590189)
            ·
              refine ⟨106779016664678559083471321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284744044439142824222590189 106779016664678559083471321)
              ·
                refine ⟨80084262498508919312603491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106779016664678559083471321 80084262498508919312603491)
                ·
                  refine ⟨120126393747763378968905237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80084262498508919312603491 120126393747763378968905237)
                  ·
                    refine ⟨5630924706926408389167433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120126393747763378968905237 5630924706926408389167433)
                    ·
                      refine ⟨4223193530194806291875575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5630924706926408389167433 4223193530194806291875575)
                      ·
                        rfl

theorem cell23_8224640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_8224640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224640 prefixEnd_8224640 := by exact prefixLift 8224640
  have htrace : WordTrace (prefixWord ++ tailWord_8224640) baseStart_8224640 baseEnd_8224640 := by
    simpa [prefixWord, tailWord_8224640, baseEnd_8224640] using wordTrace_append hprefix tailTrace_8224640
  have hstable : (prefixWord ++ tailWord_8224640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224640).length < 2 ^ (prefixWord ++ tailWord_8224640).sum := by decide
  have hdescent : baseEnd_8224640 < baseStart_8224640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224701 : List Nat := [1, 4, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_8224701 : Nat := 118140960795 + 8224701 * 2 ^ 59
def prefixEnd_8224701 : Nat := 4983230072969 + 3 ^ 40 * 8224701 * 2
def baseEnd_8224701 : Nat := 1407741617504910184404265

theorem tailTrace_8224701 : CollatzResearch.WordTrace tailWord_8224701 prefixEnd_8224701 1407741617504910184404265 := by
  unfold tailWord_8224701
  simp only [CollatzResearch.WordTrace]
  refine ⟨299979489776320418944649957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199986326517546945963099971 299979489776320418944649957)
  ·
    refine ⟨56246154333060078552121867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299979489776320418944649957 56246154333060078552121867)
    ·
      refine ⟨84369231499590117828182801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56246154333060078552121867 84369231499590117828182801)
      ·
        refine ⟨63276923624692588371137101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84369231499590117828182801 63276923624692588371137101)
        ·
          refine ⟨23728846359259720639176413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63276923624692588371137101 23728846359259720639176413)
          ·
            refine ⟨8898317384722395239691155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23728846359259720639176413 8898317384722395239691155)
            ·
              refine ⟨13347476077083592859536733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8898317384722395239691155 13347476077083592859536733)
              ·
                refine ⟨5005303528906347322326275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13347476077083592859536733 5005303528906347322326275)
                ·
                  refine ⟨7507955293359520983489413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005303528906347322326275 7507955293359520983489413)
                  ·
                    refine ⟨1407741617504910184404265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7507955293359520983489413 1407741617504910184404265)
                    ·
                      rfl

theorem cell23_8224701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_8224701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224701 prefixEnd_8224701 := by exact prefixLift 8224701
  have htrace : WordTrace (prefixWord ++ tailWord_8224701) baseStart_8224701 baseEnd_8224701 := by
    simpa [prefixWord, tailWord_8224701, baseEnd_8224701] using wordTrace_append hprefix tailTrace_8224701
  have hstable : (prefixWord ++ tailWord_8224701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224701).length < 2 ^ (prefixWord ++ tailWord_8224701).sum := by decide
  have hdescent : baseEnd_8224701 < baseStart_8224701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224740 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_8224740 : Nat := 118140960795 + 8224740 * 2 ^ 59
def prefixEnd_8224740 : Nat := 4983230072969 + 3 ^ 40 * 8224740 * 2
def baseEnd_8224740 : Nat := 1407748292753418633541705

theorem tailTrace_8224740 : CollatzResearch.WordTrace tailWord_8224740 prefixEnd_8224740 1407748292753418633541705 := by
  unfold tailWord_8224740
  simp only [CollatzResearch.WordTrace]
  refine ⟨149990456111589564302659837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199987274815452752403546449 149990456111589564302659837)
  ·
    refine ⟨56246421041846086613497439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149990456111589564302659837 56246421041846086613497439)
    ·
      refine ⟨84369631562769129920246159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56246421041846086613497439 84369631562769129920246159)
      ·
        refine ⟨126554447344153694880369239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84369631562769129920246159 126554447344153694880369239)
        ·
          refine ⟨189831671016230542320553859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126554447344153694880369239 189831671016230542320553859)
          ·
            refine ⟨284747506524345813480830789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189831671016230542320553859 284747506524345813480830789)
            ·
              refine ⟨53390157473314840027655773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284747506524345813480830789 53390157473314840027655773)
              ·
                refine ⟨20021309052493065010370915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53390157473314840027655773 20021309052493065010370915)
                ·
                  refine ⟨30031963578739597515556373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20021309052493065010370915 30031963578739597515556373)
                  ·
                    refine ⟨1407748292753418633541705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30031963578739597515556373 1407748292753418633541705)
                    ·
                      rfl

theorem cell23_8224740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_8224740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224740 prefixEnd_8224740 := by exact prefixLift 8224740
  have htrace : WordTrace (prefixWord ++ tailWord_8224740) baseStart_8224740 baseEnd_8224740 := by
    simpa [prefixWord, tailWord_8224740, baseEnd_8224740] using wordTrace_append hprefix tailTrace_8224740
  have hstable : (prefixWord ++ tailWord_8224740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224740).length < 2 ^ (prefixWord ++ tailWord_8224740).sum := by decide
  have hdescent : baseEnd_8224740 < baseStart_8224740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224760 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_8224760 : Nat := 118140960795 + 8224760 * 2 ^ 59
def prefixEnd_8224760 : Nat := 4983230072969 + 3 ^ 40 * 8224760 * 2
def baseEnd_8224760 : Nat := 4223255147873345822375023

theorem tailTrace_8224760 : CollatzResearch.WordTrace tailWord_8224760 prefixEnd_8224760 4223255147873345822375023 := by
  unfold tailWord_8224760
  simp only [CollatzResearch.WordTrace]
  refine ⟨149990820841553336010523867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199987761122071114680698489 149990820841553336010523867)
  ·
    refine ⟨224986231262330004015785801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149990820841553336010523867 224986231262330004015785801)
    ·
      refine ⟨168739673446747503011839351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224986231262330004015785801 168739673446747503011839351)
      ·
        refine ⟨253109510170121254517759027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168739673446747503011839351 253109510170121254517759027)
        ·
          refine ⟨379664265255181881776638541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253109510170121254517759027 379664265255181881776638541)
          ·
            refine ⟨142374099470693205666239453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379664265255181881776638541 142374099470693205666239453)
            ·
              refine ⟨53390287301509952124839795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142374099470693205666239453 53390287301509952124839795)
              ·
                refine ⟨80085430952264928187259693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53390287301509952124839795 80085430952264928187259693)
                ·
                  refine ⟨30032036607099348070222385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80085430952264928187259693 30032036607099348070222385)
                  ·
                    refine ⟨22524027455324511052666789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30032036607099348070222385 22524027455324511052666789)
                    ·
                      refine ⟨4223255147873345822375023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22524027455324511052666789 4223255147873345822375023)
                      ·
                        rfl

theorem cell23_8224760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_8224760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224760 prefixEnd_8224760 := by exact prefixLift 8224760
  have htrace : WordTrace (prefixWord ++ tailWord_8224760) baseStart_8224760 baseEnd_8224760 := by
    simpa [prefixWord, tailWord_8224760, baseEnd_8224760] using wordTrace_append hprefix tailTrace_8224760
  have hstable : (prefixWord ++ tailWord_8224760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224760).length < 2 ^ (prefixWord ++ tailWord_8224760).sum := by decide
  have hdescent : baseEnd_8224760 < baseStart_8224760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224764 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_8224764 : Nat := 118140960795 + 8224764 * 2 ^ 59
def prefixEnd_8224764 : Nat := 4983230072969 + 3 ^ 40 * 8224764 * 2
def baseEnd_8224764 : Nat := 4223257201795963806725005

theorem tailTrace_8224764 : CollatzResearch.WordTrace tailWord_8224764 prefixEnd_8224764 4223257201795963806725005 := by
  unfold tailWord_8224764
  simp only [CollatzResearch.WordTrace]
  refine ⟨149990893787546090352096673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199987858383394787136128897 149990893787546090352096673)
  ·
    refine ⟨112493170340659567764072505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149990893787546090352096673 112493170340659567764072505)
    ·
      refine ⟨84369877755494675823054379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112493170340659567764072505 84369877755494675823054379)
      ·
        refine ⟨126554816633242013734581569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84369877755494675823054379 126554816633242013734581569)
        ·
          refine ⟨94916112474931510300936177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126554816633242013734581569 94916112474931510300936177)
          ·
            refine ⟨71187084356198632725702133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94916112474931510300936177 71187084356198632725702133)
            ·
              refine ⟨6673789158393621818034575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71187084356198632725702133 6673789158393621818034575)
              ·
                refine ⟨10010683737590432727051863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673789158393621818034575 10010683737590432727051863)
                ·
                  refine ⟨15016025606385649090577795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10010683737590432727051863 15016025606385649090577795)
                  ·
                    refine ⟨22524038409578473635866693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15016025606385649090577795 22524038409578473635866693)
                    ·
                      refine ⟨4223257201795963806725005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22524038409578473635866693 4223257201795963806725005)
                      ·
                        rfl

theorem cell23_8224764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_8224764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224764 prefixEnd_8224764 := by exact prefixLift 8224764
  have htrace : WordTrace (prefixWord ++ tailWord_8224764) baseStart_8224764 baseEnd_8224764 := by
    simpa [prefixWord, tailWord_8224764, baseEnd_8224764] using wordTrace_append hprefix tailTrace_8224764
  have hstable : (prefixWord ++ tailWord_8224764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224764).length < 2 ^ (prefixWord ++ tailWord_8224764).sum := by decide
  have hdescent : baseEnd_8224764 < baseStart_8224764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224767 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 3]
def baseStart_8224767 : Nat := 118140960795 + 8224767 * 2 ^ 59
def prefixEnd_8224767 : Nat := 4983230072969 + 3 ^ 40 * 8224767 * 2
def baseEnd_8224767 : Nat := 4223258742237927294987491

theorem tailTrace_8224767 : CollatzResearch.WordTrace tailWord_8224767 prefixEnd_8224767 4223258742237927294987491 := by
  unfold tailWord_8224767
  simp only [CollatzResearch.WordTrace]
  refine ⟨299981896994081312216552555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199987931329387541477701703 299981896994081312216552555)
  ·
    refine ⟨449972845491121968324828833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299981896994081312216552555 449972845491121968324828833)
    ·
      refine ⟨337479634118341476243621625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449972845491121968324828833 337479634118341476243621625)
      ·
        refine ⟨253109725588756107182716219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337479634118341476243621625 253109725588756107182716219)
        ·
          refine ⟨379664588383134160774074329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253109725588756107182716219 379664588383134160774074329)
          ·
            refine ⟨284748441287350620580555747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379664588383134160774074329 284748441287350620580555747)
            ·
              refine ⟨427122661931025930870833621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284748441287350620580555747 427122661931025930870833621)
              ·
                refine ⟨10010687389008420254785163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 427122661931025930870833621 10010687389008420254785163)
                ·
                  refine ⟨15016031083512630382177745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10010687389008420254785163 15016031083512630382177745)
                  ·
                    refine ⟨11262023312634472786633309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15016031083512630382177745 11262023312634472786633309)
                    ·
                      refine ⟨4223258742237927294987491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11262023312634472786633309 4223258742237927294987491)
                      ·
                        rfl

theorem cell23_8224767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_8224767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224767 prefixEnd_8224767 := by exact prefixLift 8224767
  have htrace : WordTrace (prefixWord ++ tailWord_8224767) baseStart_8224767 baseEnd_8224767 := by
    simpa [prefixWord, tailWord_8224767, baseEnd_8224767] using wordTrace_append hprefix tailTrace_8224767
  have hstable : (prefixWord ++ tailWord_8224767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224767).length < 2 ^ (prefixWord ++ tailWord_8224767).sum := by decide
  have hdescent : baseEnd_8224767 < baseStart_8224767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224770 : List Nat := [3, 4, 1, 15]
def baseStart_8224770 : Nat := 118140960795 + 8224770 * 2 ^ 59
def prefixEnd_8224770 : Nat := 4983230072969 + 3 ^ 40 * 8224770 * 2
def baseEnd_8224770 : Nat := 1931074660576081748171

theorem tailTrace_8224770 : CollatzResearch.WordTrace tailWord_8224770 prefixEnd_8224770 1931074660576081748171 := by
  unfold tailWord_8224770
  simp only [CollatzResearch.WordTrace]
  refine ⟨74995501603267610932227941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199988004275380295819274509 74995501603267610932227941)
  ·
    refine ⟨14061656550612677049792739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74995501603267610932227941 14061656550612677049792739)
    ·
      refine ⟨21092484825919015574689109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14061656550612677049792739 21092484825919015574689109)
      ·
        refine ⟨1931074660576081748171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 21092484825919015574689109 1931074660576081748171)
        ·
          rfl

theorem cell23_8224770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 15].length) (baseStart_8224770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224770 prefixEnd_8224770 := by exact prefixLift 8224770
  have htrace : WordTrace (prefixWord ++ tailWord_8224770) baseStart_8224770 baseEnd_8224770 := by
    simpa [prefixWord, tailWord_8224770, baseEnd_8224770] using wordTrace_append hprefix tailTrace_8224770
  have hstable : (prefixWord ++ tailWord_8224770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224770).length < 2 ^ (prefixWord ++ tailWord_8224770).sum := by decide
  have hdescent : baseEnd_8224770 < baseStart_8224770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224804 : List Nat := [2, 3, 1, 4, 2, 1, 3, 7]
def baseStart_8224804 : Nat := 118140960795 + 8224804 * 2 ^ 59
def prefixEnd_8224804 : Nat := 4983230072969 + 3 ^ 40 * 8224804 * 2
def baseEnd_8224804 : Nat := 156417694111931246304623

theorem tailTrace_8224804 : CollatzResearch.WordTrace tailWord_8224804 prefixEnd_8224804 156417694111931246304623 := by
  unfold tailWord_8224804
  simp only [CollatzResearch.WordTrace]
  refine ⟨149991623247473633767824733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199988830996631511690432977 149991623247473633767824733)
  ·
    refine ⟨56246858717802612662934275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149991623247473633767824733 56246858717802612662934275)
    ·
      refine ⟨84370288076703918994401413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56246858717802612662934275 84370288076703918994401413)
      ·
        refine ⟨15819429014381984811450265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84370288076703918994401413 15819429014381984811450265)
        ·
          refine ⟨11864571760786488608587699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15819429014381984811450265 11864571760786488608587699)
          ·
            refine ⟨17796857641179732912881549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11864571760786488608587699 17796857641179732912881549)
            ·
              refine ⟨6673821615442399842330581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17796857641179732912881549 6673821615442399842330581)
              ·
                refine ⟨156417694111931246304623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6673821615442399842330581 156417694111931246304623)
                ·
                  rfl

theorem cell23_8224804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 7].length) (baseStart_8224804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224804 prefixEnd_8224804 := by exact prefixLift 8224804
  have htrace : WordTrace (prefixWord ++ tailWord_8224804) baseStart_8224804 baseEnd_8224804 := by
    simpa [prefixWord, tailWord_8224804, baseEnd_8224804] using wordTrace_append hprefix tailTrace_8224804
  have hstable : (prefixWord ++ tailWord_8224804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224804).length < 2 ^ (prefixWord ++ tailWord_8224804).sum := by decide
  have hdescent : baseEnd_8224804 < baseStart_8224804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224814 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_8224814 : Nat := 118140960795 + 8224814 * 2 ^ 59
def prefixEnd_8224814 : Nat := 4983230072969 + 3 ^ 40 * 8224814 * 2
def baseEnd_8224814 : Nat := 4223282875828688611099775

theorem tailTrace_8224814 : CollatzResearch.WordTrace tailWord_8224814 prefixEnd_8224814 4223282875828688611099775 := by
  unfold tailWord_8224814
  simp only [CollatzResearch.WordTrace]
  refine ⟨37497951403113879905439187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199989074149940692829008997 37497951403113879905439187)
  ·
    refine ⟨56246927104670819858158781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37497951403113879905439187 56246927104670819858158781)
    ·
      refine ⟨21092597664251557446809543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56246927104670819858158781 21092597664251557446809543)
      ·
        refine ⟨31638896496377336170214315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21092597664251557446809543 31638896496377336170214315)
        ·
          refine ⟨47458344744566004255321473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31638896496377336170214315 47458344744566004255321473)
          ·
            refine ⟨35593758558424503191491105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47458344744566004255321473 35593758558424503191491105)
            ·
              refine ⟨26695318918818377393618329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35593758558424503191491105 26695318918818377393618329)
              ·
                refine ⟨20021489189113783045213747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26695318918818377393618329 20021489189113783045213747)
                ·
                  refine ⟨30032233783670674567820621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20021489189113783045213747 30032233783670674567820621)
                  ·
                    refine ⟨11262087668876502962932733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30032233783670674567820621 11262087668876502962932733)
                    ·
                      refine ⟨4223282875828688611099775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11262087668876502962932733 4223282875828688611099775)
                      ·
                        rfl

theorem cell23_8224814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_8224814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224814 prefixEnd_8224814 := by exact prefixLift 8224814
  have htrace : WordTrace (prefixWord ++ tailWord_8224814) baseStart_8224814 baseEnd_8224814 := by
    simpa [prefixWord, tailWord_8224814, baseEnd_8224814] using wordTrace_append hprefix tailTrace_8224814
  have hstable : (prefixWord ++ tailWord_8224814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224814).length < 2 ^ (prefixWord ++ tailWord_8224814).sum := by decide
  have hdescent : baseEnd_8224814 < baseStart_8224814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224840 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_8224840 : Nat := 118140960795 + 8224840 * 2 ^ 59
def prefixEnd_8224840 : Nat := 4983230072969 + 3 ^ 40 * 8224840 * 2
def baseEnd_8224840 : Nat := 4223296226325705509374655

theorem tailTrace_8224840 : CollatzResearch.WordTrace tailWord_8224840 prefixEnd_8224840 4223296226325705509374655 := by
  unfold tailWord_8224840
  simp only [CollatzResearch.WordTrace]
  refine ⟨149992279761408422841979987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199989706348544563789306649 149992279761408422841979987)
  ·
    refine ⟨224988419642112634262969981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149992279761408422841979987 224988419642112634262969981)
    ·
      refine ⟨84370657365792237848613743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224988419642112634262969981 84370657365792237848613743)
      ·
        refine ⟨126555986048688356772920615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84370657365792237848613743 126555986048688356772920615)
        ·
          refine ⟨189833979073032535159380923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126555986048688356772920615 189833979073032535159380923)
          ·
            refine ⟨284750968609548802739071385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189833979073032535159380923 284750968609548802739071385)
            ·
              refine ⟨213563226457161602054303539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284750968609548802739071385 213563226457161602054303539)
              ·
                refine ⟨320344839685742403081455309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213563226457161602054303539 320344839685742403081455309)
                ·
                  refine ⟨120129314882153401155545741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320344839685742403081455309 120129314882153401155545741)
                  ·
                    refine ⟨45048493080807525433329653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120129314882153401155545741 45048493080807525433329653)
                    ·
                      refine ⟨4223296226325705509374655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45048493080807525433329653 4223296226325705509374655)
                      ·
                        rfl

theorem cell23_8224840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_8224840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224840 prefixEnd_8224840 := by exact prefixLift 8224840
  have htrace : WordTrace (prefixWord ++ tailWord_8224840) baseStart_8224840 baseEnd_8224840 := by
    simpa [prefixWord, tailWord_8224840, baseEnd_8224840] using wordTrace_append hprefix tailTrace_8224840
  have hstable : (prefixWord ++ tailWord_8224840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224840).length < 2 ^ (prefixWord ++ tailWord_8224840).sum := by decide
  have hdescent : baseEnd_8224840 < baseStart_8224840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224874 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_8224874 : Nat := 118140960795 + 8224874 * 2 ^ 59
def prefixEnd_8224874 : Nat := 4983230072969 + 3 ^ 40 * 8224874 * 2
def baseEnd_8224874 : Nat := 4223313684667958376349499

theorem tailTrace_8224874 : CollatzResearch.WordTrace tailWord_8224874 prefixEnd_8224874 4223313684667958376349499 := by
  unfold tailWord_8224874
  simp only [CollatzResearch.WordTrace]
  refine ⟨74996449901173417372674419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199990533069795779660465117 74996449901173417372674419)
  ·
    refine ⟨112494674851760126059011629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74996449901173417372674419 112494674851760126059011629)
    ·
      refine ⟨42185503069410047272129361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112494674851760126059011629 42185503069410047272129361)
      ·
        refine ⟨31639127302057535454097021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42185503069410047272129361 31639127302057535454097021)
        ·
          refine ⟨11864672738271575795286383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31639127302057535454097021 11864672738271575795286383)
          ·
            refine ⟨17797009107407363692929575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11864672738271575795286383 17797009107407363692929575)
            ·
              refine ⟨26695513661111045539394363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17797009107407363692929575 26695513661111045539394363)
              ·
                refine ⟨40043270491666568309091545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26695513661111045539394363 40043270491666568309091545)
                ·
                  refine ⟨30032452868749926231818659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40043270491666568309091545 30032452868749926231818659)
                  ·
                    refine ⟨45048679303124889347727989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30032452868749926231818659 45048679303124889347727989)
                    ·
                      refine ⟨4223313684667958376349499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45048679303124889347727989 4223313684667958376349499)
                      ·
                        rfl

theorem cell23_8224874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_8224874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224874 prefixEnd_8224874 := by exact prefixLift 8224874
  have htrace : WordTrace (prefixWord ++ tailWord_8224874) baseStart_8224874 baseEnd_8224874 := by
    simpa [prefixWord, tailWord_8224874, baseEnd_8224874] using wordTrace_append hprefix tailTrace_8224874
  have hstable : (prefixWord ++ tailWord_8224874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224874).length < 2 ^ (prefixWord ++ tailWord_8224874).sum := by decide
  have hdescent : baseEnd_8224874 < baseStart_8224874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224890 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_8224890 : Nat := 118140960795 + 8224890 * 2 ^ 59
def prefixEnd_8224890 : Nat := 4983230072969 + 3 ^ 40 * 8224890 * 2
def baseEnd_8224890 : Nat := 1407773966786143437916475

theorem tailTrace_8224890 : CollatzResearch.WordTrace tailWord_8224890 prefixEnd_8224890 1407773966786143437916475 := by
  unfold tailWord_8224890
  simp only [CollatzResearch.WordTrace]
  refine ⟨74996595793158926055820031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199990922115090469482186749 74996595793158926055820031)
  ·
    refine ⟨112494893689738389083730047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74996595793158926055820031 112494893689738389083730047)
    ·
      refine ⟨168742340534607583625595071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112494893689738389083730047 168742340534607583625595071)
      ·
        refine ⟨253113510801911375438392607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168742340534607583625595071 253113510801911375438392607)
        ·
          refine ⟨379670266202867063157588911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253113510801911375438392607 379670266202867063157588911)
          ·
            refine ⟨569505399304300594736383367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379670266202867063157588911 569505399304300594736383367)
            ·
              refine ⟨854258098956450892104575051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569505399304300594736383367 854258098956450892104575051)
              ·
                refine ⟨1281387148434676338156862577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854258098956450892104575051 1281387148434676338156862577)
                ·
                  refine ⟨961040361326007253617646933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1281387148434676338156862577 961040361326007253617646933)
                  ·
                    refine ⟨1407773966786143437916475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 961040361326007253617646933 1407773966786143437916475)
                    ·
                      rfl

theorem cell23_8224890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_8224890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224890 prefixEnd_8224890 := by exact prefixLift 8224890
  have htrace : WordTrace (prefixWord ++ tailWord_8224890) baseStart_8224890 baseEnd_8224890 := by
    simpa [prefixWord, tailWord_8224890, baseEnd_8224890] using wordTrace_append hprefix tailTrace_8224890
  have hstable : (prefixWord ++ tailWord_8224890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224890).length < 2 ^ (prefixWord ++ tailWord_8224890).sum := by decide
  have hdescent : baseEnd_8224890 < baseStart_8224890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224924 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_8224924 : Nat := 118140960795 + 8224924 * 2 ^ 59
def prefixEnd_8224924 : Nat := 4983230072969 + 3 ^ 40 * 8224924 * 2
def baseEnd_8224924 : Nat := 1407779786233561060241423

theorem tailTrace_8224924 : CollatzResearch.WordTrace tailWord_8224924 prefixEnd_8224924 1407779786233561060241423 := by
  unfold tailWord_8224924
  simp only [CollatzResearch.WordTrace]
  refine ⟨149993811627256264015008913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199991748836341685353345217 149993811627256264015008913)
  ·
    refine ⟨112495358720442198011256685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149993811627256264015008913 112495358720442198011256685)
    ·
      refine ⟨42185759520165824254221257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112495358720442198011256685 42185759520165824254221257)
      ·
        refine ⟨31639319640124368190665943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42185759520165824254221257 31639319640124368190665943)
        ·
          refine ⟨47458979460186552285998915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31639319640124368190665943 47458979460186552285998915)
          ·
            refine ⟨71188469190279828428998373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47458979460186552285998915 71188469190279828428998373)
            ·
              refine ⟨13347837973177467830437195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71188469190279828428998373 13347837973177467830437195)
              ·
                refine ⟨20021756959766201745655793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13347837973177467830437195 20021756959766201745655793)
                ·
                  refine ⟨15016317719824651309241845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20021756959766201745655793 15016317719824651309241845)
                  ·
                    refine ⟨1407779786233561060241423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15016317719824651309241845 1407779786233561060241423)
                    ·
                      rfl

theorem cell23_8224924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_8224924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224924 prefixEnd_8224924 := by exact prefixLift 8224924
  have htrace : WordTrace (prefixWord ++ tailWord_8224924) baseStart_8224924 baseEnd_8224924 := by
    simpa [prefixWord, tailWord_8224924, baseEnd_8224924] using wordTrace_append hprefix tailTrace_8224924
  have hstable : (prefixWord ++ tailWord_8224924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224924).length < 2 ^ (prefixWord ++ tailWord_8224924).sum := by decide
  have hdescent : baseEnd_8224924 < baseStart_8224924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224945 : List Nat := [1, 2, 2, 5, 3, 1, 2, 2, 5]
def baseStart_8224945 : Nat := 118140960795 + 8224945 * 2 ^ 59
def prefixEnd_8224945 : Nat := 4983230072969 + 3 ^ 40 * 8224945 * 2
def baseEnd_8224945 : Nat := 469261126866047510951297

theorem tailTrace_8224945 : CollatzResearch.WordTrace tailWord_8224945 prefixEnd_8224945 469261126866047510951297 := by
  unfold tailWord_8224945
  simp only [CollatzResearch.WordTrace]
  refine ⟨299988389187436448616532289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199992259458290965744354859 299988389187436448616532289)
  ·
    refine ⟨224991291890577336462399217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299988389187436448616532289 224991291890577336462399217)
    ·
      refine ⟨168743468917933002346799413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224991291890577336462399217 168743468917933002346799413)
      ·
        refine ⟨15819700211056218970012445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168743468917933002346799413 15819700211056218970012445)
        ·
          refine ⟨5932387579146082113754667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15819700211056218970012445 5932387579146082113754667)
          ·
            refine ⟨8898581368719123170632001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5932387579146082113754667 8898581368719123170632001)
            ·
              refine ⟨6673936026539342377974001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8898581368719123170632001 6673936026539342377974001)
              ·
                refine ⟨5005452019904506783480501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6673936026539342377974001 5005452019904506783480501)
                ·
                  refine ⟨469261126866047510951297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5005452019904506783480501 469261126866047510951297)
                  ·
                    rfl

theorem cell23_8224945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 5].length) (baseStart_8224945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224945 prefixEnd_8224945 := by exact prefixLift 8224945
  have htrace : WordTrace (prefixWord ++ tailWord_8224945) baseStart_8224945 baseEnd_8224945 := by
    simpa [prefixWord, tailWord_8224945, baseEnd_8224945] using wordTrace_append hprefix tailTrace_8224945
  have hstable : (prefixWord ++ tailWord_8224945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224945).length < 2 ^ (prefixWord ++ tailWord_8224945).sum := by decide
  have hdescent : baseEnd_8224945 < baseStart_8224945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224947 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 3]
def baseStart_8224947 : Nat := 118140960795 + 8224947 * 2 ^ 59
def prefixEnd_8224947 : Nat := 4983230072969 + 3 ^ 40 * 8224947 * 2
def baseEnd_8224947 : Nat := 4223351168755736590736663

theorem tailTrace_8224947 : CollatzResearch.WordTrace tailWord_8224947 prefixEnd_8224947 4223351168755736590736663 := by
  unfold tailWord_8224947
  simp only [CollatzResearch.WordTrace]
  refine ⟨299988462133429202958105095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199992308088952801972070063 299988462133429202958105095)
  ·
    refine ⟨449982693200143804437157643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299988462133429202958105095 449982693200143804437157643)
    ·
      refine ⟨674974039800215706655736465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449982693200143804437157643 674974039800215706655736465)
      ·
        refine ⟨506230529850161779991802349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674974039800215706655736465 506230529850161779991802349)
        ·
          refine ⟨189836448693810667496925881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506230529850161779991802349 189836448693810667496925881)
          ·
            refine ⟨142377336520358000622694411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189836448693810667496925881 142377336520358000622694411)
            ·
              refine ⟨213566004780537000934041617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142377336520358000622694411 213566004780537000934041617)
              ·
                refine ⟨160174503585402750700531213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213566004780537000934041617 160174503585402750700531213)
                ·
                  refine ⟨60065438844526031512699205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160174503585402750700531213 60065438844526031512699205)
                  ·
                    refine ⟨11262269783348630908631101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60065438844526031512699205 11262269783348630908631101)
                    ·
                      refine ⟨4223351168755736590736663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11262269783348630908631101 4223351168755736590736663)
                      ·
                        rfl

theorem cell23_8224947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_8224947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224947 prefixEnd_8224947 := by exact prefixLift 8224947
  have htrace : WordTrace (prefixWord ++ tailWord_8224947) baseStart_8224947 baseEnd_8224947 := by
    simpa [prefixWord, tailWord_8224947, baseEnd_8224947] using wordTrace_append hprefix tailTrace_8224947
  have hstable : (prefixWord ++ tailWord_8224947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224947).length < 2 ^ (prefixWord ++ tailWord_8224947).sum := by decide
  have hdescent : baseEnd_8224947 < baseStart_8224947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224957 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_8224957 : Nat := 118140960795 + 8224957 * 2 ^ 59
def prefixEnd_8224957 : Nat := 4983230072969 + 3 ^ 40 * 8224957 * 2
def baseEnd_8224957 : Nat := 4223356303562281551611617

theorem tailTrace_8224957 : CollatzResearch.WordTrace tailWord_8224957 prefixEnd_8224957 4223356303562281551611617 := by
  unfold tailWord_8224957
  simp only [CollatzResearch.WordTrace]
  refine ⟨299988826863392974665969125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199992551242261983110646083 299988826863392974665969125)
  ·
    refine ⟨56247905036886182749869211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299988826863392974665969125 56247905036886182749869211)
    ·
      refine ⟨84371857555329274124803817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56247905036886182749869211 84371857555329274124803817)
      ·
        refine ⟨63278893166496955593602863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84371857555329274124803817 63278893166496955593602863)
        ·
          refine ⟨94918339749745433390404295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63278893166496955593602863 94918339749745433390404295)
          ·
            refine ⟨142377509624618150085606443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94918339749745433390404295 142377509624618150085606443)
            ·
              refine ⟨213566264436927225128409665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142377509624618150085606443 213566264436927225128409665)
              ·
                refine ⟨160174698327695418846307249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213566264436927225128409665 160174698327695418846307249)
                ·
                  refine ⟨120131023745771564134730437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160174698327695418846307249 120131023745771564134730437)
                  ·
                    refine ⟨22524566952332168275261957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120131023745771564134730437 22524566952332168275261957)
                    ·
                      refine ⟨4223356303562281551611617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22524566952332168275261957 4223356303562281551611617)
                      ·
                        rfl

theorem cell23_8224957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_8224957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224957 prefixEnd_8224957 := by exact prefixLift 8224957
  have htrace : WordTrace (prefixWord ++ tailWord_8224957) baseStart_8224957 baseEnd_8224957 := by
    simpa [prefixWord, tailWord_8224957, baseEnd_8224957] using wordTrace_append hprefix tailTrace_8224957
  have hstable : (prefixWord ++ tailWord_8224957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224957).length < 2 ^ (prefixWord ++ tailWord_8224957).sum := by decide
  have hdescent : baseEnd_8224957 < baseStart_8224957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8224981 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_8224981 : Nat := 118140960795 + 8224981 * 2 ^ 59
def prefixEnd_8224981 : Nat := 4983230072969 + 3 ^ 40 * 8224981 * 2
def baseEnd_8224981 : Nat := 4223368627097989457711507

theorem tailTrace_8224981 : CollatzResearch.WordTrace tailWord_8224981 prefixEnd_8224981 4223368627097989457711507 := by
  unfold tailWord_8224981
  simp only [CollatzResearch.WordTrace]
  refine ⟨299989702215306026764842797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199993134810204017843228531 299989702215306026764842797)
  ·
    refine ⟨112496138330739760036816049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299989702215306026764842797 112496138330739760036816049)
    ·
      refine ⟨84372103748054820027612037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112496138330739760036816049 84372103748054820027612037)
      ·
        refine ⟨15819769452760278755177257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84372103748054820027612037 15819769452760278755177257)
        ·
          refine ⟨11864827089570209066382943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15819769452760278755177257 11864827089570209066382943)
          ·
            refine ⟨17797240634355313599574415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11864827089570209066382943 17797240634355313599574415)
            ·
              refine ⟨26695860951532970399361623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17797240634355313599574415 26695860951532970399361623)
              ·
                refine ⟨40043791427299455599042435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26695860951532970399361623 40043791427299455599042435)
                ·
                  refine ⟨60065687140949183398563653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40043791427299455599042435 60065687140949183398563653)
                  ·
                    refine ⟨11262316338927971887230685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60065687140949183398563653 11262316338927971887230685)
                    ·
                      refine ⟨4223368627097989457711507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11262316338927971887230685 4223368627097989457711507)
                      ·
                        rfl

theorem cell23_8224981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_8224981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8224981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8224981 prefixEnd_8224981 := by exact prefixLift 8224981
  have htrace : WordTrace (prefixWord ++ tailWord_8224981) baseStart_8224981 baseEnd_8224981 := by
    simpa [prefixWord, tailWord_8224981, baseEnd_8224981] using wordTrace_append hprefix tailTrace_8224981
  have hstable : (prefixWord ++ tailWord_8224981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8224981).length < 2 ^ (prefixWord ++ tailWord_8224981).sum := by decide
  have hdescent : baseEnd_8224981 < baseStart_8224981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8224981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225011 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 3]
def baseStart_8225011 : Nat := 118140960795 + 8225011 * 2 ^ 59
def prefixEnd_8225011 : Nat := 4983230072969 + 3 ^ 40 * 8225011 * 2
def baseEnd_8225011 : Nat := 4223384031517624340336369

theorem tailTrace_8225011 : CollatzResearch.WordTrace tailWord_8225011 prefixEnd_8225011 4223384031517624340336369 := by
  unfold tailWord_8225011
  simp only [CollatzResearch.WordTrace]
  refine ⟨299990796405197341888434887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199993864270131561258956591 299990796405197341888434887)
  ·
    refine ⟨449986194607796012832652331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299990796405197341888434887 449986194607796012832652331)
    ·
      refine ⟨674979291911694019248978497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449986194607796012832652331 674979291911694019248978497)
      ·
        refine ⟨506234468933770514436733873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674979291911694019248978497 506234468933770514436733873)
        ·
          refine ⟨379675851700327885827550405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506234468933770514436733873 379675851700327885827550405)
          ·
            refine ⟨71189222193811478592665701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379675851700327885827550405 71189222193811478592665701)
            ·
              refine ⟨13347979161339652236124819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71189222193811478592665701 13347979161339652236124819)
              ·
                refine ⟨20021968742009478354187229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13347979161339652236124819 20021968742009478354187229)
                ·
                  refine ⟨7508238278253554382820211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20021968742009478354187229 7508238278253554382820211)
                  ·
                    refine ⟨11262357417380331574230317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7508238278253554382820211 11262357417380331574230317)
                    ·
                      refine ⟨4223384031517624340336369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11262357417380331574230317 4223384031517624340336369)
                      ·
                        rfl

theorem cell23_8225011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 3].length) (baseStart_8225011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225011 prefixEnd_8225011 := by exact prefixLift 8225011
  have htrace : WordTrace (prefixWord ++ tailWord_8225011) baseStart_8225011 baseEnd_8225011 := by
    simpa [prefixWord, tailWord_8225011, baseEnd_8225011] using wordTrace_append hprefix tailTrace_8225011
  have hstable : (prefixWord ++ tailWord_8225011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225011).length < 2 ^ (prefixWord ++ tailWord_8225011).sum := by decide
  have hdescent : baseEnd_8225011 < baseStart_8225011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225014 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_8225014 : Nat := 118140960795 + 8225014 * 2 ^ 59
def prefixEnd_8225014 : Nat := 4983230072969 + 3 ^ 40 * 8225014 * 2
def baseEnd_8225014 : Nat := 1407795190653195942866285

theorem tailTrace_8225014 : CollatzResearch.WordTrace tailWord_8225014 prefixEnd_8225014 1407795190653195942866285 := by
  unfold tailWord_8225014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749431614011654587549631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199993937216124315600529397 18749431614011654587549631)
  ·
    refine ⟨28124147421017481881324447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18749431614011654587549631 28124147421017481881324447)
    ·
      refine ⟨42186221131526222821986671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28124147421017481881324447 42186221131526222821986671)
      ·
        refine ⟨63279331697289334232980007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42186221131526222821986671 63279331697289334232980007)
        ·
          refine ⟨94918997545934001349470011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63279331697289334232980007 94918997545934001349470011)
          ·
            refine ⟨142378496318901002024205017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94918997545934001349470011 142378496318901002024205017)
            ·
              refine ⟨106783872239175751518153763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142378496318901002024205017 106783872239175751518153763)
              ·
                refine ⟨160175808358763627277230645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106783872239175751518153763 160175808358763627277230645)
                ·
                  refine ⟨15016482033634090057240373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160175808358763627277230645 15016482033634090057240373)
                  ·
                    refine ⟨1407795190653195942866285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15016482033634090057240373 1407795190653195942866285)
                    ·
                      rfl

theorem cell23_8225014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_8225014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225014 prefixEnd_8225014 := by exact prefixLift 8225014
  have htrace : WordTrace (prefixWord ++ tailWord_8225014) baseStart_8225014 baseEnd_8225014 := by
    simpa [prefixWord, tailWord_8225014, baseEnd_8225014] using wordTrace_append hprefix tailTrace_8225014
  have hstable : (prefixWord ++ tailWord_8225014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225014).length < 2 ^ (prefixWord ++ tailWord_8225014).sum := by decide
  have hdescent : baseEnd_8225014 < baseStart_8225014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225017 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_8225017 : Nat := 118140960795 + 8225017 * 2 ^ 59
def prefixEnd_8225017 : Nat := 4983230072969 + 3 ^ 40 * 8225017 * 2
def baseEnd_8225017 : Nat := 4223387112401551316861341

theorem tailTrace_8225017 : CollatzResearch.WordTrace tailWord_8225017 prefixEnd_8225017 4223387112401551316861341 := by
  unfold tailWord_8225017
  simp only [CollatzResearch.WordTrace]
  refine ⟨299991015243175604913153305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199994010162117069942102203 299991015243175604913153305)
  ·
    refine ⟨224993261432381703684864979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299991015243175604913153305 224993261432381703684864979)
    ·
      refine ⟨337489892148572555527297469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224993261432381703684864979 337489892148572555527297469)
      ·
        refine ⟨126558709555714708322736551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337489892148572555527297469 126558709555714708322736551)
        ·
          refine ⟨189838064333572062484104827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126558709555714708322736551 189838064333572062484104827)
          ·
            refine ⟨284757096500358093726157241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189838064333572062484104827 284757096500358093726157241)
            ·
              refine ⟨213567822375268570294617931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284757096500358093726157241 213567822375268570294617931)
              ·
                refine ⟨320351733562902855441926897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213567822375268570294617931 320351733562902855441926897)
                ·
                  refine ⟨240263800172177141581445173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320351733562902855441926897 240263800172177141581445173)
                  ·
                    refine ⟨22524731266141607023260485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 240263800172177141581445173 22524731266141607023260485)
                    ·
                      refine ⟨4223387112401551316861341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22524731266141607023260485 4223387112401551316861341)
                      ·
                        rfl

theorem cell23_8225017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_8225017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225017 prefixEnd_8225017 := by exact prefixLift 8225017
  have htrace : WordTrace (prefixWord ++ tailWord_8225017) baseStart_8225017 baseEnd_8225017 := by
    simpa [prefixWord, tailWord_8225017, baseEnd_8225017] using wordTrace_append hprefix tailTrace_8225017
  have hstable : (prefixWord ++ tailWord_8225017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225017).length < 2 ^ (prefixWord ++ tailWord_8225017).sum := by decide
  have hdescent : baseEnd_8225017 < baseStart_8225017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225034 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_8225034 : Nat := 118140960795 + 8225034 * 2 ^ 59
def prefixEnd_8225034 : Nat := 4983230072969 + 3 ^ 40 * 8225034 * 2
def baseEnd_8225034 : Nat := 4223395841572677750348763

theorem tailTrace_8225034 : CollatzResearch.WordTrace tailWord_8225034 prefixEnd_8225034 4223395841572677750348763 := by
  unfold tailWord_8225034
  simp only [CollatzResearch.WordTrace]
  refine ⟨74997908821028504204130539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199994423522742677877681437 74997908821028504204130539)
  ·
    refine ⟨112496863231542756306195809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74997908821028504204130539 112496863231542756306195809)
    ·
      refine ⟨84372647423657067229646857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112496863231542756306195809 84372647423657067229646857)
      ·
        refine ⟨63279485567742800422235143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84372647423657067229646857 63279485567742800422235143)
        ·
          refine ⟨94919228351614200633352715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63279485567742800422235143 94919228351614200633352715)
          ·
            refine ⟨142378842527421300950029073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94919228351614200633352715 142378842527421300950029073)
            ·
              refine ⟨106784131895565975712521805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142378842527421300950029073 106784131895565975712521805)
              ·
                refine ⟨40044049460837240892195677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106784131895565975712521805 40044049460837240892195677)
                ·
                  refine ⟨15016518547813965334573379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40044049460837240892195677 15016518547813965334573379)
                  ·
                    refine ⟨22524777821720948001860069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15016518547813965334573379 22524777821720948001860069)
                    ·
                      refine ⟨4223395841572677750348763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22524777821720948001860069 4223395841572677750348763)
                      ·
                        rfl

theorem cell23_8225034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_8225034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225034 prefixEnd_8225034 := by exact prefixLift 8225034
  have htrace : WordTrace (prefixWord ++ tailWord_8225034) baseStart_8225034 baseEnd_8225034 := by
    simpa [prefixWord, tailWord_8225034, baseEnd_8225034] using wordTrace_append hprefix tailTrace_8225034
  have hstable : (prefixWord ++ tailWord_8225034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225034).length < 2 ^ (prefixWord ++ tailWord_8225034).sum := by decide
  have hdescent : baseEnd_8225034 < baseStart_8225034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225051 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 5, 2, 2]
def baseStart_8225051 : Nat := 118140960795 + 8225051 * 2 ^ 59
def prefixEnd_8225051 : Nat := 4983230072969 + 3 ^ 40 * 8225051 * 2
def baseEnd_8225051 : Nat := 4223404570743804183836185

theorem tailTrace_8225051 : CollatzResearch.WordTrace tailWord_8225051 prefixEnd_8225051 4223404570743804183836185 := by
  unfold tailWord_8225051
  simp only [CollatzResearch.WordTrace]
  refine ⟨299992255325052428719891007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199994836883368285813260671 299992255325052428719891007)
  ·
    refine ⟨449988382987578643079836511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299992255325052428719891007 449988382987578643079836511)
    ·
      refine ⟨674982574481367964619754767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449988382987578643079836511 674982574481367964619754767)
      ·
        refine ⟨1012473861722051946929632151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674982574481367964619754767 1012473861722051946929632151)
        ·
          refine ⟨1518710792583077920394448227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012473861722051946929632151 1518710792583077920394448227)
          ·
            refine ⟨2278066188874616880591672341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518710792583077920394448227 2278066188874616880591672341)
            ·
              refine ⟨106784352603497666277734641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2278066188874616880591672341 106784352603497666277734641)
              ·
                refine ⟨80088264452623249708300981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106784352603497666277734641 80088264452623249708300981)
                ·
                  refine ⟨7508274792433429660153217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80088264452623249708300981 7508274792433429660153217)
                  ·
                    refine ⟨5631206094325072245114913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7508274792433429660153217 5631206094325072245114913)
                    ·
                      refine ⟨4223404570743804183836185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631206094325072245114913 4223404570743804183836185)
                      ·
                        rfl

theorem cell23_8225051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 2, 2].length) (baseStart_8225051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225051 prefixEnd_8225051 := by exact prefixLift 8225051
  have htrace : WordTrace (prefixWord ++ tailWord_8225051) baseStart_8225051 baseEnd_8225051 := by
    simpa [prefixWord, tailWord_8225051, baseEnd_8225051] using wordTrace_append hprefix tailTrace_8225051
  have hstable : (prefixWord ++ tailWord_8225051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225051).length < 2 ^ (prefixWord ++ tailWord_8225051).sum := by decide
  have hdescent : baseEnd_8225051 < baseStart_8225051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225057 : List Nat := [1, 2, 3, 2, 1, 1, 13]
def baseStart_8225057 : Nat := 118140960795 + 8225057 * 2 ^ 59
def prefixEnd_8225057 : Nat := 4983230072969 + 3 ^ 40 * 8225057 * 2
def baseEnd_8225057 : Nat := 52140835205280631609397

theorem tailTrace_8225057 : CollatzResearch.WordTrace tailWord_8225057 prefixEnd_8225057 52140835205280631609397 := by
  unfold tailWord_8225057
  simp only [CollatzResearch.WordTrace]
  refine ⟨299992474163030691744609425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199994982775353794496406283 299992474163030691744609425)
  ·
    refine ⟨224994355622273018808457069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299992474163030691744609425 224994355622273018808457069)
    ·
      refine ⟨84372883358352382053171401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224994355622273018808457069 84372883358352382053171401)
      ·
        refine ⟨63279662518764286539878551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84372883358352382053171401 63279662518764286539878551)
        ·
          refine ⟨94919493778146429809817827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63279662518764286539878551 94919493778146429809817827)
          ·
            refine ⟨142379240667219644714726741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94919493778146429809817827 142379240667219644714726741)
            ·
              refine ⟨52140835205280631609397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 142379240667219644714726741 52140835205280631609397)
              ·
                rfl

theorem cell23_8225057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 13].length) (baseStart_8225057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225057 prefixEnd_8225057 := by exact prefixLift 8225057
  have htrace : WordTrace (prefixWord ++ tailWord_8225057) baseStart_8225057 baseEnd_8225057 := by
    simpa [prefixWord, tailWord_8225057, baseEnd_8225057] using wordTrace_append hprefix tailTrace_8225057
  have hstable : (prefixWord ++ tailWord_8225057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225057).length < 2 ^ (prefixWord ++ tailWord_8225057).sum := by decide
  have hdescent : baseEnd_8225057 < baseStart_8225057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225068 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 3, 2, 2]
def baseStart_8225068 : Nat := 118140960795 + 8225068 * 2 ^ 59
def prefixEnd_8225068 : Nat := 4983230072969 + 3 ^ 40 * 8225068 * 2
def baseEnd_8225068 : Nat := 4223413299914930617323607

theorem tailTrace_8225068 : CollatzResearch.WordTrace tailWord_8225068 prefixEnd_8225068 4223413299914930617323607 := by
  unfold tailWord_8225068
  simp only [CollatzResearch.WordTrace]
  refine ⟨149996437682995420311629929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199995250243993893748839905 149996437682995420311629929)
  ·
    refine ⟨112497328262246565233722447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149996437682995420311629929 112497328262246565233722447)
    ·
      refine ⟨168745992393369847850583671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112497328262246565233722447 168745992393369847850583671)
      ·
        refine ⟨253118988590054771775875507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168745992393369847850583671 253118988590054771775875507)
        ·
          refine ⟨379678482885082157663813261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253118988590054771775875507 379678482885082157663813261)
          ·
            refine ⟨142379431081905809123929973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379678482885082157663813261 142379431081905809123929973)
            ·
              refine ⟨13348071663928669605368435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142379431081905809123929973 13348071663928669605368435)
              ·
                refine ⟨20022107495893004408052653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13348071663928669605368435 20022107495893004408052653)
                ·
                  refine ⟨7508290310959876653019745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20022107495893004408052653 7508290310959876653019745)
                  ·
                    refine ⟨5631217733219907489764809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7508290310959876653019745 5631217733219907489764809)
                    ·
                      refine ⟨4223413299914930617323607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631217733219907489764809 4223413299914930617323607)
                      ·
                        rfl

theorem cell23_8225068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_8225068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225068 prefixEnd_8225068 := by exact prefixLift 8225068
  have htrace : WordTrace (prefixWord ++ tailWord_8225068) baseStart_8225068 baseEnd_8225068 := by
    simpa [prefixWord, tailWord_8225068, baseEnd_8225068] using wordTrace_append hprefix tailTrace_8225068
  have hstable : (prefixWord ++ tailWord_8225068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225068).length < 2 ^ (prefixWord ++ tailWord_8225068).sum := by decide
  have hdescent : baseEnd_8225068 < baseStart_8225068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225124 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_8225124 : Nat := 118140960795 + 8225124 * 2 ^ 59
def prefixEnd_8225124 : Nat := 4983230072969 + 3 ^ 40 * 8225124 * 2
def baseEnd_8225124 : Nat := 4223442054831582398223349

theorem tailTrace_8225124 : CollatzResearch.WordTrace tailWord_8225124 prefixEnd_8225124 4223442054831582398223349 := by
  unfold tailWord_8225124
  simp only [CollatzResearch.WordTrace]
  refine ⟨149997458926893981093649213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199996611902525308124865617 149997458926893981093649213)
  ·
    refine ⟨56249047097585242910118455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149997458926893981093649213 56249047097585242910118455)
    ·
      refine ⟨84373570646377864365177683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56249047097585242910118455 84373570646377864365177683)
      ·
        refine ⟨126560355969566796547766525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84373570646377864365177683 126560355969566796547766525)
        ·
          refine ⟨47460133488587548705412447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126560355969566796547766525 47460133488587548705412447)
          ·
            refine ⟨71190200232881323058118671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47460133488587548705412447 71190200232881323058118671)
            ·
              refine ⟨106785300349321984587178007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71190200232881323058118671 106785300349321984587178007)
              ·
                refine ⟨160177950523982976880767011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106785300349321984587178007 160177950523982976880767011)
                ·
                  refine ⟨240266925785974465321150517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160177950523982976880767011 240266925785974465321150517)
                  ·
                    refine ⟨22525024292435106123857861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 240266925785974465321150517 22525024292435106123857861)
                    ·
                      refine ⟨4223442054831582398223349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22525024292435106123857861 4223442054831582398223349)
                      ·
                        rfl

theorem cell23_8225124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_8225124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225124 prefixEnd_8225124 := by exact prefixLift 8225124
  have htrace : WordTrace (prefixWord ++ tailWord_8225124) baseStart_8225124 baseEnd_8225124 := by
    simpa [prefixWord, tailWord_8225124, baseEnd_8225124] using wordTrace_append hprefix tailTrace_8225124
  have hstable : (prefixWord ++ tailWord_8225124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225124).length < 2 ^ (prefixWord ++ tailWord_8225124).sum := by decide
  have hdescent : baseEnd_8225124 < baseStart_8225124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225128 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_8225128 : Nat := 118140960795 + 8225128 * 2 ^ 59
def prefixEnd_8225128 : Nat := 4983230072969 + 3 ^ 40 * 8225128 * 2
def baseEnd_8225128 : Nat := 4223444108754200382573331

theorem tailTrace_8225128 : CollatzResearch.WordTrace tailWord_8225128 prefixEnd_8225128 4223444108754200382573331 := by
  unfold tailWord_8225128
  simp only [CollatzResearch.WordTrace]
  refine ⟨149997531872886735435222019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199996709163848980580296025 149997531872886735435222019)
  ·
    refine ⟨224996297809330103152833029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149997531872886735435222019 224996297809330103152833029)
    ·
      refine ⟨42186805839249394341156193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224996297809330103152833029 42186805839249394341156193)
      ·
        refine ⟨31640104379437045755867145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42186805839249394341156193 31640104379437045755867145)
        ·
          refine ⟨23730078284577784316900359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31640104379437045755867145 23730078284577784316900359)
          ·
            refine ⟨35595117426866676475350539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23730078284577784316900359 35595117426866676475350539)
            ·
              refine ⟨53392676140300014713025809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35595117426866676475350539 53392676140300014713025809)
              ·
                refine ⟨40044507105225011034769357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53392676140300014713025809 40044507105225011034769357)
                ·
                  refine ⟨15016690164459379138038509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40044507105225011034769357 15016690164459379138038509)
                  ·
                    refine ⟨5631258811672267176764441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15016690164459379138038509 5631258811672267176764441)
                    ·
                      refine ⟨4223444108754200382573331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631258811672267176764441 4223444108754200382573331)
                      ·
                        rfl

theorem cell23_8225128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_8225128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225128 prefixEnd_8225128 := by exact prefixLift 8225128
  have htrace : WordTrace (prefixWord ++ tailWord_8225128) baseStart_8225128 baseEnd_8225128 := by
    simpa [prefixWord, tailWord_8225128, baseEnd_8225128] using wordTrace_append hprefix tailTrace_8225128
  have hstable : (prefixWord ++ tailWord_8225128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225128).length < 2 ^ (prefixWord ++ tailWord_8225128).sum := by decide
  have hdescent : baseEnd_8225128 < baseStart_8225128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225162 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_8225162 : Nat := 118140960795 + 8225162 * 2 ^ 59
def prefixEnd_8225162 : Nat := 4983230072969 + 3 ^ 40 * 8225162 * 2
def baseEnd_8225162 : Nat := 4223461567096453249548175

theorem tailTrace_8225162 : CollatzResearch.WordTrace tailWord_8225162 prefixEnd_8225162 4223461567096453249548175 := by
  unfold tailWord_8225162
  simp only [CollatzResearch.WordTrace]
  refine ⟨74999075956912573669295435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199997535885100196451454493 74999075956912573669295435)
  ·
    refine ⟨112498613935368860503943153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74999075956912573669295435 112498613935368860503943153)
    ·
      refine ⟨84373960451526645377957365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112498613935368860503943153 84373960451526645377957365)
      ·
        refine ⟨7910058792330623004183503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84373960451526645377957365 7910058792330623004183503)
        ·
          refine ⟨11865088188495934506275255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910058792330623004183503 11865088188495934506275255)
          ·
            refine ⟨17797632282743901759412883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11865088188495934506275255 17797632282743901759412883)
            ·
              refine ⟨26696448424115852639119325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17797632282743901759412883 26696448424115852639119325)
              ·
                refine ⟨10011168159043444739669747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26696448424115852639119325 10011168159043444739669747)
                ·
                  refine ⟨15016752238565167109504621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10011168159043444739669747 15016752238565167109504621)
                  ·
                    refine ⟨5631282089461937666064233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15016752238565167109504621 5631282089461937666064233)
                    ·
                      refine ⟨4223461567096453249548175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631282089461937666064233 4223461567096453249548175)
                      ·
                        rfl

theorem cell23_8225162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_8225162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225162 prefixEnd_8225162 := by exact prefixLift 8225162
  have htrace : WordTrace (prefixWord ++ tailWord_8225162) baseStart_8225162 baseEnd_8225162 := by
    simpa [prefixWord, tailWord_8225162, baseEnd_8225162] using wordTrace_append hprefix tailTrace_8225162
  have hstable : (prefixWord ++ tailWord_8225162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225162).length < 2 ^ (prefixWord ++ tailWord_8225162).sum := by decide
  have hdescent : baseEnd_8225162 < baseStart_8225162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225175 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 2, 2, 2]
def baseStart_8225175 : Nat := 118140960795 + 8225175 * 2 ^ 59
def prefixEnd_8225175 : Nat := 4983230072969 + 3 ^ 40 * 8225175 * 2
def baseEnd_8225175 : Nat := 4223468242344961698685615

theorem tailTrace_8225175 : CollatzResearch.WordTrace tailWord_8225175 prefixEnd_8225175 4223468242344961698685615 := by
  unfold tailWord_8225175
  simp only [CollatzResearch.WordTrace]
  refine ⟨299996777976603197897404979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199997851984402131931603319 299996777976603197897404979)
  ·
    refine ⟨449995166964904796846107469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299996777976603197897404979 449995166964904796846107469)
    ·
      refine ⟨168748187611839298817290301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449995166964904796846107469 168748187611839298817290301)
      ·
        refine ⟨63280570354439737056483863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168748187611839298817290301 63280570354439737056483863)
        ·
          refine ⟨94920855531659605584725795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63280570354439737056483863 94920855531659605584725795)
          ·
            refine ⟨142381283297489408377088693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94920855531659605584725795 142381283297489408377088693)
            ·
              refine ⟨13348245309139632035352065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142381283297489408377088693 13348245309139632035352065)
              ·
                refine ⟨10011183981854724026514049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13348245309139632035352065 10011183981854724026514049)
                ·
                  refine ⟨7508387986391043019885537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10011183981854724026514049 7508387986391043019885537)
                  ·
                    refine ⟨5631290989793282264914153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7508387986391043019885537 5631290989793282264914153)
                    ·
                      refine ⟨4223468242344961698685615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631290989793282264914153 4223468242344961698685615)
                      ·
                        rfl

theorem cell23_8225175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_8225175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225175 prefixEnd_8225175 := by exact prefixLift 8225175
  have htrace : WordTrace (prefixWord ++ tailWord_8225175) baseStart_8225175 baseEnd_8225175 := by
    simpa [prefixWord, tailWord_8225175, baseEnd_8225175] using wordTrace_append hprefix tailTrace_8225175
  have hstable : (prefixWord ++ tailWord_8225175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225175).length < 2 ^ (prefixWord ++ tailWord_8225175).sum := by decide
  have hdescent : baseEnd_8225175 < baseStart_8225175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225192 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_8225192 : Nat := 118140960795 + 8225192 * 2 ^ 59
def prefixEnd_8225192 : Nat := 4983230072969 + 3 ^ 40 * 8225192 * 2
def baseEnd_8225192 : Nat := 4223476971516088132173037

theorem tailTrace_8225192 : CollatzResearch.WordTrace tailWord_8225192 prefixEnd_8225192 4223476971516088132173037 := by
  unfold tailWord_8225192
  simp only [CollatzResearch.WordTrace]
  refine ⟨149998699008770804900386915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199998265345027739867182553 149998699008770804900386915)
  ·
    refine ⟨224998048513156207350580373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149998699008770804900386915 224998048513156207350580373)
    ·
      refine ⟨10546783524054197219558455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224998048513156207350580373 10546783524054197219558455)
      ·
        refine ⟨15820175286081295829337683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10546783524054197219558455 15820175286081295829337683)
        ·
          refine ⟨23730262929121943744006525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15820175286081295829337683 23730262929121943744006525)
          ·
            refine ⟨8898848598420728904002447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23730262929121943744006525 8898848598420728904002447)
            ·
              refine ⟨13348272897631093356003671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8898848598420728904002447 13348272897631093356003671)
              ·
                refine ⟨20022409346446640034005507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13348272897631093356003671 20022409346446640034005507)
                ·
                  refine ⟨30033614019669960051008261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20022409346446640034005507 30033614019669960051008261)
                  ·
                    refine ⟨5631302628688117509564049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30033614019669960051008261 5631302628688117509564049)
                    ·
                      refine ⟨4223476971516088132173037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631302628688117509564049 4223476971516088132173037)
                      ·
                        rfl

theorem cell23_8225192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_8225192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225192 prefixEnd_8225192 := by exact prefixLift 8225192
  have htrace : WordTrace (prefixWord ++ tailWord_8225192) baseStart_8225192 baseEnd_8225192 := by
    simpa [prefixWord, tailWord_8225192, baseEnd_8225192] using wordTrace_append hprefix tailTrace_8225192
  have hstable : (prefixWord ++ tailWord_8225192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225192).length < 2 ^ (prefixWord ++ tailWord_8225192).sum := by decide
  have hdescent : baseEnd_8225192 < baseStart_8225192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225228 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_8225228 : Nat := 118140960795 + 8225228 * 2 ^ 59
def prefixEnd_8225228 : Nat := 4983230072969 + 3 ^ 40 * 8225228 * 2
def baseEnd_8225228 : Nat := 1407831818939883330440957

theorem tailTrace_8225228 : CollatzResearch.WordTrace tailWord_8225228 prefixEnd_8225228 1407831818939883330440957 := by
  unfold tailWord_8225228
  simp only [CollatzResearch.WordTrace]
  refine ⟨149999355522705593974542169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199999140696940791966056225 149999355522705593974542169)
  ·
    refine ⟨112499516642029195480906627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149999355522705593974542169 112499516642029195480906627)
    ·
      refine ⟨168749274963043793221359941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112499516642029195480906627 168749274963043793221359941)
      ·
        refine ⟨31640489055570711229004989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168749274963043793221359941 31640489055570711229004989)
        ·
          refine ⟨11865183395839016710876871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31640489055570711229004989 11865183395839016710876871)
          ·
            refine ⟨17797775093758525066315307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11865183395839016710876871 17797775093758525066315307)
            ·
              refine ⟨26696662640637787599472961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17797775093758525066315307 26696662640637787599472961)
              ·
                refine ⟨20022496980478340699604721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26696662640637787599472961 20022496980478340699604721)
                ·
                  refine ⟨15016872735358755524703541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20022496980478340699604721 15016872735358755524703541)
                  ·
                    refine ⟨1407831818939883330440957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15016872735358755524703541 1407831818939883330440957)
                    ·
                      rfl

theorem cell23_8225228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_8225228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225228 prefixEnd_8225228 := by exact prefixLift 8225228
  have htrace : WordTrace (prefixWord ++ tailWord_8225228) baseStart_8225228 baseEnd_8225228 := by
    simpa [prefixWord, tailWord_8225228, baseEnd_8225228] using wordTrace_append hprefix tailTrace_8225228
  have hstable : (prefixWord ++ tailWord_8225228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225228).length < 2 ^ (prefixWord ++ tailWord_8225228).sum := by decide
  have hdescent : baseEnd_8225228 < baseStart_8225228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225238 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_8225238 : Nat := 118140960795 + 8225238 * 2 ^ 59
def prefixEnd_8225238 : Nat := 4983230072969 + 3 ^ 40 * 8225238 * 2
def baseEnd_8225238 : Nat := 4223500591626194952197825

theorem tailTrace_8225238 : CollatzResearch.WordTrace tailWord_8225238 prefixEnd_8225238 4223500591626194952197825 := by
  unfold tailWord_8225238
  simp only [CollatzResearch.WordTrace]
  refine ⟨18749942235960934978559273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199999383850249973104632245 18749942235960934978559273)
  ·
    refine ⟨14062456676970701233919455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18749942235960934978559273 14062456676970701233919455)
    ·
      refine ⟨21093685015456051850879183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14062456676970701233919455 21093685015456051850879183)
      ·
        refine ⟨31640527523184077776318775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21093685015456051850879183 31640527523184077776318775)
        ·
          refine ⟨47460791284776116664478163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31640527523184077776318775 47460791284776116664478163)
          ·
            refine ⟨71191186927164174996717245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47460791284776116664478163 71191186927164174996717245)
            ·
              refine ⟨26696695097686565623768967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71191186927164174996717245 26696695097686565623768967)
              ·
                refine ⟨40045042646529848435653451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26696695097686565623768967 40045042646529848435653451)
                ·
                  refine ⟨60067563969794772653480177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40045042646529848435653451 60067563969794772653480177)
                  ·
                    refine ⟨45050672977346079490110133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60067563969794772653480177 45050672977346079490110133)
                    ·
                      refine ⟨4223500591626194952197825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45050672977346079490110133 4223500591626194952197825)
                      ·
                        rfl

theorem cell23_8225238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_8225238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225238 prefixEnd_8225238 := by exact prefixLift 8225238
  have htrace : WordTrace (prefixWord ++ tailWord_8225238) baseStart_8225238 baseEnd_8225238 := by
    simpa [prefixWord, tailWord_8225238, baseEnd_8225238] using wordTrace_append hprefix tailTrace_8225238
  have hstable : (prefixWord ++ tailWord_8225238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225238).length < 2 ^ (prefixWord ++ tailWord_8225238).sum := by decide
  have hdescent : baseEnd_8225238 < baseStart_8225238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225292 : List Nat := [2, 2, 1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_8225292 : Nat := 118140960795 + 8225292 * 2 ^ 59
def prefixEnd_8225292 : Nat := 4983230072969 + 3 ^ 40 * 8225292 * 2
def baseEnd_8225292 : Nat := 1407842773193845913640859

theorem tailTrace_8225292 : CollatzResearch.WordTrace tailWord_8225292 prefixEnd_8225292 1407842773193845913640859 := by
  unfold tailWord_8225292
  simp only [CollatzResearch.WordTrace]
  refine ⟨150000522658589663439707065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200000696878119551252942753 150000522658589663439707065)
  ·
    refine ⟨112500391993942247579780299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150000522658589663439707065 112500391993942247579780299)
    ·
      refine ⟨168750587990913371369670449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112500391993942247579780299 168750587990913371369670449)
      ·
        refine ⟨126562940993185028527252837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168750587990913371369670449 126562940993185028527252837)
        ·
          refine ⟨23730551436222192848859907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126562940993185028527252837 23730551436222192848859907)
          ·
            refine ⟨35595827154333289273289861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23730551436222192848859907 35595827154333289273289861)
            ·
              refine ⟨6674217591437491738741849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35595827154333289273289861 6674217591437491738741849)
              ·
                refine ⟨5005663193578118804056387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6674217591437491738741849 5005663193578118804056387)
                ·
                  refine ⟨7508494790367178206084581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005663193578118804056387 7508494790367178206084581)
                  ·
                    refine ⟨1407842773193845913640859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7508494790367178206084581 1407842773193845913640859)
                    ·
                      rfl

theorem cell23_8225292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_8225292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225292 prefixEnd_8225292 := by exact prefixLift 8225292
  have htrace : WordTrace (prefixWord ++ tailWord_8225292) baseStart_8225292 baseEnd_8225292 := by
    simpa [prefixWord, tailWord_8225292, baseEnd_8225292] using wordTrace_append hprefix tailTrace_8225292
  have hstable : (prefixWord ++ tailWord_8225292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225292).length < 2 ^ (prefixWord ++ tailWord_8225292).sum := by decide
  have hdescent : baseEnd_8225292 < baseStart_8225292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225301 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_8225301 : Nat := 118140960795 + 8225301 * 2 ^ 59
def prefixEnd_8225301 : Nat := 4983230072969 + 3 ^ 40 * 8225301 * 2
def baseEnd_8225301 : Nat := 1407844313635809401903345

theorem tailTrace_8225301 : CollatzResearch.WordTrace tailWord_8225301 prefixEnd_8225301 1407844313635809401903345 := by
  unfold tailWord_8225301
  simp only [CollatzResearch.WordTrace]
  refine ⟨300001373574146721416491757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200000915716097814277661171 300001373574146721416491757)
  ·
    refine ⟨112500515090305020531184409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300001373574146721416491757 112500515090305020531184409)
    ·
      refine ⟨84375386317728765398388307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112500515090305020531184409 84375386317728765398388307)
      ·
        refine ⟨126563079476593148097582461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84375386317728765398388307 126563079476593148097582461)
        ·
          refine ⟨47461154803722430536593423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126563079476593148097582461 47461154803722430536593423)
          ·
            refine ⟨71191732205583645804890135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47461154803722430536593423 71191732205583645804890135)
            ·
              refine ⟨106787598308375468707335203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71191732205583645804890135 106787598308375468707335203)
              ·
                refine ⟨160181397462563203061002805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106787598308375468707335203 160181397462563203061002805)
                ·
                  refine ⟨15017006012115300286969013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160181397462563203061002805 15017006012115300286969013)
                  ·
                    refine ⟨1407844313635809401903345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15017006012115300286969013 1407844313635809401903345)
                    ·
                      rfl

theorem cell23_8225301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_8225301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225301 prefixEnd_8225301 := by exact prefixLift 8225301
  have htrace : WordTrace (prefixWord ++ tailWord_8225301) baseStart_8225301 baseEnd_8225301 := by
    simpa [prefixWord, tailWord_8225301, baseEnd_8225301] using wordTrace_append hprefix tailTrace_8225301
  have hstable : (prefixWord ++ tailWord_8225301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225301).length < 2 ^ (prefixWord ++ tailWord_8225301).sum := by decide
  have hdescent : baseEnd_8225301 < baseStart_8225301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225315 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 3]
def baseStart_8225315 : Nat := 118140960795 + 8225315 * 2 ^ 59
def prefixEnd_8225315 : Nat := 4983230072969 + 3 ^ 40 * 8225315 * 2
def baseEnd_8225315 : Nat := 4223540129636591150934971

theorem tailTrace_8225315 : CollatzResearch.WordTrace tailWord_8225315 prefixEnd_8225315 4223540129636591150934971 := by
  unfold tailWord_8225315
  simp only [CollatzResearch.WordTrace]
  refine ⟨300001884196096001807501399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200001256130730667871667599 300001884196096001807501399)
  ·
    refine ⟨450002826294144002711252099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300001884196096001807501399 450002826294144002711252099)
    ·
      refine ⟨675004239441216004066878149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450002826294144002711252099 675004239441216004066878149)
      ·
        refine ⟨126563294895228000762539653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 675004239441216004066878149 126563294895228000762539653)
        ·
          refine ⟨23730617792855250142976185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126563294895228000762539653 23730617792855250142976185)
          ·
            refine ⟨17797963344641437607232139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23730617792855250142976185 17797963344641437607232139)
            ·
              refine ⟨26696945016962156410848209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17797963344641437607232139 26696945016962156410848209)
              ·
                refine ⟨20022708762721617308136157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26696945016962156410848209 20022708762721617308136157)
                ·
                  refine ⟨7508515786020606490551059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20022708762721617308136157 7508515786020606490551059)
                  ·
                    refine ⟨11262773679030909735826589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7508515786020606490551059 11262773679030909735826589)
                    ·
                      refine ⟨4223540129636591150934971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11262773679030909735826589 4223540129636591150934971)
                      ·
                        rfl

theorem cell23_8225315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_8225315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225315 prefixEnd_8225315 := by exact prefixLift 8225315
  have htrace : WordTrace (prefixWord ++ tailWord_8225315) baseStart_8225315 baseEnd_8225315 := by
    simpa [prefixWord, tailWord_8225315, baseEnd_8225315] using wordTrace_append hprefix tailTrace_8225315
  have hstable : (prefixWord ++ tailWord_8225315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225315).length < 2 ^ (prefixWord ++ tailWord_8225315).sum := by decide
  have hdescent : baseEnd_8225315 < baseStart_8225315 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225319 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_8225319 : Nat := 118140960795 + 8225319 * 2 ^ 59
def prefixEnd_8225319 : Nat := 4983230072969 + 3 ^ 40 * 8225319 * 2
def baseEnd_8225319 : Nat := 4223542183559209135284953

theorem tailTrace_8225319 : CollatzResearch.WordTrace tailWord_8225319 prefixEnd_8225319 4223542183559209135284953 := by
  unfold tailWord_8225319
  simp only [CollatzResearch.WordTrace]
  refine ⟨300002030088081510490647011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200001353392054340327098007 300002030088081510490647011)
  ·
    refine ⟨450003045132122265735970517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300002030088081510490647011 450003045132122265735970517)
    ·
      refine ⟨10546946370284115603186809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 450003045132122265735970517 10546946370284115603186809)
      ·
        refine ⟨7910209777713086702390107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10546946370284115603186809 7910209777713086702390107)
        ·
          refine ⟨11865314666569630053585161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910209777713086702390107 11865314666569630053585161)
          ·
            refine ⟨8898985999927222540188871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11865314666569630053585161 8898985999927222540188871)
            ·
              refine ⟨13348478999890833810283307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8898985999927222540188871 13348478999890833810283307)
              ·
                refine ⟨20022718499836250715424961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13348478999890833810283307 20022718499836250715424961)
                ·
                  refine ⟨15017038874877188036568721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20022718499836250715424961 15017038874877188036568721)
                  ·
                    refine ⟨11262779156157891027426541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15017038874877188036568721 11262779156157891027426541)
                    ·
                      refine ⟨4223542183559209135284953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11262779156157891027426541 4223542183559209135284953)
                      ·
                        rfl

theorem cell23_8225319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_8225319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225319 prefixEnd_8225319 := by exact prefixLift 8225319
  have htrace : WordTrace (prefixWord ++ tailWord_8225319) baseStart_8225319 baseEnd_8225319 := by
    simpa [prefixWord, tailWord_8225319, baseEnd_8225319] using wordTrace_append hprefix tailTrace_8225319
  have hstable : (prefixWord ++ tailWord_8225319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225319).length < 2 ^ (prefixWord ++ tailWord_8225319).sum := by decide
  have hdescent : baseEnd_8225319 < baseStart_8225319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225331 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 1, 6]
def baseStart_8225331 : Nat := 118140960795 + 8225331 * 2 ^ 59
def prefixEnd_8225331 : Nat := 4983230072969 + 3 ^ 40 * 8225331 * 2
def baseEnd_8225331 : Nat := 1407849448442354362778299

theorem tailTrace_8225331 : CollatzResearch.WordTrace tailWord_8225331 prefixEnd_8225331 1407849448442354362778299 := by
  unfold tailWord_8225331
  simp only [CollatzResearch.WordTrace]
  refine ⟨300002467764038036540083847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200001645176025357693389231 300002467764038036540083847)
  ·
    refine ⟨450003701646057054810125771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300002467764038036540083847 450003701646057054810125771)
    ·
      refine ⟨675005552469085582215188657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450003701646057054810125771 675005552469085582215188657)
      ·
        refine ⟨506254164351814186661391493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675005552469085582215188657 506254164351814186661391493)
        ·
          refine ⟨94922655815965159999010905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 506254164351814186661391493 94922655815965159999010905)
          ·
            refine ⟨71191991861973869999258179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94922655815965159999010905 71191991861973869999258179)
            ·
              refine ⟨106787987792960804998887269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71191991861973869999258179 106787987792960804998887269)
              ·
                refine ⟨20022747711180150937291363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106787987792960804998887269 20022747711180150937291363)
                ·
                  refine ⟨30034121566770226405937045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20022747711180150937291363 30034121566770226405937045)
                  ·
                    refine ⟨1407849448442354362778299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30034121566770226405937045 1407849448442354362778299)
                    ·
                      rfl

theorem cell23_8225331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 6].length) (baseStart_8225331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225331 prefixEnd_8225331 := by exact prefixLift 8225331
  have htrace : WordTrace (prefixWord ++ tailWord_8225331) baseStart_8225331 baseEnd_8225331 := by
    simpa [prefixWord, tailWord_8225331, baseEnd_8225331] using wordTrace_append hprefix tailTrace_8225331
  have hstable : (prefixWord ++ tailWord_8225331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225331).length < 2 ^ (prefixWord ++ tailWord_8225331).sum := by decide
  have hdescent : baseEnd_8225331 < baseStart_8225331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225355 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 3, 2, 2]
def baseStart_8225355 : Nat := 118140960795 + 8225355 * 2 ^ 59
def prefixEnd_8225355 : Nat := 4983230072969 + 3 ^ 40 * 8225355 * 2
def baseEnd_8225355 : Nat := 4223560668862770994434787

theorem tailTrace_8225355 : CollatzResearch.WordTrace tailWord_8225355 prefixEnd_8225355 4223560668862770994434787 := by
  unfold tailWord_8225355
  simp only [CollatzResearch.WordTrace]
  refine ⟨300003343115951088638957519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200002228743967392425971679 300003343115951088638957519)
  ·
    refine ⟨450005014673926632958436279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300003343115951088638957519 450005014673926632958436279)
    ·
      refine ⟨675007522010889949437654419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450005014673926632958436279 675007522010889949437654419)
      ·
        refine ⟨1012511283016334924156481629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675007522010889949437654419 1012511283016334924156481629)
        ·
          refine ⟨379691731131125596558680611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1012511283016334924156481629 379691731131125596558680611)
          ·
            refine ⟨569537596696688394838020917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379691731131125596558680611 569537596696688394838020917)
            ·
              refine ⟨53394149690314537016064461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 569537596696688394838020917 53394149690314537016064461)
              ·
                refine ⟨20022806133867951381024173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53394149690314537016064461 20022806133867951381024173)
                ·
                  refine ⟨7508552300200481767884065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20022806133867951381024173 7508552300200481767884065)
                  ·
                    refine ⟨5631414225150361325913049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7508552300200481767884065 5631414225150361325913049)
                    ·
                      refine ⟨4223560668862770994434787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631414225150361325913049 4223560668862770994434787)
                      ·
                        rfl

theorem cell23_8225355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 2, 2].length) (baseStart_8225355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225355 prefixEnd_8225355 := by exact prefixLift 8225355
  have htrace : WordTrace (prefixWord ++ tailWord_8225355) baseStart_8225355 baseEnd_8225355 := by
    simpa [prefixWord, tailWord_8225355, baseEnd_8225355] using wordTrace_append hprefix tailTrace_8225355
  have hstable : (prefixWord ++ tailWord_8225355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225355).length < 2 ^ (prefixWord ++ tailWord_8225355).sum := by decide
  have hdescent : baseEnd_8225355 < baseStart_8225355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225358 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_8225358 : Nat := 118140960795 + 8225358 * 2 ^ 59
def prefixEnd_8225358 : Nat := 4983230072969 + 3 ^ 40 * 8225358 * 2
def baseEnd_8225358 : Nat := 4223562209304734482697273

theorem tailTrace_8225358 : CollatzResearch.WordTrace tailWord_8225358 prefixEnd_8225358 4223562209304734482697273 := by
  unfold tailWord_8225358
  simp only [CollatzResearch.WordTrace]
  refine ⟨37500431566867527518914591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200002301689960146767544485 37500431566867527518914591)
  ·
    refine ⟨56250647350301291278371887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37500431566867527518914591 56250647350301291278371887)
    ·
      refine ⟨84375971025451936917557831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56250647350301291278371887 84375971025451936917557831)
      ·
        refine ⟨126563956538177905376336747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84375971025451936917557831 126563956538177905376336747)
        ·
          refine ⟨189845934807266858064505121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126563956538177905376336747 189845934807266858064505121)
          ·
            refine ⟨142384451105450143548378841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189845934807266858064505121 142384451105450143548378841)
            ·
              refine ⟨106788338329087607661284131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142384451105450143548378841 106788338329087607661284131)
              ·
                refine ⟨160182507493631411491926197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106788338329087607661284131 160182507493631411491926197)
                ·
                  refine ⟨15017110077527944827368081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160182507493631411491926197 15017110077527944827368081)
                  ·
                    refine ⟨11262832558145958620526061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15017110077527944827368081 11262832558145958620526061)
                    ·
                      refine ⟨4223562209304734482697273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11262832558145958620526061 4223562209304734482697273)
                      ·
                        rfl

theorem cell23_8225358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_8225358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225358 prefixEnd_8225358 := by exact prefixLift 8225358
  have htrace : WordTrace (prefixWord ++ tailWord_8225358) baseStart_8225358 baseEnd_8225358 := by
    simpa [prefixWord, tailWord_8225358, baseEnd_8225358] using wordTrace_append hprefix tailTrace_8225358
  have hstable : (prefixWord ++ tailWord_8225358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225358).length < 2 ^ (prefixWord ++ tailWord_8225358).sum := by decide
  have hdescent : baseEnd_8225358 < baseStart_8225358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225368 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_8225368 : Nat := 118140960795 + 8225368 * 2 ^ 59
def prefixEnd_8225368 : Nat := 4983230072969 + 3 ^ 40 * 8225368 * 2
def baseEnd_8225368 : Nat := 4223567344111279443572227

theorem tailTrace_8225368 : CollatzResearch.WordTrace tailWord_8225368 prefixEnd_8225368 4223567344111279443572227 := by
  unfold tailWord_8225368
  simp only [CollatzResearch.WordTrace]
  refine ⟨150001908632451995929590379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200002544843269327906120505 150001908632451995929590379)
  ·
    refine ⟨225002862948677993894385569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150001908632451995929590379 225002862948677993894385569)
    ·
      refine ⟨168752147211508495420789177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225002862948677993894385569 168752147211508495420789177)
      ·
        refine ⟨126564110408631371565591883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168752147211508495420789177 126564110408631371565591883)
        ·
          refine ⟨189846165612947057348387825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126564110408631371565591883 189846165612947057348387825)
          ·
            refine ⟨142384624209710293011290869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189846165612947057348387825 142384624209710293011290869)
            ·
              refine ⟨13348558519660339969808519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142384624209710293011290869 13348558519660339969808519)
              ·
                refine ⟨20022837779490509954712779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13348558519660339969808519 20022837779490509954712779)
                ·
                  refine ⟨30034256669235764932069169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20022837779490509954712779 30034256669235764932069169)
                  ·
                    refine ⟨22525692501926823699051877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30034256669235764932069169 22525692501926823699051877)
                    ·
                      refine ⟨4223567344111279443572227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22525692501926823699051877 4223567344111279443572227)
                      ·
                        rfl

theorem cell23_8225368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_8225368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225368 prefixEnd_8225368 := by exact prefixLift 8225368
  have htrace : WordTrace (prefixWord ++ tailWord_8225368) baseStart_8225368 baseEnd_8225368 := by
    simpa [prefixWord, tailWord_8225368, baseEnd_8225368] using wordTrace_append hprefix tailTrace_8225368
  have hstable : (prefixWord ++ tailWord_8225368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225368).length < 2 ^ (prefixWord ++ tailWord_8225368).sum := by decide
  have hdescent : baseEnd_8225368 < baseStart_8225368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225372 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_8225372 : Nat := 118140960795 + 8225372 * 2 ^ 59
def prefixEnd_8225372 : Nat := 4983230072969 + 3 ^ 40 * 8225372 * 2
def baseEnd_8225372 : Nat := 4223569398033897427922209

theorem tailTrace_8225372 : CollatzResearch.WordTrace tailWord_8225372 prefixEnd_8225372 4223569398033897427922209 := by
  unfold tailWord_8225372
  simp only [CollatzResearch.WordTrace]
  refine ⟨150001981578444750271163185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200002642104593000361550913 150001981578444750271163185)
  ·
    refine ⟨112501486183833562703372389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150001981578444750271163185 112501486183833562703372389)
    ·
      refine ⟨21094028659468793006882323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112501486183833562703372389 21094028659468793006882323)
      ·
        refine ⟨31641042989203189510323485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21094028659468793006882323 31641042989203189510323485)
        ·
          refine ⟨11865391120951196066371307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31641042989203189510323485 11865391120951196066371307)
          ·
            refine ⟨17798086681426794099556961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11865391120951196066371307 17798086681426794099556961)
            ·
              refine ⟨13348565011070095574667721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17798086681426794099556961 13348565011070095574667721)
              ·
                refine ⟨10011423758302571681000791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13348565011070095574667721 10011423758302571681000791)
                ·
                  refine ⟨15017135637453857521501187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10011423758302571681000791 15017135637453857521501187)
                  ·
                    refine ⟨22525703456180786282251781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15017135637453857521501187 22525703456180786282251781)
                    ·
                      refine ⟨4223569398033897427922209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22525703456180786282251781 4223569398033897427922209)
                      ·
                        rfl

theorem cell23_8225372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_8225372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225372 prefixEnd_8225372 := by exact prefixLift 8225372
  have htrace : WordTrace (prefixWord ++ tailWord_8225372) baseStart_8225372 baseEnd_8225372 := by
    simpa [prefixWord, tailWord_8225372, baseEnd_8225372] using wordTrace_append hprefix tailTrace_8225372
  have hstable : (prefixWord ++ tailWord_8225372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225372).length < 2 ^ (prefixWord ++ tailWord_8225372).sum := by decide
  have hdescent : baseEnd_8225372 < baseStart_8225372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225388 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_8225388 : Nat := 118140960795 + 8225388 * 2 ^ 59
def prefixEnd_8225388 : Nat := 4983230072969 + 3 ^ 40 * 8225388 * 2
def baseEnd_8225388 : Nat := 4223577613724369365322135

theorem tailTrace_8225388 : CollatzResearch.WordTrace tailWord_8225388 prefixEnd_8225388 4223577613724369365322135 := by
  unfold tailWord_8225388
  simp only [CollatzResearch.WordTrace]
  refine ⟨150002273362415767637454409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200003031149887690183272545 150002273362415767637454409)
  ·
    refine ⟨112501705021811825728090807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150002273362415767637454409 112501705021811825728090807)
    ·
      refine ⟨168752557532717738592136211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112501705021811825728090807 168752557532717738592136211)
      ·
        refine ⟨253128836299076607888204317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168752557532717738592136211 253128836299076607888204317)
        ·
          refine ⟨94923313612153727958076619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253128836299076607888204317 94923313612153727958076619)
          ·
            refine ⟨142384970418230591937114929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94923313612153727958076619 142384970418230591937114929)
            ·
              refine ⟨106788727813672943952836197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142384970418230591937114929 106788727813672943952836197)
              ·
                refine ⟨20022886465063676991156787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106788727813672943952836197 20022886465063676991156787)
                ·
                  refine ⟨30034329697595515486735181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20022886465063676991156787 30034329697595515486735181)
                  ·
                    refine ⟨11262873636598318307525693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30034329697595515486735181 11262873636598318307525693)
                    ·
                      refine ⟨4223577613724369365322135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11262873636598318307525693 4223577613724369365322135)
                      ·
                        rfl

theorem cell23_8225388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_8225388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225388 prefixEnd_8225388 := by exact prefixLift 8225388
  have htrace : WordTrace (prefixWord ++ tailWord_8225388) baseStart_8225388 baseEnd_8225388 := by
    simpa [prefixWord, tailWord_8225388, baseEnd_8225388] using wordTrace_append hprefix tailTrace_8225388
  have hstable : (prefixWord ++ tailWord_8225388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225388).length < 2 ^ (prefixWord ++ tailWord_8225388).sum := by decide
  have hdescent : baseEnd_8225388 < baseStart_8225388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225415 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_8225415 : Nat := 118140960795 + 8225415 * 2 ^ 59
def prefixEnd_8225415 : Nat := 4983230072969 + 3 ^ 40 * 8225415 * 2
def baseEnd_8225415 : Nat := 4223591477702040759684511

theorem tailTrace_8225415 : CollatzResearch.WordTrace tailWord_8225415 prefixEnd_8225415 4223591477702040759684511 := by
  unfold tailWord_8225415
  simp only [CollatzResearch.WordTrace]
  refine ⟨300005531495733718886141699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200003687663822479257427799 300005531495733718886141699)
  ·
    refine ⟨450008297243600578329212549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300005531495733718886141699 450008297243600578329212549)
    ·
      refine ⟨84376555733175108436727353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450008297243600578329212549 84376555733175108436727353)
      ·
        refine ⟨63282416799881331327545515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84376555733175108436727353 63282416799881331327545515)
        ·
          refine ⟨94923625199821996991318273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63282416799881331327545515 94923625199821996991318273)
          ·
            refine ⟨71192718899866497743488705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94923625199821996991318273 71192718899866497743488705)
            ·
              refine ⟨53394539174899873307616529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71192718899866497743488705 53394539174899873307616529)
              ·
                refine ⟨40045904381174904980712397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53394539174899873307616529 40045904381174904980712397)
                ·
                  refine ⟨15017214142940589367767149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40045904381174904980712397 15017214142940589367767149)
                  ·
                    refine ⟨5631455303602721012912681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15017214142940589367767149 5631455303602721012912681)
                    ·
                      refine ⟨4223591477702040759684511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631455303602721012912681 4223591477702040759684511)
                      ·
                        rfl

theorem cell23_8225415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_8225415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225415 prefixEnd_8225415 := by exact prefixLift 8225415
  have htrace : WordTrace (prefixWord ++ tailWord_8225415) baseStart_8225415 baseEnd_8225415 := by
    simpa [prefixWord, tailWord_8225415, baseEnd_8225415] using wordTrace_append hprefix tailTrace_8225415
  have hstable : (prefixWord ++ tailWord_8225415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225415).length < 2 ^ (prefixWord ++ tailWord_8225415).sum := by decide
  have hdescent : baseEnd_8225415 < baseStart_8225415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225422 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_8225422 : Nat := 118140960795 + 8225422 * 2 ^ 59
def prefixEnd_8225422 : Nat := 4983230072969 + 3 ^ 40 * 8225422 * 2
def baseEnd_8225422 : Nat := 4223595072066622232296979

theorem tailTrace_8225422 : CollatzResearch.WordTrace tailWord_8225422 prefixEnd_8225422 4223595072066622232296979 := by
  unfold tailWord_8225422
  simp only [CollatzResearch.WordTrace]
  refine ⟨37500723350838544885205815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200003857871138906054431013 37500723350838544885205815)
  ·
    refine ⟨56251085026257817327808723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37500723350838544885205815 56251085026257817327808723)
    ·
      refine ⟨84376627539386725991713085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56251085026257817327808723 84376627539386725991713085)
      ·
        refine ⟨31641235327270022246892407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84376627539386725991713085 31641235327270022246892407)
        ·
          refine ⟨47461852990905033370338611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31641235327270022246892407 47461852990905033370338611)
          ·
            refine ⟨71192779486357550055507917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47461852990905033370338611 71192779486357550055507917)
            ·
              refine ⟨26697292307384081270815469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71192779486357550055507917 26697292307384081270815469)
              ·
                refine ⟨10011484615269030476555801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26697292307384081270815469 10011484615269030476555801)
                ·
                  refine ⟨7508613461451772857416851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10011484615269030476555801 7508613461451772857416851)
                  ·
                    refine ⟨11262920192177659286125277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7508613461451772857416851 11262920192177659286125277)
                    ·
                      refine ⟨4223595072066622232296979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11262920192177659286125277 4223595072066622232296979)
                      ·
                        rfl

theorem cell23_8225422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_8225422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225422 prefixEnd_8225422 := by exact prefixLift 8225422
  have htrace : WordTrace (prefixWord ++ tailWord_8225422) baseStart_8225422 baseEnd_8225422 := by
    simpa [prefixWord, tailWord_8225422, baseEnd_8225422] using wordTrace_append hprefix tailTrace_8225422
  have hstable : (prefixWord ++ tailWord_8225422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225422).length < 2 ^ (prefixWord ++ tailWord_8225422).sum := by decide
  have hdescent : baseEnd_8225422 < baseStart_8225422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225458 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_8225458 : Nat := 118140960795 + 8225458 * 2 ^ 59
def prefixEnd_8225458 : Nat := 4983230072969 + 3 ^ 40 * 8225458 * 2
def baseEnd_8225458 : Nat := 4223613557370184091446813

theorem tailTrace_8225458 : CollatzResearch.WordTrace tailWord_8225458 prefixEnd_8225458 4223613557370184091446813 := by
  unfold tailWord_8225458
  simp only [CollatzResearch.WordTrace]
  refine ⟨75001774958644484307489257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200004733223051958153304685 75001774958644484307489257)
  ·
    refine ⟨56251331218983363230616943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75001774958644484307489257 56251331218983363230616943)
    ·
      refine ⟨84376996828475044845925415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56251331218983363230616943 84376996828475044845925415)
      ·
        refine ⟨126565495242712567268888123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84376996828475044845925415 126565495242712567268888123)
        ·
          refine ⟨189848242864068850903332185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126565495242712567268888123 189848242864068850903332185)
          ·
            refine ⟨142386182148051638177499139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189848242864068850903332185 142386182148051638177499139)
            ·
              refine ⟨213579273222077457266248709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142386182148051638177499139 213579273222077457266248709)
              ·
                refine ⟨40046113729139523237421633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213579273222077457266248709 40046113729139523237421633)
                ·
                  refine ⟨30034585296854642428066225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40046113729139523237421633 30034585296854642428066225)
                  ·
                    refine ⟨22525938972640981821049669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30034585296854642428066225 22525938972640981821049669)
                    ·
                      refine ⟨4223613557370184091446813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22525938972640981821049669 4223613557370184091446813)
                      ·
                        rfl

theorem cell23_8225458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_8225458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225458 prefixEnd_8225458 := by exact prefixLift 8225458
  have htrace : WordTrace (prefixWord ++ tailWord_8225458) baseStart_8225458 baseEnd_8225458 := by
    simpa [prefixWord, tailWord_8225458, baseEnd_8225458] using wordTrace_append hprefix tailTrace_8225458
  have hstable : (prefixWord ++ tailWord_8225458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225458).length < 2 ^ (prefixWord ++ tailWord_8225458).sum := by decide
  have hdescent : baseEnd_8225458 < baseStart_8225458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225468 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 7]
def baseStart_8225468 : Nat := 118140960795 + 8225468 * 2 ^ 59
def prefixEnd_8225468 : Nat := 4983230072969 + 3 ^ 40 * 8225468 * 2
def baseEnd_8225468 : Nat := 469290965797414339146863

theorem tailTrace_8225468 : CollatzResearch.WordTrace tailWord_8225468 prefixEnd_8225468 469290965797414339146863 := by
  unfold tailWord_8225468
  simp only [CollatzResearch.WordTrace]
  refine ⟨150003732282270854468910529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200004976376361139291880705 150003732282270854468910529)
  ·
    refine ⟨112502799211703140851682897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150003732282270854468910529 112502799211703140851682897)
    ·
      refine ⟨84377099408777355638762173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112502799211703140851682897 84377099408777355638762173)
      ·
        refine ⟨31641412278291508364535815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84377099408777355638762173 31641412278291508364535815)
        ·
          refine ⟨47462118417437262546803723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31641412278291508364535815 47462118417437262546803723)
          ·
            refine ⟨71193177626155893820205585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47462118417437262546803723 71193177626155893820205585)
            ·
              refine ⟨53394883219616920365154189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71193177626155893820205585 53394883219616920365154189)
              ·
                refine ⟨20023081207356345136932821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53394883219616920365154189 20023081207356345136932821)
                ·
                  refine ⟨469290965797414339146863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20023081207356345136932821 469290965797414339146863)
                  ·
                    rfl

theorem cell23_8225468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_8225468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225468 prefixEnd_8225468 := by exact prefixLift 8225468
  have htrace : WordTrace (prefixWord ++ tailWord_8225468) baseStart_8225468 baseEnd_8225468 := by
    simpa [prefixWord, tailWord_8225468, baseEnd_8225468] using wordTrace_append hprefix tailTrace_8225468
  have hstable : (prefixWord ++ tailWord_8225468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225468).length < 2 ^ (prefixWord ++ tailWord_8225468).sum := by decide
  have hdescent : baseEnd_8225468 < baseStart_8225468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225498 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_8225498 : Nat := 118140960795 + 8225498 * 2 ^ 59
def prefixEnd_8225498 : Nat := 4983230072969 + 3 ^ 40 * 8225498 * 2
def baseEnd_8225498 : Nat := 1407878032198787978315543

theorem tailTrace_8225498 : CollatzResearch.WordTrace tailWord_8225498 prefixEnd_8225498 1407878032198787978315543 := by
  unfold tailWord_8225498
  simp only [CollatzResearch.WordTrace]
  refine ⟨75002139688608256015353287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200005705836288682707608765 75002139688608256015353287)
  ·
    refine ⟨112503209532912384023029931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75002139688608256015353287 112503209532912384023029931)
    ·
      refine ⟨168754814299368576034544897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112503209532912384023029931 168754814299368576034544897)
      ·
        refine ⟨126566110724526432025908673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168754814299368576034544897 126566110724526432025908673)
        ·
          refine ⟨94924583043394824019431505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126566110724526432025908673 94924583043394824019431505)
          ·
            refine ⟨71193437282546118014573629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94924583043394824019431505 71193437282546118014573629)
            ·
              refine ⟨26697538980954794255465111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71193437282546118014573629 26697538980954794255465111)
              ·
                refine ⟨40046308471432191383197667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26697538980954794255465111 40046308471432191383197667)
                ·
                  refine ⟨60069462707148287074796501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40046308471432191383197667 60069462707148287074796501)
                  ·
                    refine ⟨1407878032198787978315543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60069462707148287074796501 1407878032198787978315543)
                    ·
                      rfl

theorem cell23_8225498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_8225498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225498 prefixEnd_8225498 := by exact prefixLift 8225498
  have htrace : WordTrace (prefixWord ++ tailWord_8225498) baseStart_8225498 baseEnd_8225498 := by
    simpa [prefixWord, tailWord_8225498, baseEnd_8225498] using wordTrace_append hprefix tailTrace_8225498
  have hstable : (prefixWord ++ tailWord_8225498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225498).length < 2 ^ (prefixWord ++ tailWord_8225498).sum := by decide
  have hdescent : baseEnd_8225498 < baseStart_8225498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225545 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 3, 4]
def baseStart_8225545 : Nat := 118140960795 + 8225545 * 2 ^ 59
def prefixEnd_8225545 : Nat := 4983230072969 + 3 ^ 40 * 8225545 * 2
def baseEnd_8225545 : Nat := 1407886076729041750352971

theorem tailTrace_8225545 : CollatzResearch.WordTrace tailWord_8225545 prefixEnd_8225545 1407886076729041750352971 := by
  unfold tailWord_8225545
  simp only [CollatzResearch.WordTrace]
  refine ⟨300010272985262751088374089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200006848656841834058916059 300010272985262751088374089)
  ·
    refine ⟨225007704738947063316280567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300010272985262751088374089 225007704738947063316280567)
    ·
      refine ⟨337511557108420594974420851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225007704738947063316280567 337511557108420594974420851)
      ·
        refine ⟨506267335662630892461631277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337511557108420594974420851 506267335662630892461631277)
        ·
          refine ⟨189850250873486584673111729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506267335662630892461631277 189850250873486584673111729)
          ·
            refine ⟨142387688155114938504833797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189850250873486584673111729 142387688155114938504833797)
            ·
              refine ⟨26697691529084050969656337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142387688155114938504833797 26697691529084050969656337)
              ·
                refine ⟨20023268646813038227242253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26697691529084050969656337 20023268646813038227242253)
                ·
                  refine ⟨7508725742554889335215845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20023268646813038227242253 7508725742554889335215845)
                  ·
                    refine ⟨1407886076729041750352971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7508725742554889335215845 1407886076729041750352971)
                    ·
                      rfl

theorem cell23_8225545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 4].length) (baseStart_8225545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225545 prefixEnd_8225545 := by exact prefixLift 8225545
  have htrace : WordTrace (prefixWord ++ tailWord_8225545) baseStart_8225545 baseEnd_8225545 := by
    simpa [prefixWord, tailWord_8225545, baseEnd_8225545] using wordTrace_append hprefix tailTrace_8225545
  have hstable : (prefixWord ++ tailWord_8225545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225545).length < 2 ^ (prefixWord ++ tailWord_8225545).sum := by decide
  have hdescent : baseEnd_8225545 < baseStart_8225545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225548 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_8225548 : Nat := 118140960795 + 8225548 * 2 ^ 59
def prefixEnd_8225548 : Nat := 4983230072969 + 3 ^ 40 * 8225548 * 2
def baseEnd_8225548 : Nat := 4223659770629088739321399

theorem tailTrace_8225548 : CollatzResearch.WordTrace tailWord_8225548 prefixEnd_8225548 4223659770629088739321399 := by
  unfold tailWord_8225548
  simp only [CollatzResearch.WordTrace]
  refine ⟨150005191202125941300366649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200006921602834588400488865 150005191202125941300366649)
  ·
    refine ⟨112503893401594455975274987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150005191202125941300366649 112503893401594455975274987)
    ·
      refine ⟨168755840102391683962912481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112503893401594455975274987 168755840102391683962912481)
      ·
        refine ⟨126566880076793762972184361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168755840102391683962912481 126566880076793762972184361)
        ·
          refine ⟨94925160057595322229138271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126566880076793762972184361 94925160057595322229138271)
          ·
            refine ⟨142387740086392983343707407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94925160057595322229138271 142387740086392983343707407)
            ·
              refine ⟨213581610129589475015561111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142387740086392983343707407 213581610129589475015561111)
              ·
                refine ⟨320372415194384212523341667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213581610129589475015561111 320372415194384212523341667)
                ·
                  refine ⟨480558622791576318785012501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320372415194384212523341667 480558622791576318785012501)
                  ·
                    refine ⟨22526185443355139943047461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 480558622791576318785012501 22526185443355139943047461)
                    ·
                      refine ⟨4223659770629088739321399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22526185443355139943047461 4223659770629088739321399)
                      ·
                        rfl

theorem cell23_8225548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_8225548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225548 prefixEnd_8225548 := by exact prefixLift 8225548
  have htrace : WordTrace (prefixWord ++ tailWord_8225548) baseStart_8225548 baseEnd_8225548 := by
    simpa [prefixWord, tailWord_8225548, baseEnd_8225548] using wordTrace_append hprefix tailTrace_8225548
  have hstable : (prefixWord ++ tailWord_8225548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225548).length < 2 ^ (prefixWord ++ tailWord_8225548).sum := by decide
  have hdescent : baseEnd_8225548 < baseStart_8225548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225555 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 3]
def baseStart_8225555 : Nat := 118140960795 + 8225555 * 2 ^ 59
def prefixEnd_8225555 : Nat := 4983230072969 + 3 ^ 40 * 8225555 * 2
def baseEnd_8225555 : Nat := 4223663364993670211933867

theorem tailTrace_8225555 : CollatzResearch.WordTrace tailWord_8225555 prefixEnd_8225555 4223663364993670211933867 := by
  unfold tailWord_8225555
  simp only [CollatzResearch.WordTrace]
  refine ⟨300010637715226522796238119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200007091810151015197492079 300010637715226522796238119)
  ·
    refine ⟨450015956572839784194357179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300010637715226522796238119 450015956572839784194357179)
    ·
      refine ⟨675023934859259676291535769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450015956572839784194357179 675023934859259676291535769)
      ·
        refine ⟨506267951144444757218651827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675023934859259676291535769 506267951144444757218651827)
        ·
          refine ⟨759401926716667135827977741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506267951144444757218651827 759401926716667135827977741)
          ·
            refine ⟨284775722518750175935491653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759401926716667135827977741 284775722518750175935491653)
            ·
              refine ⟨53395447972265657987904685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284775722518750175935491653 53395447972265657987904685)
              ·
                refine ⟨20023292989599621745464257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53395447972265657987904685 20023292989599621745464257)
                ·
                  refine ⟨15017469742199716309098193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20023292989599621745464257 15017469742199716309098193)
                  ·
                    refine ⟨11263102306649787231823645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15017469742199716309098193 11263102306649787231823645)
                    ·
                      refine ⟨4223663364993670211933867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11263102306649787231823645 4223663364993670211933867)
                      ·
                        rfl

theorem cell23_8225555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_8225555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225555 prefixEnd_8225555 := by exact prefixLift 8225555
  have htrace : WordTrace (prefixWord ++ tailWord_8225555) baseStart_8225555 baseEnd_8225555 := by
    simpa [prefixWord, tailWord_8225555, baseEnd_8225555] using wordTrace_append hprefix tailTrace_8225555
  have hstable : (prefixWord ++ tailWord_8225555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225555).length < 2 ^ (prefixWord ++ tailWord_8225555).sum := by decide
  have hdescent : baseEnd_8225555 < baseStart_8225555 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225605 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_8225605 : Nat := 118140960795 + 8225605 * 2 ^ 59
def prefixEnd_8225605 : Nat := 4983230072969 + 3 ^ 40 * 8225605 * 2
def baseEnd_8225605 : Nat := 1407896346342131672102879

theorem tailTrace_8225605 : CollatzResearch.WordTrace tailWord_8225605 prefixEnd_8225605 1407896346342131672102879 := by
  unfold tailWord_8225605
  simp only [CollatzResearch.WordTrace]
  refine ⟨300012461365045381335558269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200008307576696920890372179 300012461365045381335558269)
  ·
    refine ⟨112504673011892018000834351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300012461365045381335558269 112504673011892018000834351)
    ·
      refine ⟨168757009517838027001251527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112504673011892018000834351 168757009517838027001251527)
      ·
        refine ⟨253135514276757040501877291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168757009517838027001251527 253135514276757040501877291)
        ·
          refine ⟨379703271415135560752815937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253135514276757040501877291 379703271415135560752815937)
          ·
            refine ⟨284777453561351670564611953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379703271415135560752815937 284777453561351670564611953)
            ·
              refine ⟨213583090171013752923458965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284777453561351670564611953 213583090171013752923458965)
              ·
                refine ⟨10011707351766269668287139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213583090171013752923458965 10011707351766269668287139)
                ·
                  refine ⟨15017561027649404502430709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10011707351766269668287139 15017561027649404502430709)
                  ·
                    refine ⟨1407896346342131672102879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15017561027649404502430709 1407896346342131672102879)
                    ·
                      rfl

theorem cell23_8225605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_8225605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225605 prefixEnd_8225605 := by exact prefixLift 8225605
  have htrace : WordTrace (prefixWord ++ tailWord_8225605) baseStart_8225605 baseEnd_8225605 := by
    simpa [prefixWord, tailWord_8225605, baseEnd_8225605] using wordTrace_append hprefix tailTrace_8225605
  have hstable : (prefixWord ++ tailWord_8225605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225605).length < 2 ^ (prefixWord ++ tailWord_8225605).sum := by decide
  have hdescent : baseEnd_8225605 < baseStart_8225605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225636 : List Nat := [2, 3, 1, 1, 4, 2, 1, 4, 1, 1, 3]
def baseStart_8225636 : Nat := 118140960795 + 8225636 * 2 ^ 59
def prefixEnd_8225636 : Nat := 4983230072969 + 3 ^ 40 * 8225636 * 2
def baseEnd_8225636 : Nat := 4223704956926684395020995

theorem tailTrace_8225636 : CollatzResearch.WordTrace tailWord_8225636 prefixEnd_8225636 4223704956926684395020995 := by
  unfold tailWord_8225636
  simp only [CollatzResearch.WordTrace]
  refine ⟨150006796013966536814968381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200009061351955382419957841 150006796013966536814968381)
  ·
    refine ⟨56252548505237451305613143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150006796013966536814968381 56252548505237451305613143)
    ·
      refine ⟨84378822757856176958419715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56252548505237451305613143 84378822757856176958419715)
      ·
        refine ⟨126568234136784265437629573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84378822757856176958419715 126568234136784265437629573)
        ·
          refine ⟨23731543900647049769555545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126568234136784265437629573 23731543900647049769555545)
          ·
            refine ⟨17798657925485287327166659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23731543900647049769555545 17798657925485287327166659)
            ·
              refine ⟨26697986888227930990749989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17798657925485287327166659 26697986888227930990749989)
              ·
                refine ⟨5005872541542737060765623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26697986888227930990749989 5005872541542737060765623)
                ·
                  refine ⟨7508808812314105591148435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005872541542737060765623 7508808812314105591148435)
                  ·
                    refine ⟨11263213218471158386722653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7508808812314105591148435 11263213218471158386722653)
                    ·
                      refine ⟨4223704956926684395020995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11263213218471158386722653 4223704956926684395020995)
                      ·
                        rfl

theorem cell23_8225636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_8225636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225636 prefixEnd_8225636 := by exact prefixLift 8225636
  have htrace : WordTrace (prefixWord ++ tailWord_8225636) baseStart_8225636 baseEnd_8225636 := by
    simpa [prefixWord, tailWord_8225636, baseEnd_8225636] using wordTrace_append hprefix tailTrace_8225636
  have hstable : (prefixWord ++ tailWord_8225636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225636).length < 2 ^ (prefixWord ++ tailWord_8225636).sum := by decide
  have hdescent : baseEnd_8225636 < baseStart_8225636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225645 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_8225645 : Nat := 118140960795 + 8225645 * 2 ^ 59
def prefixEnd_8225645 : Nat := 4983230072969 + 3 ^ 40 * 8225645 * 2
def baseEnd_8225645 : Nat := 4223709578252574859808453

theorem tailTrace_8225645 : CollatzResearch.WordTrace tailWord_8225645 prefixEnd_8225645 4223709578252574859808453 := by
  unfold tailWord_8225645
  simp only [CollatzResearch.WordTrace]
  refine ⟨300013920284900468167014389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200009280189933645444676259 300013920284900468167014389)
  ·
    refine ⟨28126305026709418890657599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300013920284900468167014389 28126305026709418890657599)
    ·
      refine ⟨42189457540064128335986399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28126305026709418890657599 42189457540064128335986399)
      ·
        refine ⟨63284186310096192503979599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42189457540064128335986399 63284186310096192503979599)
        ·
          refine ⟨94926279465144288755969399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63284186310096192503979599 94926279465144288755969399)
          ·
            refine ⟨142389419197716433133954099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94926279465144288755969399 142389419197716433133954099)
            ·
              refine ⟨213584128796574649700931149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142389419197716433133954099 213584128796574649700931149)
              ·
                refine ⟨80094048298715493637849181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213584128796574649700931149 80094048298715493637849181)
                ·
                  refine ⟨30035268112018310114193443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80094048298715493637849181 30035268112018310114193443)
                  ·
                    refine ⟨45052902168027465171290165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30035268112018310114193443 45052902168027465171290165)
                    ·
                      refine ⟨4223709578252574859808453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45052902168027465171290165 4223709578252574859808453)
                      ·
                        rfl

theorem cell23_8225645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_8225645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225645 prefixEnd_8225645 := by exact prefixLift 8225645
  have htrace : WordTrace (prefixWord ++ tailWord_8225645) baseStart_8225645 baseEnd_8225645 := by
    simpa [prefixWord, tailWord_8225645, baseEnd_8225645] using wordTrace_append hprefix tailTrace_8225645
  have hstable : (prefixWord ++ tailWord_8225645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225645).length < 2 ^ (prefixWord ++ tailWord_8225645).sum := by decide
  have hdescent : baseEnd_8225645 < baseStart_8225645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225672 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_8225672 : Nat := 118140960795 + 8225672 * 2 ^ 59
def prefixEnd_8225672 : Nat := 4983230072969 + 3 ^ 40 * 8225672 * 2
def baseEnd_8225672 : Nat := 4223723442230246254170829

theorem tailTrace_8225672 : CollatzResearch.WordTrace tailWord_8225672 prefixEnd_8225672 4223723442230246254170829 := by
  unfold tailWord_8225672
  simp only [CollatzResearch.WordTrace]
  refine ⟨150007452527901325889123635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200009936703868434518831513 150007452527901325889123635)
  ·
    refine ⟨225011178791851988833685453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150007452527901325889123635 225011178791851988833685453)
    ·
      refine ⟨84379192046944495812632045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225011178791851988833685453 84379192046944495812632045)
      ·
        refine ⟨31642197017604185929737017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84379192046944495812632045 31642197017604185929737017)
        ·
          refine ⟨23731647763203139447302763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31642197017604185929737017 23731647763203139447302763)
          ·
            refine ⟨35597471644804709170954145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23731647763203139447302763 35597471644804709170954145)
            ·
              refine ⟨26698103733603531878215609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35597471644804709170954145 26698103733603531878215609)
              ·
                refine ⟨20023577800202648908661707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26698103733603531878215609 20023577800202648908661707)
                ·
                  refine ⟨30035366700303973362992561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20023577800202648908661707 30035366700303973362992561)
                  ·
                    refine ⟨22526525025227980022244421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30035366700303973362992561 22526525025227980022244421)
                    ·
                      refine ⟨4223723442230246254170829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22526525025227980022244421 4223723442230246254170829)
                      ·
                        rfl

theorem cell23_8225672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_8225672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225672 prefixEnd_8225672 := by exact prefixLift 8225672
  have htrace : WordTrace (prefixWord ++ tailWord_8225672) baseStart_8225672 baseEnd_8225672 := by
    simpa [prefixWord, tailWord_8225672, baseEnd_8225672] using wordTrace_append hprefix tailTrace_8225672
  have hstable : (prefixWord ++ tailWord_8225672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225672).length < 2 ^ (prefixWord ++ tailWord_8225672).sum := by decide
  have hdescent : baseEnd_8225672 < baseStart_8225672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225676 : List Nat := [2, 2, 1, 2, 1, 2, 3, 5, 1, 2, 2]
def baseStart_8225676 : Nat := 118140960795 + 8225676 * 2 ^ 59
def prefixEnd_8225676 : Nat := 4983230072969 + 3 ^ 40 * 8225676 * 2
def baseEnd_8225676 : Nat := 4223725496152864238520811

theorem tailTrace_8225676 : CollatzResearch.WordTrace tailWord_8225676 prefixEnd_8225676 4223725496152864238520811 := by
  unfold tailWord_8225676
  simp only [CollatzResearch.WordTrace]
  refine ⟨150007525473894080230696441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200010033965192106974261921 150007525473894080230696441)
  ·
    refine ⟨112505644105420560173022331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150007525473894080230696441 112505644105420560173022331)
    ·
      refine ⟨168758466158130840259533497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112505644105420560173022331 168758466158130840259533497)
      ·
        refine ⟨126568849618598130194650123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168758466158130840259533497 126568849618598130194650123)
        ·
          refine ⟨189853274427897195291975185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126568849618598130194650123 189853274427897195291975185)
          ·
            refine ⟨142389955820922896468981389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189853274427897195291975185 142389955820922896468981389)
            ·
              refine ⟨53396233432846086175868021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142389955820922896468981389 53396233432846086175868021)
              ·
                refine ⟨5005896884329320578987627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53396233432846086175868021 5005896884329320578987627)
                ·
                  refine ⟨7508845326493980868481441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005896884329320578987627 7508845326493980868481441)
                  ·
                    refine ⟨5631633994870485651361081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7508845326493980868481441 5631633994870485651361081)
                    ·
                      refine ⟨4223725496152864238520811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631633994870485651361081 4223725496152864238520811)
                      ·
                        rfl

theorem cell23_8225676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_8225676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225676 prefixEnd_8225676 := by exact prefixLift 8225676
  have htrace : WordTrace (prefixWord ++ tailWord_8225676) baseStart_8225676 baseEnd_8225676 := by
    simpa [prefixWord, tailWord_8225676, baseEnd_8225676] using wordTrace_append hprefix tailTrace_8225676
  have hstable : (prefixWord ++ tailWord_8225676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225676).length < 2 ^ (prefixWord ++ tailWord_8225676).sum := by decide
  have hdescent : baseEnd_8225676 < baseStart_8225676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225682 : List Nat := [3, 2, 3, 2, 2, 1, 10]
def baseStart_8225682 : Nat := 118140960795 + 8225682 * 2 ^ 59
def prefixEnd_8225682 : Nat := 4983230072969 + 3 ^ 40 * 8225682 * 2
def baseEnd_8225682 : Nat := 52144797247367792778343

theorem tailTrace_8225682 : CollatzResearch.WordTrace tailWord_8225682 prefixEnd_8225682 52144797247367792778343 := by
  unfold tailWord_8225682
  simp only [CollatzResearch.WordTrace]
  refine ⟨75003817446441605871527825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200010179857177615657407533 75003817446441605871527825)
  ·
    refine ⟨56252863084831204403645869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75003817446441605871527825 56252863084831204403645869)
    ·
      refine ⟨21094823656811701651367201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56252863084831204403645869 21094823656811701651367201)
      ·
        refine ⟨15821117742608776238525401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21094823656811701651367201 15821117742608776238525401)
        ·
          refine ⟨11865838306956582178894051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15821117742608776238525401 11865838306956582178894051)
          ·
            refine ⟨17798757460434873268341077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11865838306956582178894051 17798757460434873268341077)
            ·
              refine ⟨52144797247367792778343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17798757460434873268341077 52144797247367792778343)
              ·
                rfl

theorem cell23_8225682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 10].length) (baseStart_8225682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225682 prefixEnd_8225682 := by exact prefixLift 8225682
  have htrace : WordTrace (prefixWord ++ tailWord_8225682) baseStart_8225682 baseEnd_8225682 := by
    simpa [prefixWord, tailWord_8225682, baseEnd_8225682] using wordTrace_append hprefix tailTrace_8225682
  have hstable : (prefixWord ++ tailWord_8225682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225682).length < 2 ^ (prefixWord ++ tailWord_8225682).sum := by decide
  have hdescent : baseEnd_8225682 < baseStart_8225682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225716 : List Nat := [2, 5, 2, 1, 1, 3, 2, 7]
def baseStart_8225716 : Nat := 118140960795 + 8225716 * 2 ^ 59
def prefixEnd_8225716 : Nat := 4983230072969 + 3 ^ 40 * 8225716 * 2
def baseEnd_8225716 : Nat := 156435038347372003037801

theorem tailTrace_8225716 : CollatzResearch.WordTrace tailWord_8225716 prefixEnd_8225716 156435038347372003037801 := by
  unfold tailWord_8225716
  simp only [CollatzResearch.WordTrace]
  refine ⟨150008254933821623646424501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200011006578428831528566001 150008254933821623646424501)
  ·
    refine ⟨14063273900045777216852297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150008254933821623646424501 14063273900045777216852297)
    ·
      refine ⟨10547455425034332912639223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14063273900045777216852297 10547455425034332912639223)
      ·
        refine ⟨15821183137551499368958835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10547455425034332912639223 15821183137551499368958835)
        ·
          refine ⟨23731774706327249053438253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15821183137551499368958835 23731774706327249053438253)
          ·
            refine ⟨8899415514872718395039345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23731774706327249053438253 8899415514872718395039345)
            ·
              refine ⟨6674561636154538796279509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8899415514872718395039345 6674561636154538796279509)
              ·
                refine ⟨156435038347372003037801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6674561636154538796279509 156435038347372003037801)
                ·
                  rfl

theorem cell23_8225716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 7].length) (baseStart_8225716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225716 prefixEnd_8225716 := by exact prefixLift 8225716
  have htrace : WordTrace (prefixWord ++ tailWord_8225716) baseStart_8225716 baseEnd_8225716 := by
    simpa [prefixWord, tailWord_8225716, baseEnd_8225716] using wordTrace_append hprefix tailTrace_8225716
  have hstable : (prefixWord ++ tailWord_8225716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225716).length < 2 ^ (prefixWord ++ tailWord_8225716).sum := by decide
  have hdescent : baseEnd_8225716 < baseStart_8225716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225719 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 1, 3, 2]
def baseStart_8225719 : Nat := 118140960795 + 8225719 * 2 ^ 59
def prefixEnd_8225719 : Nat := 4983230072969 + 3 ^ 40 * 8225719 * 2
def baseEnd_8225719 : Nat := 4223747575821007570283113

theorem tailTrace_8225719 : CollatzResearch.WordTrace tailWord_8225719 prefixEnd_8225719 4223747575821007570283113 := by
  unfold tailWord_8225719
  simp only [CollatzResearch.WordTrace]
  refine ⟨300016619286632378805208211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200011079524421585870138807 300016619286632378805208211)
  ·
    refine ⟨450024928929948568207812317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300016619286632378805208211 450024928929948568207812317)
    ·
      refine ⟨168759348348730713077929619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450024928929948568207812317 168759348348730713077929619)
      ·
        refine ⟨253139022523096069616894429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168759348348730713077929619 253139022523096069616894429)
        ·
          refine ⟨94927133446161026106335411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253139022523096069616894429 94927133446161026106335411)
          ·
            refine ⟨142390700169241539159503117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94927133446161026106335411 142390700169241539159503117)
            ·
              refine ⟨53396512563465577184813669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142390700169241539159503117 53396512563465577184813669)
              ·
                refine ⟨10011846105649795722152563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53396512563465577184813669 10011846105649795722152563)
                ·
                  refine ⟨15017769158474693583228845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10011846105649795722152563 15017769158474693583228845)
                  ·
                    refine ⟨5631663434428010093710817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15017769158474693583228845 5631663434428010093710817)
                    ·
                      refine ⟨4223747575821007570283113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631663434428010093710817 4223747575821007570283113)
                      ·
                        rfl

theorem cell23_8225719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_8225719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225719 prefixEnd_8225719 := by exact prefixLift 8225719
  have htrace : WordTrace (prefixWord ++ tailWord_8225719) baseStart_8225719 baseEnd_8225719 := by
    simpa [prefixWord, tailWord_8225719, baseEnd_8225719] using wordTrace_append hprefix tailTrace_8225719
  have hstable : (prefixWord ++ tailWord_8225719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225719).length < 2 ^ (prefixWord ++ tailWord_8225719).sum := by decide
  have hdescent : baseEnd_8225719 < baseStart_8225719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225735 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_8225735 : Nat := 118140960795 + 8225735 * 2 ^ 59
def prefixEnd_8225735 : Nat := 4983230072969 + 3 ^ 40 * 8225735 * 2
def baseEnd_8225735 : Nat := 4223755791511479507683039

theorem tailTrace_8225735 : CollatzResearch.WordTrace tailWord_8225735 prefixEnd_8225735 4223755791511479507683039 := by
  unfold tailWord_8225735
  simp only [CollatzResearch.WordTrace]
  refine ⟨300017202854574413537790659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200011468569716275691860439 300017202854574413537790659)
  ·
    refine ⟨450025804281861620306685989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300017202854574413537790659 450025804281861620306685989)
    ·
      refine ⟨84379838302849053807503623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450025804281861620306685989 84379838302849053807503623)
      ·
        refine ⟨126569757454273580711255435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84379838302849053807503623 126569757454273580711255435)
        ·
          refine ⟨189854636181410371066883153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126569757454273580711255435 189854636181410371066883153)
          ·
            refine ⟨142390977136057778300162365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189854636181410371066883153 142390977136057778300162365)
            ·
              refine ⟨53396616426021666862560887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142390977136057778300162365 53396616426021666862560887)
              ·
                refine ⟨80094924639032500293841331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53396616426021666862560887 80094924639032500293841331)
                ·
                  refine ⟨120142386958548750440761997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80094924639032500293841331 120142386958548750440761997)
                  ·
                    refine ⟨45053395109455781415285749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120142386958548750440761997 45053395109455781415285749)
                    ·
                      refine ⟨4223755791511479507683039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45053395109455781415285749 4223755791511479507683039)
                      ·
                        rfl

theorem cell23_8225735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_8225735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225735 prefixEnd_8225735 := by exact prefixLift 8225735
  have htrace : WordTrace (prefixWord ++ tailWord_8225735) baseStart_8225735 baseEnd_8225735 := by
    simpa [prefixWord, tailWord_8225735, baseEnd_8225735] using wordTrace_append hprefix tailTrace_8225735
  have hstable : (prefixWord ++ tailWord_8225735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225735).length < 2 ^ (prefixWord ++ tailWord_8225735).sum := by decide
  have hdescent : baseEnd_8225735 < baseStart_8225735 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225806 : List Nat := [4, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_8225806 : Nat := 118140960795 + 8225806 * 2 ^ 59
def prefixEnd_8225806 : Nat := 4983230072969 + 3 ^ 40 * 8225806 * 2
def baseEnd_8225806 : Nat := 469310249848660969988357

theorem tailTrace_8225806 : CollatzResearch.WordTrace tailWord_8225806 prefixEnd_8225806 469310249848660969988357 := by
  unfold tailWord_8225806
  simp only [CollatzResearch.WordTrace]
  refine ⟨37502474054664649082953159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200013194958211461775750181 37502474054664649082953159)
  ·
    refine ⟨56253711081996973624429739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37502474054664649082953159 56253711081996973624429739)
    ·
      refine ⟨84380566622995460436644609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56253711081996973624429739 84380566622995460436644609)
      ·
        refine ⟨63285424967246595327483457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84380566622995460436644609 63285424967246595327483457)
        ·
          refine ⟨47464068725434946495612593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63285424967246595327483457 47464068725434946495612593)
          ·
            refine ⟨35598051544076209871709445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47464068725434946495612593 35598051544076209871709445)
            ·
              refine ⟨6674634664514289350945521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35598051544076209871709445 6674634664514289350945521)
              ·
                refine ⟨5005975998385717013209141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6674634664514289350945521 5005975998385717013209141)
                ·
                  refine ⟨469310249848660969988357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5005975998385717013209141 469310249848660969988357)
                  ·
                    rfl

theorem cell23_8225806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_8225806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225806 prefixEnd_8225806 := by exact prefixLift 8225806
  have htrace : WordTrace (prefixWord ++ tailWord_8225806) baseStart_8225806 baseEnd_8225806 := by
    simpa [prefixWord, tailWord_8225806, baseEnd_8225806] using wordTrace_append hprefix tailTrace_8225806
  have hstable : (prefixWord ++ tailWord_8225806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225806).length < 2 ^ (prefixWord ++ tailWord_8225806).sum := by decide
  have hdescent : baseEnd_8225806 < baseStart_8225806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225852 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_8225852 : Nat := 118140960795 + 8225852 * 2 ^ 59
def prefixEnd_8225852 : Nat := 4983230072969 + 3 ^ 40 * 8225852 * 2
def baseEnd_8225852 : Nat := 4223815868748055549920001

theorem tailTrace_8225852 : CollatzResearch.WordTrace tailWord_8225852 prefixEnd_8225852 4223815868748055549920001 := by
  unfold tailWord_8225852
  simp only [CollatzResearch.WordTrace]
  refine ⟨150010735097575271259899905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200014313463433695013199873 150010735097575271259899905)
  ·
    refine ⟨112508051323181453444924929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150010735097575271259899905 112508051323181453444924929)
    ·
      refine ⟨84381038492386090083693697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112508051323181453444924929 84381038492386090083693697)
      ·
        refine ⟨63285778869289567562770273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84381038492386090083693697 63285778869289567562770273)
        ·
          refine ⟨47464334151967175672077705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63285778869289567562770273 47464334151967175672077705)
          ·
            refine ⟨35598250613975381754058279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47464334151967175672077705 35598250613975381754058279)
            ·
              refine ⟨53397375920963072631087419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35598250613975381754058279 53397375920963072631087419)
              ·
                refine ⟨80096063881444608946631129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53397375920963072631087419 80096063881444608946631129)
                ·
                  refine ⟨60072047911083456709973347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80096063881444608946631129 60072047911083456709973347)
                  ·
                    refine ⟨90108071866625185064960021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60072047911083456709973347 90108071866625185064960021)
                    ·
                      refine ⟨4223815868748055549920001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90108071866625185064960021 4223815868748055549920001)
                      ·
                        rfl

theorem cell23_8225852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_8225852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225852 prefixEnd_8225852 := by exact prefixLift 8225852
  have htrace : WordTrace (prefixWord ++ tailWord_8225852) baseStart_8225852 baseEnd_8225852 := by
    simpa [prefixWord, tailWord_8225852, baseEnd_8225852] using wordTrace_append hprefix tailTrace_8225852
  have hstable : (prefixWord ++ tailWord_8225852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225852).length < 2 ^ (prefixWord ++ tailWord_8225852).sum := by decide
  have hdescent : baseEnd_8225852 < baseStart_8225852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225866 : List Nat := [3, 1, 2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_8225866 : Nat := 118140960795 + 8225866 * 2 ^ 59
def prefixEnd_8225866 : Nat := 4983230072969 + 3 ^ 40 * 8225866 * 2
def baseEnd_8225866 : Nat := 1407941019159072831714979

theorem tailTrace_8225866 : CollatzResearch.WordTrace tailWord_8225866 prefixEnd_8225866 1407941019159072831714979 := by
  unfold tailWord_8225866
  simp only [CollatzResearch.WordTrace]
  refine ⟨75005495204274955727702363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200014653878066548607206301 75005495204274955727702363)
  ·
    refine ⟨112508242806412433591553545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75005495204274955727702363 112508242806412433591553545)
    ·
      refine ⟨84381182104809325193665159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112508242806412433591553545 84381182104809325193665159)
      ·
        refine ⟨126571773157213987790497739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84381182104809325193665159 126571773157213987790497739)
        ·
          refine ⟨189857659735820981685746609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126571773157213987790497739 189857659735820981685746609)
          ·
            refine ⟨142393244801865736264309957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189857659735820981685746609 142393244801865736264309957)
            ·
              refine ⟨26698733400349825549558117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142393244801865736264309957 26698733400349825549558117)
              ·
                refine ⟨5006012512565592290542147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26698733400349825549558117 5006012512565592290542147)
                ·
                  refine ⟨7509018768848388435813221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006012512565592290542147 7509018768848388435813221)
                  ·
                    refine ⟨1407941019159072831714979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7509018768848388435813221 1407941019159072831714979)
                    ·
                      rfl

theorem cell23_8225866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_8225866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225866 prefixEnd_8225866 := by exact prefixLift 8225866
  have htrace : WordTrace (prefixWord ++ tailWord_8225866) baseStart_8225866 baseEnd_8225866 := by
    simpa [prefixWord, tailWord_8225866, baseEnd_8225866] using wordTrace_append hprefix tailTrace_8225866
  have hstable : (prefixWord ++ tailWord_8225866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225866).length < 2 ^ (prefixWord ++ tailWord_8225866).sum := by decide
  have hdescent : baseEnd_8225866 < baseStart_8225866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225899 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 8, 3, 2]
def baseStart_8225899 : Nat := 118140960795 + 8225899 * 2 ^ 59
def prefixEnd_8225899 : Nat := 4983230072969 + 3 ^ 40 * 8225899 * 2
def baseEnd_8225899 : Nat := 4223840002338816866032285

theorem tailTrace_8225899 : CollatzResearch.WordTrace tailWord_8225899 prefixEnd_8225899 4223840002338816866032285 := by
  unfold tailWord_8225899
  simp only [CollatzResearch.WordTrace]
  refine ⟨300023184425980269546760751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200015456283986846364507167 300023184425980269546760751)
  ·
    refine ⟨450034776638970404320141127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300023184425980269546760751 450034776638970404320141127)
    ·
      refine ⟨675052164958455606480211691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450034776638970404320141127 675052164958455606480211691)
      ·
        refine ⟨1012578247437683409720317537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675052164958455606480211691 1012578247437683409720317537)
        ·
          refine ⟨759433685578262557290238153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012578247437683409720317537 759433685578262557290238153)
          ·
            refine ⟨569575264183696917967678615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759433685578262557290238153 569575264183696917967678615)
            ·
              refine ⟨854362896275545376951517923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569575264183696917967678615 854362896275545376951517923)
              ·
                refine ⟨1281544344413318065427276885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854362896275545376951517923 1281544344413318065427276885)
                ·
                  refine ⟨15018097786093571079225901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1281544344413318065427276885 15018097786093571079225901)
                  ·
                    refine ⟨5631786669785089154709713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15018097786093571079225901 5631786669785089154709713)
                    ·
                      refine ⟨4223840002338816866032285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631786669785089154709713 4223840002338816866032285)
                      ·
                        rfl

theorem cell23_8225899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 3, 2].length) (baseStart_8225899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225899 prefixEnd_8225899 := by exact prefixLift 8225899
  have htrace : WordTrace (prefixWord ++ tailWord_8225899) baseStart_8225899 baseEnd_8225899 := by
    simpa [prefixWord, tailWord_8225899, baseEnd_8225899] using wordTrace_append hprefix tailTrace_8225899
  have hstable : (prefixWord ++ tailWord_8225899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225899).length < 2 ^ (prefixWord ++ tailWord_8225899).sum := by decide
  have hdescent : baseEnd_8225899 < baseStart_8225899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225916 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_8225916 : Nat := 118140960795 + 8225916 * 2 ^ 59
def prefixEnd_8225916 : Nat := 4983230072969 + 3 ^ 40 * 8225916 * 2
def baseEnd_8225916 : Nat := 4223848731509943299519707

theorem tailTrace_8225916 : CollatzResearch.WordTrace tailWord_8225916 prefixEnd_8225916 4223848731509943299519707 := by
  unfold tailWord_8225916
  simp only [CollatzResearch.WordTrace]
  refine ⟨150011902233459340725064801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200015869644612454300086401 150011902233459340725064801)
  ·
    refine ⟨112508926675094505543798601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150011902233459340725064801 112508926675094505543798601)
    ·
      refine ⟨84381695006320879157848951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112508926675094505543798601 84381695006320879157848951)
      ·
        refine ⟨126572542509481318736773427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84381695006320879157848951 126572542509481318736773427)
        ·
          refine ⟨189858813764221978105160141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126572542509481318736773427 189858813764221978105160141)
          ·
            refine ⟨71197055161583241789435053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189858813764221978105160141 71197055161583241789435053)
            ·
              refine ⟨26698895685593715671038145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71197055161583241789435053 26698895685593715671038145)
              ·
                refine ⟨20024171764195286753278609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26698895685593715671038145 20024171764195286753278609)
                ·
                  refine ⟨15018128823146465064958957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20024171764195286753278609 15018128823146465064958957)
                  ·
                    refine ⟨5631798308679924399359609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15018128823146465064958957 5631798308679924399359609)
                    ·
                      refine ⟨4223848731509943299519707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631798308679924399359609 4223848731509943299519707)
                      ·
                        rfl

theorem cell23_8225916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_8225916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225916 prefixEnd_8225916 := by exact prefixLift 8225916
  have htrace : WordTrace (prefixWord ++ tailWord_8225916) baseStart_8225916 baseEnd_8225916 := by
    simpa [prefixWord, tailWord_8225916, baseEnd_8225916] using wordTrace_append hprefix tailTrace_8225916
  have hstable : (prefixWord ++ tailWord_8225916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225916).length < 2 ^ (prefixWord ++ tailWord_8225916).sum := by decide
  have hdescent : baseEnd_8225916 < baseStart_8225916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225946 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_8225946 : Nat := 118140960795 + 8225946 * 2 ^ 59
def prefixEnd_8225946 : Nat := 4983230072969 + 3 ^ 40 * 8225946 * 2
def baseEnd_8225946 : Nat := 4223864135929578182144569

theorem tailTrace_8225946 : CollatzResearch.WordTrace tailWord_8225946 prefixEnd_8225946 4223864135929578182144569 := by
  unfold tailWord_8225946
  simp only [CollatzResearch.WordTrace]
  refine ⟨75006224664202499143430423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200016599104539997715814461 75006224664202499143430423)
  ·
    refine ⟨112509336996303748715145635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75006224664202499143430423 112509336996303748715145635)
    ·
      refine ⟨168764005494455623072718453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112509336996303748715145635 168764005494455623072718453)
      ·
        refine ⟨15821625515105214663067355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168764005494455623072718453 15821625515105214663067355)
        ·
          refine ⟨23732438272657821994601033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15821625515105214663067355 23732438272657821994601033)
          ·
            refine ⟨17799328704493366495950775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23732438272657821994601033 17799328704493366495950775)
            ·
              refine ⟨26698993056740049743926163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17799328704493366495950775 26698993056740049743926163)
              ·
                refine ⟨40048489585110074615889245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26698993056740049743926163 40048489585110074615889245)
                ·
                  refine ⟨15018183594416277980958467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40048489585110074615889245 15018183594416277980958467)
                  ·
                    refine ⟨22527275391624416971437701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15018183594416277980958467 22527275391624416971437701)
                    ·
                      refine ⟨4223864135929578182144569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22527275391624416971437701 4223864135929578182144569)
                      ·
                        rfl

theorem cell23_8225946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_8225946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225946 prefixEnd_8225946 := by exact prefixLift 8225946
  have htrace : WordTrace (prefixWord ++ tailWord_8225946) baseStart_8225946 baseEnd_8225946 := by
    simpa [prefixWord, tailWord_8225946, baseEnd_8225946] using wordTrace_append hprefix tailTrace_8225946
  have hstable : (prefixWord ++ tailWord_8225946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225946).length < 2 ^ (prefixWord ++ tailWord_8225946).sum := by decide
  have hdescent : baseEnd_8225946 < baseStart_8225946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225950 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_8225950 : Nat := 118140960795 + 8225950 * 2 ^ 59
def prefixEnd_8225950 : Nat := 4983230072969 + 3 ^ 40 * 8225950 * 2
def baseEnd_8225950 : Nat := 4223866189852196166494551

theorem tailTrace_8225950 : CollatzResearch.WordTrace tailWord_8225950 prefixEnd_8225950 4223866189852196166494551 := by
  unfold tailWord_8225950
  simp only [CollatzResearch.WordTrace]
  refine ⟨37503130568599438157108413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200016696365863670171244869 37503130568599438157108413)
  ·
    refine ⟨14063673963224789308915655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37503130568599438157108413 14063673963224789308915655)
    ·
      refine ⟨21095510944837183963373483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14063673963224789308915655 21095510944837183963373483)
      ·
        refine ⟨31643266417255775945060225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21095510944837183963373483 31643266417255775945060225)
        ·
          refine ⟨23732449812941831958795169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31643266417255775945060225 23732449812941831958795169)
          ·
            refine ⟨17799337359706373969096377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23732449812941831958795169 17799337359706373969096377)
            ·
              refine ⟨13349503019779780476822283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17799337359706373969096377 13349503019779780476822283)
              ·
                refine ⟨20024254529669670715233425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13349503019779780476822283 20024254529669670715233425)
                ·
                  refine ⟨15018190897252253036425069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20024254529669670715233425 15018190897252253036425069)
                  ·
                    refine ⟨5631821586469594888659401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15018190897252253036425069 5631821586469594888659401)
                    ·
                      refine ⟨4223866189852196166494551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631821586469594888659401 4223866189852196166494551)
                      ·
                        rfl

theorem cell23_8225950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_8225950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225950 prefixEnd_8225950 := by exact prefixLift 8225950
  have htrace : WordTrace (prefixWord ++ tailWord_8225950) baseStart_8225950 baseEnd_8225950 := by
    simpa [prefixWord, tailWord_8225950, baseEnd_8225950] using wordTrace_append hprefix tailTrace_8225950
  have hstable : (prefixWord ++ tailWord_8225950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225950).length < 2 ^ (prefixWord ++ tailWord_8225950).sum := by decide
  have hdescent : baseEnd_8225950 < baseStart_8225950 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225952 : List Nat := [2, 1, 1, 4, 2, 1, 1, 11]
def baseStart_8225952 : Nat := 118140960795 + 8225952 * 2 ^ 59
def prefixEnd_8225952 : Nat := 4983230072969 + 3 ^ 40 * 8225952 * 2
def baseEnd_8225952 : Nat := 156439526548648339209983

theorem tailTrace_8225952 : CollatzResearch.WordTrace tailWord_8225952 prefixEnd_8225952 156439526548648339209983 := by
  unfold tailWord_8225952
  simp only [CollatzResearch.WordTrace]
  refine ⟨150012558747394129799220055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200016744996525506398960073 150012558747394129799220055)
  ·
    refine ⟨225018838121091194698830083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150012558747394129799220055 225018838121091194698830083)
    ·
      refine ⟨337528257181636792048245125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225018838121091194698830083 337528257181636792048245125)
      ·
        refine ⟨63286548221556898509045961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337528257181636792048245125 63286548221556898509045961)
        ·
          refine ⟨47464911166167673881784471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63286548221556898509045961 47464911166167673881784471)
          ·
            refine ⟨71197366749251510822676707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47464911166167673881784471 71197366749251510822676707)
            ·
              refine ⟨106796050123877266234015061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71197366749251510822676707 106796050123877266234015061)
              ·
                refine ⟨156439526548648339209983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 106796050123877266234015061 156439526548648339209983)
                ·
                  rfl

theorem cell23_8225952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 11].length) (baseStart_8225952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225952 prefixEnd_8225952 := by exact prefixLift 8225952
  have htrace : WordTrace (prefixWord ++ tailWord_8225952) baseStart_8225952 baseEnd_8225952 := by
    simpa [prefixWord, tailWord_8225952, baseEnd_8225952] using wordTrace_append hprefix tailTrace_8225952
  have hstable : (prefixWord ++ tailWord_8225952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225952).length < 2 ^ (prefixWord ++ tailWord_8225952).sum := by decide
  have hdescent : baseEnd_8225952 < baseStart_8225952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8225974 : List Nat := [5, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_8225974 : Nat := 118140960795 + 8225974 * 2 ^ 59
def prefixEnd_8225974 : Nat := 4983230072969 + 3 ^ 40 * 8225974 * 2
def baseEnd_8225974 : Nat := 4223878513387904072594441

theorem tailTrace_8225974 : CollatzResearch.WordTrace tailWord_8225974 prefixEnd_8225974 4223878513387904072594441 := by
  unfold tailWord_8225974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18751619993794284834733811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200017279933805704903827317 18751619993794284834733811)
  ·
    refine ⟨28127429990691427252100717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18751619993794284834733811 28127429990691427252100717)
    ·
      refine ⟨10547786246509285219537769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28127429990691427252100717 10547786246509285219537769)
      ·
        refine ⟨7910839684881963914653327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10547786246509285219537769 7910839684881963914653327)
        ·
          refine ⟨11866259527322945871979991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910839684881963914653327 11866259527322945871979991)
          ·
            refine ⟨17799389290984418807969987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11866259527322945871979991 17799389290984418807969987)
            ·
              refine ⟨26699083936476628211954981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17799389290984418807969987 26699083936476628211954981)
              ·
                refine ⟨5006078238089367789741559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26699083936476628211954981 5006078238089367789741559)
                ·
                  refine ⟨7509117357134051684612339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006078238089367789741559 7509117357134051684612339)
                  ·
                    refine ⟨11263676035701077526918509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7509117357134051684612339 11263676035701077526918509)
                    ·
                      refine ⟨4223878513387904072594441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11263676035701077526918509 4223878513387904072594441)
                      ·
                        rfl

theorem cell23_8225974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_8225974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8225974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8225974 prefixEnd_8225974 := by exact prefixLift 8225974
  have htrace : WordTrace (prefixWord ++ tailWord_8225974) baseStart_8225974 baseEnd_8225974 := by
    simpa [prefixWord, tailWord_8225974, baseEnd_8225974] using wordTrace_append hprefix tailTrace_8225974
  have hstable : (prefixWord ++ tailWord_8225974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8225974).length < 2 ^ (prefixWord ++ tailWord_8225974).sum := by decide
  have hdescent : baseEnd_8225974 < baseStart_8225974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8225974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226046 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_8226046 : Nat := 118140960795 + 8226046 * 2 ^ 59
def prefixEnd_8226046 : Nat := 4983230072969 + 3 ^ 40 * 8226046 * 2
def baseEnd_8226046 : Nat := 1407971827998342596964703

theorem tailTrace_8226046 : CollatzResearch.WordTrace tailWord_8226046 prefixEnd_8226046 1407971827998342596964703 := by
  unfold tailWord_8226046
  simp only [CollatzResearch.WordTrace]
  refine ⟨37503568244555964206545249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200019030637631809101574661 37503568244555964206545249)
  ·
    refine ⟨28127676183416973154908937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37503568244555964206545249 28127676183416973154908937)
    ·
      refine ⟨21095757137562729866181703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28127676183416973154908937 21095757137562729866181703)
      ·
        refine ⟨31643635706344094799272555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21095757137562729866181703 31643635706344094799272555)
        ·
          refine ⟨47465453559516142198908833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31643635706344094799272555 47465453559516142198908833)
          ·
            refine ⟨35599090169637106649181625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47465453559516142198908833 35599090169637106649181625)
            ·
              refine ⟨26699317627227829986886219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35599090169637106649181625 26699317627227829986886219)
              ·
                refine ⟨40048976440841744980329329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26699317627227829986886219 40048976440841744980329329)
                ·
                  refine ⟨30036732330631308735246997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40048976440841744980329329 30036732330631308735246997)
                  ·
                    refine ⟨1407971827998342596964703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30036732330631308735246997 1407971827998342596964703)
                    ·
                      rfl

theorem cell23_8226046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_8226046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226046 prefixEnd_8226046 := by exact prefixLift 8226046
  have htrace : WordTrace (prefixWord ++ tailWord_8226046) baseStart_8226046 baseEnd_8226046 := by
    simpa [prefixWord, tailWord_8226046, baseEnd_8226046] using wordTrace_append hprefix tailTrace_8226046
  have hstable : (prefixWord ++ tailWord_8226046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226046).length < 2 ^ (prefixWord ++ tailWord_8226046).sum := by decide
  have hdescent : baseEnd_8226046 < baseStart_8226046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226059 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 7]
def baseStart_8226059 : Nat := 118140960795 + 8226059 * 2 ^ 59
def prefixEnd_8226059 : Nat := 4983230072969 + 3 ^ 40 * 8226059 * 2
def baseEnd_8226059 : Nat := 469324684360392915559061

theorem tailTrace_8226059 : CollatzResearch.WordTrace tailWord_8226059 prefixEnd_8226059 469324684360392915559061 := by
  unfold tailWord_8226059
  simp only [CollatzResearch.WordTrace]
  refine ⟨300029020105400616872585231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200019346736933744581723487 300029020105400616872585231)
  ·
    refine ⟨450043530158100925308877847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300029020105400616872585231 450043530158100925308877847)
    ·
      refine ⟨675065295237151387963316771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450043530158100925308877847 675065295237151387963316771)
      ·
        refine ⟨1012597942855727081944975157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675065295237151387963316771 1012597942855727081944975157)
        ·
          refine ⟨94931057142724413932341421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1012597942855727081944975157 94931057142724413932341421)
          ·
            refine ⟨35599146428521655224628033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94931057142724413932341421 35599146428521655224628033)
            ·
              refine ⟨26699359821391241418471025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35599146428521655224628033 26699359821391241418471025)
              ·
                refine ⟨20024519866043431063853269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26699359821391241418471025 20024519866043431063853269)
                ·
                  refine ⟨469324684360392915559061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20024519866043431063853269 469324684360392915559061)
                  ·
                    rfl

theorem cell23_8226059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 7].length) (baseStart_8226059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226059 prefixEnd_8226059 := by exact prefixLift 8226059
  have htrace : WordTrace (prefixWord ++ tailWord_8226059) baseStart_8226059 baseEnd_8226059 := by
    simpa [prefixWord, tailWord_8226059, baseEnd_8226059] using wordTrace_append hprefix tailTrace_8226059
  have hstable : (prefixWord ++ tailWord_8226059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226059).length < 2 ^ (prefixWord ++ tailWord_8226059).sum := by decide
  have hdescent : baseEnd_8226059 < baseStart_8226059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226093 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 7]
def baseStart_8226093 : Nat := 118140960795 + 8226093 * 2 ^ 59
def prefixEnd_8226093 : Nat := 4983230072969 + 3 ^ 40 * 8226093 * 2
def baseEnd_8226093 : Nat := 469326624176198789667377

theorem tailTrace_8226093 : CollatzResearch.WordTrace tailWord_8226093 prefixEnd_8226093 469326624176198789667377 := by
  unfold tailWord_8226093
  simp only [CollatzResearch.WordTrace]
  refine ⟨300030260187277440679322933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200020173458184960452881955 300030260187277440679322933)
  ·
    refine ⟨28127836892557260063686525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300030260187277440679322933 28127836892557260063686525)
    ·
      refine ⟨10547938834708972523882447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28127836892557260063686525 10547938834708972523882447)
      ·
        refine ⟨15821908252063458785823671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10547938834708972523882447 15821908252063458785823671)
        ·
          refine ⟨23732862378095188178735507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15821908252063458785823671 23732862378095188178735507)
          ·
            refine ⟨35599293567142782268103261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23732862378095188178735507 35599293567142782268103261)
            ·
              refine ⟨13349735087678543350538723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35599293567142782268103261 13349735087678543350538723)
              ·
                refine ⟨20024602631517815025808085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13349735087678543350538723 20024602631517815025808085)
                ·
                  refine ⟨469326624176198789667377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20024602631517815025808085 469326624176198789667377)
                  ·
                    rfl

theorem cell23_8226093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_8226093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226093 prefixEnd_8226093 := by exact prefixLift 8226093
  have htrace : WordTrace (prefixWord ++ tailWord_8226093) baseStart_8226093 baseEnd_8226093 := by
    simpa [prefixWord, tailWord_8226093, baseEnd_8226093] using wordTrace_append hprefix tailTrace_8226093
  have hstable : (prefixWord ++ tailWord_8226093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226093).length < 2 ^ (prefixWord ++ tailWord_8226093).sum := by decide
  have hdescent : baseEnd_8226093 < baseStart_8226093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226096 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 2, 5, 2]
def baseStart_8226096 : Nat := 118140960795 + 8226096 * 2 ^ 59
def prefixEnd_8226096 : Nat := 4983230072969 + 3 ^ 40 * 8226096 * 2
def baseEnd_8226096 : Nat := 4223941158027752595268879

theorem tailTrace_8226096 : CollatzResearch.WordTrace tailWord_8226096 prefixEnd_8226096 4223941158027752595268879 := by
  unfold tailWord_8226096
  simp only [CollatzResearch.WordTrace]
  refine ⟨150015184803133286095841071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200020246404177714794454761 150015184803133286095841071)
  ·
    refine ⟨225022777204699929143761607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150015184803133286095841071 225022777204699929143761607)
    ·
      refine ⟨337534165807049893715642411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225022777204699929143761607 337534165807049893715642411)
      ·
        refine ⟨506301248710574840573463617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337534165807049893715642411 506301248710574840573463617)
        ·
          refine ⟨379725936532931130430097713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506301248710574840573463617 379725936532931130430097713)
          ·
            refine ⟨284794452399698347822573285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379725936532931130430097713 284794452399698347822573285)
            ·
              refine ⟨53398959824943440216732491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284794452399698347822573285 53398959824943440216732491)
              ·
                refine ⟨80098439737415160325098737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53398959824943440216732491 80098439737415160325098737)
                ·
                  refine ⟨60073829803061370243824053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80098439737415160325098737 60073829803061370243824053)
                  ·
                    refine ⟨5631921544037003460358505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60073829803061370243824053 5631921544037003460358505)
                    ·
                      refine ⟨4223941158027752595268879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5631921544037003460358505 4223941158027752595268879)
                      ·
                        rfl

theorem cell23_8226096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 5, 2].length) (baseStart_8226096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226096 prefixEnd_8226096 := by exact prefixLift 8226096
  have htrace : WordTrace (prefixWord ++ tailWord_8226096) baseStart_8226096 baseEnd_8226096 := by
    simpa [prefixWord, tailWord_8226096, baseEnd_8226096] using wordTrace_append hprefix tailTrace_8226096
  have hstable : (prefixWord ++ tailWord_8226096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226096).length < 2 ^ (prefixWord ++ tailWord_8226096).sum := by decide
  have hdescent : baseEnd_8226096 < baseStart_8226096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226099 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 7]
def baseStart_8226099 : Nat := 118140960795 + 8226099 * 2 ^ 59
def prefixEnd_8226099 : Nat := 4983230072969 + 3 ^ 40 * 8226099 * 2
def baseEnd_8226099 : Nat := 4223942698469716083531365

theorem tailTrace_8226099 : CollatzResearch.WordTrace tailWord_8226099 prefixEnd_8226099 4223942698469716083531365 := by
  unfold tailWord_8226099
  simp only [CollatzResearch.WordTrace]
  refine ⟨300030479025255703704041351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200020319350170469136027567 300030479025255703704041351)
  ·
    refine ⟨450045718537883555556062027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300030479025255703704041351 450045718537883555556062027)
    ·
      refine ⟨675068577806825333334093041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450045718537883555556062027 675068577806825333334093041)
      ·
        refine ⟨506301433355119000000569781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675068577806825333334093041 506301433355119000000569781)
        ·
          refine ⟨47465759377042406250053417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 506301433355119000000569781 47465759377042406250053417)
          ·
            refine ⟨35599319532781804687540063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47465759377042406250053417 35599319532781804687540063)
            ·
              refine ⟨53398979299172707031310095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35599319532781804687540063 53398979299172707031310095)
              ·
                refine ⟨80098468948759060546965143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53398979299172707031310095 80098468948759060546965143)
                ·
                  refine ⟨120147703423138590820447715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80098468948759060546965143 120147703423138590820447715)
                  ·
                    refine ⟨180221555134707886230671573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120147703423138590820447715 180221555134707886230671573)
                    ·
                      refine ⟨4223942698469716083531365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180221555134707886230671573 4223942698469716083531365)
                      ·
                        rfl

theorem cell23_8226099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_8226099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226099 prefixEnd_8226099 := by exact prefixLift 8226099
  have htrace : WordTrace (prefixWord ++ tailWord_8226099) baseStart_8226099 baseEnd_8226099 := by
    simpa [prefixWord, tailWord_8226099, baseEnd_8226099] using wordTrace_append hprefix tailTrace_8226099
  have hstable : (prefixWord ++ tailWord_8226099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226099).length < 2 ^ (prefixWord ++ tailWord_8226099).sum := by decide
  have hdescent : baseEnd_8226099 < baseStart_8226099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226146 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_8226146 : Nat := 118140960795 + 8226146 * 2 ^ 59
def prefixEnd_8226146 : Nat := 4983230072969 + 3 ^ 40 * 8226146 * 2
def baseEnd_8226146 : Nat := 4223966832060477399643649

theorem tailTrace_8226146 : CollatzResearch.WordTrace tailWord_8226146 prefixEnd_8226146 4223966832060477399643649 := by
  unfold tailWord_8226146
  simp only [CollatzResearch.WordTrace]
  refine ⟨75008048314021357682750573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200021462170723620487334861 75008048314021357682750573)
  ·
    refine ⟨28128018117758009131031465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75008048314021357682750573 28128018117758009131031465)
    ·
      refine ⟨21096013588318506848273599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28128018117758009131031465 21096013588318506848273599)
      ·
        refine ⟨31644020382477760272410399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21096013588318506848273599 31644020382477760272410399)
        ·
          refine ⟨47466030573716640408615599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31644020382477760272410399 47466030573716640408615599)
          ·
            refine ⟨71199045860574960612923399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47466030573716640408615599 71199045860574960612923399)
            ·
              refine ⟨106798568790862440919385099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71199045860574960612923399 106798568790862440919385099)
              ·
                refine ⟨160197853186293661379077649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106798568790862440919385099 160197853186293661379077649)
                ·
                  refine ⟨120148389889720246034308237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160197853186293661379077649 120148389889720246034308237)
                  ·
                    refine ⟨45055646208645092262865589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120148389889720246034308237 45055646208645092262865589)
                    ·
                      refine ⟨4223966832060477399643649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45055646208645092262865589 4223966832060477399643649)
                      ·
                        rfl

theorem cell23_8226146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_8226146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226146 prefixEnd_8226146 := by exact prefixLift 8226146
  have htrace : WordTrace (prefixWord ++ tailWord_8226146) baseStart_8226146 baseEnd_8226146 := by
    simpa [prefixWord, tailWord_8226146, baseEnd_8226146] using wordTrace_append hprefix tailTrace_8226146
  have hstable : (prefixWord ++ tailWord_8226146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226146).length < 2 ^ (prefixWord ++ tailWord_8226146).sum := by decide
  have hdescent : baseEnd_8226146 < baseStart_8226146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226174 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_8226174 : Nat := 118140960795 + 8226174 * 2 ^ 59
def prefixEnd_8226174 : Nat := 4983230072969 + 3 ^ 40 * 8226174 * 2
def baseEnd_8226174 : Nat := 1407993736506267763364507

theorem tailTrace_8226174 : CollatzResearch.WordTrace tailWord_8226174 prefixEnd_8226174 1407993736506267763364507 := by
  unfold tailWord_8226174
  simp only [CollatzResearch.WordTrace]
  refine ⟨37504151812497998939127697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200022142999989327675347717 37504151812497998939127697)
  ·
    refine ⟨28128113859373499204345773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37504151812497998939127697 28128113859373499204345773)
    ·
      refine ⟨10548042697265062201629665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28128113859373499204345773 10548042697265062201629665)
      ·
        refine ⟨7911032022948796651222249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10548042697265062201629665 7911032022948796651222249)
        ·
          refine ⟨5933274017211597488416687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7911032022948796651222249 5933274017211597488416687)
          ·
            refine ⟨8899911025817396232625031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933274017211597488416687 8899911025817396232625031)
            ·
              refine ⟨13349866538726094348937547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8899911025817396232625031 13349866538726094348937547)
              ·
                refine ⟨20024799808089141523406321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13349866538726094348937547 20024799808089141523406321)
                ·
                  refine ⟨15018599856066856142554741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20024799808089141523406321 15018599856066856142554741)
                  ·
                    refine ⟨1407993736506267763364507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15018599856066856142554741 1407993736506267763364507)
                    ·
                      rfl

theorem cell23_8226174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_8226174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226174 prefixEnd_8226174 := by exact prefixLift 8226174
  have htrace : WordTrace (prefixWord ++ tailWord_8226174) baseStart_8226174 baseEnd_8226174 := by
    simpa [prefixWord, tailWord_8226174, baseEnd_8226174] using wordTrace_append hprefix tailTrace_8226174
  have hstable : (prefixWord ++ tailWord_8226174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226174).length < 2 ^ (prefixWord ++ tailWord_8226174).sum := by decide
  have hdescent : baseEnd_8226174 < baseStart_8226174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226177 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_8226177 : Nat := 118140960795 + 8226177 * 2 ^ 59
def prefixEnd_8226177 : Nat := 4983230072969 + 3 ^ 40 * 8226177 * 2
def baseEnd_8226177 : Nat := 4223982749960766778356007

theorem tailTrace_8226177 : CollatzResearch.WordTrace tailWord_8226177 prefixEnd_8226177 4223982749960766778356007 := by
  unfold tailWord_8226177
  simp only [CollatzResearch.WordTrace]
  refine ⟨300033323918973123025380785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200022215945982082016920523 300033323918973123025380785)
  ·
    refine ⟨225024992939229842269035589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300033323918973123025380785 225024992939229842269035589)
    ·
      refine ⟨42192186176105595425444173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225024992939229842269035589 42192186176105595425444173)
      ·
        refine ⟨15822069816039598284541565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42192186176105595425444173 15822069816039598284541565)
        ·
          refine ⟨5933276181014849356703087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15822069816039598284541565 5933276181014849356703087)
          ·
            refine ⟨8899914271522274035054631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933276181014849356703087 8899914271522274035054631)
            ·
              refine ⟨13349871407283411052581947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8899914271522274035054631 13349871407283411052581947)
              ·
                refine ⟨20024807110925116578872921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13349871407283411052581947 20024807110925116578872921)
                ·
                  refine ⟨15018605333193837434154691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20024807110925116578872921 15018605333193837434154691)
                  ·
                    refine ⟨22527907999790756151232037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15018605333193837434154691 22527907999790756151232037)
                    ·
                      refine ⟨4223982749960766778356007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22527907999790756151232037 4223982749960766778356007)
                      ·
                        rfl

theorem cell23_8226177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_8226177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226177 prefixEnd_8226177 := by exact prefixLift 8226177
  have htrace : WordTrace (prefixWord ++ tailWord_8226177) baseStart_8226177 baseEnd_8226177 := by
    simpa [prefixWord, tailWord_8226177, baseEnd_8226177] using wordTrace_append hprefix tailTrace_8226177
  have hstable : (prefixWord ++ tailWord_8226177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226177).length < 2 ^ (prefixWord ++ tailWord_8226177).sum := by decide
  have hdescent : baseEnd_8226177 < baseStart_8226177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226180 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_8226180 : Nat := 118140960795 + 8226180 * 2 ^ 59
def prefixEnd_8226180 : Nat := 4983230072969 + 3 ^ 40 * 8226180 * 2
def baseEnd_8226180 : Nat := 4223984290402730266618493

theorem tailTrace_8226180 : CollatzResearch.WordTrace tailWord_8226180 prefixEnd_8226180 4223984290402730266618493 := by
  unfold tailWord_8226180
  simp only [CollatzResearch.WordTrace]
  refine ⟨150016716668981127268869997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200022288891974836358493329 150016716668981127268869997)
  ·
    refine ⟨56256268750867922725826249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150016716668981127268869997 56256268750867922725826249)
    ·
      refine ⟨42192201563150942044369687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56256268750867922725826249 42192201563150942044369687)
      ·
        refine ⟨63288302344726413066554531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42192201563150942044369687 63288302344726413066554531)
        ·
          refine ⟨94932453517089619599831797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63288302344726413066554531 94932453517089619599831797)
          ·
            refine ⟨8899917517227151837484231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94932453517089619599831797 8899917517227151837484231)
            ·
              refine ⟨13349876275840727756226347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8899917517227151837484231 13349876275840727756226347)
              ·
                refine ⟨20024814413761091634339521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13349876275840727756226347 20024814413761091634339521)
                ·
                  refine ⟨15018610810320818725754641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20024814413761091634339521 15018610810320818725754641)
                  ·
                    refine ⟨11263958107740614044315981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15018610810320818725754641 11263958107740614044315981)
                    ·
                      refine ⟨4223984290402730266618493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11263958107740614044315981 4223984290402730266618493)
                      ·
                        rfl

theorem cell23_8226180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_8226180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226180 prefixEnd_8226180 := by exact prefixLift 8226180
  have htrace : WordTrace (prefixWord ++ tailWord_8226180) baseStart_8226180 baseEnd_8226180 := by
    simpa [prefixWord, tailWord_8226180, baseEnd_8226180] using wordTrace_append hprefix tailTrace_8226180
  have hstable : (prefixWord ++ tailWord_8226180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226180).length < 2 ^ (prefixWord ++ tailWord_8226180).sum := by decide
  have hdescent : baseEnd_8226180 < baseStart_8226180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226200 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 6]
def baseStart_8226200 : Nat := 118140960795 + 8226200 * 2 ^ 59
def prefixEnd_8226200 : Nat := 4983230072969 + 3 ^ 40 * 8226200 * 2
def baseEnd_8226200 : Nat := 469332728890646687596489

theorem tailTrace_8226200 : CollatzResearch.WordTrace tailWord_8226200 prefixEnd_8226200 469332728890646687596489 := by
  unfold tailWord_8226200
  simp only [CollatzResearch.WordTrace]
  refine ⟨150017081398944898976734027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200022775198593198635645369 150017081398944898976734027)
  ·
    refine ⟨225025622098417348465101041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150017081398944898976734027 225025622098417348465101041)
    ·
      refine ⟨168769216573813011348825781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225025622098417348465101041 168769216573813011348825781)
      ·
        refine ⟨15822114053794969813952417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168769216573813011348825781 15822114053794969813952417)
        ·
          refine ⟨11866585540346227360464313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15822114053794969813952417 11866585540346227360464313)
          ·
            refine ⟨8899939155259670520348235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11866585540346227360464313 8899939155259670520348235)
            ·
              refine ⟨13349908732889505780522353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8899939155259670520348235 13349908732889505780522353)
              ·
                refine ⟨10012431549667129335391765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13349908732889505780522353 10012431549667129335391765)
                ·
                  refine ⟨469332728890646687596489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10012431549667129335391765 469332728890646687596489)
                  ·
                    rfl

theorem cell23_8226200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 6].length) (baseStart_8226200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226200 prefixEnd_8226200 := by exact prefixLift 8226200
  have htrace : WordTrace (prefixWord ++ tailWord_8226200) baseStart_8226200 baseEnd_8226200 := by
    simpa [prefixWord, tailWord_8226200, baseEnd_8226200] using wordTrace_append hprefix tailTrace_8226200
  have hstable : (prefixWord ++ tailWord_8226200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226200).length < 2 ^ (prefixWord ++ tailWord_8226200).sum := by decide
  have hdescent : baseEnd_8226200 < baseStart_8226200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226210 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_8226210 : Nat := 118140960795 + 8226210 * 2 ^ 59
def prefixEnd_8226210 : Nat := 4983230072969 + 3 ^ 40 * 8226210 * 2
def baseEnd_8226210 : Nat := 4223999694822365149243355

theorem tailTrace_8226210 : CollatzResearch.WordTrace tailWord_8226210 prefixEnd_8226210 4223999694822365149243355 := by
  unfold tailWord_8226210
  simp only [CollatzResearch.WordTrace]
  refine ⟨75008631881963392415333021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200023018351902379774221389 75008631881963392415333021)
  ·
    refine ⟨28128236955736272155749883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75008631881963392415333021 28128236955736272155749883)
    ·
      refine ⟨42192355433604408233624825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28128236955736272155749883 42192355433604408233624825)
      ·
        refine ⟨31644266575203306175218619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42192355433604408233624825 31644266575203306175218619)
        ·
          refine ⟨47466399862804959262827929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31644266575203306175218619 47466399862804959262827929)
          ·
            refine ⟨35599799897103719447120947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47466399862804959262827929 35599799897103719447120947)
            ·
              refine ⟨53399699845655579170681421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35599799897103719447120947 53399699845655579170681421)
              ·
                refine ⟨20024887442120842189005533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53399699845655579170681421 20024887442120842189005533)
                ·
                  refine ⟨7509332790795315820877075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20024887442120842189005533 7509332790795315820877075)
                  ·
                    refine ⟨11263999186192973731315613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7509332790795315820877075 11263999186192973731315613)
                    ·
                      refine ⟨4223999694822365149243355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11263999186192973731315613 4223999694822365149243355)
                      ·
                        rfl

theorem cell23_8226210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_8226210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226210 prefixEnd_8226210 := by exact prefixLift 8226210
  have htrace : WordTrace (prefixWord ++ tailWord_8226210) baseStart_8226210 baseEnd_8226210 := by
    simpa [prefixWord, tailWord_8226210, baseEnd_8226210] using wordTrace_append hprefix tailTrace_8226210
  have hstable : (prefixWord ++ tailWord_8226210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226210).length < 2 ^ (prefixWord ++ tailWord_8226210).sum := by decide
  have hdescent : baseEnd_8226210 < baseStart_8226210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226226 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_8226226 : Nat := 118140960795 + 8226226 * 2 ^ 59
def prefixEnd_8226226 : Nat := 4983230072969 + 3 ^ 40 * 8226226 * 2
def baseEnd_8226226 : Nat := 1408002636837612362214427

theorem tailTrace_8226226 : CollatzResearch.WordTrace tailWord_8226226 prefixEnd_8226226 1408002636837612362214427 := by
  unfold tailWord_8226226
  simp only [CollatzResearch.WordTrace]
  refine ⟨75008777773948901098478633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200023407397197069595943021 75008777773948901098478633)
  ·
    refine ⟨56256583330461675823858975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75008777773948901098478633 56256583330461675823858975)
    ·
      refine ⟨84384874995692513735788463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56256583330461675823858975 84384874995692513735788463)
      ·
        refine ⟨126577312493538770603682695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84384874995692513735788463 126577312493538770603682695)
        ·
          refine ⟨189865968740308155905524043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126577312493538770603682695 189865968740308155905524043)
          ·
            refine ⟨284798953110462233858286065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189865968740308155905524043 284798953110462233858286065)
            ·
              refine ⟨213599214832846675393714549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284798953110462233858286065 213599214832846675393714549)
              ·
                refine ⟨20024926390579375818160739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213599214832846675393714549 20024926390579375818160739)
                ·
                  refine ⟨30037389585869063727241109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20024926390579375818160739 30037389585869063727241109)
                  ·
                    refine ⟨1408002636837612362214427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30037389585869063727241109 1408002636837612362214427)
                    ·
                      rfl

theorem cell23_8226226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_8226226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226226 prefixEnd_8226226 := by exact prefixLift 8226226
  have htrace : WordTrace (prefixWord ++ tailWord_8226226) baseStart_8226226 baseEnd_8226226 := by
    simpa [prefixWord, tailWord_8226226, baseEnd_8226226] using wordTrace_append hprefix tailTrace_8226226
  have hstable : (prefixWord ++ tailWord_8226226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226226).length < 2 ^ (prefixWord ++ tailWord_8226226).sum := by decide
  have hdescent : baseEnd_8226226 < baseStart_8226226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226244 : List Nat := [2, 3, 3, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_8226244 : Nat := 118140960795 + 8226244 * 2 ^ 59
def prefixEnd_8226244 : Nat := 4983230072969 + 3 ^ 40 * 8226244 * 2
def baseEnd_8226244 : Nat := 4224017153164618016218199

theorem tailTrace_8226244 : CollatzResearch.WordTrace tailWord_8226244 prefixEnd_8226244 4224017153164618016218199 := by
  unfold tailWord_8226244
  simp only [CollatzResearch.WordTrace]
  refine ⟨150017883804865196734034893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200023845073153595645379857 150017883804865196734034893)
  ·
    refine ⟨56256706426824448775263085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150017883804865196734034893 56256706426824448775263085)
    ·
      refine ⟨21096264910059168290723657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56256706426824448775263085 21096264910059168290723657)
      ·
        refine ⟨15822198682544376218042743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21096264910059168290723657 15822198682544376218042743)
        ·
          refine ⟨23733298023816564327064115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15822198682544376218042743 23733298023816564327064115)
          ·
            refine ⟨35599947035724846490596173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23733298023816564327064115 35599947035724846490596173)
            ·
              refine ⟨13349980138396817433973565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35599947035724846490596173 13349980138396817433973565)
              ·
                refine ⟨5006242551898806537740087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13349980138396817433973565 5006242551898806537740087)
                ·
                  refine ⟨7509363827848209806610131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006242551898806537740087 7509363827848209806610131)
                  ·
                    refine ⟨11264045741772314709915197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7509363827848209806610131 11264045741772314709915197)
                    ·
                      refine ⟨4224017153164618016218199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11264045741772314709915197 4224017153164618016218199)
                      ·
                        rfl

theorem cell23_8226244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_8226244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226244 prefixEnd_8226244 := by exact prefixLift 8226244
  have htrace : WordTrace (prefixWord ++ tailWord_8226244) baseStart_8226244 baseEnd_8226244 := by
    simpa [prefixWord, tailWord_8226244, baseEnd_8226244] using wordTrace_append hprefix tailTrace_8226244
  have hstable : (prefixWord ++ tailWord_8226244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226244).length < 2 ^ (prefixWord ++ tailWord_8226244).sum := by decide
  have hdescent : baseEnd_8226244 < baseStart_8226244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226277 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_8226277 : Nat := 118140960795 + 8226277 * 2 ^ 59
def prefixEnd_8226277 : Nat := 4983230072969 + 3 ^ 40 * 8226277 * 2
def baseEnd_8226277 : Nat := 1408011366008738795701849

theorem tailTrace_8226277 : CollatzResearch.WordTrace tailWord_8226277 prefixEnd_8226277 1408011366008738795701849 := by
  unfold tailWord_8226277
  simp only [CollatzResearch.WordTrace]
  refine ⟨300036971218610840104021085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200024647479073893402680723 300036971218610840104021085)
  ·
    refine ⟨112513864206979065039007907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300036971218610840104021085 112513864206979065039007907)
    ·
      refine ⟨168770796310468597558511861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112513864206979065039007907 168770796310468597558511861)
      ·
        refine ⟨15822262154106431021110487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168770796310468597558511861 15822262154106431021110487)
        ·
          refine ⟨23733393231159646531665731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15822262154106431021110487 23733393231159646531665731)
          ·
            refine ⟨35600089846739469797498597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23733393231159646531665731 35600089846739469797498597)
            ·
              refine ⟨6675016846263650587030987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35600089846739469797498597 6675016846263650587030987)
              ·
                refine ⟨10012525269395475880546481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6675016846263650587030987 10012525269395475880546481)
                ·
                  refine ⟨7509393952046606910409861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10012525269395475880546481 7509393952046606910409861)
                  ·
                    refine ⟨1408011366008738795701849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7509393952046606910409861 1408011366008738795701849)
                    ·
                      rfl

theorem cell23_8226277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_8226277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226277 prefixEnd_8226277 := by exact prefixLift 8226277
  have htrace : WordTrace (prefixWord ++ tailWord_8226277) baseStart_8226277 baseEnd_8226277 := by
    simpa [prefixWord, tailWord_8226277, baseEnd_8226277] using wordTrace_append hprefix tailTrace_8226277
  have hstable : (prefixWord ++ tailWord_8226277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226277).length < 2 ^ (prefixWord ++ tailWord_8226277).sum := by decide
  have hdescent : baseEnd_8226277 < baseStart_8226277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226283 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 3]
def baseStart_8226283 : Nat := 118140960795 + 8226283 * 2 ^ 59
def prefixEnd_8226283 : Nat := 4983230072969 + 3 ^ 40 * 8226283 * 2
def baseEnd_8226283 : Nat := 4224037178910143363630519

theorem tailTrace_8226283 : CollatzResearch.WordTrace tailWord_8226283 prefixEnd_8226283 4224037178910143363630519 := by
  unfold tailWord_8226283
  simp only [CollatzResearch.WordTrace]
  refine ⟨300037190056589103128739503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200024793371059402085826335 300037190056589103128739503)
  ·
    refine ⟨450055785084883654693109255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300037190056589103128739503 450055785084883654693109255)
    ·
      refine ⟨675083677627325482039663883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450055785084883654693109255 675083677627325482039663883)
      ·
        refine ⟨1012625516440988223059495825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675083677627325482039663883 1012625516440988223059495825)
        ·
          refine ⟨759469137330741167294621869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012625516440988223059495825 759469137330741167294621869)
          ·
            refine ⟨284800926499027937735483201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759469137330741167294621869 284800926499027937735483201)
            ·
              refine ⟨213600694874270953301612401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284800926499027937735483201 213600694874270953301612401)
              ·
                refine ⟨160200521155703214976209301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213600694874270953301612401 160200521155703214976209301)
                ·
                  refine ⟨7509399429173588202009811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160200521155703214976209301 7509399429173588202009811)
                  ·
                    refine ⟨11264099143760382303014717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7509399429173588202009811 11264099143760382303014717)
                    ·
                      refine ⟨4224037178910143363630519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11264099143760382303014717 4224037178910143363630519)
                      ·
                        rfl

theorem cell23_8226283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 3].length) (baseStart_8226283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226283 prefixEnd_8226283 := by exact prefixLift 8226283
  have htrace : WordTrace (prefixWord ++ tailWord_8226283) baseStart_8226283 baseEnd_8226283 := by
    simpa [prefixWord, tailWord_8226283, baseEnd_8226283] using wordTrace_append hprefix tailTrace_8226283
  have hstable : (prefixWord ++ tailWord_8226283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226283).length < 2 ^ (prefixWord ++ tailWord_8226283).sum := by decide
  have hdescent : baseEnd_8226283 < baseStart_8226283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226318 : List Nat := [4, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2]
def baseStart_8226318 : Nat := 118140960795 + 8226318 * 2 ^ 59
def prefixEnd_8226318 : Nat := 4983230072969 + 3 ^ 40 * 8226318 * 2
def baseEnd_8226318 : Nat := 4224055150733050726692859

theorem tailTrace_8226318 : CollatzResearch.WordTrace tailWord_8226318 prefixEnd_8226318 4224055150733050726692859 := by
  unfold tailWord_8226318
  simp only [CollatzResearch.WordTrace]
  refine ⟨37504808326432788013282951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200025644407641536070842405 37504808326432788013282951)
  ·
    refine ⟨56257212489649182019924427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37504808326432788013282951 56257212489649182019924427)
    ·
      refine ⟨84385818734473773029886641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56257212489649182019924427 84385818734473773029886641)
      ·
        refine ⟨63289364050855329772414981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84385818734473773029886641 63289364050855329772414981)
        ·
          refine ⟨11866755759535374332327809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63289364050855329772414981 11866755759535374332327809)
          ·
            refine ⟨8900066819651530749245857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11866755759535374332327809 8900066819651530749245857)
            ·
              refine ⟨6675050114738648061934393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8900066819651530749245857 6675050114738648061934393)
              ·
                refine ⟨5006287586053986046450795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6675050114738648061934393 5006287586053986046450795)
                ·
                  refine ⟨7509431379080979069676193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006287586053986046450795 7509431379080979069676193)
                  ·
                    refine ⟨5632073534310734302257145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7509431379080979069676193 5632073534310734302257145)
                    ·
                      refine ⟨4224055150733050726692859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632073534310734302257145 4224055150733050726692859)
                      ·
                        rfl

theorem cell23_8226318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_8226318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226318 prefixEnd_8226318 := by exact prefixLift 8226318
  have htrace : WordTrace (prefixWord ++ tailWord_8226318) baseStart_8226318 baseEnd_8226318 := by
    simpa [prefixWord, tailWord_8226318, baseEnd_8226318] using wordTrace_append hprefix tailTrace_8226318
  have hstable : (prefixWord ++ tailWord_8226318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226318).length < 2 ^ (prefixWord ++ tailWord_8226318).sum := by decide
  have hdescent : baseEnd_8226318 < baseStart_8226318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226333 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_8226333 : Nat := 118140960795 + 8226333 * 2 ^ 59
def prefixEnd_8226333 : Nat := 4983230072969 + 3 ^ 40 * 8226333 * 2
def baseEnd_8226333 : Nat := 1408020950980956056001763

theorem tailTrace_8226333 : CollatzResearch.WordTrace tailWord_8226333 prefixEnd_8226333 1408020950980956056001763 := by
  unfold tailWord_8226333
  simp only [CollatzResearch.WordTrace]
  refine ⟨300039013706407961668059653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200026009137605307778706435 300039013706407961668059653)
  ·
    refine ⟨56257315069951492812761185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300039013706407961668059653 56257315069951492812761185)
    ·
      refine ⟨42192986302463619609570889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56257315069951492812761185 42192986302463619609570889)
      ·
        refine ⟨31644739726847714707178167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42192986302463619609570889 31644739726847714707178167)
        ·
          refine ⟨47467109590271572060767251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31644739726847714707178167 47467109590271572060767251)
          ·
            refine ⟨71200664385407358091150877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47467109590271572060767251 71200664385407358091150877)
            ·
              refine ⟨26700249144527759284181579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71200664385407358091150877 26700249144527759284181579)
              ·
                refine ⟨40050373716791638926272369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26700249144527759284181579 40050373716791638926272369)
                ·
                  refine ⟨30037780287593729194704277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40050373716791638926272369 30037780287593729194704277)
                  ·
                    refine ⟨1408020950980956056001763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30037780287593729194704277 1408020950980956056001763)
                    ·
                      rfl

theorem cell23_8226333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_8226333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226333 prefixEnd_8226333 := by exact prefixLift 8226333
  have htrace : WordTrace (prefixWord ++ tailWord_8226333) baseStart_8226333 baseEnd_8226333 := by
    simpa [prefixWord, tailWord_8226333, baseEnd_8226333] using wordTrace_append hprefix tailTrace_8226333
  have hstable : (prefixWord ++ tailWord_8226333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226333).length < 2 ^ (prefixWord ++ tailWord_8226333).sum := by decide
  have hdescent : baseEnd_8226333 < baseStart_8226333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226373 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_8226373 : Nat := 118140960795 + 8226373 * 2 ^ 59
def prefixEnd_8226373 : Nat := 4983230072969 + 3 ^ 40 * 8226373 * 2
def baseEnd_8226373 : Nat := 4224083392169048011505105

theorem tailTrace_8226373 : CollatzResearch.WordTrace tailWord_8226373 prefixEnd_8226373 4224083392169048011505105 := by
  unfold tailWord_8226373
  simp only [CollatzResearch.WordTrace]
  refine ⟨300040472626263048499515773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200026981750842032333010515 300040472626263048499515773)
  ·
    refine ⟨112515177234848643187318415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300040472626263048499515773 112515177234848643187318415)
    ·
      refine ⟨168772765852272964780977623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112515177234848643187318415 168772765852272964780977623)
      ·
        refine ⟨253159148778409447171466435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168772765852272964780977623 253159148778409447171466435)
        ·
          refine ⟨379738723167614170757199653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253159148778409447171466435 379738723167614170757199653)
          ·
            refine ⟨71201010593927657016974935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379738723167614170757199653 71201010593927657016974935)
            ·
              refine ⟨106801515890891485525462403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71201010593927657016974935 106801515890891485525462403)
              ·
                refine ⟨160202273836337228288193605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106801515890891485525462403 160202273836337228288193605)
                ·
                  refine ⟨30037926344313230304036301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160202273836337228288193605 30037926344313230304036301)
                  ·
                    refine ⟨11264222379117461364013613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30037926344313230304036301 11264222379117461364013613)
                    ·
                      refine ⟨4224083392169048011505105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11264222379117461364013613 4224083392169048011505105)
                      ·
                        rfl

theorem cell23_8226373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_8226373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226373 prefixEnd_8226373 := by exact prefixLift 8226373
  have htrace : WordTrace (prefixWord ++ tailWord_8226373) baseStart_8226373 baseEnd_8226373 := by
    simpa [prefixWord, tailWord_8226373, baseEnd_8226373] using wordTrace_append hprefix tailTrace_8226373
  have hstable : (prefixWord ++ tailWord_8226373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226373).length < 2 ^ (prefixWord ++ tailWord_8226373).sum := by decide
  have hdescent : baseEnd_8226373 < baseStart_8226373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226380 : List Nat := [2, 2, 1, 3, 1, 3, 2, 4, 5]
def baseStart_8226380 : Nat := 118140960795 + 8226380 * 2 ^ 59
def prefixEnd_8226380 : Nat := 4983230072969 + 3 ^ 40 * 8226380 * 2
def baseEnd_8226380 : Nat := 469342998503736609346397

theorem tailTrace_8226380 : CollatzResearch.WordTrace tailWord_8226380 prefixEnd_8226380 469342998503736609346397 := by
  unfold tailWord_8226380
  simp only [CollatzResearch.WordTrace]
  refine ⟨150020363968618844347510297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200027151958158459130013729 150020363968618844347510297)
  ·
    refine ⟨112515272976464133260632723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150020363968618844347510297 112515272976464133260632723)
    ·
      refine ⟨168772909464696199890949085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112515272976464133260632723 168772909464696199890949085)
      ·
        refine ⟨63289841049261074959105907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168772909464696199890949085 63289841049261074959105907)
        ·
          refine ⟨94934761573891612438658861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63289841049261074959105907 94934761573891612438658861)
          ·
            refine ⟨35600535590209354664497073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94934761573891612438658861 35600535590209354664497073)
            ·
              refine ⟨26700401692657015998372805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35600535590209354664497073 26700401692657015998372805)
              ·
                refine ⟨5006325317373190499694901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26700401692657015998372805 5006325317373190499694901)
                ·
                  refine ⟨469342998503736609346397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5006325317373190499694901 469342998503736609346397)
                  ·
                    rfl

theorem cell23_8226380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_8226380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226380 prefixEnd_8226380 := by exact prefixLift 8226380
  have htrace : WordTrace (prefixWord ++ tailWord_8226380) baseStart_8226380 baseEnd_8226380 := by
    simpa [prefixWord, tailWord_8226380, baseEnd_8226380] using wordTrace_append hprefix tailTrace_8226380
  have hstable : (prefixWord ++ tailWord_8226380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226380).length < 2 ^ (prefixWord ++ tailWord_8226380).sum := by decide
  have hdescent : baseEnd_8226380 < baseStart_8226380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226414 : List Nat := [4, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_8226414 : Nat := 118140960795 + 8226414 * 2 ^ 59
def prefixEnd_8226414 : Nat := 4983230072969 + 3 ^ 40 * 8226414 * 2
def baseEnd_8226414 : Nat := 469344938319542483454713

theorem tailTrace_8226414 : CollatzResearch.WordTrace tailWord_8226414 prefixEnd_8226414 469344938319542483454713 := by
  unfold tailWord_8226414
  simp only [CollatzResearch.WordTrace]
  refine ⟨37505246002389314062719787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200027978679409675001172197 37505246002389314062719787)
  ·
    refine ⟨56257869003583971094079681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37505246002389314062719787 56257869003583971094079681)
    ·
      refine ⟨42193401752687978320559761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56257869003583971094079681 42193401752687978320559761)
      ·
        refine ⟨31645051314515983740419821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42193401752687978320559761 31645051314515983740419821)
        ·
          refine ⟨11866894242943493902657433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31645051314515983740419821 11866894242943493902657433)
          ·
            refine ⟨8900170682207620426993075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11866894242943493902657433 8900170682207620426993075)
            ·
              refine ⟨13350256023311430640489613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900170682207620426993075 13350256023311430640489613)
              ·
                refine ⟨5006346008741786490183605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13350256023311430640489613 5006346008741786490183605)
                ·
                  refine ⟨469344938319542483454713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5006346008741786490183605 469344938319542483454713)
                  ·
                    rfl

theorem cell23_8226414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_8226414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226414 prefixEnd_8226414 := by exact prefixLift 8226414
  have htrace : WordTrace (prefixWord ++ tailWord_8226414) baseStart_8226414 baseEnd_8226414 := by
    simpa [prefixWord, tailWord_8226414, baseEnd_8226414] using wordTrace_append hprefix tailTrace_8226414
  have hstable : (prefixWord ++ tailWord_8226414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226414).length < 2 ^ (prefixWord ++ tailWord_8226414).sum := by decide
  have hdescent : baseEnd_8226414 < baseStart_8226414 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226498 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_8226498 : Nat := 118140960795 + 8226498 * 2 ^ 59
def prefixEnd_8226498 : Nat := 4983230072969 + 3 ^ 40 * 8226498 * 2
def baseEnd_8226498 : Nat := 4224147577250860022442031

theorem tailTrace_8226498 : CollatzResearch.WordTrace tailWord_8226498 prefixEnd_8226498 4224147577250860022442031 := by
  unfold tailWord_8226498
  simp only [CollatzResearch.WordTrace]
  refine ⟨75011257937702548711954037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200030021167206796565210765 75011257937702548711954037)
  ·
    refine ⟨7032305431659613941745691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75011257937702548711954037 7032305431659613941745691)
    ·
      refine ⟨10548458147489420912618537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032305431659613941745691 10548458147489420912618537)
      ·
        refine ⟨7911343610617065684463903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10548458147489420912618537 7911343610617065684463903)
        ·
          refine ⟨11867015415925598526695855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7911343610617065684463903 11867015415925598526695855)
          ·
            refine ⟨17800523123888397790043783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11867015415925598526695855 17800523123888397790043783)
            ·
              refine ⟨26700784685832596685065675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17800523123888397790043783 26700784685832596685065675)
              ·
                refine ⟨40051177028748895027598513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26700784685832596685065675 40051177028748895027598513)
                ·
                  refine ⟨30038382771561671270698885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40051177028748895027598513 30038382771561671270698885)
                  ·
                    refine ⟨5632196769667813363256041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30038382771561671270698885 5632196769667813363256041)
                    ·
                      refine ⟨4224147577250860022442031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632196769667813363256041 4224147577250860022442031)
                      ·
                        rfl

theorem cell23_8226498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_8226498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226498 prefixEnd_8226498 := by exact prefixLift 8226498
  have htrace : WordTrace (prefixWord ++ tailWord_8226498) baseStart_8226498 baseEnd_8226498 := by
    simpa [prefixWord, tailWord_8226498, baseEnd_8226498] using wordTrace_append hprefix tailTrace_8226498
  have hstable : (prefixWord ++ tailWord_8226498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226498).length < 2 ^ (prefixWord ++ tailWord_8226498).sum := by decide
  have hdescent : baseEnd_8226498 < baseStart_8226498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226500 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_8226500 : Nat := 118140960795 + 8226500 * 2 ^ 59
def prefixEnd_8226500 : Nat := 4983230072969 + 3 ^ 40 * 8226500 * 2
def baseEnd_8226500 : Nat := 1408049534737389671539007

theorem tailTrace_8226500 : CollatzResearch.WordTrace tailWord_8226500 prefixEnd_8226500 1408049534737389671539007 := by
  unfold tailWord_8226500
  simp only [CollatzResearch.WordTrace]
  refine ⟨150022552348401474594694477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200030069797868632792925969 150022552348401474594694477)
  ·
    refine ⟨56258457130650552973010429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150022552348401474594694477 56258457130650552973010429)
    ·
      refine ⟨21096921423993957364878911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56258457130650552973010429 21096921423993957364878911)
      ·
        refine ⟨31645382135990936047318367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21096921423993957364878911 31645382135990936047318367)
        ·
          refine ⟨47468073203986404070977551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31645382135990936047318367 47468073203986404070977551)
          ·
            refine ⟨71202109805979606106466327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47468073203986404070977551 71202109805979606106466327)
            ·
              refine ⟨106803164708969409159699491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71202109805979606106466327 106803164708969409159699491)
              ·
                refine ⟨160204747063454113739549237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106803164708969409159699491 160204747063454113739549237)
                ·
                  refine ⟨15019195037198823163082741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160204747063454113739549237 15019195037198823163082741)
                  ·
                    refine ⟨1408049534737389671539007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15019195037198823163082741 1408049534737389671539007)
                    ·
                      rfl

theorem cell23_8226500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_8226500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226500 prefixEnd_8226500 := by exact prefixLift 8226500
  have htrace : WordTrace (prefixWord ++ tailWord_8226500) baseStart_8226500 baseEnd_8226500 := by
    simpa [prefixWord, tailWord_8226500, baseEnd_8226500] using wordTrace_append hprefix tailTrace_8226500
  have hstable : (prefixWord ++ tailWord_8226500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226500).length < 2 ^ (prefixWord ++ tailWord_8226500).sum := by decide
  have hdescent : baseEnd_8226500 < baseStart_8226500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226514 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_8226514 : Nat := 118140960795 + 8226514 * 2 ^ 59
def prefixEnd_8226514 : Nat := 4983230072969 + 3 ^ 40 * 8226514 * 2
def baseEnd_8226514 : Nat := 4224155792941331959841957

theorem tailTrace_8226514 : CollatzResearch.WordTrace tailWord_8226514 prefixEnd_8226514 4224155792941331959841957 := by
  unfold tailWord_8226514
  simp only [CollatzResearch.WordTrace]
  refine ⟨75011403829688057395099649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200030410212501486386932397 75011403829688057395099649)
  ·
    refine ⟨56258552872266043046324737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75011403829688057395099649 56258552872266043046324737)
    ·
      refine ⟨42193914654199532284743553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56258552872266043046324737 42193914654199532284743553)
      ·
        refine ⟨31645435990649649213557665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42193914654199532284743553 31645435990649649213557665)
        ·
          refine ⟨23734076992987236910168249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31645435990649649213557665 23734076992987236910168249)
          ·
            refine ⟨17800557744740427682626187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23734076992987236910168249 17800557744740427682626187)
            ·
              refine ⟨26700836617110641523939281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17800557744740427682626187 26700836617110641523939281)
              ·
                refine ⟨20025627462832981142954461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26700836617110641523939281 20025627462832981142954461)
                ·
                  refine ⟨7509610298562367928607923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20025627462832981142954461 7509610298562367928607923)
                  ·
                    refine ⟨11264415447843551892911885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7509610298562367928607923 11264415447843551892911885)
                    ·
                      refine ⟨4224155792941331959841957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11264415447843551892911885 4224155792941331959841957)
                      ·
                        rfl

theorem cell23_8226514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_8226514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226514 prefixEnd_8226514 := by exact prefixLift 8226514
  have htrace : WordTrace (prefixWord ++ tailWord_8226514) baseStart_8226514 baseEnd_8226514 := by
    simpa [prefixWord, tailWord_8226514, baseEnd_8226514] using wordTrace_append hprefix tailTrace_8226514
  have hstable : (prefixWord ++ tailWord_8226514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226514).length < 2 ^ (prefixWord ++ tailWord_8226514).sum := by decide
  have hdescent : baseEnd_8226514 < baseStart_8226514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226518 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_8226518 : Nat := 118140960795 + 8226518 * 2 ^ 59
def prefixEnd_8226518 : Nat := 4983230072969 + 3 ^ 40 * 8226518 * 2
def baseEnd_8226518 : Nat := 4224157846863949944191939

theorem tailTrace_8226518 : CollatzResearch.WordTrace tailWord_8226518 prefixEnd_8226518 4224157846863949944191939 := by
  unfold tailWord_8226518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18752860075671108641471513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200030507473825158842362805 18752860075671108641471513)
  ·
    refine ⟨14064645056753331481103635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18752860075671108641471513 14064645056753331481103635)
    ·
      refine ⟨21096967585129997221655453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14064645056753331481103635 21096967585129997221655453)
      ·
        refine ⟨7911362844423748958120795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21096967585129997221655453 7911362844423748958120795)
        ·
          refine ⟨11867044266635623437181193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7911362844423748958120795 11867044266635623437181193)
          ·
            refine ⟨8900283199976717577885895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11867044266635623437181193 8900283199976717577885895)
            ·
              refine ⟨13350424799965076366828843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900283199976717577885895 13350424799965076366828843)
              ·
                refine ⟨20025637199947614550243265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13350424799965076366828843 20025637199947614550243265)
                ·
                  refine ⟨15019227899960710912682449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20025637199947614550243265 15019227899960710912682449)
                  ·
                    refine ⟨11264420924970533184511837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15019227899960710912682449 11264420924970533184511837)
                    ·
                      refine ⟨4224157846863949944191939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11264420924970533184511837 4224157846863949944191939)
                      ·
                        rfl

theorem cell23_8226518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_8226518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226518 prefixEnd_8226518 := by exact prefixLift 8226518
  have htrace : WordTrace (prefixWord ++ tailWord_8226518) baseStart_8226518 baseEnd_8226518 := by
    simpa [prefixWord, tailWord_8226518, baseEnd_8226518] using wordTrace_append hprefix tailTrace_8226518
  have hstable : (prefixWord ++ tailWord_8226518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226518).length < 2 ^ (prefixWord ++ tailWord_8226518).sum := by decide
  have hdescent : baseEnd_8226518 < baseStart_8226518 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226520 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_8226520 : Nat := 118140960795 + 8226520 * 2 ^ 59
def prefixEnd_8226520 : Nat := 4983230072969 + 3 ^ 40 * 8226520 * 2
def baseEnd_8226520 : Nat := 4224158873825258936366929

theorem tailTrace_8226520 : CollatzResearch.WordTrace tailWord_8226520 prefixEnd_8226520 4224158873825258936366929 := by
  unfold tailWord_8226520
  simp only [CollatzResearch.WordTrace]
  refine ⟨150022917078365246302558507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200030556104486995070078009 150022917078365246302558507)
  ·
    refine ⟨225034375617547869453837761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150022917078365246302558507 225034375617547869453837761)
    ·
      refine ⟨168775781713160902090378321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225034375617547869453837761 168775781713160902090378321)
      ·
        refine ⟨126581836284870676567783741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168775781713160902090378321 126581836284870676567783741)
        ·
          refine ⟨47468188606826503712918903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126581836284870676567783741 47468188606826503712918903)
          ·
            refine ⟨71202282910239755569378355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47468188606826503712918903 71202282910239755569378355)
            ·
              refine ⟨106803424365359633354067533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71202282910239755569378355 106803424365359633354067533)
              ·
                refine ⟨40051284137009862507775325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106803424365359633354067533 40051284137009862507775325)
                ·
                  refine ⟨15019231551378698440415747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40051284137009862507775325 15019231551378698440415747)
                  ·
                    refine ⟨22528847327068047660623621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15019231551378698440415747 22528847327068047660623621)
                    ·
                      refine ⟨4224158873825258936366929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22528847327068047660623621 4224158873825258936366929)
                      ·
                        rfl

theorem cell23_8226520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_8226520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226520 prefixEnd_8226520 := by exact prefixLift 8226520
  have htrace : WordTrace (prefixWord ++ tailWord_8226520) baseStart_8226520 baseEnd_8226520 := by
    simpa [prefixWord, tailWord_8226520, baseEnd_8226520] using wordTrace_append hprefix tailTrace_8226520
  have hstable : (prefixWord ++ tailWord_8226520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226520).length < 2 ^ (prefixWord ++ tailWord_8226520).sum := by decide
  have hdescent : baseEnd_8226520 < baseStart_8226520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226537 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 7, 2, 2]
def baseStart_8226537 : Nat := 118140960795 + 8226537 * 2 ^ 59
def prefixEnd_8226537 : Nat := 4983230072969 + 3 ^ 40 * 8226537 * 2
def baseEnd_8226537 : Nat := 4224167602996385369854351

theorem tailTrace_8226537 : CollatzResearch.WordTrace tailWord_8226537 prefixEnd_8226537 4224167602996385369854351 := by
  unfold tailWord_8226537
  simp only [CollatzResearch.WordTrace]
  refine ⟨300046454197668904508485865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200030969465112603005657243 300046454197668904508485865)
  ·
    refine ⟨225034840648251678381364399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300046454197668904508485865 225034840648251678381364399)
    ·
      refine ⟨337552260972377517572046599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225034840648251678381364399 337552260972377517572046599)
      ·
        refine ⟨506328391458566276358069899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337552260972377517572046599 506328391458566276358069899)
        ·
          refine ⟨759492587187849414537104849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506328391458566276358069899 759492587187849414537104849)
          ·
            refine ⟨569619440390887060902828637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759492587187849414537104849 569619440390887060902828637)
            ·
              refine ⟨213607290146582647838560739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569619440390887060902828637 213607290146582647838560739)
              ·
                refine ⟨320410935219873971757841109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213607290146582647838560739 320410935219873971757841109)
                ·
                  refine ⟨7509631294215796213074401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 320410935219873971757841109 7509631294215796213074401)
                  ·
                    refine ⟨5632223470661847159805801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7509631294215796213074401 5632223470661847159805801)
                    ·
                      refine ⟨4224167602996385369854351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632223470661847159805801 4224167602996385369854351)
                      ·
                        rfl

theorem cell23_8226537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 2, 2].length) (baseStart_8226537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226537 prefixEnd_8226537 := by exact prefixLift 8226537
  have htrace : WordTrace (prefixWord ++ tailWord_8226537) baseStart_8226537 baseEnd_8226537 := by
    simpa [prefixWord, tailWord_8226537, baseEnd_8226537] using wordTrace_append hprefix tailTrace_8226537
  have hstable : (prefixWord ++ tailWord_8226537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226537).length < 2 ^ (prefixWord ++ tailWord_8226537).sum := by decide
  have hdescent : baseEnd_8226537 < baseStart_8226537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226543 : List Nat := [1, 1, 2, 1, 5, 1, 12]
def baseStart_8226543 : Nat := 118140960795 + 8226543 * 2 ^ 59
def prefixEnd_8226543 : Nat := 4983230072969 + 3 ^ 40 * 8226543 * 2
def baseEnd_8226543 : Nat := 52150255356547066004683

theorem tailTrace_8226543 : CollatzResearch.WordTrace tailWord_8226543 prefixEnd_8226543 52150255356547066004683 := by
  unfold tailWord_8226543
  simp only [CollatzResearch.WordTrace]
  refine ⟨300046673035647167533204283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200031115357098111688802855 300046673035647167533204283)
  ·
    refine ⟨450070009553470751299806425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300046673035647167533204283 450070009553470751299806425)
    ·
      refine ⟨337552507165103063474854819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450070009553470751299806425 337552507165103063474854819)
      ·
        refine ⟨506328760747654595212282229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337552507165103063474854819 506328760747654595212282229)
        ·
          refine ⟨47468321320092618301151459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 506328760747654595212282229 47468321320092618301151459)
          ·
            refine ⟨71202481980138927451727189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47468321320092618301151459 71202481980138927451727189)
            ·
              refine ⟨52150255356547066004683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 71202481980138927451727189 52150255356547066004683)
              ·
                rfl

theorem cell23_8226543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 12].length) (baseStart_8226543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226543 prefixEnd_8226543 := by exact prefixLift 8226543
  have htrace : WordTrace (prefixWord ++ tailWord_8226543) baseStart_8226543 baseEnd_8226543 := by
    simpa [prefixWord, tailWord_8226543, baseEnd_8226543] using wordTrace_append hprefix tailTrace_8226543
  have hstable : (prefixWord ++ tailWord_8226543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226543).length < 2 ^ (prefixWord ++ tailWord_8226543).sum := by decide
  have hdescent : baseEnd_8226543 < baseStart_8226543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226547 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 2, 4]
def baseStart_8226547 : Nat := 118140960795 + 8226547 * 2 ^ 59
def prefixEnd_8226547 : Nat := 4983230072969 + 3 ^ 40 * 8226547 * 2
def baseEnd_8226547 : Nat := 1408057579267643443576435

theorem tailTrace_8226547 : CollatzResearch.WordTrace tailWord_8226547 prefixEnd_8226547 1408057579267643443576435 := by
  unfold tailWord_8226547
  simp only [CollatzResearch.WordTrace]
  refine ⟨300046818927632676216349895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200031212618421784144233263 300046818927632676216349895)
  ·
    refine ⟨450070228391449014324524843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300046818927632676216349895 450070228391449014324524843)
    ·
      refine ⟨675105342587173521486787265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450070228391449014324524843 675105342587173521486787265)
      ·
        refine ⟨506329006940380141115090449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675105342587173521486787265 506329006940380141115090449)
        ·
          refine ⟨379746755205285105836317837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506329006940380141115090449 379746755205285105836317837)
          ·
            refine ⟨142405033201981914688619189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379746755205285105836317837 142405033201981914688619189)
            ·
              refine ⟨13350471862685804502058049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142405033201981914688619189 13350471862685804502058049)
              ·
                refine ⟨10012853897014353376543537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13350471862685804502058049 10012853897014353376543537)
                ·
                  refine ⟨7509640422760765032407653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10012853897014353376543537 7509640422760765032407653)
                  ·
                    refine ⟨1408057579267643443576435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7509640422760765032407653 1408057579267643443576435)
                    ·
                      rfl

theorem cell23_8226547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 4].length) (baseStart_8226547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226547 prefixEnd_8226547 := by exact prefixLift 8226547
  have htrace : WordTrace (prefixWord ++ tailWord_8226547) baseStart_8226547 baseEnd_8226547 := by
    simpa [prefixWord, tailWord_8226547, baseEnd_8226547] using wordTrace_append hprefix tailTrace_8226547
  have hstable : (prefixWord ++ tailWord_8226547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226547).length < 2 ^ (prefixWord ++ tailWord_8226547).sum := by decide
  have hdescent : baseEnd_8226547 < baseStart_8226547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226548 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_8226548 : Nat := 118140960795 + 8226548 * 2 ^ 59
def prefixEnd_8226548 : Nat := 4983230072969 + 3 ^ 40 * 8226548 * 2
def baseEnd_8226548 : Nat := 4224173251283584826816801

theorem tailTrace_8226548 : CollatzResearch.WordTrace tailWord_8226548 prefixEnd_8226548 4224173251283584826816801 := by
  unfold tailWord_8226548
  simp only [CollatzResearch.WordTrace]
  refine ⟨150023427700314526693568149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200031236933752702258090865 150023427700314526693568149)
  ·
    refine ⟨7032348173452243438761007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150023427700314526693568149 7032348173452243438761007)
    ·
      refine ⟨10548522260178365158141511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032348173452243438761007 10548522260178365158141511)
      ·
        refine ⟨15822783390267547737212267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10548522260178365158141511 15822783390267547737212267)
        ·
          refine ⟨23734175085401321605818401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15822783390267547737212267 23734175085401321605818401)
          ·
            refine ⟨17800631314050991204363801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23734175085401321605818401 17800631314050991204363801)
            ·
              refine ⟨13350473485538243403272851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17800631314050991204363801 13350473485538243403272851)
              ·
                refine ⟨20025710228307365104909277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13350473485538243403272851 20025710228307365104909277)
                ·
                  refine ⟨7509641335615261914340979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20025710228307365104909277 7509641335615261914340979)
                  ·
                    refine ⟨11264462003422892871511469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7509641335615261914340979 11264462003422892871511469)
                    ·
                      refine ⟨4224173251283584826816801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11264462003422892871511469 4224173251283584826816801)
                      ·
                        rfl

theorem cell23_8226548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_8226548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226548 prefixEnd_8226548 := by exact prefixLift 8226548
  have htrace : WordTrace (prefixWord ++ tailWord_8226548) baseStart_8226548 baseEnd_8226548 := by
    simpa [prefixWord, tailWord_8226548, baseEnd_8226548] using wordTrace_append hprefix tailTrace_8226548
  have hstable : (prefixWord ++ tailWord_8226548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226548).length < 2 ^ (prefixWord ++ tailWord_8226548).sum := by decide
  have hdescent : baseEnd_8226548 < baseStart_8226548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226553 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_8226553 : Nat := 118140960795 + 8226553 * 2 ^ 59
def prefixEnd_8226553 : Nat := 4983230072969 + 3 ^ 40 * 8226553 * 2
def baseEnd_8226553 : Nat := 4224175818686857307254277

theorem tailTrace_8226553 : CollatzResearch.WordTrace tailWord_8226553 prefixEnd_8226553 4224175818686857307254277 := by
  unfold tailWord_8226553
  simp only [CollatzResearch.WordTrace]
  refine ⟨300047037765610939241068313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200031358510407292827378875 300047037765610939241068313)
  ·
    refine ⟨225035278324208204430801235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300047037765610939241068313 225035278324208204430801235)
    ·
      refine ⟨337552917486312306646201853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225035278324208204430801235 337552917486312306646201853)
      ·
        refine ⟨126582344057367114992325695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337552917486312306646201853 126582344057367114992325695)
        ·
          refine ⟨189873516086050672488488543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126582344057367114992325695 189873516086050672488488543)
          ·
            refine ⟨284810274129076008732732815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189873516086050672488488543 284810274129076008732732815)
            ·
              refine ⟨427215411193614013099099223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284810274129076008732732815 427215411193614013099099223)
              ·
                refine ⟨640823116790421019648648835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427215411193614013099099223 640823116790421019648648835)
                ·
                  refine ⟨961234675185631529472973253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640823116790421019648648835 961234675185631529472973253)
                  ·
                    refine ⟨180231501597305911776182485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 961234675185631529472973253 180231501597305911776182485)
                    ·
                      refine ⟨4224175818686857307254277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180231501597305911776182485 4224175818686857307254277)
                      ·
                        rfl

theorem cell23_8226553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_8226553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226553 prefixEnd_8226553 := by exact prefixLift 8226553
  have htrace : WordTrace (prefixWord ++ tailWord_8226553) baseStart_8226553 baseEnd_8226553 := by
    simpa [prefixWord, tailWord_8226553, baseEnd_8226553] using wordTrace_append hprefix tailTrace_8226553
  have hstable : (prefixWord ++ tailWord_8226553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226553).length < 2 ^ (prefixWord ++ tailWord_8226553).sum := by decide
  have hdescent : baseEnd_8226553 < baseStart_8226553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226567 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_8226567 : Nat := 118140960795 + 8226567 * 2 ^ 59
def prefixEnd_8226567 : Nat := 4983230072969 + 3 ^ 40 * 8226567 * 2
def baseEnd_8226567 : Nat := 4224183007416020252479213

theorem tailTrace_8226567 : CollatzResearch.WordTrace tailWord_8226567 prefixEnd_8226567 4224183007416020252479213 := by
  unfold tailWord_8226567
  simp only [CollatzResearch.WordTrace]
  refine ⟨300047548387560219632077955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200031698925040146421385303 300047548387560219632077955)
  ·
    refine ⟨450071322581340329448116933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300047548387560219632077955 450071322581340329448116933)
    ·
      refine ⟨84388372984001311771521925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450071322581340329448116933 84388372984001311771521925)
      ·
        refine ⟨15822819934500245957160361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84388372984001311771521925 15822819934500245957160361)
        ·
          refine ⟨11867114950875184467870271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15822819934500245957160361 11867114950875184467870271)
          ·
            refine ⟨17800672426312776701805407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11867114950875184467870271 17800672426312776701805407)
            ·
              refine ⟨26701008639469165052708111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17800672426312776701805407 26701008639469165052708111)
              ·
                refine ⟨40051512959203747579062167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26701008639469165052708111 40051512959203747579062167)
                ·
                  refine ⟨60077269438805621368593251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40051512959203747579062167 60077269438805621368593251)
                  ·
                    refine ⟨90115904158208432052889877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60077269438805621368593251 90115904158208432052889877)
                    ·
                      refine ⟨4224183007416020252479213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90115904158208432052889877 4224183007416020252479213)
                      ·
                        rfl

theorem cell23_8226567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_8226567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226567 prefixEnd_8226567 := by exact prefixLift 8226567
  have htrace : WordTrace (prefixWord ++ tailWord_8226567) baseStart_8226567 baseEnd_8226567 := by
    simpa [prefixWord, tailWord_8226567, baseEnd_8226567] using wordTrace_append hprefix tailTrace_8226567
  have hstable : (prefixWord ++ tailWord_8226567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226567).length < 2 ^ (prefixWord ++ tailWord_8226567).sum := by decide
  have hdescent : baseEnd_8226567 < baseStart_8226567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226620 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_8226620 : Nat := 118140960795 + 8226620 * 2 ^ 59
def prefixEnd_8226620 : Nat := 4983230072969 + 3 ^ 40 * 8226620 * 2
def baseEnd_8226620 : Nat := 1408070073963569515038823

theorem tailTrace_8226620 : CollatzResearch.WordTrace tailWord_8226620 prefixEnd_8226620 1408070073963569515038823 := by
  unfold tailWord_8226620
  simp only [CollatzResearch.WordTrace]
  refine ⟨150024740728184104841878657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200032987637578806455838209 150024740728184104841878657)
  ·
    refine ⟨112518555546138078631408993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150024740728184104841878657 112518555546138078631408993)
    ·
      refine ⟨84388916659603558973556745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112518555546138078631408993 84388916659603558973556745)
      ·
        refine ⟨63291687494702669230167559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84388916659603558973556745 63291687494702669230167559)
        ·
          refine ⟨94937531242054003845251339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63291687494702669230167559 94937531242054003845251339)
          ·
            refine ⟨142406296863081005767877009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94937531242054003845251339 142406296863081005767877009)
            ·
              refine ⟨106804722647310754325907757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142406296863081005767877009 106804722647310754325907757)
              ·
                refine ⟨40051770992741532872215409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106804722647310754325907757 40051770992741532872215409)
                ·
                  refine ⟨30038828244556149654161557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40051770992741532872215409 30038828244556149654161557)
                  ·
                    refine ⟨1408070073963569515038823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30038828244556149654161557 1408070073963569515038823)
                    ·
                      rfl

theorem cell23_8226620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_8226620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226620 prefixEnd_8226620 := by exact prefixLift 8226620
  have htrace : WordTrace (prefixWord ++ tailWord_8226620) baseStart_8226620 baseEnd_8226620 := by
    simpa [prefixWord, tailWord_8226620, baseEnd_8226620] using wordTrace_append hprefix tailTrace_8226620
  have hstable : (prefixWord ++ tailWord_8226620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226620).length < 2 ^ (prefixWord ++ tailWord_8226620).sum := by decide
  have hdescent : baseEnd_8226620 < baseStart_8226620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226621 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_8226621 : Nat := 118140960795 + 8226621 * 2 ^ 59
def prefixEnd_8226621 : Nat := 4983230072969 + 3 ^ 40 * 8226621 * 2
def baseEnd_8226621 : Nat := 4224210735371363041203965

theorem tailTrace_8226621 : CollatzResearch.WordTrace tailWord_8226621 prefixEnd_8226621 4224210735371363041203965 := by
  unfold tailWord_8226621
  simp only [CollatzResearch.WordTrace]
  refine ⟨300049517929364586854543717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200033011952909724569695811 300049517929364586854543717)
  ·
    refine ⟨56259284611755860035226947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300049517929364586854543717 56259284611755860035226947)
    ·
      refine ⟨84388926917633790052840421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56259284611755860035226947 84388926917633790052840421)
      ·
        refine ⟨15822923797056335634907579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84388926917633790052840421 15822923797056335634907579)
        ·
          refine ⟨23734385695584503452361369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15822923797056335634907579 23734385695584503452361369)
          ·
            refine ⟨17800789271688377589271027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23734385695584503452361369 17800789271688377589271027)
            ·
              refine ⟨26701183907532566383906541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17800789271688377589271027 26701183907532566383906541)
              ·
                refine ⟨10012943965324712393964953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26701183907532566383906541 10012943965324712393964953)
                ·
                  refine ⟨7509707973993534295473715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10012943965324712393964953 7509707973993534295473715)
                  ·
                    refine ⟨11264561960990301443210573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7509707973993534295473715 11264561960990301443210573)
                    ·
                      refine ⟨4224210735371363041203965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11264561960990301443210573 4224210735371363041203965)
                      ·
                        rfl

theorem cell23_8226621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_8226621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226621 prefixEnd_8226621 := by exact prefixLift 8226621
  have htrace : WordTrace (prefixWord ++ tailWord_8226621) baseStart_8226621 baseEnd_8226621 := by
    simpa [prefixWord, tailWord_8226621, baseEnd_8226621] using wordTrace_append hprefix tailTrace_8226621
  have hstable : (prefixWord ++ tailWord_8226621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226621).length < 2 ^ (prefixWord ++ tailWord_8226621).sum := by decide
  have hdescent : baseEnd_8226621 < baseStart_8226621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226640 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_8226640 : Nat := 118140960795 + 8226640 * 2 ^ 59
def prefixEnd_8226640 : Nat := 4983230072969 + 3 ^ 40 * 8226640 * 2
def baseEnd_8226640 : Nat := 4224220491503798466866377

theorem tailTrace_8226640 : CollatzResearch.WordTrace tailWord_8226640 prefixEnd_8226640 4224220491503798466866377 := by
  unfold tailWord_8226640
  simp only [CollatzResearch.WordTrace]
  refine ⟨150025105458147876549742687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200033473944197168732990249 150025105458147876549742687)
  ·
    refine ⟨225037658187221814824614031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150025105458147876549742687 225037658187221814824614031)
    ·
      refine ⟨337556487280832722236921047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225037658187221814824614031 337556487280832722236921047)
      ·
        refine ⟨506334730921249083355381571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337556487280832722236921047 506334730921249083355381571)
        ·
          refine ⟨759502096381873625033072357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506334730921249083355381571 759502096381873625033072357)
          ·
            refine ⟨142406643071601304693701067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 759502096381873625033072357 142406643071601304693701067)
            ·
              refine ⟨213609964607401957040551601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142406643071601304693701067 213609964607401957040551601)
              ·
                refine ⟨160207473455551467780413701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213609964607401957040551601 160207473455551467780413701)
                ·
                  refine ⟨30038901272915900208827569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160207473455551467780413701 30038901272915900208827569)
                  ·
                    refine ⟨22529175954686925156620677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30038901272915900208827569 22529175954686925156620677)
                    ·
                      refine ⟨4224220491503798466866377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22529175954686925156620677 4224220491503798466866377)
                      ·
                        rfl

theorem cell23_8226640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_8226640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226640 prefixEnd_8226640 := by exact prefixLift 8226640
  have htrace : WordTrace (prefixWord ++ tailWord_8226640) baseStart_8226640 baseEnd_8226640 := by
    simpa [prefixWord, tailWord_8226640, baseEnd_8226640] using wordTrace_append hprefix tailTrace_8226640
  have hstable : (prefixWord ++ tailWord_8226640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226640).length < 2 ^ (prefixWord ++ tailWord_8226640).sum := by decide
  have hdescent : baseEnd_8226640 < baseStart_8226640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226644 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_8226644 : Nat := 118140960795 + 8226644 * 2 ^ 59
def prefixEnd_8226644 : Nat := 4983230072969 + 3 ^ 40 * 8226644 * 2
def baseEnd_8226644 : Nat := 4224222545426416451216359

theorem tailTrace_8226644 : CollatzResearch.WordTrace tailWord_8226644 prefixEnd_8226644 4224222545426416451216359 := by
  unfold tailWord_8226644
  simp only [CollatzResearch.WordTrace]
  refine ⟨150025178404140630891315493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200033571205520841188420657 150025178404140630891315493)
  ·
    refine ⟨28129720950776368292121655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150025178404140630891315493 28129720950776368292121655)
    ·
      refine ⟨42194581426164552438182483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28129720950776368292121655 42194581426164552438182483)
      ·
        refine ⟨63291872139246828657273725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42194581426164552438182483 63291872139246828657273725)
        ·
          refine ⟨23734452052217560746477647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63291872139246828657273725 23734452052217560746477647)
          ·
            refine ⟨35601678078326341119716471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23734452052217560746477647 35601678078326341119716471)
            ·
              refine ⟨53402517117489511679574707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35601678078326341119716471 53402517117489511679574707)
              ·
                refine ⟨80103775676234267519362061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53402517117489511679574707 80103775676234267519362061)
                ·
                  refine ⟨30038915878587850319760773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80103775676234267519362061 30038915878587850319760773)
                  ·
                    refine ⟨5632296727235221934955145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30038915878587850319760773 5632296727235221934955145)
                    ·
                      refine ⟨4224222545426416451216359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632296727235221934955145 4224222545426416451216359)
                      ·
                        rfl

theorem cell23_8226644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_8226644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226644 prefixEnd_8226644 := by exact prefixLift 8226644
  have htrace : WordTrace (prefixWord ++ tailWord_8226644) baseStart_8226644 baseEnd_8226644 := by
    simpa [prefixWord, tailWord_8226644, baseEnd_8226644] using wordTrace_append hprefix tailTrace_8226644
  have hstable : (prefixWord ++ tailWord_8226644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226644).length < 2 ^ (prefixWord ++ tailWord_8226644).sum := by decide
  have hdescent : baseEnd_8226644 < baseStart_8226644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226678 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_8226678 : Nat := 118140960795 + 8226678 * 2 ^ 59
def prefixEnd_8226678 : Nat := 4983230072969 + 3 ^ 40 * 8226678 * 2
def baseEnd_8226678 : Nat := 4224240003768669318191203

theorem tailTrace_8226678 : CollatzResearch.WordTrace tailWord_8226678 prefixEnd_8226678 4224240003768669318191203 := by
  unfold tailWord_8226678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753224805634880349335543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200034397926772057059579125 18753224805634880349335543)
  ·
    refine ⟨28129837208452320524003315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18753224805634880349335543 28129837208452320524003315)
    ·
      refine ⟨42194755812678480786004973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28129837208452320524003315 42194755812678480786004973)
      ·
        refine ⟨15823033429754430294751865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42194755812678480786004973 15823033429754430294751865)
        ·
          refine ⟨11867275072315822721063899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15823033429754430294751865 11867275072315822721063899)
          ·
            refine ⟨17800912608473734081595849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11867275072315822721063899 17800912608473734081595849)
            ·
              refine ⟨13350684456355300561196887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17800912608473734081595849 13350684456355300561196887)
              ·
                refine ⟨20026026684532950841795331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13350684456355300561196887 20026026684532950841795331)
                ·
                  refine ⟨30039040026799426262692997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20026026684532950841795331 30039040026799426262692997)
                  ·
                    refine ⟨5632320005024892424254937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30039040026799426262692997 5632320005024892424254937)
                    ·
                      refine ⟨4224240003768669318191203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632320005024892424254937 4224240003768669318191203)
                      ·
                        rfl

theorem cell23_8226678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_8226678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226678 prefixEnd_8226678 := by exact prefixLift 8226678
  have htrace : WordTrace (prefixWord ++ tailWord_8226678) baseStart_8226678 baseEnd_8226678 := by
    simpa [prefixWord, tailWord_8226678, baseEnd_8226678] using wordTrace_append hprefix tailTrace_8226678
  have hstable : (prefixWord ++ tailWord_8226678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226678).length < 2 ^ (prefixWord ++ tailWord_8226678).sum := by decide
  have hdescent : baseEnd_8226678 < baseStart_8226678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226687 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 4, 5, 2]
def baseStart_8226687 : Nat := 118140960795 + 8226687 * 2 ^ 59
def prefixEnd_8226687 : Nat := 4983230072969 + 3 ^ 40 * 8226687 * 2
def baseEnd_8226687 : Nat := 4224244625094559782978661

theorem tailTrace_8226687 : CollatzResearch.WordTrace tailWord_8226687 prefixEnd_8226687 4224244625094559782978661 := by
  unfold tailWord_8226687
  simp only [CollatzResearch.WordTrace]
  refine ⟨300051925147125480126446315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200034616764750320084297543 300051925147125480126446315)
  ·
    refine ⟨450077887720688220189669473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300051925147125480126446315 450077887720688220189669473)
    ·
      refine ⟨337558415790516165142252105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450077887720688220189669473 337558415790516165142252105)
      ·
        refine ⟨253168811842887123856689079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337558415790516165142252105 253168811842887123856689079)
        ·
          refine ⟨379753217764330685785033619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253168811842887123856689079 379753217764330685785033619)
          ·
            refine ⟨569629826646496028677550429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379753217764330685785033619 569629826646496028677550429)
            ·
              refine ⟨213611184992436010754081411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569629826646496028677550429 213611184992436010754081411)
              ·
                refine ⟨320416777488654016131122117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213611184992436010754081411 320416777488654016131122117)
                ·
                  refine ⟨60078145779122628024585397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320416777488654016131122117 60078145779122628024585397)
                  ·
                    refine ⟨5632326166792746377304881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60078145779122628024585397 5632326166792746377304881)
                    ·
                      refine ⟨4224244625094559782978661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632326166792746377304881 4224244625094559782978661)
                      ·
                        rfl

theorem cell23_8226687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_8226687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226687 prefixEnd_8226687 := by exact prefixLift 8226687
  have htrace : WordTrace (prefixWord ++ tailWord_8226687) baseStart_8226687 baseEnd_8226687 := by
    simpa [prefixWord, tailWord_8226687, baseEnd_8226687] using wordTrace_append hprefix tailTrace_8226687
  have hstable : (prefixWord ++ tailWord_8226687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226687).length < 2 ^ (prefixWord ++ tailWord_8226687).sum := by decide
  have hdescent : baseEnd_8226687 < baseStart_8226687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226712 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 2, 2, 2]
def baseStart_8226712 : Nat := 118140960795 + 8226712 * 2 ^ 59
def prefixEnd_8226712 : Nat := 4983230072969 + 3 ^ 40 * 8226712 * 2
def baseEnd_8226712 : Nat := 4224257462110922185166047

theorem tailTrace_8226712 : CollatzResearch.WordTrace tailWord_8226712 prefixEnd_8226712 4224257462110922185166047 := by
  unfold tailWord_8226712
  simp only [CollatzResearch.WordTrace]
  refine ⟨150026418486017454698053195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200035224648023272930737593 150026418486017454698053195)
  ·
    refine ⟨225039627729026182047079793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150026418486017454698053195 225039627729026182047079793)
    ·
      refine ⟨168779720796769636535309845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225039627729026182047079793 168779720796769636535309845)
      ·
        refine ⟨7911549412348576712592649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168779720796769636535309845 7911549412348576712592649)
        ·
          refine ⟨5933662059261432534444487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7911549412348576712592649 5933662059261432534444487)
          ·
            refine ⟨8900493088892148801666731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933662059261432534444487 8900493088892148801666731)
            ·
              refine ⟨13350739633338223202500097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900493088892148801666731 13350739633338223202500097)
              ·
                refine ⟨10013054725003667401875073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13350739633338223202500097 10013054725003667401875073)
                ·
                  refine ⟨7509791043752750551406305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10013054725003667401875073 7509791043752750551406305)
                  ·
                    refine ⟨5632343282814562913554729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7509791043752750551406305 5632343282814562913554729)
                    ·
                      refine ⟨4224257462110922185166047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632343282814562913554729 4224257462110922185166047)
                      ·
                        rfl

theorem cell23_8226712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_8226712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226712 prefixEnd_8226712 := by exact prefixLift 8226712
  have htrace : WordTrace (prefixWord ++ tailWord_8226712) baseStart_8226712 baseEnd_8226712 := by
    simpa [prefixWord, tailWord_8226712, baseEnd_8226712] using wordTrace_append hprefix tailTrace_8226712
  have hstable : (prefixWord ++ tailWord_8226712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226712).length < 2 ^ (prefixWord ++ tailWord_8226712).sum := by decide
  have hdescent : baseEnd_8226712 < baseStart_8226712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226778 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_8226778 : Nat := 118140960795 + 8226778 * 2 ^ 59
def prefixEnd_8226778 : Nat := 4983230072969 + 3 ^ 40 * 8226778 * 2
def baseEnd_8226778 : Nat := 1408097117278039642313581

theorem tailTrace_8226778 : CollatzResearch.WordTrace tailWord_8226778 prefixEnd_8226778 1408097117278039642313581 := by
  unfold tailWord_8226778
  simp only [CollatzResearch.WordTrace]
  refine ⟨75013811047448950667002247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200036829459863868445339325 75013811047448950667002247)
  ·
    refine ⟨112520716571173426000503371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75013811047448950667002247 112520716571173426000503371)
    ·
      refine ⟨168781074856760139000755057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112520716571173426000503371 168781074856760139000755057)
      ·
        refine ⟨126585806142570104250566293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168781074856760139000755057 126585806142570104250566293)
        ·
          refine ⟨5933709662932973636745295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126585806142570104250566293 5933709662932973636745295)
          ·
            refine ⟨8900564494399460455117943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933709662932973636745295 8900564494399460455117943)
            ·
              refine ⟨13350846741599190682676915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900564494399460455117943 13350846741599190682676915)
              ·
                refine ⟨20026270112398786024015373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13350846741599190682676915 20026270112398786024015373)
                ·
                  refine ⟨7509851292149544759005765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20026270112398786024015373 7509851292149544759005765)
                  ·
                    refine ⟨1408097117278039642313581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7509851292149544759005765 1408097117278039642313581)
                    ·
                      rfl

theorem cell23_8226778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_8226778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226778 prefixEnd_8226778 := by exact prefixLift 8226778
  have htrace : WordTrace (prefixWord ++ tailWord_8226778) baseStart_8226778 baseEnd_8226778 := by
    simpa [prefixWord, tailWord_8226778, baseEnd_8226778] using wordTrace_append hprefix tailTrace_8226778
  have hstable : (prefixWord ++ tailWord_8226778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226778).length < 2 ^ (prefixWord ++ tailWord_8226778).sum := by decide
  have hdescent : baseEnd_8226778 < baseStart_8226778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226821 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_8226821 : Nat := 118140960795 + 8226821 * 2 ^ 59
def prefixEnd_8226821 : Nat := 4983230072969 + 3 ^ 40 * 8226821 * 2
def baseEnd_8226821 : Nat := 1408104477167420752901015

theorem tailTrace_8226821 : CollatzResearch.WordTrace tailWord_8226821 prefixEnd_8226821 1408104477167420752901015 := by
  unfold tailWord_8226821
  simp only [CollatzResearch.WordTrace]
  refine ⟨300056812528640021011824317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200037875019093347341216211 300056812528640021011824317)
  ·
    refine ⟨112521304698240007879434119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300056812528640021011824317 112521304698240007879434119)
    ·
      refine ⟨168781957047360011819151179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112521304698240007879434119 168781957047360011819151179)
      ·
        refine ⟨253172935571040017728726769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168781957047360011819151179 253172935571040017728726769)
        ·
          refine ⟨189879701678280013296545077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253172935571040017728726769 189879701678280013296545077)
          ·
            refine ⟨17801222032338751246551101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189879701678280013296545077 17801222032338751246551101)
            ·
              refine ⟨6675458262127031717456663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17801222032338751246551101 6675458262127031717456663)
              ·
                refine ⟨10013187393190547576184995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6675458262127031717456663 10013187393190547576184995)
                ·
                  refine ⟨15019781089785821364277493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10013187393190547576184995 15019781089785821364277493)
                  ·
                    refine ⟨1408104477167420752901015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15019781089785821364277493 1408104477167420752901015)
                    ·
                      rfl

theorem cell23_8226821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_8226821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226821 prefixEnd_8226821 := by exact prefixLift 8226821
  have htrace : WordTrace (prefixWord ++ tailWord_8226821) baseStart_8226821 baseEnd_8226821 := by
    simpa [prefixWord, tailWord_8226821, baseEnd_8226821] using wordTrace_append hprefix tailTrace_8226821
  have hstable : (prefixWord ++ tailWord_8226821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226821).length < 2 ^ (prefixWord ++ tailWord_8226821).sum := by decide
  have hdescent : baseEnd_8226821 < baseStart_8226821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226841 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 3, 2, 2]
def baseStart_8226841 : Nat := 118140960795 + 8226841 * 2 ^ 59
def prefixEnd_8226841 : Nat := 4983230072969 + 3 ^ 40 * 8226841 * 2
def baseEnd_8226841 : Nat := 4224323701115352180452953

theorem tailTrace_8226841 : CollatzResearch.WordTrace tailWord_8226841 prefixEnd_8226841 4224323701115352180452953 := by
  unfold tailWord_8226841
  simp only [CollatzResearch.WordTrace]
  refine ⟨300057541988567564427552377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200038361325711709618368251 300057541988567564427552377)
  ·
    refine ⟨225043156491425673320664283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300057541988567564427552377 225043156491425673320664283)
    ·
      refine ⟨337564734737138509980996425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225043156491425673320664283 337564734737138509980996425)
      ·
        refine ⟨253173551052853882485747319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337564734737138509980996425 253173551052853882485747319)
        ·
          refine ⟨379760326579280823728620979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253173551052853882485747319 379760326579280823728620979)
          ·
            refine ⟨569640489868921235592931469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379760326579280823728620979 569640489868921235592931469)
            ·
              refine ⟨213615183700845463347349301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569640489868921235592931469 213615183700845463347349301)
              ·
                refine ⟨20026423471954262188813997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213615183700845463347349301 20026423471954262188813997)
                ·
                  refine ⟨7509908801982848320805249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20026423471954262188813997 7509908801982848320805249)
                  ·
                    refine ⟨5632431601487136240603937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7509908801982848320805249 5632431601487136240603937)
                    ·
                      refine ⟨4224323701115352180452953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632431601487136240603937 4224323701115352180452953)
                      ·
                        rfl

theorem cell23_8226841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_8226841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226841 prefixEnd_8226841 := by exact prefixLift 8226841
  have htrace : WordTrace (prefixWord ++ tailWord_8226841) baseStart_8226841 baseEnd_8226841 := by
    simpa [prefixWord, tailWord_8226841, baseEnd_8226841] using wordTrace_append hprefix tailTrace_8226841
  have hstable : (prefixWord ++ tailWord_8226841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226841).length < 2 ^ (prefixWord ++ tailWord_8226841).sum := by decide
  have hdescent : baseEnd_8226841 < baseStart_8226841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
